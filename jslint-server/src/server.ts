/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import {
	createConnection, IConnection,
	ResponseError, RequestType, IRequestHandler, NotificationType, INotificationHandler,
	InitializeParams, InitializeResult, InitializeError,
	DidChangeConfigurationParams, DidChangeWatchedFilesParams,
	Diagnostic, DiagnosticSeverity, Position, Files,
	TextDocuments, ITextDocument,
	ErrorMessageTracker, IPCMessageReader, IPCMessageWriter
} from 'vscode-languageserver';

import fs = require('fs');
import path = require('path');

import * as minimatch from 'minimatch';
import * as _ from 'lodash';

import processIgnoreFile = require('parse-gitignore');


interface JSLintOptions {
	config?: string;
	[key: string]: any;
}

interface FileSettings {
	[pattern: string]: boolean
}

interface JSLintSettings {
	enable: boolean;
	config?: string;
	options: JSLintOptions;
	excludePath?: string;
	exclude: FileSettings;
	version: string;
}

interface Settings {
	jslint: JSLintSettings,
	[key: string]: any;
}

interface JSLintError {
	id: string;
	raw: string;
	code: string;
	line: number;
	character: number;
	scope: string;
	reason: string;
}

interface JSLintUnused {
	name: string;
	line: number;
	character: number;
}

interface JSLintReport {
	options: any;
	errors: JSLintError[];
	unused: JSLintUnused[];
}

interface PackageJSLintConfig {
	jsLintConfig: any;
}

interface JSLINT {
	(content: string, options: any, globals: any): any;
	data: any;
}

function makeDiagnostic(problem: JSLintError): Diagnostic {
	// Setting errors (and potentially global file errors) will report on line zero, char zero.
	// Ensure that the start and end are >=0 (gets dropped by one in the return)
	if (problem.line <= 0) {
		problem.line = 1;
	}
	if (problem.character <= 0) {
		problem.character = 1;
	}
	return {
		message: problem.reason + (problem.code ? ` (${problem.code})` : ''),
		severity: getSeverity(problem),
		source: 'jsLint',
		code: problem.code,
		range: {
			start: { line: problem.line - 1, character: problem.character - 1 },
			end: { line: problem.line - 1, character: problem.character - 1 }
		}
	};
}

function getSeverity(problem: JSLintError): number {
	// If there is no code (that would be very odd) we'll push it as an error as well.
	// See http://jsLint.com/docs/ (search for error. It is only mentioned once.)
	if (!problem.code || problem.code[0] === 'E') {
		return DiagnosticSeverity.Error;
	}
	return DiagnosticSeverity.Warning;
}

function locateFile(directory: string, fileName: string) {
	let parent = directory;
	do {
		directory = parent;
		let location = path.join(directory, fileName);
		if (fs.existsSync(location)) {
			return location;
		}
		parent = path.dirname(directory);
	} while (parent !== directory);
	return undefined;
};

const JSLINTRC = 'jslint.conf';
class OptionsResolver {

	private connection: IConnection;
	private configPath: string;
	private jslintOptions: JSLintOptions;
	private optionsCache: { [key: string]: any };
	private version: string;

	constructor(connection: IConnection) {
		this.connection = connection;
		this.clear();
		this.configPath = null;
		this.jslintOptions = null;
	}

	public setVersion(version: string) {
		this.version = version;
	}

	public getVersion() {
		return this.version;
	}

	public configure(path: string, jslintOptions?: JSLintOptions) {
		this.optionsCache = Object.create(null);
		this.configPath = path;
		this.jslintOptions = jslintOptions;
	}

	public clear(jslintOptions?: JSLintOptions) {
		this.optionsCache = Object.create(null);
	}

	public getOptions(fsPath: string): any {
		let result = this.optionsCache[fsPath];
		if (!result) {
			result = this.readOptions(fsPath);
			this.optionsCache[fsPath] = result;
		}
		return result;
	}

	private readOptions(fsPath: string = null): any {
		let that = this;

		function stripComments(content: string): string {
			/**
			* First capturing group matches double quoted string
			* Second matches single quotes string
			* Third matches block comments
			* Fourth matches line comments
			*/
			var regexp: RegExp = /("(?:[^\\\"]*(?:\\.)?)*")|('(?:[^\\\']*(?:\\.)?)*')|(\/\*(?:\r?\n|.)*?\*\/)|(\/{2,}.*?(?:(?:\r?\n)|$))/g;
			let result = content.replace(regexp, (match, m1, m2, m3, m4) => {
				// Only one of m1, m2, m3, m4 matches
				if (m3) {
					// A block comment. Replace with nothing
					return "";
				} else if (m4) {
					// A line comment. If it ends in \r?\n then keep it.
					let length = m4.length;
					if (length > 2 && m4[length - 1] === '\n') {
						return m4[length - 2] === '\r' ? '\r\n' : '\n';
					} else {
						return "";
					}
				} else {
					// We match a string
					return match;
				}
			});
			return result;
		};

		function readJsonFile(file: string, extendedFrom?: string): any {
			try {
				return JSON.parse(stripComments(fs.readFileSync(file).toString()));
			}
			catch (err) {
				let location = extendedFrom ? `${file} extended from ${extendedFrom}` : file;
				that.connection.window.showErrorMessage(`Can't load JSLint configuration from file ${location}. Please check the file for syntax errors.`);
				return {};
			}
		}

		function readJSLintFile(file: string, extendedFrom?: string): any {
			let content = readJsonFile(file, extendedFrom);
			if (content.extends) {
				let baseFile = path.resolve(path.dirname(file), content.extends);

				if (fs.existsSync(baseFile)) {
					content = _.mergeWith(readJSLintFile(baseFile, file), content, (baseValue, contentValue) => {
						if (_.isArray(baseValue)) {
							return baseValue.concat(contentValue);
						}
					});
				} else {
					that.connection.window.showErrorMessage(`Can't find JSLint file ${baseFile} extended from ${file}`);
				}

				delete content.extends;
			}
			return content;
		}

		function isWindows(): boolean {
			return process.platform === 'win32';
		}

		function getUserHome() {
			return process.env[isWindows() ? 'USERPROFILE' : 'HOME'];
		}

		if (this.configPath && fs.existsSync(this.configPath)) {
			return readJsonFile(this.configPath);
		}

		let jslintOptions = this.jslintOptions;
		// backward compatibility
		if (jslintOptions && jslintOptions.config && fs.existsSync(jslintOptions.config)) {
			return readJsonFile(jslintOptions.config);
		}

		if (fsPath) {
			let packageFile = locateFile(fsPath, 'package.json');
			if (packageFile) {
				let content = readJsonFile(packageFile);
				if (content.jslintConfig) {
					return content.jslintConfig;
				}
			}

			let configFile = locateFile(fsPath, JSLINTRC);
			if (configFile) {
				return readJSLintFile(configFile);
			}
		}

		let home = getUserHome();
		if (home) {
			let file = path.join(home, JSLINTRC);
			if (fs.existsSync(file)) {
				return readJSLintFile(file);
			}
		}
		return jslintOptions;
	}
}

const JSLINTIGNORE = '.jslintignore';
class FileMatcher {
	private configPath: string;
	private defaultExcludePatterns: string[];
	private excludeCache: { [key: string]: any };

	constructor() {
		this.configPath = null;
		this.defaultExcludePatterns = null;
		this.excludeCache = {};
	}

	private pickTrueKeys(obj: FileSettings) {
		return _.keys(_.pickBy(obj, (value) => {
			return value === true;
		}));
	}

	public configure(path: string, exclude?: FileSettings): void {
		this.configPath = path;
		this.excludeCache = {};
		this.defaultExcludePatterns = this.pickTrueKeys(exclude);
	}

	public clear(exclude?: FileSettings): void {
		this.excludeCache = {};
	}

	private relativeTo(fsPath: string, folder: string): string {
		if (folder && 0 === fsPath.indexOf(folder)) {
			let cuttingPoint = folder.length;
			if (cuttingPoint < fsPath.length && '/' === fsPath.charAt(cuttingPoint)) {
				cuttingPoint += 1;
			}
			return fsPath.substr(cuttingPoint);
		}
		return fsPath;
	}

	private folderOf(fsPath: string): string {
		let index = fsPath.lastIndexOf('/');
		return index > -1 ? fsPath.substr(0, index) : fsPath;
	}

	private match(excludePatters: string[], path: string, root: string): boolean {
		let relativePath = this.relativeTo(path, root);
		return _.some(excludePatters, (pattern) => {
			return minimatch(relativePath, pattern);
		});
	};

	public excludes(fsPath: string, root: string): boolean {
		if (fsPath) {

			if (this.excludeCache.hasOwnProperty(fsPath)) {
				return this.excludeCache[fsPath];
			}

			let shouldBeExcluded = false;

			if (this.configPath && fs.existsSync(this.configPath)) {
				shouldBeExcluded = this.match(processIgnoreFile(this.configPath), fsPath, root);
			} else {
				let ignoreFile = locateFile(fsPath, JSLINTIGNORE);
				if (ignoreFile) {
					shouldBeExcluded = this.match(processIgnoreFile(ignoreFile), fsPath, this.folderOf(ignoreFile));
				} else {
					shouldBeExcluded = this.match(this.defaultExcludePatterns, fsPath, root);
				}
			}

			this.excludeCache[fsPath] = shouldBeExcluded;
			return shouldBeExcluded;
		}

		return true;
	}
}

class Linter {
	private connection: IConnection;
	private options: OptionsResolver;
	private fileMatcher: FileMatcher;
	private documents: TextDocuments;

	private workspaceRoot: string;
	private lib: any;

	constructor() {
		this.connection = createConnection(new IPCMessageReader(process), new IPCMessageWriter(process));
		this.options = new OptionsResolver(this.connection);
		this.fileMatcher = new FileMatcher();
		this.documents = new TextDocuments();
		this.documents.onDidChangeContent(event => this.validateSingle(event.document));
		this.documents.listen(this.connection);

		this.connection.onInitialize(params => this.onInitialize(params));
		this.connection.onDidChangeConfiguration(params => {
			let jslintSettings = _.assign<Object, JSLintSettings>({ options: {}, exclude: {} }, (<Settings>params.settings).jslint);
			this.options.configure(jslintSettings.config, jslintSettings.options);
			this.fileMatcher.configure(jslintSettings.excludePath, jslintSettings.exclude);
			this.options.setVersion(jslintSettings.version);
			this.validateAll();
		});
		this.connection.onDidChangeWatchedFiles(params => {
			var needsValidating = false;
			if (params.changes) {
				params.changes.forEach(change => {
					switch (this.lastSegment(change.uri)) {
						case JSLINTRC:
							this.options.clear();
							needsValidating = true;
							break;
						case JSLINTIGNORE:
							this.fileMatcher.clear();
							needsValidating = true;
							break;
					}
				});
			}
			if (needsValidating) {
				this.validateAll();
			}
		})
	}

	public listen(): void {
		this.connection.listen();
	}

	private lastSegment(fsPath: string): string {
		let index = fsPath.lastIndexOf('/');
		return index > -1 ? fsPath.substr(index + 1) : fsPath;
	}

	private onInitialize(params: InitializeParams): Thenable<InitializeResult | ResponseError<InitializeError>> {
		this.workspaceRoot = params.rootPath;
		return Files.resolveModule(this.workspaceRoot, 'jslint').then((value) => {
			console.log(value);
			if (!value.load) {
				return new ResponseError(99, 'The jslint library doesn\'t export a load property.', { retry: false });
			}
			this.lib = value;
			let result: InitializeResult = { capabilities: { textDocumentSync: this.documents.syncKind } };
			return result;
		}, (error) => {
			return Promise.reject(
				new ResponseError<InitializeError>(99,
					'Failed to load jslint library. Please install jslint in your workspace folder using \'npm install jslint\' or globally using \'npm install -g jslint\' and then press Retry.',
					{ retry: true }));
		});
	}

	private validateAll(): void {
		let tracker = new ErrorMessageTracker();
		this.documents.all().forEach(document => {
			try {
				this.validate(document);
			} catch (err) {
				tracker.add(this.getMessage(err, document));
			}
		});
		tracker.sendErrors(this.connection);
	}

	private validateSingle(document: ITextDocument): void {
		try {
			this.validate(document);
		} catch (err) {
			this.connection.window.showErrorMessage(this.getMessage(err, document));
		}
	}


	private lintContent(content: string, fsPath: string): JSLintError[] {
		const JSLINT: JSLINT = this.lib.load('es6');
		const options = this.options.getOptions(fsPath) || {};
		JSLINT(content, options, options.globals || {});
		let output;
		try {
			output = JSLINT.data();
		} catch (err) {
			this.connection.window.showErrorMessage('JSLint library does not export a data() method.  The JSLint verions you are using is probably out of date.');
		}
		const errors = output.warnings.map(function (warning, i) {
			return {
				code: warning.code,
				id: i,
				line: warning.line,
				character: warning.column,
				reason: warning.message,
			};
		});
		return errors;
	}


	private validate(document: ITextDocument) {
		let fsPath = Files.uriToFilePath(document.uri);
		if (!fsPath) {
			fsPath = this.workspaceRoot;
		}

		let diagnostics: Diagnostic[] = [];

		if (!this.fileMatcher.excludes(fsPath, this.workspaceRoot)) {
			let errors = this.lintContent(document.getText(), fsPath);
			if (errors) {
				errors.forEach((error) => {
					// For some reason the errors array contains null.
					if (error) {
						diagnostics.push(makeDiagnostic(error));
					}
				});
			}
		}
		this.connection.sendDiagnostics({ uri: document.uri, diagnostics });
	}

	private getMessage(err: any, document: ITextDocument): string {
		let result: string = null;
		if (typeof err.message === 'string' || err.message instanceof String) {
			result = <string>err.message;
		} else {
			result = `An unknown error occured while validating file: ${Files.uriToFilePath(document.uri)}`;
		}
		return result;
	}
}

new Linter().listen();