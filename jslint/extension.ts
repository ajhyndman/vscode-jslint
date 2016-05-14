/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import * as path from 'path';
import { workspace, Disposable, ExtensionContext } from 'vscode';
import { LanguageClient, LanguageClientOptions, SettingMonitor, ServerOptions, RequestType, TransportKind } from 'vscode-languageclient';

export function activate(context: ExtensionContext) {

	// We need to go one level up since an extension compile the js code into
	// the output folder.
	let serverModule = path.join(__dirname, '..', 'server', 'server.js');
	let debugOptions = { execArgv: ["--nolazy", "--debug=6004"] };
	let serverOptions: ServerOptions = {
		run: { module: serverModule, transport: TransportKind.ipc },
		debug: { module: serverModule, transport: TransportKind.ipc, options: debugOptions}
	};
	let clientOptions: LanguageClientOptions = {
		documentSelector: ['javascript'],
		synchronize: {
			configurationSection: 'jslint',
			fileEvents: workspace.createFileSystemWatcher('**/jslint.conf')
		}
	}

	let client = new LanguageClient('JSLint Linter', serverOptions, clientOptions);
	context.subscriptions.push(new SettingMonitor(client, 'jslint.enable').start());
}