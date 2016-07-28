# VS Code JSLint extension

Integrates [JSLint](http://jslint.com/) into VS Code.

## Disable JSLint

In order to disable JSLint for a workspace, specify `"jslint.enable": false` in the workspace settings. JSLint is enabled by default.

## JSLint Version

The VS Code JSLint extension looks for a local or global npm installation of [jslint](https://www.npmjs.com/package/jslint).  This extension supports the `"jslint.version"` setting.  Available versions correspond to the 'editions' supported by your installation of jslint.

### Usage:

* `"jslint.version": "es6"`
* `"jslint.version": "latest"`
* `"jslint.version": "2013-02-03"`
