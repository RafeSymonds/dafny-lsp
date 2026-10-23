// Runs test/suite.js inside the installed VS Code with an isolated profile.
// Usage: node test/run.js [workspace dir] [profile dir]
// The profile dir path must be short: VS Code puts a socket in it and macOS limits socket paths to 103 bytes.
const path = require('path');
const { runTests } = require('@vscode/test-electron');

async function main() {
  const workspace = path.resolve(process.argv[2] || path.join(__dirname, 'fixture'));
  const scratch = path.resolve(process.argv[3] || path.join(__dirname, '..', '.vscode-test'));
  const code = await runTests({
    vscodeExecutablePath: '/Applications/Visual Studio Code.app/Contents/MacOS/Code',
    extensionDevelopmentPath: path.resolve(__dirname, '..'),
    extensionTestsPath: path.join(__dirname, 'suite.js'),
    launchArgs: [
      workspace,
      '--user-data-dir', path.join(scratch, 'user'),
      '--extensions-dir', path.join(scratch, 'extensions'),
      '--disable-workspace-trust',
      '--skip-welcome',
      '--skip-release-notes',
    ],
    extensionTestsEnv: { DAFNY_TEST_WS: workspace, DAFNY_TEST_OUT: path.join(scratch, 'result.json') },
  });
  console.log(require('fs').readFileSync(path.join(scratch, 'result.json'), 'utf8'));
  return code;
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
