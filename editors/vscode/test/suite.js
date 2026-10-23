// Exercises the extension through VS Code's provider commands and writes the results to a JSON file.
const fs = require('fs');
const path = require('path');
const vscode = require('vscode');

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

function positionOf(doc, needle, delta = 0) {
  return doc.positionAt(doc.getText().indexOf(needle) + delta);
}

exports.run = async function () {
  const ws = process.env.DAFNY_TEST_WS;
  const result = {};
  try {
    const uri = vscode.Uri.file(path.join(ws, 'main.dfy'));
    const doc = await vscode.workspace.openTextDocument(uri);
    await vscode.window.showTextDocument(doc);
    result.languageId = doc.languageId;

    let diags = [];
    for (let i = 0; i < 150 && diags.length === 0; i++) {
      await sleep(200);
      diags = vscode.languages.getDiagnostics(uri);
    }
    result.diagnostics = diags.map((d) => `${d.range.start.line}: ${d.message}`);

    const twice = positionOf(doc, 'Twice(a)');
    const defs = await vscode.commands.executeCommand('vscode.executeDefinitionProvider', uri, twice);
    result.definition = defs.map((d) => `${path.basename((d.uri || d.targetUri).fsPath)}:${(d.range || d.targetRange).start.line}`);

    const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', uri, twice);
    result.hover = hovers.flatMap((h) => h.contents.map((c) => (typeof c === 'string' ? c : c.value)));

    const sig = await vscode.commands.executeCommand('vscode.executeSignatureHelpProvider', uri, positionOf(doc, 'Abs(3', 4));
    result.signature = sig && sig.signatures.map((s) => s.label);

    const general = await vscode.commands.executeCommand('vscode.executeCompletionItemProvider', uri, positionOf(doc, 'assert t'));
    const labels = general.items.map((i) => (typeof i.label === 'string' ? i.label : i.label.label));
    result.generalCompletionSample = ['a', 't', 'Abs', 'Twice', 'Circle', 'assert'].filter((l) => labels.includes(l));

    const symbols = await vscode.commands.executeCommand('vscode.executeDocumentSymbolProvider', uri);
    result.symbols = symbols.map((s) => `${s.name}[${(s.children || []).map((c) => c.name).join(',')}]`);

    const refs = await vscode.commands.executeCommand('vscode.executeReferenceProvider', uri, positionOf(doc, 'Abs(x'));
    result.references = refs.map((r) => r.range.start.line);

    const commands = await vscode.commands.getCommands(true);
    result.commands = commands.filter((c) => c.startsWith('dafny-lsp.'));
    await vscode.commands.executeCommand('dafny-lsp.verifyFile');
    await sleep(2000);
    result.diagnosticsAfterVerify = vscode.languages.getDiagnostics(uri).map((d) => `${d.range.start.line}: ${d.message}`);
  } catch (err) {
    result.error = String(err && err.stack ? err.stack : err);
  }
  fs.writeFileSync(process.env.DAFNY_TEST_OUT, JSON.stringify(result, null, 2));
};
