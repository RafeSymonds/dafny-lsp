import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { LanguageClient, LanguageClientOptions, ServerOptions } from 'vscode-languageclient/node';

let client: LanguageClient | undefined;
let gutter: Gutter | undefined;

const OFFICIAL_EXTENSION = 'dafny-lang.ide-vscode';

function settings(): Record<string, unknown> {
  const cfg = vscode.workspace.getConfiguration('dafny-lsp');
  return {
    dafnyPath: cfg.get<string>('dafnyPath'),
    verifyOn: cfg.get<string>('verifyOn'),
    debounceMs: cfg.get<number>('debounceMs'),
    verificationTimeLimit: cfg.get<number | null>('verificationTimeLimit'),
    cores: cfg.get<string | null>('cores'),
    extraArgs: cfg.get<string[]>('extraArgs'),
  };
}

function serverPath(context: vscode.ExtensionContext): string {
  const configured = vscode.workspace.getConfiguration('dafny-lsp').get<string>('serverPath');
  if (configured) {
    return configured;
  }
  const bundled = context.asAbsolutePath(path.join('server', 'dafny-lsp'));
  if (fs.existsSync(bundled)) {
    // Extracting the .vsix does not always keep the executable bit.
    fs.chmodSync(bundled, 0o755);
    return bundled;
  }
  const cargo = path.join(os.homedir(), '.cargo', 'bin', 'dafny-lsp');
  return fs.existsSync(cargo) ? cargo : 'dafny-lsp';
}

/** Draws the per-line verification status the server sends as gutter bars. */
class Gutter {
  private readonly types: Map<string, vscode.TextEditorDecorationType>;
  private readonly status = new Map<string, number[]>();

  constructor(context: vscode.ExtensionContext) {
    const bar = (name: string) =>
      vscode.window.createTextEditorDecorationType({
        gutterIconPath: context.asAbsolutePath(path.join('media', `${name}.svg`)),
        gutterIconSize: 'contain',
      });
    this.types = new Map([
      ['verified', bar('verified')],
      ['error', bar('error')],
      ['failed', bar('failed')],
      ['pending', bar('pending')],
      ['resolution', bar('resolution')],
    ]);
  }

  /** Maps a LineVerificationStatus value to a decoration name. */
  private category(value: number): string | undefined {
    if (value === 1 || value === 2 || (value >= 200 && value % 10 !== 0 && value < 500)) {
      return 'pending';
    }
    if (value >= 200 && value < 300) {
      return 'verified';
    }
    if (value >= 300 && value < 400) {
      return 'error';
    }
    if (value >= 400 && value < 500) {
      return 'failed';
    }
    if (value === 500) {
      return 'resolution';
    }
    return undefined;
  }

  update(uri: string, perLineStatus: number[]): void {
    this.status.set(uri, perLineStatus);
    for (const editor of vscode.window.visibleTextEditors) {
      if (editor.document.uri.toString() === uri) {
        this.apply(editor);
      }
    }
  }

  apply(editor: vscode.TextEditor): void {
    const lines = this.status.get(editor.document.uri.toString());
    if (!lines) {
      return;
    }
    const ranges = new Map<string, vscode.Range[]>();
    lines.forEach((value, line) => {
      const name = this.category(value);
      if (name && line < editor.document.lineCount) {
        const list = ranges.get(name) ?? [];
        list.push(new vscode.Range(line, 0, line, 0));
        ranges.set(name, list);
      }
    });
    for (const [name, type] of this.types) {
      editor.setDecorations(type, ranges.get(name) ?? []);
    }
  }

  forget(uri: string): void {
    this.status.delete(uri);
  }

  dispose(): void {
    for (const type of this.types.values()) {
      type.dispose();
    }
  }
}

async function startClient(context: vscode.ExtensionContext): Promise<void> {
  const command = serverPath(context);
  const serverOptions: ServerOptions = { run: { command }, debug: { command } };
  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ language: 'dafny' }],
    initializationOptions: settings(),
    synchronize: { configurationSection: 'dafny-lsp' },
  };
  client = new LanguageClient('dafny-lsp', 'Dafny (dafny-lsp)', serverOptions, clientOptions);
  client.onNotification('dafny/verification/status/gutter', (params: { uri: string; perLineStatus: number[] }) => {
    gutter?.update(params.uri, params.perLineStatus);
  });
  await client.start();
}

async function runServerCommand(command: string, withPosition: boolean): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!client || !editor || editor.document.languageId !== 'dafny') {
    return;
  }
  const args: unknown[] = [editor.document.uri.toString()];
  if (withPosition) {
    args.push(client.code2ProtocolConverter.asPosition(editor.selection.active));
  }
  await client.sendRequest('workspace/executeCommand', { command, arguments: args });
}

function warnAboutOfficialExtension(): void {
  if (!vscode.extensions.getExtension(OFFICIAL_EXTENSION)) {
    return;
  }
  const open = 'Show Extension';
  vscode.window
    .showWarningMessage(
      'The Dafny extension (dafny-lang.ide-vscode) is also enabled and runs its own language server, so diagnostics will show up twice. Disable one of the two extensions.',
      open,
    )
    .then((choice) => {
      if (choice === open) {
        vscode.commands.executeCommand('workbench.extensions.search', `@id:${OFFICIAL_EXTENSION}`);
      }
    });
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  gutter = new Gutter(context);
  context.subscriptions.push(
    gutter,
    vscode.window.onDidChangeVisibleTextEditors((editors) => editors.forEach((e) => gutter?.apply(e))),
    vscode.workspace.onDidCloseTextDocument((doc) => gutter?.forget(doc.uri.toString())),
    vscode.commands.registerCommand('dafny-lsp.verifyFile', () => runServerCommand('dafny-lsp.verify', false)),
    vscode.commands.registerCommand('dafny-lsp.verifyCursor', () => runServerCommand('dafny-lsp.verifyAt', true)),
    vscode.commands.registerCommand('dafny-lsp.cancelVerification', () => runServerCommand('dafny-lsp.cancel', false)),
    vscode.commands.registerCommand('dafny-lsp.restart', async () => {
      await client?.stop();
      await startClient(context);
    }),
  );
  warnAboutOfficialExtension();
  await startClient(context);
}

export async function deactivate(): Promise<void> {
  await client?.stop();
}
