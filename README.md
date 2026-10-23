# dafny-lsp

A language server for Dafny written in Rust. Editor features (completion, go to
definition, references, rename, hover, signature help, symbols) come from a
tree-sitter parse of the code. Diagnostics and verification come from running
the `dafny` CLI.

## Requirements

- `dafny` 4.x. The server looks for it on `PATH`, then in `/opt/homebrew/bin`,
  `/usr/local/bin` and `~/.dotnet/tools`. Set `dafnyPath` to use another one.
- A Rust toolchain to build the server.
- Node.js only if you build the VS Code extension.

## Build and install

```sh
cargo install --path .
```

This puts `dafny-lsp` in `~/.cargo/bin`.

## Neovim

```lua
vim.lsp.config('dafny', {
  cmd = { 'dafny-lsp' },
  filetypes = { 'dafny' },
  root_markers = { 'dfyconfig.toml', '.git' },
  -- optional, see Settings below
  init_options = { verifyOn = 'save' },
})
vim.lsp.enable 'dafny'
```

Keep the client name `dafny` if you use
[dafny-verify.nvim](https://github.com/kevincal1226/dafny-verify.nvim). The server
sends the same `dafny/textDocument/symbolStatus` and
`dafny/verification/status/gutter` notifications as `dafny server
--notify-line-verification-status`, so the plugin works unchanged.

The verification commands below can be called with `client:exec_cmd`. For example,
to verify the declaration under the cursor:

```lua
local client = vim.lsp.get_clients({ bufnr = 0, name = 'dafny' })[1]
client:exec_cmd({
  title = 'verify',
  command = 'dafny-lsp.verifyAt',
  arguments = { vim.uri_from_bufnr(0), vim.lsp.util.make_position_params(0, client.offset_encoding).position },
})
```

## VS Code

```sh
cargo build --release
cd editors/vscode
npm install
mkdir -p server && cp ../../target/release/dafny-lsp server/
npm run package
code --install-extension dafny-lsp.vsix
```

The extension bundles the server binary, adds syntax highlighting, draws the
verification status in the gutter, and adds these commands: `Dafny: Verify File`,
`Dafny: Verify Declaration at Cursor`, `Dafny: Cancel Verification`,
`Dafny: Restart Language Server`.

Disable the official Dafny extension (`dafny-lang.ide-vscode`) while using this
one. Otherwise both language servers run and every diagnostic shows up twice.

## Settings

Neovim passes these in `init_options`. VS Code reads them from the `dafny-lsp.*`
settings.

| Setting                 | Default   | Meaning |
|-------------------------|-----------|---------|
| `dafnyPath`             | `"dafny"` | dafny executable |
| `verifyOn`              | `"save"`  | `"change"`: verify after each edit. `"save"`: type check after each edit, verify on open and save. `"never"`: type check only, verify through commands |
| `debounceMs`            | `300`     | delay after the last edit before dafny runs |
| `verificationTimeLimit` | unset     | seconds per assertion batch (`--verification-time-limit`) |
| `cores`                 | unset     | number of cores or a percentage like `"50%"` (`--cores`) |
| `extraArgs`             | `[]`      | extra arguments for every dafny run |

## Commands

Sent with `workspace/executeCommand`. The first argument is always the document URI.

| Command                  | Arguments          | Effect |
|--------------------------|--------------------|--------|
| `dafny-lsp.verify`       | uri                | verify the whole file |
| `dafny-lsp.verifySymbol` | uri, qualified name (`M.C.Foo`) | verify one declaration |
| `dafny-lsp.verifyAt`     | uri, position      | verify the declaration that contains the position |
| `dafny-lsp.cancel`       | uri                | stop the running verification |

## How diagnostics work

Every check runs `dafny verify --json-output --stdin` in the file's directory
with the buffer contents on stdin, so unsaved changes are checked and relative
`include`s resolve. A type check is the same command with a `--filter-symbol`
that matches nothing, which stops after resolution (about 0.3s). A new run for a
document cancels the previous one. Results that arrive after further edits are
moved to account for lines added or removed in between.

If the file is part of a `dfyconfig.toml` project, the `[options]` table is
passed as flags and the other project files are passed as `--library`, so names
from those files resolve without an `include`.

## Limitations

- Navigation and completion use declarations, scopes, imports and declared
  types. There is no full type inference, so member access on an expression
  whose type cannot be worked out falls back to members with that name on any
  type.
- Hover shows the declaration of a name, not the type of an arbitrary expression.
- No formatting. Use `dafny format`.
- Each run starts a new dafny process, so nothing is cached between runs.

## Development

```sh
cargo test
cargo run --release --example resolve_corpus -- path/to/*.dfy   # identifiers that resolve to nothing
cargo run --release --example sexp -- file.dfy                  # print the tree-sitter tree
cargo run --release --example def_at -- file.dfy LINE COL       # definition targets at a position
```

The VS Code extension has an integration test. It opens `test/fixture` in the
installed VS Code with an empty profile, so other extensions and settings are not
loaded, and prints what each provider returned:

```sh
cd editors/vscode && npm test
```
