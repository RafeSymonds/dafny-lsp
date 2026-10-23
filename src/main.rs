use dafny_lsp::server;
use tower_lsp::{LspService, Server};

const USAGE: &str = "dafny-lsp: language server for Dafny

Usage: dafny-lsp [--stdio]

Speaks the Language Server Protocol over stdin/stdout. Diagnostics and
verification come from the `dafny` CLI, which must be installed.";

#[tokio::main]
async fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--version" || a == "-V") {
        println!("dafny-lsp {}", env!("CARGO_PKG_VERSION"));
        return;
    }
    if args.iter().any(|a| a == "--help" || a == "-h") {
        println!("{USAGE}");
        return;
    }
    let (service, socket) = LspService::new(server::Backend::new);
    Server::new(tokio::io::stdin(), tokio::io::stdout(), socket).serve(service).await;
}
