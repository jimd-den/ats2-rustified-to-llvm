//! # ats2llvm — the thin controller
//!
//! *Literate note.*  `main` owns nothing but the wiring: it converts OS
//! arguments into a request, hands the request to the infrastructure CLI
//! controller, and maps the outcome to a process exit code.  All real
//! decisions belong to the use cases one layer down.

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    std::process::exit(ats2_infrastructure::cli::run(args));
}
