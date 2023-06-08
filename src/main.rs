//! Parse some of that sweet, sweet text
use std::{
    eprintln,
    io::{self, Read},
    println,
};

use clap::Parser;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Opts {
    #[clap(value_name = "MEXPR")]
    query_def: Option<String>,
}

fn main() -> io::Result<()> {
    let args = Opts::parse();

    let qdef = match args.query_def {
        Some(text) => text,
        None => {
            let mut text = String::new();
            let mut stdin = io::stdin();
            stdin.read_to_string(&mut text)?;
            text
        }
    };
    let res = mexpr_parser::try_parse(&qdef);
    match res {
        Ok((len, v)) => {
            if len < qdef.len() {
                eprintln!(
                    "Warning: Was only able to parse {}, chracters, out of {} total characters",
                    len,
                    qdef.len()
                );
            }
            println!("{:#}", serde_json::to_string(&v).unwrap());
        }
        Err(e) => eprintln!("{}", e),
    };
    Ok(())
}
