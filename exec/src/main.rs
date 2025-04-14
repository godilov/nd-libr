use std::{fs::File, path::PathBuf};

use anyhow::Error;
use clap::{Parser, Subcommand};

use ndlibr::math::{Prime, Primes};

#[derive(Parser)]
#[command(version, about, long_about)]
struct Cli {
    #[command(subcommand)]
    cmd: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Primes {
        #[command(subcommand)]
        cmd: PrimeCommands,

        /// Output json filepath
        #[arg(short, long, default_value = "./primes.json")]
        output: PathBuf,
    },
}

#[derive(Subcommand)]
enum PrimeCommands {
    /// Generate primes by count
    #[command(name = "by-count")]
    Count {
        /// Count value
        val: usize,
    },

    /// Generate primes by limit
    #[command(name = "by-limit")]
    Limit {
        /// Limit value
        val: u64,
    },
}

fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt().try_init().map_err(Error::from_boxed)?;

    let cli = Cli::parse();

    match cli.cmd {
        Commands::Primes { cmd, output } => {
            let primes = match cmd {
                PrimeCommands::Count { val } => Primes::by_count(val).collect::<Vec<Prime>>(),
                PrimeCommands::Limit { val } => Primes::by_limit(val).collect::<Vec<Prime>>(),
            };

            serde_json::to_writer(File::create(output)?, &primes)?;
        },
    }

    Ok(())
}
