use std::{fs::File, path::PathBuf};

use anyhow::Error;
use clap::{Parser, Subcommand};
use ndlib::num::{prime::Primes, Num};

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

        /// Json filepath for prime array
        #[arg(short, long)]
        filepath: Option<PathBuf>,

        /// Pretty Json file
        #[arg(long)]
        pretty: bool,
    },
}

#[derive(Subcommand)]
enum PrimeCommands {
    /// Generate primes by count
    #[command(name = "by-count")]
    Count {
        /// Count value
        val: usize,

        /// Use fast test
        #[arg(short, long)]
        fast: bool,
    },

    /// Generate primes by limit
    #[command(name = "by-limit")]
    Limit {
        /// Limit value
        val: u64,

        /// Use fast test
        #[arg(short, long)]
        fast: bool,
    },

    /// Generate prime
    #[command(name = "rand")]
    Rand {
        /// Order
        order: usize,

        /// Count
        count: usize,
    },
}

fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt().try_init().map_err(Error::from_boxed)?;

    let cli = Cli::parse();

    match cli.cmd {
        Commands::Primes { cmd, filepath, pretty } => {
            let primes = match cmd {
                PrimeCommands::Count { val, fast } => match fast {
                    false => Primes::by_count_full(val).collect::<Vec<u64>>(),
                    true => Primes::by_count_fast(val).collect::<Vec<u64>>(),
                },
                PrimeCommands::Limit { val, fast } => match fast {
                    false => Primes::by_limit_full(val).collect::<Vec<u64>>(),
                    true => Primes::by_limit_fast(val).collect::<Vec<u64>>(),
                },
                PrimeCommands::Rand { order, count } => {
                    let mut vec = u64::rand_par_primes(order, count);

                    vec.sort_unstable();
                    vec.reverse();
                    vec
                },
            };

            if let Some(file) = filepath {
                let file = File::create(file)?;

                match pretty {
                    false => serde_json::to_writer(file, &primes)?,
                    true => serde_json::to_writer_pretty(file, &primes)?,
                };
            } else {
                tracing::info!("Count: {}", primes.len());
                tracing::info!("Primes: {:?}", &primes);
            }
        },
    }

    Ok(())
}
