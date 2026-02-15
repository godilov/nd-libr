use std::{fs::File, path::PathBuf};

use anyhow::Error;
use clap::{Parser, Subcommand};
use ndlib::num::prime::{PrimalityExt, Primes};

#[derive(Parser)]
#[command(version, about, long_about)]
struct Cli {
    #[command(subcommand)]
    cmd: Commands,

    /// Json filepath for prime array
    #[arg(short, long)]
    filepath: Option<PathBuf>,

    /// Json file prettified
    #[arg(long)]
    pretty: bool,
}

#[derive(Subcommand)]
enum Commands {
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
        val: u128,

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

    let primes = match cli.cmd {
        Commands::Count { val, fast } => match fast {
            false => Primes::by_count_full(val).collect::<Vec<u128>>(),
            true => Primes::by_count_fast(val).collect::<Vec<u128>>(),
        },
        Commands::Limit { val, fast } => match fast {
            false => Primes::by_limit_full(val).collect::<Vec<u128>>(),
            true => Primes::by_limit_fast(val).collect::<Vec<u128>>(),
        },
        Commands::Rand { order, count } => {
            let mut vec = u128::rand_primes_par(order, count);

            vec.sort_unstable();
            vec.reverse();
            vec
        },
    };

    if let Some(filepath) = cli.filepath {
        let file = File::create(&filepath)?;

        match cli.pretty {
            false => serde_json::to_writer(file, &primes)?,
            true => serde_json::to_writer_pretty(file, &primes)?,
        };

        tracing::info!("Filepath: {}", filepath.display());
    } else {
        tracing::info!("Count: {}", primes.len());
        tracing::info!("Primes: {:?}", &primes);
    }

    Ok(())
}
