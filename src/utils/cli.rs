/**
 * A generic command-line interface for 6.035 compilers.  This class
 * provides command-line parsing for student projects.  It recognizes
 * the required <tt>-target</tt>, <tt>-debug</tt>, <tt>-opt</tt>, and
 * <tt>-o</tt> switches, and generates a name for input and output
 * files.
 *
 * @author 6.1100 Staff, last updated January 2024
 */
use clap::Parser;

#[derive(Clone, clap::ValueEnum, Debug)]
pub enum CompilerAction {
    Default,
    Scan,
    Parse,
    Inter,
    Assembly,
}

#[derive(Clone, clap::ValueEnum, Debug, PartialEq, Eq, Hash)]
pub enum Optimization {
    #[clap(name = "cp")]
    CopyPropagation,
    #[clap(name = "dce")]
    DeadCodeElimination,
    #[clap(name = "cse")]
    CommonSubexpressionElimination,
    #[clap(name = "gvnpre")]
    GVNPRE,
    #[clap(name = "all")]
    All,
}

#[derive(Parser, Debug)]
pub struct Args {
    /// compile to the given stage
    #[clap(short, long, value_enum, default_value_t=CompilerAction::Default, value_name = "stage")]
    pub target: CompilerAction,

    /// write output to
    #[clap(short = 'o', long, value_name = "outname")]
    pub output: Option<std::path::PathBuf>,

    /// Perform the listed optimizations
    #[clap(
        short = 'O',
        long,
        value_delimiter = ',',
        value_enum,
        value_name = "optimization,.."
    )]
    pub opt: Vec<Optimization>,

    /// Print debugging information
    #[arg(short, long, default_value_t = false)]
    pub debug: bool,

    /// Decaf file
    pub input: Option<std::path::PathBuf>,

    // stuff for godbolt
    #[arg(long, default_value_t = false)]
    pub version: bool,

    #[arg(short = 'g', long, default_value_t = false)]
    pub emit_debug_symbols: bool,

    #[arg(short = 'S', long, default_value_t = false)]
    pub output_assembly: bool,
}

pub fn parse() -> Args {
    Args::parse()
}
