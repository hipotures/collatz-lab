//! Command-line front end. All mathematics lives in the `collatz_lab` library.

use std::error::Error;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Args, Parser, Subcommand};
use num_bigint::BigUint;

use collatz_lab::certificate::{certify, walk_first_descent, CoverNode};
use collatz_lab::collatz;
use collatz_lab::hypothesis::{run_experiment, ExperimentParams, LedgerEntry};
use collatz_lab::nogo;
use collatz_lab::prefix::{residue_by_inverse, Cylinder, ParityPrefix};
use collatz_lab::report::render_summary;
use collatz_lab::verifier;

type CliResult<T> = Result<T, Box<dyn Error>>;

/// Bounds above which a command refuses to run without `--allow-large`.
const MAX_DEFAULT_PREFIX_LENGTH: usize = 16;
const MAX_DEFAULT_DEPTH: usize = 24;
const MAX_DEFAULT_LIMIT: u64 = 10_000_000;
const MAX_DEFAULT_SAMPLES: usize = 100_000;

#[derive(Parser)]
#[command(
    name = "collatz-lab",
    version,
    about = "Exact-arithmetic workbench for Collatz parity prefixes and conditional descent certificates",
    long_about = "Exact-arithmetic workbench for the accelerated Collatz map \
                  T(n) = n/2 (n even), (3n+1)/2 (n odd).\n\n\
                  All results are bounded and labelled by epistemic status. \
                  Nothing this tool prints is a proof of the Collatz conjecture."
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Run the deterministic self-checks, or re-check a ledger file.
    Verify(VerifyArgs),
    /// Show parity prefixes with their affine form and residue class.
    Prefixes(PrefixArgs),
    /// Enumerate conditional descent certificates and uncovered classes.
    Certificates(CertificateArgs),
    /// Run the bounded hypothesis experiment and write ledger + summary.
    Experiment(ExperimentArgs),
}

#[derive(Args)]
struct VerifyArgs {
    /// Exhaustively check stopping times for 2 <= n <= LIMIT.
    #[arg(long, default_value_t = 100_000)]
    limit: u64,
    /// Step budget per starting value.
    #[arg(long, default_value_t = 10_000)]
    max_steps: u64,
    /// Check the Mersenne identity for all 0 <= L <= MERSENNE_MAX.
    #[arg(long, default_value_t = 128)]
    mersenne_max: usize,
    /// Depth of the first-descent cover whose certificates are re-verified.
    #[arg(long, default_value_t = 12)]
    depth: usize,
    /// Instead of the self-checks, re-verify every failure case in this JSONL ledger.
    #[arg(long)]
    ledger: Option<PathBuf>,
    /// Permit bounds above the laptop-friendly defaults.
    #[arg(long)]
    allow_large: bool,
}

#[derive(Args)]
struct PrefixArgs {
    /// Prefix length k. Alone: list all 2^k prefixes. With --n: prefix of n.
    #[arg(long)]
    length: Option<usize>,
    /// A single parity string, e.g. 11010 (1 = odd step, 0 = even step).
    #[arg(long, conflicts_with_all = ["n"])]
    parity: Option<String>,
    /// A positive integer in decimal (any size); requires --length.
    #[arg(long, requires = "length")]
    n: Option<BigUint>,
    /// Permit listing more than 2^16 prefixes.
    #[arg(long)]
    allow_large: bool,
}

#[derive(Args)]
struct CertificateArgs {
    /// Depth of the first-descent tree.
    #[arg(long, default_value_t = 12)]
    depth: usize,
    /// Certificate for exactly this parity string instead of the tree.
    #[arg(long)]
    parity: Option<String>,
    /// Write every leaf (certificates and uncovered classes) as JSONL.
    #[arg(long)]
    out: Option<PathBuf>,
    /// How many uncovered classes to print.
    #[arg(long, default_value_t = 20)]
    show_uncovered: usize,
    /// Permit depth above 24.
    #[arg(long)]
    allow_large: bool,
}

#[derive(Args)]
struct ExperimentArgs {
    #[arg(long, default_value_t = ExperimentParams::default().seed)]
    seed: u64,
    /// Depth of the first-descent cover.
    #[arg(long, default_value_t = ExperimentParams::default().depth)]
    depth: usize,
    /// Exhaustive searches cover 2 <= n <= LIMIT.
    #[arg(long, default_value_t = ExperimentParams::default().limit)]
    limit: u64,
    /// Candidate universal descent window W.
    #[arg(long, default_value_t = ExperimentParams::default().window)]
    window: usize,
    /// Candidate constant C in "stopping time <= C * bit length".
    #[arg(long, default_value_t = ExperimentParams::default().bits_factor)]
    bits_factor: u64,
    /// Bit length of sampled integers.
    #[arg(long, default_value_t = ExperimentParams::default().sample_bits)]
    sample_bits: usize,
    /// Number of sampled integers.
    #[arg(long, default_value_t = ExperimentParams::default().samples)]
    samples: usize,
    /// Step budget for sampled stopping times.
    #[arg(long, default_value_t = ExperimentParams::default().max_steps)]
    max_steps: u64,
    /// Output directory for ledger.jsonl and summary.md.
    #[arg(long, default_value = "research/runs/latest")]
    out_dir: PathBuf,
    /// Permit bounds above the laptop-friendly defaults.
    #[arg(long)]
    allow_large: bool,
}

fn require_bound<T: PartialOrd + std::fmt::Display>(
    name: &str,
    value: T,
    max: T,
    allow_large: bool,
) -> CliResult<()> {
    if value > max && !allow_large {
        return Err(format!(
            "--{name} {value} exceeds the default bound {max}; pass --allow-large to run it anyway"
        )
        .into());
    }
    Ok(())
}

fn decimal_list(values: &[BigUint]) -> String {
    let texts: Vec<String> = values.iter().map(BigUint::to_string).collect();
    texts.join(", ")
}

fn describe_cylinder(cylinder: &Cylinder) -> String {
    let affine = cylinder.affine();
    let k = affine.steps();
    let descent = match certify(cylinder) {
        Some(cert) => format!("T^{k}(n) < n iff n >= {}", cert.threshold),
        None => format!(
            "2^{k} <= 3^{}: T^{k}(n) >= n on the whole class",
            affine.odd_steps()
        ),
    };
    format!(
        "{:<width$}  n = {} (mod 2^{k})  T^{k}(n) = (3^{} n + {}) / 2^{k}  [{descent}]",
        if k == 0 {
            "(empty)".to_string()
        } else {
            cylinder.prefix().to_string()
        },
        cylinder.residue(),
        affine.odd_steps(),
        affine.offset(),
        width = k.max(7),
    )
}

fn cmd_verify(args: &VerifyArgs) -> CliResult<()> {
    if let Some(path) = &args.ledger {
        return verify_ledger(path);
    }
    require_bound("limit", args.limit, MAX_DEFAULT_LIMIT, args.allow_large)?;
    require_bound("depth", args.depth, MAX_DEFAULT_DEPTH, args.allow_large)?;
    require_bound("mersenne-max", args.mersenne_max, 2048, args.allow_large)?;

    // 1. Small-range oracle.
    eprintln!("[progress] range oracle for 2 <= n <= {}", args.limit);
    let oracle = collatz::range_oracle(args.limit, args.max_steps);
    if oracle.all_reach_one() {
        println!(
            "[verified-for-finite-domain] every 2 <= n <= {} descends below itself within {} steps \
             (max stopping time {} at n = {}); by strong induction every 1 <= n <= {} reaches 1",
            oracle.limit, oracle.max_steps, oracle.max_stopping_time, oracle.argmax, oracle.limit
        );
    } else {
        println!(
            "[unresolved] {} starting values did not descend within {} steps (first: {}); \
             this is a budget outcome, not a counterexample",
            oracle.unresolved.len(),
            oracle.max_steps,
            oracle.unresolved[0]
        );
    }

    // 2. Primitive fast path against BigUint.
    let cross = args.limit.min(20_000);
    for n in (2..=cross).chain([u64::MAX, u64::MAX - 2, (1 << 63) + 1]) {
        let fast = collatz::stopping_time_fast(n, args.max_steps);
        let exact = collatz::stopping_time(&BigUint::from(n), args.max_steps);
        if fast != exact {
            return Err(format!("u64 fast path disagrees with BigUint at n = {n}").into());
        }
    }
    println!(
        "[verified-for-finite-domain] checked u64 fast path equals BigUint evaluation for \
         2 <= n <= {cross} and three values near 2^64 that overflow u64"
    );

    // 3. Mersenne identity.
    for l in 0..=args.mersenne_max {
        nogo::check_mersenne_identity(l)
            .map_err(|j| format!("Mersenne identity fails for L = {l}, j = {j}"))?;
        if !nogo::refutes_window(&nogo::mersenne(l), l) {
            return Err(format!("2^{l} - 1 descends within {l} steps").into());
        }
    }
    println!(
        "[verified-for-finite-domain] T^j(2^L - 1) = 3^j 2^(L-j) - 1 for all 0 <= j <= L <= {} \
         (direct iteration; the identity itself is proven by induction, see src/nogo.rs)",
        args.mersenne_max
    );
    println!(
        "[proven-by-algebra] consequently no fixed window W gives T^j(n) < n for some j <= W \
         for all large n: n = 2^W m - 1 is a witness for every m >= 1"
    );

    // 4. Symbolic layer against direct iteration, and the independent verifier.
    eprintln!("[progress] first-descent cover to depth {}", args.depth);
    let (mut certified, mut uncovered) = (0u64, 0u64);
    let mut failure = None;
    walk_first_descent(args.depth, |node| match node {
        CoverNode::Certified(cert) => {
            certified += 1;
            if failure.is_none() {
                failure = verifier::verify_certificate(&cert, 3)
                    .err()
                    .map(|reason| format!("certificate {}: {reason}", cert.parity));
            }
        }
        CoverNode::Uncovered(class) => {
            uncovered += 1;
            let prefix: Result<ParityPrefix, _> = class.parity.parse();
            let consistent = prefix.is_ok_and(|prefix| {
                let cylinder = Cylinder::from_prefix(&prefix);
                residue_by_inverse(cylinder.affine()) == class.residue
                    && ParityPrefix::of(&(&class.residue + &class.modulus), class.steps) == prefix
            });
            if !consistent && failure.is_none() {
                failure = Some(format!("uncovered class {} is inconsistent", class.parity));
            }
        }
    });
    if let Some(reason) = failure {
        return Err(reason.into());
    }
    println!(
        "[verified-for-finite-domain] depth {}: {certified} descent certificates passed the \
         independent verifier; {uncovered} residue classes modulo 2^{} remain uncovered",
        args.depth, args.depth
    );
    println!("verify: all checks passed (bounded checks only; no claim about the conjecture)");
    Ok(())
}

fn verify_ledger(path: &Path) -> CliResult<()> {
    let reader = BufReader::new(File::open(path)?);
    let (mut entries, mut cases) = (0usize, 0usize);
    for (index, line) in reader.lines().enumerate() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let entry: LedgerEntry = serde_json::from_str(&line)
            .map_err(|e| format!("{}:{}: {e}", path.display(), index + 1))?;
        for case in &entry.failure_cases {
            verifier::verify_failure_case(case).map_err(|reason| {
                format!(
                    "{}:{}: failure case of {} rejected: {reason}",
                    path.display(),
                    index + 1,
                    entry.hypothesis_id
                )
            })?;
            cases += 1;
        }
        entries += 1;
    }
    println!(
        "ledger {}: {entries} entries, {cases} failure cases re-verified by direct iteration",
        path.display()
    );
    Ok(())
}

fn cmd_prefixes(args: &PrefixArgs) -> CliResult<()> {
    if let Some(parity) = &args.parity {
        let prefix: ParityPrefix = parity.parse()?;
        if args.length.is_some_and(|length| length != prefix.len()) {
            return Err("--length does not match the length of --parity".into());
        }
        println!("{}", describe_cylinder(&Cylinder::from_prefix(&prefix)));
        return Ok(());
    }
    let Some(length) = args.length else {
        return Err("give --length K, --parity BITS, or --n N --length K".into());
    };
    if let Some(n) = &args.n {
        let cylinder = Cylinder::containing(n, length);
        println!("{}", describe_cylinder(&cylinder));
        let image = cylinder
            .image(n)
            .ok_or("internal error: n is not in its own cylinder")?;
        if image != collatz::t_iter(n, length) {
            return Err("internal error: affine form disagrees with direct iteration".into());
        }
        println!("T^{length}({n}) = {image}  (affine form and direct iteration agree)");
        return Ok(());
    }
    require_bound(
        "length",
        length,
        MAX_DEFAULT_PREFIX_LENGTH,
        args.allow_large,
    )?;
    let stdout = std::io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut stack = vec![Cylinder::root()];
    while let Some(cylinder) = stack.pop() {
        if cylinder.len() == length {
            writeln!(out, "{}", describe_cylinder(&cylinder))?;
        } else {
            stack.push(cylinder.extend(true));
            stack.push(cylinder.extend(false));
        }
    }
    out.flush()?;
    Ok(())
}

fn cmd_certificates(args: &CertificateArgs) -> CliResult<()> {
    if let Some(parity) = &args.parity {
        let prefix: ParityPrefix = parity.parse()?;
        let cylinder = Cylinder::from_prefix(&prefix);
        match certify(&cylinder) {
            Some(cert) => {
                verifier::verify_certificate(&cert, 3)?;
                println!("certificate: {}", cert.statement());
                println!(
                    "positive class members below the threshold: {} {{{}}}",
                    cert.exception_count,
                    decimal_list(&cert.exceptions)
                );
                println!("scope: this one residue class and this one step count only; verified by the independent verifier");
            }
            None => println!(
                "no certificate: 2^{} <= 3^{}, so T^{}(n) >= n for every n = {} (mod 2^{}); \
                 the class is uncovered at this length",
                cylinder.len(),
                cylinder.affine().odd_steps(),
                cylinder.len(),
                cylinder.residue(),
                cylinder.len()
            ),
        }
        return Ok(());
    }
    require_bound("depth", args.depth, MAX_DEFAULT_DEPTH, args.allow_large)?;

    let mut writer = match &args.out {
        Some(path) => {
            if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
                fs::create_dir_all(parent)?;
            }
            Some(BufWriter::new(File::create(path)?))
        }
        None => None,
    };
    let (mut certified, mut uncovered, mut with_exceptions) = (0u64, 0u64, Vec::new());
    let mut shown = Vec::new();
    let mut longest = 0usize;
    let mut error: Option<Box<dyn Error>> = None;
    walk_first_descent(args.depth, |node| {
        if error.is_some() {
            return;
        }
        if let Some(writer) = writer.as_mut() {
            // One complete JSON object per line, so a partial file stays parseable.
            let result = serde_json::to_writer(&mut *writer, &node)
                .map_err(Box::<dyn Error>::from)
                .and_then(|()| writer.write_all(b"\n").map_err(Box::<dyn Error>::from));
            if let Err(e) = result {
                error = Some(e);
                return;
            }
        }
        match node {
            CoverNode::Certified(cert) => {
                if let Err(reason) = verifier::verify_certificate(&cert, 2) {
                    error = Some(format!("certificate {}: {reason}", cert.parity).into());
                    return;
                }
                certified += 1;
                longest = longest.max(cert.steps);
                if !cert.exceptions.is_empty() {
                    with_exceptions.push(cert);
                }
            }
            CoverNode::Uncovered(class) => {
                uncovered += 1;
                if shown.len() < args.show_uncovered {
                    shown.push(class);
                }
            }
        }
        let leaves = certified + uncovered;
        if leaves % 100_000 == 0 {
            eprintln!("[progress] {leaves} leaves ({certified} certified, {uncovered} uncovered)");
        }
    });
    if let Some(e) = error {
        return Err(e);
    }
    if let Some(writer) = writer.as_mut() {
        writer.flush()?;
    }

    let depth = args.depth;
    println!("first-descent cover to depth {depth} (accelerated map T)");
    println!("  certified first-descent prefixes : {certified} (longest length {longest})");
    println!("  uncovered classes modulo 2^{depth}    : {uncovered}");
    println!(
        "  covered classes modulo 2^{depth}      : {} of {}",
        (BigUint::from(1u32) << depth) - uncovered,
        BigUint::from(1u32) << depth
    );
    println!("  every certificate passed the independent verifier");
    println!("certificates with positive members below their threshold:");
    if with_exceptions.is_empty() {
        println!("  none");
    }
    for cert in &with_exceptions {
        println!(
            "  prefix {}: n in {{{}}} does not descend at step {}",
            cert.parity,
            decimal_list(&cert.exceptions),
            cert.steps
        );
    }
    println!("uncovered classes (first {} of {uncovered}):", shown.len());
    for class in &shown {
        println!(
            "  n = {} (mod 2^{})  prefix {}",
            class.residue, class.steps, class.parity
        );
    }
    println!(
        "note: certificates are conditional single-descent statements; uncovered classes exist \
         at every depth, so this is not a convergence result"
    );
    if let Some(path) = &args.out {
        println!("wrote {}", path.display());
    }
    Ok(())
}

fn cmd_experiment(args: &ExperimentArgs) -> CliResult<()> {
    require_bound("depth", args.depth, MAX_DEFAULT_DEPTH, args.allow_large)?;
    require_bound("limit", args.limit, MAX_DEFAULT_LIMIT, args.allow_large)?;
    require_bound(
        "samples",
        args.samples,
        MAX_DEFAULT_SAMPLES,
        args.allow_large,
    )?;
    require_bound("window", args.window, 4096, args.allow_large)?;
    let params = ExperimentParams {
        seed: args.seed,
        depth: args.depth,
        limit: args.limit,
        window: args.window,
        bits_factor: args.bits_factor,
        sample_bits: args.sample_bits,
        samples: args.samples,
        max_steps: args.max_steps,
    };
    fs::create_dir_all(&args.out_dir)?;
    let ledger_path = args.out_dir.join("ledger.jsonl");
    let summary_path = args.out_dir.join("summary.md");
    let mut ledger = File::create(&ledger_path)?;

    let outcome = run_experiment(
        &params,
        |entry| {
            // Append one complete line and flush, so an interrupted run
            // leaves a valid (shorter) ledger behind.
            let mut line = serde_json::to_vec(entry)?;
            line.push(b'\n');
            ledger.write_all(&line)?;
            ledger.flush()?;
            Ok(())
        },
        |message| eprintln!("[progress] {message}"),
    )?;

    let defaults = ExperimentParams::default();
    let mut command = String::from("cargo run --release -- experiment");
    let mut flag = |name: &str, value: String, default: String| {
        if value != default {
            command.push_str(&format!(" --{name} {value}"));
        }
    };
    flag("seed", params.seed.to_string(), defaults.seed.to_string());
    flag(
        "depth",
        params.depth.to_string(),
        defaults.depth.to_string(),
    );
    flag(
        "limit",
        params.limit.to_string(),
        defaults.limit.to_string(),
    );
    flag(
        "window",
        params.window.to_string(),
        defaults.window.to_string(),
    );
    flag(
        "bits-factor",
        params.bits_factor.to_string(),
        defaults.bits_factor.to_string(),
    );
    flag(
        "sample-bits",
        params.sample_bits.to_string(),
        defaults.sample_bits.to_string(),
    );
    flag(
        "samples",
        params.samples.to_string(),
        defaults.samples.to_string(),
    );
    flag(
        "max-steps",
        params.max_steps.to_string(),
        defaults.max_steps.to_string(),
    );
    command.push_str(&format!(" --out-dir {}", args.out_dir.display()));

    fs::write(&summary_path, render_summary(&outcome, &command))?;

    println!("hypothesis                                status");
    for entry in &outcome.entries {
        println!("{:<41} {}", entry.hypothesis_id, entry.status.label());
    }
    println!(
        "cover depth {}: {} certificates, {} uncovered classes",
        outcome.cover.depth, outcome.cover.certificates, outcome.cover.uncovered
    );
    println!("wrote {}", ledger_path.display());
    println!("wrote {}", summary_path.display());
    println!("bounded experiment only: no proof, novelty or counterexample claim follows");
    Ok(())
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let result = match &cli.command {
        Command::Verify(args) => cmd_verify(args),
        Command::Prefixes(args) => cmd_prefixes(args),
        Command::Certificates(args) => cmd_certificates(args),
        Command::Experiment(args) => cmd_experiment(args),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}
