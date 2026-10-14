use std::fs::File;
use std::io::{Error, Write};
use std::time::Instant;

use num_prime::factor::{one_line, pollard_rho, squfof, SQUFOF_MULTIPLIERS};
use num_prime::RandPrime;
use rand::random;

/// Collect the best case of each factorization algorithm
fn profile_n_min(n: u128) -> Vec<(String, usize)> {
    let k_squfof: Vec<u16> = SQUFOF_MULTIPLIERS.to_vec();
    let k_oneline: Vec<u16> = vec![1, 360, 480];
    const MAXITER: usize = 1 << 24;
    const POLLARD_REPEATS: usize = 4;

    let mut n_stats = Vec::new();

    // pollard rho
    let mut pollard_best = (MAXITER, u128::MAX);
    for _ in 0..POLLARD_REPEATS {
        let tstart = Instant::now();
        let (result, iters) = pollard_rho(&n, random(), random(), pollard_best.0);
        if result.is_some() {
            pollard_best = pollard_best.min((iters, tstart.elapsed().as_micros()));
        }
    }
    n_stats.push(("pollard_rho".to_string(), pollard_best.0));
    n_stats.push(("time_pollard_rho".to_string(), pollard_best.1 as usize));

    // squfof
    let mut squfof_best = (MAXITER, u128::MAX);
    for &k in &k_squfof {
        if let Some(kn) = n.checked_mul(u128::from(k)) {
            let tstart = Instant::now();
            let (result, iters) = squfof(&n, kn, squfof_best.0);
            if result.is_some() {
                squfof_best = squfof_best.min((iters, tstart.elapsed().as_micros()));
            }
        }
    }
    n_stats.push(("squfof".to_string(), squfof_best.0));
    n_stats.push(("time_squfof".to_string(), squfof_best.1 as usize));

    // one line
    let mut oneline_best = (MAXITER, u128::MAX);
    for &k in &k_oneline {
        if let Some(kn) = n.checked_mul(u128::from(k)) {
            let tstart = Instant::now();
            let (result, iters) = one_line(&n, kn, oneline_best.0);
            if result.is_some() {
                oneline_best = oneline_best.min((iters, tstart.elapsed().as_micros()));
            }
        }
    }
    n_stats.push(("one_line".to_string(), oneline_best.0));
    n_stats.push(("time_one_line".to_string(), squfof_best.1 as usize));

    n_stats
}

/// This program try various factorization methods, and log down their iterations number into a csv file
fn main() -> Result<(), Error> {
    let mut rng = rand::rng();
    const REPEATS: u32 = 4;

    let mut n_list = Vec::<(u128, f32)>::new(); // n and bits of n
    let mut stats: Vec<Vec<(String, usize)>> = Vec::new();

    for total_bits in 20..120 {
        for _ in 0..REPEATS {
            let p1: u128 = rng.gen_prime(total_bits / 2, None);
            let p2: u128 =
                rng.gen_prime_exact(total_bits - (128 - p1.leading_zeros()) as usize, None);
            if p1 == p2 {
                continue;
            }

            let n = p1 * p2;
            n_list.push((n, (n as f64).log2() as f32));
            println!("Semiprime ({total_bits}bits): {n} = {p1} * {p2}");
            stats.push(profile_n_min(n));
        }
    }

    // Log into the CSV file
    let mut fout = File::create("profile_stats.csv")?;
    fout.write_all(b"n,n_bits")?;
    for k in stats[0].iter().map(|(k, _)| k) {
        fout.write_all(b",")?;
        fout.write_all(k.as_bytes())?;
    }

    for ((n, bits), n_stats) in n_list.iter().zip(stats) {
        fout.write_all(b"\n")?;
        fout.write_all(n.to_string().as_bytes())?;
        fout.write_all(b",")?;
        fout.write_all(bits.to_string().as_bytes())?;
        for (_, v) in n_stats {
            fout.write_all(b",")?;
            fout.write_all(v.to_string().as_bytes())?;
        }
    }

    Ok(())
}
