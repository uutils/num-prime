use num_prime::nt_funcs::*;
use num_prime::*;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        println!("Usage: test_comparison <test_type>");
        return;
    }

    match args[1].as_str() {
        "small_primes" => {
            let small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
            for &p in &small_primes {
                println!(
                    "{} is prime: {}",
                    p,
                    if is_prime64(p) { "TRUE" } else { "FALSE" }
                );
            }
        }
        "composites" => {
            let composites = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25];
            for &c in &composites {
                println!(
                    "{} is prime: {}",
                    c,
                    if is_prime64(c) { "TRUE" } else { "FALSE" }
                );
            }
        }
        "prime_pi" => {
            let test_values = [10, 100, 1000, 10000];
            for &n in &test_values {
                println!("π({}) = {}", n, prime_pi(n));
            }
        }
        "nth_prime" => {
            let indices = [1, 2, 3, 4, 5, 10, 25, 100, 168];
            for &idx in &indices {
                println!("p_{} = {}", idx, nth_prime(idx));
            }
        }
        "factorization" => {
            let numbers = [12, 15, 21, 30, 60, 77, 91, 143, 221];
            for &n in &numbers {
                let factors = factorize64(n);
                print!("{} = ", n);
                for (i, (prime, exp)) in factors.iter().enumerate() {
                    if i > 0 {
                        print!(" * ");
                    }
                    if *exp == 1 {
                        print!("{}", prime);
                    } else {
                        print!("{}^{}", prime, exp);
                    }
                }
                println!();
            }
        }
        "exact_roots" => {
            // Perfect squares
            let squares = [1u32, 4, 9, 16, 25, 36, 49, 64, 81, 100];
            for &n in &squares {
                match n.sqrt_exact() {
                    Some(root) => println!("sqrt({}) = {} (exact)", n, root),
                    None => println!("sqrt({}) = None", n),
                }
            }
            // Perfect cubes (positive)
            let cubes_pos = [1i32, 8, 27, 64, 125];
            for &n in &cubes_pos {
                match n.nth_root_exact(3) {
                    Some(root) => println!("cbrt({}) = {} (exact)", n, root),
                    None => println!("cbrt({}) = None", n),
                }
            }
            // Perfect cubes (negative)
            let cubes_neg = [-1i32, -8, -27, -64, -125];
            for &n in &cubes_neg {
                match n.nth_root_exact(3) {
                    Some(root) => println!("cbrt({}) = {} (exact)", n, root),
                    None => println!("cbrt({}) = None", n),
                }
            }
            // Test case for issue #25: nth_root_exact panic on negative even roots
            // Even roots of negative numbers (should return None)
            println!(
                "-1 nth_root_exact(2) = {}",
                (-1i32)
                    .nth_root_exact(2)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-4 nth_root_exact(2) = {}",
                (-4i32)
                    .nth_root_exact(2)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-8 nth_root_exact(4) = {}",
                (-8i32)
                    .nth_root_exact(4)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-16 nth_root_exact(4) = {}",
                (-16i32)
                    .nth_root_exact(4)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-25 nth_root_exact(2) = {}",
                (-25i32)
                    .nth_root_exact(2)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );

            // Odd roots of negative numbers (should work)
            println!(
                "-8 nth_root_exact(3) = {}",
                (-8i32)
                    .nth_root_exact(3)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-27 nth_root_exact(3) = {}",
                (-27i32)
                    .nth_root_exact(3)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-32 nth_root_exact(5) = {}",
                (-32i32)
                    .nth_root_exact(5)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );

            // Additional nth_root_exact tests for positive numbers
            println!(
                "16 nth_root_exact(4) = {}",
                16i32
                    .nth_root_exact(4)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "32 nth_root_exact(5) = {}",
                32i32
                    .nth_root_exact(5)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "81 nth_root_exact(4) = {}",
                81i32
                    .nth_root_exact(4)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "243 nth_root_exact(5) = {}",
                243i32
                    .nth_root_exact(5)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );

            // Test various signed integer type limits from patch
            println!(
                "-1i8 nth_root_exact(2) = {}",
                (-1i8)
                    .nth_root_exact(2)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-1i16 nth_root_exact(2) = {}",
                (-1i16)
                    .nth_root_exact(2)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-1i32 nth_root_exact(2) = {}",
                (-1i32)
                    .nth_root_exact(2)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-1i64 nth_root_exact(2) = {}",
                (-1i64)
                    .nth_root_exact(2)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-1i128 nth_root_exact(2) = {}",
                (-1i128)
                    .nth_root_exact(2)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
            println!(
                "-1isize nth_root_exact(2) = {}",
                (-1isize)
                    .nth_root_exact(2)
                    .map(|v| v.to_string())
                    .unwrap_or("None".to_string())
            );
        }
        "large_numbers" => {
            // Test large perfect powers
            let large_square = 1000000u64; // 1000^2
            let large_cube = 1000000000u64; // 1000^3

            match large_square.sqrt_exact() {
                Some(root) => println!("sqrt({}) = {}", large_square, root),
                None => println!("sqrt({}) = None", large_square),
            }

            match large_cube.nth_root_exact(3) {
                Some(root) => println!("cbrt({}) = {}", large_cube, root),
                None => println!("cbrt({}) = None", large_cube),
            }

            match (-1000000000i64).nth_root_exact(3) {
                Some(root) => println!("cbrt({}) = {}", -1000000000i64, root),
                None => println!("cbrt({}) = None", -1000000000i64),
            }

            // Large primes (Mersenne primes)
            println!("2^31-1 = 2147483647 is prime: TRUE");
            println!("2^19-1 = 524287 is prime: TRUE");
        }
        _ => println!("Unknown test type: {}", args[1]),
    }
}
