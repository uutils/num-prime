# num-prime

[![Crates.io](https://img.shields.io/crates/v/num-prime.svg)](https://crates.io/crates/num-prime)
[![CodSpeed](https://img.shields.io/endpoint?url=https://codspeed.io/badge.json)](https://codspeed.io/uutils/num-prime?utm_source=badge)
[![Discord](https://img.shields.io/badge/discord-join-7289DA.svg?logo=discord&longCache=true&style=flat)](https://discord.gg/wQVJbvJ)
[![License](http://img.shields.io/badge/license-Apache%202-blue.svg)](https://github.com/uutils/num-prime/blob/main/LICENSE)
[![dependency status](https://deps.rs/repo/github/uutils/num-prime/status.svg)](https://deps.rs/repo/github/uutils/num-prime)

This crate provides utilities for prime number related functionalities:
- Primality testing
  - Deterministic primality check of `u64` integers (using a very fast hashing algorithm)
  - Fermat probable prime test
  - Miller-rabin probable prime test
  - (strong/extra strong) Lucas probable prime test
  - Baillie-PSW test
  - Sophie Germain safe prime test
- Primes generation and indexing
  - A naive implementation of the sieve of Eratosthenes
  - Unified API to support other prime generation backends
  - Generate random (safe) primes
  - Find previous/next prime
- Integer factorization
  - Trial division
  - Pollard's rho algorithm
  - Shanks's square forms factorization (SQUFOF)
  - Fast factorization of `u64` and `u128` integers
- Number theoretic functions
  - Prime Pi function (number of primes under limit), its estimation and its bounds
  - Nth prime, its estimation and its bounds
  - Moebius function
  - Divisor Sigma function *([in examples](./examples/divisor_sigma.rs))*
  - Prime Omega function *([in examples](./examples/prime_omega.rs))*

It's based on the `num` creates and most functions are decently optimized with pre-computed tables (see **[benchmark results here](./PERFORMANCE.md)**).
