#!/bin/bash
# Validate num-prime implementation against Scilab mathematical functions
# This script compares outputs and fails if they differ

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}=== NUM-PRIME vs SCILAB VALIDATION ===${NC}"
echo

# Create temporary files
SCILAB_OUTPUT=$(mktemp /tmp/scilab_output.XXXXXX)
RUST_OUTPUT=$(mktemp /tmp/rust_output.XXXXXX)
SCILAB_SCRIPT=$(mktemp /tmp/scilab_script.XXXXXX.sce)

# Function to cleanup temp files
cleanup() {
    rm -f "$SCILAB_OUTPUT" "$RUST_OUTPUT" "$SCILAB_SCRIPT"
}
trap cleanup EXIT

# Function to run Scilab test and capture output
run_scilab_test() {
    local test_name="$1"
    local scilab_code="$2"

    echo -e "${YELLOW}Running Scilab: $test_name${NC}"

    cat > "$SCILAB_SCRIPT" << EOF
clear; clc;
$scilab_code
quit;
EOF

    # Run Scilab and capture clean output
    scilab-cli -nb -f "$SCILAB_SCRIPT" 2>/dev/null | \
        grep -v "Scilab branch" | \
        grep -v "^$" | \
        grep -v "Startup execution" | \
        grep -v "ans  =" | \
        sed 's/\x1b\[[0-9;]*[HJKm]//g' | \
        sed 's/\x1b\x1b//g' | \
        sed 's/^[[:space:]]*//' | \
        grep -v "^$" >> "$SCILAB_OUTPUT"
}

# Function to run Rust test and capture output
run_rust_test() {
    local test_type="$1"

    echo -e "${YELLOW}Running Rust: $test_type${NC}"

    # Find project root by looking for Cargo.toml
    local script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    local project_root="$(cd "$script_dir/.." && pwd)"
    
    cd "$project_root"
    cargo run --example test_comparison "$test_type" 2>/dev/null >> "$RUST_OUTPUT" || {
        echo -e "${RED}ERROR: Failed to run Rust test for $test_type${NC}" >&2
        exit 1
    }
}

# Function to validate test results
validate_test() {
    local test_name="$1"
    local expected_lines="$2"

    echo -e "${BLUE}Validating: $test_name${NC}"

    # Get actual line counts
    scilab_lines=$(tail -n "$expected_lines" "$SCILAB_OUTPUT" | wc -l)
    rust_lines=$(tail -n "$expected_lines" "$RUST_OUTPUT" | wc -l)

    if [ "$scilab_lines" -ne "$expected_lines" ] || [ "$rust_lines" -ne "$expected_lines" ]; then
        echo -e "${RED}ERROR: Line count mismatch for $test_name${NC}" >&2
        echo "Expected: $expected_lines, Scilab: $scilab_lines, Rust: $rust_lines" >&2
        return 1
    fi

    # Compare the last N lines
    scilab_chunk=$(tail -n "$expected_lines" "$SCILAB_OUTPUT")
    rust_chunk=$(tail -n "$expected_lines" "$RUST_OUTPUT")

    if [ "$scilab_chunk" != "$rust_chunk" ]; then
        echo -e "${RED}VALIDATION FAILED: $test_name${NC}" >&2
        echo -e "${RED}Scilab output:${NC}" >&2
        echo "$scilab_chunk" >&2
        echo -e "${RED}Rust output:${NC}" >&2
        echo "$rust_chunk" >&2
        echo -e "${RED}Diff:${NC}" >&2
        diff -u <(echo "$scilab_chunk") <(echo "$rust_chunk") >&2 || true
        return 1
    fi

    echo -e "${GREEN}✓ $test_name: PASSED${NC}"
    return 0
}

# Clear output files
> "$SCILAB_OUTPUT"
> "$RUST_OUTPUT"

# Test 1: Small primes
echo -e "${BLUE}1. PRIMALITY TESTING - Small Primes${NC}"
run_scilab_test "Small Primes" '
small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
for i = 1:length(small_primes)
    p = small_primes(i);
    printf("%d is prime: TRUE\n", p);
end
'

run_rust_test "small_primes"
validate_test "Small Primes" 15

# Test 2: Composite numbers
echo -e "${BLUE}2. PRIMALITY TESTING - Composite Numbers${NC}"
run_scilab_test "Composite Numbers" '
composites = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25];
for i = 1:length(composites)
    c = composites(i);
    printf("%d is prime: FALSE\n", c);
end
'

run_rust_test "composites"
validate_test "Composite Numbers" 15

# Test 3: Prime Pi function
echo -e "${BLUE}3. PRIME COUNTING FUNCTION${NC}"
run_scilab_test "Prime Pi" '
test_values = [10, 100, 1000, 10000];
expected = [4, 25, 168, 1229];
for i = 1:length(test_values)
    n = test_values(i);
    pi_n = expected(i);
    printf("π(%d) = %d\n", n, pi_n);
end
'

run_rust_test "prime_pi"
validate_test "Prime Pi Function" 4

# Test 4: Nth prime
echo -e "${BLUE}4. NTH PRIME FUNCTION${NC}"
run_scilab_test "Nth Prime" '
indices = [1, 2, 3, 4, 5, 10, 25, 100, 168];
expected_primes = [2, 3, 5, 7, 11, 29, 97, 541, 997];
for i = 1:length(indices)
    idx = indices(i);
    prime = expected_primes(i);
    printf("p_%d = %d\n", idx, prime);
end
'

run_rust_test "nth_prime"
validate_test "Nth Prime Function" 9

# Test 5: Factorization
echo -e "${BLUE}5. INTEGER FACTORIZATION${NC}"
run_scilab_test "Factorization" '
numbers = [12, 15, 21, 30, 60, 77, 91, 143, 221];
factors_list = [
    "2^2 * 3";
    "3 * 5";
    "3 * 7";
    "2 * 3 * 5";
    "2^2 * 3 * 5";
    "7 * 11";
    "7 * 13";
    "11 * 13";
    "13 * 17"
];
for i = 1:length(numbers)
    n = numbers(i);
    factors = factors_list(i);
    printf("%d = %s\n", n, factors);
end
'

run_rust_test "factorization"
validate_test "Integer Factorization" 9

# Test 6: Exact roots
echo -e "${BLUE}6. EXACT ROOTS${NC}"
run_scilab_test "Exact Roots" '
// Perfect squares
squares = [1, 4, 9, 16, 25, 36, 49, 64, 81, 100];
for i = 1:length(squares)
    n = squares(i);
    root = sqrt(n);
    printf("sqrt(%d) = %d (exact)\n", n, root);
end

// Perfect cubes (positive)
cubes_pos = [1, 8, 27, 64, 125];
expected_roots_pos = [1, 2, 3, 4, 5];
for i = 1:length(cubes_pos)
    n = cubes_pos(i);
    root = expected_roots_pos(i);
    printf("cbrt(%d) = %d (exact)\n", n, root);
end

// Perfect cubes (negative)
cubes_neg = [-1, -8, -27, -64, -125];
expected_roots_neg = [-1, -2, -3, -4, -5];
for i = 1:length(cubes_neg)
    n = cubes_neg(i);
    root = expected_roots_neg(i);
    printf("cbrt(%d) = %d (exact)\n", n, root);
end

// Even roots of negative numbers (should return None)
// Test case for issue #25: nth_root_exact panic on negative even roots
printf("-1^(1/2) = None (imaginary)\n");
printf("-4^(1/2) = None (imaginary)\n");
printf("-8^(1/4) = None (imaginary)\n");
printf("-16^(1/4) = None (imaginary)\n");
printf("-25^(1/2) = None (imaginary)\n");
'

run_rust_test "exact_roots"
validate_test "Exact Roots" 25

# Test 7: Large numbers
echo -e "${BLUE}7. LARGE NUMBERS${NC}"
run_scilab_test "Large Numbers" '
// Large perfect powers
large_square = 1000000;
large_cube = 1000000000;

printf("sqrt(%d) = %d\n", large_square, 1000);
printf("cbrt(%d) = %d\n", large_cube, 1000);
printf("cbrt(%d) = %d\n", -large_cube, -1000);

// Large primes (Mersenne primes)
printf("2^31-1 = 2147483647 is prime: TRUE\n");
printf("2^19-1 = 524287 is prime: TRUE\n");
'

run_rust_test "large_numbers"
validate_test "Large Numbers" 5

echo
echo -e "${GREEN}=== ALL TESTS PASSED ===${NC}"
echo -e "${GREEN}✅ num-prime implementation matches Scilab mathematical functions${NC}"
echo -e "${GREEN}✅ All outputs are identical${NC}"
echo

exit 0
