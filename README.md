# soroban-fixed-point-math
A fixed-point math library for Soroban smart contacts.

## Safety
This is **experimental software** and is provided on an "as is" and "as available" basis.

We do **not give any warranties** and **will not be liable for any loss** incurred through any use of this codebase.

## Usage
Add this to your `Cargo.toml`:

```toml
[dependencies]
soroban_fixed_point_math = "<desired version>"
```

### FixedPoint Trait

The `FixedPoint` trait is implemented for the Rust generic integers `i64`, `u64`, `i128`, and `u128`. Any overflow or divide by zero that occurs during the fixed point math calculation will return a value of `None`, in line with Rust's existing checked math functions.

Phantom overflows are errors that result from an overflow during an intermediate calculation, but the expected result would be within bounds. This trait manages this differently for each implemented integer type:

* i64 and u64
    * In the event of a phantom overflow, the intermediary computation gets scaled to `i128` / `u128` and is retried.
* i128 and u128
    * In the event of a phantom overflow, the function will terminate and return `None`. If you need larger numbers to be handled, please use the `SorobanFixedPoint` trait.

### SorobanFixedPoint Trait

The `SorobanFixedPoint` trait is implemented for the Soroban host types `I256` and `U256`. The trait will panic if any `I256` or `U256` arithmetic error occurs, as host function calls panic by default.

Additional implementations of the `SorobanFixedPoint` trait are included for `i128` and `u128` integer types to support larger intermediary computations. This removes the majority of phantom overflow events for 128 bit fixed point math.

### Examples
For any supported type implementing `FixedPoint`, you can perform fixed-point operations like this:

```rust
use soroban_fixed_point_math::FixedPoint;

let x: u64 = 1_5000000;
let y: u64 = 2_0000000;
assert_eq!(x.fixed_mul_floor(y, 1_0000000).unwrap(), 3_0000000);
```

For any support type implementing `SorobanFixedPoint`, you can perform fixed-point operations like this:

```rust
use soroban_fixed_point_math::SorobanFixedPoint;
use soroban_sdk::{Env, I256};

let env: Env //... from your contract, or Env::default() in a test
let x: I256 = I256::from_i32(&env, 1_5000000);
let y: I256 = I256::from_i32(&env, 2_0000000);
assert_eq!(x.fixed_mul_ceil(&x, &y, I256::from_i32(&env, 1_0000000)), 3_0000000);
```

## Acknowledgements
This library was inspired by or directly modified from many sources, primary:
- [Solmate](https://github.com/transmissions11/solmate)
- [OpenZeppelin](https://github.com/OpenZeppelin/openzeppelin-contracts)

## WASM
The WASM target `wasm32-unknown-unknown` is supported.

## Formal verification

The standalone Lean project in [`verification`](verification/README.md) models checked signed-`I256` and signed-`i128` arithmetic. It proves that the positive-denominator floor and ceiling paths in `src/i256.rs`, and the non-widening `FixedPoint for i128` paths in `src/i128.rs`, refine mathematical floor and ceiling under explicit range hypotheses. It also verifies the `i128` implementation's `none` result for phantom overflow and zero denominators. Downstream users must prove the success hypotheses for their own operating domains.

## Contributions
Contributions are welcome. Please check out the contribution guide (TODO)!

## License
This library is released under the [MIT License](../LICENSE).
