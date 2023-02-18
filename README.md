An unnamed toy programming language, inspired by Rust and Python.

Sample code:
```rust
// Calculates the x'th Fibonacci number
let fib = |x| {
	if x == 0 {
		0
	} else if x == 1 {
		1
	} else {
		fib(x - 1) + fib(x - 2)
	}
}

fib(15)
```

To run locally:
1. Clone this repository somewhere
2. Run `cargo test` to verify everything works correctly
3. Run `cargo run --release sample.txt` to run the above sample code.
