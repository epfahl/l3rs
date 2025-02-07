A prototype _little logic language_ (L3) in Rust.

This is similar in spirit to what is described in
[_Beyond unification: A little logic language_](https://www.ericpfahl.com/beyond-unification-a-basic-logical-toolkit/).
However, instead of using higher-order functions, this Rust implementation represents the
basic logical goals as `enum` variants, and a logic program (a composition of goals) is executed
by recursively interpreting these variants.
