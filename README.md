# edit-distance

Formal verification of the Levenshtein (edit) distance in [Rocq](https://rocq-prover.org/),
including a proof that a C implementation refines a verified functional model using the
[Verified Software Toolchain](http://vst.cs.princeton.edu/) (VST).

This proof development was carried out with assistance from Claude and Codex.

The development is structured in three layers, each proved equivalent to the next:

1. an **intrinsically-correct recursive** model, whose dependently-typed definition
   carries its own optimality proof;
2. a **dynamic-programming** model in the Wagner–Fischer style, proved to compute
   the same value as the recursive model; and
3. a **C implementation** (`levenshtein.c`), proved with VST to refine the
   dynamic-programming model.

## What Is Proved

### Recursive model

`theories/Levenshtein_recursive.v` defines edit scripts as indexed Rocq types:

- `edit s t` is one insertion, deletion, or non-equal-character update from
  `s` to `t`.
- `chain s t n` is an edit script from `s` to `t` with exactly `n` charged
  edits; equal heads are skipped at no cost.
- `levenshtein_chain s t` computes both a distance and a witness edit script.
- `levenshtein_recursive s t` is the numeric distance extracted from that
  witness.

The main theorem, `levenshtein_recursive_is_minimal`, proves that the computed
distance is minimal: for every edit script `chain s t n`,
`levenshtein_recursive s t <= n`.  Since `levenshtein_chain` also returns a
witness script with exactly that distance, the recursive model computes the true
Levenshtein distance.

### Dynamic-programming model

`theories/Levenshtein_dp.v` defines `levenshtein_dp`, a Wagner-Fischer-style
dynamic-programming implementation over Rocq strings.  It also contains
index-based cache and loop-state lemmas used by the C proof.

The main theorem, `levenshtein_dp_eq_levenshtein_recursive`, proves that for all
strings `s` and `t`, `levenshtein_dp s t = levenshtein_recursive s t`.  The DP
proof first shows that the left-to-right cache traversal computes the recursive
model on reversed inputs, then uses reversal invariance of the recursive
distance to remove the reversals.

### C implementation

`theories/Verif_levenshtein.v` proves the generated Clight body of `levenshtein_n`
against a VST function specification.  The specification interprets the input
byte arrays as Rocq strings with `bytes_to_string`, requires the usual pointer
and `size_t` bounds, and states that the returned `size_t` is exactly:

```coq
Levenshtein.levenshtein_recursive
  (bytes_to_string a)
  (bytes_to_string b)
```

The proof connects the C loops to the DP cache model, then uses
`levenshtein_dp_eq_levenshtein_recursive` to conclude that the C result is the
intrinsic Levenshtein distance.

## Files

| File | Description |
| --- | --- |
| `theories/Levenshtein_recursive.v` | Intrinsic edit-script model and proof that `levenshtein_recursive` is minimal among all edit scripts. |
| `theories/Levenshtein_dp.v` | Wagner-Fischer dynamic-programming model `levenshtein_dp`, proved equal to `levenshtein_recursive`. |
| `levenshtein.c` | The C implementation that is verified. |
| `theories/levenshtein.v` | CompCert Clight AST generated from `levenshtein.c` (via `clightgen`). |
| `theories/Verif_levenshtein.v` | VST proof that `levenshtein_n` returns the intrinsic recursive distance for the input byte arrays. |

All `.v` files live under `theories/` and form the Coq theory `EditDistance`,
so modules are referenced as `EditDistance.Levenshtein_dp`, etc.

## Requirements

- Rocq / `coq-core` ≥ 9.0
- [VST](https://vst.cs.princeton.edu/) ≥ 2.16 (which bundles CompCert and Flocq)
- dune ≥ 3.21

These can be installed with opam:

```sh
opam install dune coq-vst
```

## Building

The project is built with [dune](https://dune.build/); the `Makefile` is a thin
frontend to it.

```sh
make          # dune build
make clean    # dune clean + git clean
make install  # dune install
```

Equivalently, run `dune build` directly. Build artifacts go under `_build/`.

## Regenerating the Clight AST

`theories/levenshtein.v` is generated from `levenshtein.c` and should not be edited by hand:

```sh
clightgen -normalize -o theories/levenshtein.v levenshtein.c
```
