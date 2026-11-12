# Asymptotic 1-factorization of dense regular graphs (Lean 4)

A Lean 4 / Mathlib proof that for every `ε > 0` there is `N` such that every `d`-regular simple
graph on `2n` vertices with `n ≥ N` and `d ≥ (1 + ε) n` is 1-factorizable (Perković–Reed 1997,
Häggkvist), following E. R. Vaughan, *An asymptotic version of the multigraph 1-factorization
conjecture* (arXiv:1010.5192), for multiplicity 1.

## Statements (`AOFChallenge.lean`, Mathlib definitions only)

* `PerkovicReed.one_factorization`: the statement with a real `ε > 0`.
* `PerkovicReed.one_factorization_of_ge`: the integer form `(q + 1) n ≤ q d`.

## Proof (`AOF/`)

| File | Content |
|---|---|
| `Chernoff`, `Partition` | counting Chernoff bound; balanced bipartition (Vaughan, Lemma 13) |
| `Matchings`, `Classes` | matchings, Hall (Lemma 9, regular bipartite), equitable classes with matched sizes |
| `State`, `PathExists`, `Exchange*`, `Step2` | Step 2: alternating-path exchanges and their invariants |
| `Step1`, `Initial` | Step 1: the initial state |
| `Family`, `Extend`, `Lemma14` | Steps 3–4 and Vaughan's Lemma 14 |
| `Main` | parameters and the final theorem |

Equitable edge colourings (Vizing + McDiarmid) come from the registered Vizing entry
([jtraverso/vizing](https://github.com/jtraverso/vizing) @ `33b2de8`, PALOMAR-2026-10-15-000004),
required as a lake dependency; no code is copied. See `NOTES.md` for the repaired step.

## Build

Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`: `lake build`. Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

## License

Apache 2.0. Author: Juan Pablo Traverso Gianini.
