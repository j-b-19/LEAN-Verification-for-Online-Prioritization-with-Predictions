# LEAN-Verification-for-Online-Prioritization-with-Predictions

This repository contains a Lean 4 formalization of the main results of the paper _"Tight Consistency-Robustness Tradeoff for Online Prioritization with Predictions"_:

- **Upper bound:** for every `λ ≥ 1`, the algorithm `λ`-SwapGreedy is online and `min(η · λ̂, 1 + λ)`-competitive on instances with prediction error `η`, where `λ̂ = max(λ, (1 + λ)/λ)`. In particular, it is `λ̂`-consistent and `(1 + λ)`-robust.
- **Lower bound:** no online algorithm is `c`-consistent for `c < φ` or `r`-robust for `r < 2`, and every `c`-consistent online algorithm has robustness at least `c/(c-1)`.

The parameter `λ` of the paper is denoted `δ` in the formalization.

## Trusted Code

Certifying the formalization requires reading only the following three files, which sum to approximately 150 lines. They contain the model, the algorithm and the statements of the main theorems. All remaining files contain proofs, which are checked by Lean.

| File                                                         | Contents                                                                                                                                                                                                     |
| ------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| [`SwapGreedy/Defs.lean`](SwapGreedy/Defs.lean)               | The model: instances, the objective value, competitiveness, `η`-optimality of the prediction, the prediction error, algorithms, and the notions of online, competitive, consistent and robust algorithms     |
| [`SwapGreedy/Algorithms.lean`](SwapGreedy/Algorithms.lean)   | The algorithm `δ`-SwapGreedy                                                                                                                                                                                 |
| [`SwapGreedy/MainTheorem.lean`](SwapGreedy/MainTheorem.lean) | The statements of the main theorems: `φ_le_consistency`, `two_le_robustness`, `consistency_robustness_tradeoff`, `swapGreedy_online`, `swapGreedy_competitive`, `swapGreedy_consistent`, `swapGreedy_robust` |

The formalization contains no `sorry` and introduces no additional axioms. All main theorems depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`, as can be confirmed with `#print axioms`.

[`CORRESPONDENCE.md`](CORRESPONDENCE.md) relates each definition, lemma and proposition of the paper to its counterpart in the formalization.

## Building

The project uses Lean `v4.28.0` and Mathlib `v4.28.0` (see `lean-toolchain` and `lakefile.toml`). With [elan](https://github.com/leanprover/elan) installed, the project is built by

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Repository Structure

```
CORRESPONDENCE.md          correspondence between the paper and the formalization
SwapGreedy.lean            library root
SwapGreedy/
  Defs.lean                model and definitions             (trusted)
  Algorithms.lean          δ-SwapGreedy                      (trusted)
  MainTheorem.lean         statements of the main theorems   (trusted)
  Proofs/
    SGRun.lean             runs of the algorithm and their invariants
    Existence.lean         well-definedness of the algorithm
    Online.lean            the algorithm is online
    Greedy.lean            the algorithmic inequalities (A), (M), (P)
    Splitting.lean         the splitting lemma, inequality (S)
    PredictionError.lean   properties of the prediction error
    ConsistencyRobustness.lean  consistency and robustness from competitiveness
    Robustness.lean        robustness 1 + δ
    Components.lean        components of the graph formed by prediction and optimum
    Ledger.lean            the potential Φ_C and the ledger lemma
    PerComponent.lean      per-component analysis
    SmallComponents.lean   components with one or two steps
    GoldenRatio.lean       properties of φ
    Conclusion.lean        proof of the upper bound
    LowerBound.lean        proof of the lower bound
```

## Disclosure of AI Usage

The definitions and main theorem statements of this formalization were guided by the authors. All proofs were written by Claude Opus 5.5.
