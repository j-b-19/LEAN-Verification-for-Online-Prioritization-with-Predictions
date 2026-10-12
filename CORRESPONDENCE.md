# Correspondence between the paper and the Lean formalization

Only `SwapGreedy/Defs.lean`, `SwapGreedy/Algorithms.lean` and `SwapGreedy/MainTheorem.lean` need to be human-checked.
All other files contain proofs.
Paths are relative to `SwapGreedy/`.
The paper's parameter `λ` is `δ` in Lean, and `λ̂ = max(λ, (1 + λ)/λ)` is `lamHat δ = max δ (1 + 1/δ)`; steps and items are 0-indexed, and the stopping step `k` is `l + 1` for the last step `l : Fin n` of the prefix.

## Introduction

| Paper | Lean |
| --- | --- |
| instance: non-negative matrix with non-increasing rows | `Defs.lean`: `Instance` (coerces to its matrix) |
| objective value `f_k(τ)` | `Defs.lean`: `value` |
| prediction model: `τ(t)` only depends on the first `t` columns | `Defs.lean`: `Algorithm` (output `Fin n ↪ Fin n`), `Algorithm.Online` |
| Definition `η`-optimality (of the identity) | `Defs.lean`: `EtaOptimal`, `PredictionError` |
| Definition *Consistency and Robustness* | `Defs.lean`: `CompetitiveSchedule`, `Algorithm.Competitive`, `Algorithm.Consistent`, `Algorithm.Robust`; `Proofs/ConsistencyRobustness.lean`: `predictionError_eq_one_iff`, `Algorithm.Competitive.consistent` |
| `thmUpper`: `ρ = min(η · λ̂, 1 + λ)`, `λ̂`-consistent, `(1 + λ)`-robust | `MainTheorem.lean`: `swapGreedy_competitive`, `swapGreedy_consistent`, `swapGreedy_robust` |
| `thmLower` | `MainTheorem.lean`: `φ_le_consistency`, `two_le_robustness`, `consistency_robustness_tradeoff` |

Notes:
- `Algorithm.Robust` only asks for `r`-competitiveness on instances on which the identity is `η`-optimal for some `η`, while the paper asks it on every instance.
  `Run.robust` holds on every instance.
- `thmLower` is proved for instances with two steps; padding to `n` steps is not formalized.
- An arbitrary initial schedule `τ_0` is encoded by permuting `S`, as in the paper, so the prediction is always the identity.
- Not formalized: the special cases `λ = 1` and `λ = φ` stated after `thmUpper`, and the remark that `η`-optimality implies `f_n(OPT) ≤ η f_n(τ)`.

## The Algorithm

| Paper | Lean |
| --- | --- |
| `alg:swapgreedy` (with tie-breaking by smallest index) | `Algorithms.lean`: `Step`, `IsSGResult`, `swapGreedy`; `Proofs/SGRun.lean`: `Run`, `Run.isSGResult_iff` |
| well-definedness (no counterpart in the paper) | `Proofs/Existence.lean`: `exists_isSGResult`, `isSGResult_swapGreedy` |
| remark: `λ`-SwapGreedy is online | `MainTheorem.lean`: `swapGreedy_online`; `Proofs/Online.lean`: `Step.congr`, `Step.unique`, `Run.state_eq_of_agree` |
| facts about runs used implicitly | `Proofs/SGRun.lean`: `Step.eq_swap_or_eq`, `Inv`, `Run.inv_state`, `Run.result_injective`, `Run.exists_pos_of_available`, `Run.home_of_available` |

## Algorithmic Inequalities

| Paper | Lean |
| --- | --- |
| `lem:PMA` (A), (M), (P) | `Proofs/Greedy.lean`: `Greedy` (the inequalities as fields); `Proofs/SGRun.lean`: `Run.le_mul_of_available` (A), `Run.le_of_ne` (M), `Run.ineq_P` (P), `Run.toGreedy` |
| (D) | `Instance.antitone` |
| (S) | `EtaOptimal`; `Proofs/Splitting.lean`: `splitting` (for a map injective on a set), `etaOptimal_of_perm` |

"`c` is available at step `t`" (`c ∉ SG[t-1]`) is `∀ p < t, result p ≠ c`; `Greedy.available_iff` and `Greedy.not_mem_iff` restate availability and `t ∉ SG[t]` with the collection time `t_c = Greedy.collTime c`.

## Robustness

| Paper | Lean |
| --- | --- |
| `prop:robustness` | `Proofs/Robustness.lean`: `Run.robust`; `Proofs/Conclusion.lean`: `swapGreedy_robust_aux` |

## Components and Transfers

| Paper | Lean |
| --- | --- |
| graph `G`, components, `T_C`, `I_C`; step sets partition `[k]` | `Proofs/Components.lean`: `adj`, `Component`, `steps`, `IsItem`, `sum_steps`, `IsItem.unique` |
| `eq:competitive` | `Proofs/SmallComponents.lean`: `Greedy.prefix_le` |
| `ω`, `v_t`, `Φ_C` | `Proofs/Ledger.lean`: `Greedy.ω`, `Greedy.v`, `Greedy.Φ`; `ω` in (A), (M): `Greedy.ω_le_δ_mul`, `Greedy.ω_le` |
| `eq:charging_scheme` | `Proofs/Ledger.lean`: `LedgerIneq` (with `η = c`, `λ̂ = ρ`) |
| `lem:ledger` | `Proofs/Ledger.lean`: `Greedy.ledger` (for every comparison schedule, not only `OPT_k`) |

## Per-Component Analysis

| Paper | Lean |
| --- | --- |
| `lem:structure` | `Proofs/Components.lean`: `component_items`, `outer` (`= E_C`), `card_outer_le_one` |
| `def:steptypes`: `A_C`, `M_C`, `P_C`, partition of `T_C` | `Proofs/PerComponent.lean`: `Greedy.stepsA`, `stepsM`, `stepsP`, `sum_steps_eq`, `card_steps_eq` |
| `prop:generic` | `Proofs/PerComponent.lean`: `Greedy.generic`, from `dem_le_sum_items` ((S)), `sum_coll_hi_ge` (`eq:prop_generic_e_C`), `sum_A_bound`, `sum_coll_lo_ge` and `sum_M_bound` (`eq:prop_generic_A_C`, `eq:prop_generic_M_C`), `sum_P_bound` (`eq:prop_generic_P_C`) |
| `lem:covering` | `Proofs/SmallComponents.lean`: `Greedy.covering`, `Greedy.bracket` |
| `prop:onestep` | `Proofs/SmallComponents.lean`: `Greedy.onestep` |
| `prop:twosteps` | `Proofs/SmallComponents.lean`: `Greedy.twosteps` (Case 2: `twosteps_arith`) |

The parts of `Φ_C`'s first sum over the items of `A_C ∪ M_C` and of `P_C` are bounded together by indexing the sum by items (`sum_coll_lo_ge`): an item of `A_C ∪ M_C` is collected at a step `t_i ≤ i`, so its term is at least `i(i) - ω` by (D), and an item of `P_C` contributes `v_t - ω ≥ 0` by (M).

## Proof of Main Theorems

| Paper | Lean |
| --- | --- |
| proof of `thmUpper`: weights at least those at `φ` | `Proofs/SmallComponents.lean`: `weights_ge_φ` |
| remaining cases: `P_C = ∅` and `A_C`, `M_C` of sizes `(1, 0)`, `(0, 1)` or `(2, 0)` | `Proofs/SmallComponents.lean`: `one_le_weights_φ`, `Greedy.small_components` |
| assembly | `Proofs/SmallComponents.lean`: `Greedy.prefix_le`; `Proofs/Conclusion.lean`: `Run.competitive`, `swapGreedy_competitive_aux`, `swapGreedy_competitive_min_aux` |
| proof of `thmLower` | `Proofs/LowerBound.lean`: `lbInstance`, `lbInstance'`, `lb_dichotomy`, `φ_le_of_consistent`, `two_le_of_robust`, `one_le_tradeoff`, `div_le_of_consistent_of_robust` |

All main theorems depend only on the axioms `propext`, `Classical.choice`, `Quot.sound`.
