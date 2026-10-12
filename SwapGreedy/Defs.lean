import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Defs

/-! Definitions of the problem, the prediction, and algorithms (human-checked, with `Algorithms.lean` and `MainTheorem.lean`). -/

namespace SwapGreedy

variable {n : ℕ}

/-- The golden ratio `φ = (1 + √5) / 2`. -/
noncomputable def φ : ℝ := (1 + √5) / 2

/-! ## The problem -/

/-- An instance: `S i t ≥ 0` is the value of item `i` collected at step `t`, non-increasing in `t`. -/
structure Instance (n : ℕ) where
  S : Fin n → Fin n → ℝ
  nonneg : ∀ i t, 0 ≤ S i t
  antitone : ∀ i, Antitone (S i)

attribute [coe] Instance.S

/-- An instance is used as its matrix. -/
instance : CoeFun (Instance n) (fun _ => Fin n → Fin n → ℝ) := ⟨Instance.S⟩

/-- The value `f_k(σ) = ∑_{t < k} S (σ t) t` of a sequence `σ` of `k ≤ n` items. -/
def value (S : Instance n) {k : ℕ} (hk : k ≤ n) (σ : Fin k → Fin n) : ℝ :=
  ∑ t : Fin k, S (σ t) (Fin.castLE hk t)

/-- `π` is `c`-competitive on `S`: for every `k ≤ n`, no schedule of length `k` beats `c` times the length-`k` prefix of `π`. -/
def CompetitiveSchedule (S : Instance n) (c : ℝ) (π : Fin n → Fin n) : Prop :=
  ∀ (k : ℕ) (hk : k ≤ n) (σ : Fin k ↪ Fin n),
    value S hk σ ≤ c * value S hk (π ∘ Fin.castLE hk)

/-! ## The prediction -/

/-- The prediction, the identity, is `η`-optimal on `S`. -/
def EtaOptimal (S : Instance n) (η : ℝ) : Prop :=
  ∀ (I J : Finset (Fin n)), J ⊆ I → ∀ μ : J ↪ I, ∑ i : J, S (μ i) i ≤ η * ∑ i ∈ I, S i i

/-- The prediction error: the smallest `η ≥ 1` for which the identity is `η`-optimal (`0` if there is none). `η ≥ 1` is automatic except on the zero instance, where it avoids `sInf ℝ = 0`. -/
noncomputable def PredictionError (S : Instance n) : ℝ :=
  sInf {η : ℝ | 1 ≤ η ∧ EtaOptimal S η}

/-! ## Algorithms -/

/-- An algorithm maps an instance of any size `n` to a schedule, the injective sequence of items it collects at the steps `0, …, n-1`. -/
def Algorithm : Type := ∀ ⦃n : ℕ⦄, Instance n → Fin n ↪ Fin n

/-- The item collected at step `t` only depends on the columns `s ≤ t` of the instance. -/
def Algorithm.Online (A : Algorithm) : Prop :=
  ∀ ⦃n : ℕ⦄ (S S' : Instance n) (t : Fin n),
    (∀ i s : Fin n, s ≤ t → S i s = S' i s) → A S t = A S' t

/-- On every instance with some `η`-optimal prediction, the output is `ρ η`-competitive for the prediction error `η`. -/
def Algorithm.Competitive (ρ : ℝ → ℝ) (A : Algorithm) : Prop :=
  ∀ ⦃n : ℕ⦄ (S : Instance n), (∃ η : ℝ, EtaOptimal S η) →
    CompetitiveSchedule S (ρ (PredictionError S)) (A S)

/-- The output is `c`-competitive on every instance with prediction error `1`. -/
def Algorithm.Consistent (c : ℝ) (A : Algorithm) : Prop :=
  ∀ ⦃n : ℕ⦄ (S : Instance n), PredictionError S = 1 → CompetitiveSchedule S c (A S)

/-- The output is `r`-competitive on every instance with some `η`-optimal prediction. -/
def Algorithm.Robust (r : ℝ) (A : Algorithm) : Prop := A.Competitive fun _ => r

end SwapGreedy
