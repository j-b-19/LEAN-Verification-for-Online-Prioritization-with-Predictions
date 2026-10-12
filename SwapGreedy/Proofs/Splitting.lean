import SwapGreedy.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.Linarith

/-!
# Splitting

Section 5 of `latex/swap_greedy.tex`, Lemma `lem:splitting`, in the generalized form for
`c`-optimal initial schedules (`c = 1` is the lemma of the paper).

The family `(i_ρ, t_ρ)` of the paper is given by a set of steps `T` and the map
`t_ρ ↦ i_ρ`, which is injective on `T`.
-/

namespace SwapGreedy

open Finset

variable {n : ℕ}

/-- A map that is injective on `T ⊆ I` and maps `T` into `I` extends to an injective map
that maps `I` into `I` and is the identity outside `I`. -/
theorem exists_injective_extend (I T : Finset (Fin n)) (f : Fin n → Fin n) (hT : T ⊆ I)
    (hf : Set.InjOn f T) (hfI : ∀ t ∈ T, f t ∈ I) :
    ∃ τ : Fin n → Fin n, Function.Injective τ ∧ (∀ t ∈ T, τ t = f t) ∧ (∀ t ∉ I, τ t = t) ∧
      ∀ t ∈ I, τ t ∈ I := by
  classical
  set A := I \ T
  set B := I \ T.image f
  have hcard : Fintype.card A = Fintype.card B := by
    simp only [Fintype.card_coe, A, B, card_sdiff_of_subset hT,
      card_sdiff_of_subset (image_subset_iff.mpr hfI), card_image_of_injOn hf]
  let e : A ≃ B := Fintype.equivOfCardEq hcard
  let τ : Fin n → Fin n := fun t =>
    if t ∈ T then f t else if h : t ∈ A then (e ⟨t, h⟩ : Fin n) else t
  have hτT : ∀ t ∈ T, τ t = f t := fun t ht => by simp [τ, ht]
  have hτA : ∀ t (h : t ∈ A), τ t = e ⟨t, h⟩ := fun t h => by
    simp [τ, (mem_sdiff.mp h).2, h]
  have hτI : ∀ t ∉ I, τ t = t := fun t ht => by
    have : t ∉ T := fun h => ht (hT h)
    have : t ∉ A := fun h => ht (mem_sdiff.mp h).1
    simp [τ, *]
  have hB : ∀ t (h : t ∈ A), (e ⟨t, h⟩ : Fin n) ∈ B := fun t h => (e ⟨t, h⟩).2
  refine ⟨τ, ?_, hτT, hτI, fun t ht => ?_⟩
  · intro a b hab
    by_cases haT : a ∈ T <;> by_cases hbT : b ∈ T
    · exact hf haT hbT (by rwa [hτT a haT, hτT b hbT] at hab)
    · have hbI : b ∈ I := by
        by_contra hbI; rw [hτT a haT, hτI b hbI] at hab; exact hbI (hab ▸ hfI a haT)
      have hbA : b ∈ A := mem_sdiff.mpr ⟨hbI, hbT⟩
      rw [hτT a haT, hτA b hbA] at hab
      exact absurd (mem_image_of_mem f haT) (hab ▸ (mem_sdiff.mp (hB b hbA)).2)
    · have haI : a ∈ I := by
        by_contra haI; rw [hτT b hbT, hτI a haI] at hab; exact haI (hab ▸ hfI b hbT)
      have haA : a ∈ A := mem_sdiff.mpr ⟨haI, haT⟩
      rw [hτT b hbT, hτA a haA] at hab
      exact absurd (mem_image_of_mem f hbT) (hab ▸ (mem_sdiff.mp (hB a haA)).2)
    · by_cases haI : a ∈ I <;> by_cases hbI : b ∈ I
      · have haA : a ∈ A := mem_sdiff.mpr ⟨haI, haT⟩
        have hbA : b ∈ A := mem_sdiff.mpr ⟨hbI, hbT⟩
        rw [hτA a haA, hτA b hbA] at hab
        simpa using e.injective (Subtype.ext hab)
      · have haA : a ∈ A := mem_sdiff.mpr ⟨haI, haT⟩
        rw [hτA a haA, hτI b hbI] at hab
        exact absurd (hab ▸ (mem_sdiff.mp (hB a haA)).1) hbI
      · have hbA : b ∈ A := mem_sdiff.mpr ⟨hbI, hbT⟩
        rw [hτA b hbA, hτI a haI] at hab
        exact absurd (hab ▸ (mem_sdiff.mp (hB b hbA)).1) haI
      · rwa [hτI a haI, hτI b hbI] at hab
  · by_cases htT : t ∈ T
    · rw [hτT t htT]; exact hfI t htT
    · have htA : t ∈ A := mem_sdiff.mpr ⟨ht, htT⟩
      rw [hτA t htA]; exact (mem_sdiff.mp (hB t htA)).1

/-- `lem:splitting`, generalized: for a `c`-optimal identity, distinct items `f t ∈ I` at
distinct steps `t ∈ T ⊆ I` collect at most `c · ∑_{a ∈ I} a(a)`. This is `c`-optimality
for the injection `T ↪ I` induced by `f`. -/
theorem splitting {S : Instance n} {c : ℝ} (hloc : EtaOptimal S c)
    (I T : Finset (Fin n)) (f : Fin n → Fin n) (hT : T ⊆ I) (hf : Set.InjOn f T)
    (hfI : ∀ t ∈ T, f t ∈ I) :
    ∑ t ∈ T, S (f t) t ≤ c * ∑ a ∈ I, S a a := by
  let μ : T ↪ I := ⟨fun t => ⟨f t, hfI t t.2⟩, fun a b h =>
    Subtype.ext (hf a.2 b.2 (congrArg Subtype.val h))⟩
  rw [← Finset.sum_coe_sort T]
  exact hloc I T hT μ

/-- Conversely, `c`-optimality (for `c ≥ 1` on a non-negative instance) follows from its
permutation form: rearranging the identity by a permutation `τ` of the steps gains at most
a factor `c` on the affected steps `τ.support`. -/
theorem etaOptimal_of_perm {S : Instance n}
    {c : ℝ} (hc : 1 ≤ c)
    (hperm : ∀ τ : Equiv.Perm (Fin n), ∑ t ∈ τ.support, S (τ t) t ≤ c * ∑ t ∈ τ.support, S t t) :
    EtaOptimal S c := by
  classical
  intro I T hT μ
  let f : Fin n → Fin n := fun t => if h : t ∈ T then (μ ⟨t, h⟩ : Fin n) else t
  have hfT : ∀ t (h : t ∈ T), f t = μ ⟨t, h⟩ := fun t h => by simp [f, h]
  have hf : Set.InjOn f T := fun a ha b hb hab => by
    rw [hfT a ha, hfT b hb] at hab
    simpa using μ.injective (Subtype.ext hab)
  have hfI : ∀ t ∈ T, f t ∈ I := fun t ht => by rw [hfT t ht]; exact (μ _).2
  have hsum : ∑ i : T, S (μ i) i = ∑ t ∈ T, S (f t) t := by
    rw [← Finset.sum_coe_sort T]
    exact Finset.sum_congr rfl fun t _ => by rw [hfT t t.2]
  rw [hsum]
  obtain ⟨τ, hτinj, hτT, hτI, -⟩ := exists_injective_extend I T f hT hf hfI
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
  have he : ∀ t, e t = τ t := fun _ => rfl
  have hsupp : e.support ⊆ I := fun t ht => by
    by_contra hI; exact (Equiv.Perm.mem_support.mp ht) (by rw [he, hτI t hI])
  have hloc' := hperm e
  have h1 : ∑ t ∈ T, S (f t) t ≤ ∑ t ∈ I, S (τ t) t := by
    have : ∑ t ∈ T, S (f t) t = ∑ t ∈ T, S (τ t) t :=
      Finset.sum_congr rfl fun t ht => by rw [hτT t ht]
    rw [this]
    exact sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => S.nonneg _ _
  have h2 : ∑ t ∈ I, S (τ t) t = ∑ t ∈ I \ e.support, S t t + ∑ t ∈ e.support, S (e t) t := by
    rw [← sum_sdiff hsupp]
    congr 1
    refine sum_congr rfl fun t ht => ?_
    have := (mem_sdiff.mp ht).2
    rw [Equiv.Perm.mem_support, not_not, he] at this
    rw [this]
  have h3 : ∑ t ∈ I, S t t = ∑ t ∈ I \ e.support, S t t + ∑ t ∈ e.support, S t t :=
    (sum_sdiff hsupp).symm
  have h4 : 0 ≤ ∑ t ∈ I \ e.support, S t t := sum_nonneg fun _ _ => S.nonneg _ _
  nlinarith

/-- A sequence of `k ≤ n` items, extended by the identity to all steps of `Fin n`. -/
def extend {k : ℕ} (σ : Fin k → Fin n) : Fin n → Fin n :=
  fun j => if h : (j : ℕ) < k then σ ⟨j, h⟩ else j

theorem extend_castLE {k : ℕ} (hk : k ≤ n) (σ : Fin k → Fin n) (t : Fin k) :
    extend σ (Fin.castLE hk t) = σ t := by
  simp [extend, t.isLt]

end SwapGreedy
