import SwapGreedy.Proofs.Ledger
import Mathlib.Tactic.LinearCombination

/-!
# Per-component analysis

Section *Per-Component Analysis* of `latex/swap_greedy.tex` up to *Large Components and
Cycles*: `def:steptypes` and `prop:generic`, for a schedule `G : Greedy δ S` satisfying the
algorithmic inequalities, with `δ ≥ 1` for the paper's `λ` and `λ̂ = max(δ, 1 + 1/δ)`
(`lamHat δ`). `lem:structure` is `component_items` (`Components.lean`); `E_C = I_C \ T_C` is
`outer σ C`. As in `Ledger.lean`, the stopping step is `k = l + 1`.
-/

namespace SwapGreedy

open Finset Classical

variable {n : ℕ} {δ : ℝ} {S : Instance n} {l : Fin n}

/-! ## `λ̂` -/

/-- `λ̂ = max(λ, (1 + λ)/λ)`, written `max δ (1 + 1/δ)`. -/
noncomputable abbrev lamHat (δ : ℝ) : ℝ := max δ (1 + 1 / δ)

theorem le_lamHat (δ : ℝ) : δ ≤ lamHat δ := le_max_left _ _

theorem one_add_inv_le_lamHat (δ : ℝ) : 1 + 1 / δ ≤ lamHat δ := le_max_right _ _

theorem one_le_lamHat (hδ : 1 ≤ δ) : 1 ≤ lamHat δ := hδ.trans (le_lamHat δ)

/-- `λ̂ ≥ 1 + 1/λ`, multiplied by `λ`. -/
theorem add_one_le_lamHat_mul (hδ : 1 ≤ δ) : δ + 1 ≤ lamHat δ * δ := by
  have hδ0 : 0 < δ := by linarith
  calc δ + 1 = (1 + 1 / δ) * δ := by field_simp
    _ ≤ lamHat δ * δ := mul_le_mul_of_nonneg_right (one_add_inv_le_lamHat δ) hδ0.le

/-! ## `def:steptypes` -/

namespace Greedy

variable (G : Greedy δ S) (σ : Fin (l + 1) ↪ Fin n) (C : Component σ)

/-- The availability steps `A_C = {t ∈ T_C | t = SG(t)}`. -/
noncomputable def stepsA : Finset (Fin (l + 1)) :=
  (steps σ C).filter fun t => G.result (Fin.castLE l.isLt t) = Fin.castLE l.isLt t

/-- The maximum availability steps `M_C = {t ∈ T_C | t ∈ SG[t-1]}`. -/
noncomputable def stepsM : Finset (Fin (l + 1)) :=
  (steps σ C).filter fun t =>
    ∃ p : Fin n, p < Fin.castLE l.isLt t ∧ G.result p = Fin.castLE l.isLt t

/-- The preemption steps `P_C = {t ∈ T_C | t ∉ SG[t]}`. -/
noncomputable def stepsP : Finset (Fin (l + 1)) :=
  (steps σ C).filter fun t =>
    ∀ p : Fin n, p ≤ Fin.castLE l.isLt t → G.result p ≠ Fin.castLE l.isLt t

variable {G σ C}

theorem mem_stepsA {t : Fin (l + 1)} :
    t ∈ G.stepsA σ C ↔ t ∈ steps σ C ∧ G.collTime (Fin.castLE l.isLt t) = Fin.castLE l.isLt t := by
  simp only [stepsA, mem_filter, G.collTime_eq_iff]

theorem mem_stepsM {t : Fin (l + 1)} :
    t ∈ G.stepsM σ C ↔ t ∈ steps σ C ∧ G.collTime (Fin.castLE l.isLt t) < Fin.castLE l.isLt t := by
  simp only [stepsM, mem_filter]
  refine and_congr_right fun _ => ⟨fun ⟨p, hp, hpe⟩ => ?_, fun h => ⟨_, h, G.result_collTime _⟩⟩
  rwa [G.collTime_eq_iff.mpr hpe]

theorem mem_stepsP {t : Fin (l + 1)} :
    t ∈ G.stepsP σ C ↔ t ∈ steps σ C ∧ Fin.castLE l.isLt t < G.collTime (Fin.castLE l.isLt t) := by
  simp only [stepsP, mem_filter, G.not_mem_iff]

theorem ne_of_mem_stepsM {t : Fin (l + 1)} (ht : t ∈ G.stepsM σ C) :
    G.result (Fin.castLE l.isLt t) ≠ Fin.castLE l.isLt t := fun h =>
  (mem_stepsM.mp ht).2.ne (G.collTime_eq_iff.mpr h)

/-- `A_C`, `M_C`, `P_C` partition `T_C`. -/
theorem sum_steps_eq (f : Fin (l + 1) → ℝ) :
    ∑ t ∈ steps σ C, f t =
      ∑ t ∈ G.stepsA σ C, f t + ∑ t ∈ G.stepsM σ C, f t + ∑ t ∈ G.stepsP σ C, f t := by
  have hA : G.stepsA σ C =
      (steps σ C).filter fun t => G.collTime (Fin.castLE l.isLt t) = Fin.castLE l.isLt t := by
    ext t; simp only [mem_stepsA, mem_filter]
  have hM : G.stepsM σ C =
      ((steps σ C).filter fun t => ¬ G.collTime (Fin.castLE l.isLt t) = Fin.castLE l.isLt t).filter
      fun t => G.collTime (Fin.castLE l.isLt t) < Fin.castLE l.isLt t := by
    ext t; simp only [mem_stepsM, mem_filter]
    exact ⟨fun h => ⟨⟨h.1, h.2.ne⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  have hP : G.stepsP σ C =
      ((steps σ C).filter fun t => ¬ G.collTime (Fin.castLE l.isLt t) = Fin.castLE l.isLt t).filter
      fun t => ¬ G.collTime (Fin.castLE l.isLt t) < Fin.castLE l.isLt t := by
    ext t; simp only [mem_stepsP, mem_filter]
    exact ⟨fun h => ⟨⟨h.1, h.2.ne'⟩, not_lt.mpr h.2.le⟩,
      fun h => ⟨h.1.1, lt_of_le_of_ne (not_lt.mp h.2) (Ne.symm h.1.2)⟩⟩
  rw [hA, hM, hP, add_assoc, sum_filter_add_sum_filter_not, sum_filter_add_sum_filter_not]

theorem card_steps_eq :
    (steps σ C).card = (G.stepsA σ C).card + (G.stepsM σ C).card + (G.stepsP σ C).card := by
  have := sum_steps_eq (G := G) (C := C) (fun _ => (1 : ℝ))
  simp only [sum_const, nsmul_eq_mul, mul_one] at this
  exact_mod_cast this

/-! ## `prop:generic` -/

/-- `ineq:S` applied to `T_C ⊆ I_C` with the injection `OPT_k`:
`∑_{t ∈ T_C} OPT_k(t)(t) ≤ η · ∑_{i ∈ I_C} i(i)`. -/
theorem dem_le_sum_items {c : ℝ} (hloc : EtaOptimal S c) :
    dem S σ C ≤ c * ∑ a ∈ univ.filter (IsItem σ C), S a a := by
  set ι := Fin.castLE l.isLt
  have h := splitting hloc (univ.filter (IsItem σ C)) ((steps σ C).image ι)
    (extend σ)
    (fun x hx => by
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_univ _, isItem_castLE _ ht⟩)
    (fun a ha b hb hab => by
      simp only [coe_image, Set.mem_image, mem_coe] at ha hb
      obtain ⟨a, -, rfl⟩ := ha
      obtain ⟨b, -, rfl⟩ := hb
      rw [extend_castLE, extend_castLE] at hab
      rw [σ.injective hab])
    (fun x hx => by
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
      rw [extend_castLE]
      exact mem_filter.mpr ⟨mem_univ _, isItem_apply ht⟩)
  rw [sum_image (Fin.castLE_injective _).injOn] at h
  simp only [extend_castLE] at h
  exact h

/-- `I_C = T_C ⊔ E_C`: `∑_{i ∈ I_C} i(i) = ∑_{t ∈ T_C} t(t) + ∑_{e ∈ E_C} e(e)`. -/
theorem sum_items_eq :
    ∑ a ∈ univ.filter (IsItem σ C), S a a =
      ∑ t ∈ steps σ C, S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t) +
        ∑ j ∈ outer σ C, S j j := by
  set ι := Fin.castLE l.isLt
  rw [← sum_filter_add_sum_filter_not (univ.filter (IsItem σ C))
    (fun a : Fin n => (a : ℕ) < l + 1)]
  congr 1
  · have : (univ.filter (IsItem σ C)).filter (fun a : Fin n => (a : ℕ) < l + 1) =
        (steps σ C).image ι := by
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · rintro ⟨ha, hlt⟩
        exact ⟨⟨a, hlt⟩, mem_steps_of_isItem ha hlt, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨isItem_castLE _ ht, by simp [ι, Nat.lt_succ_iff.mp t.isLt]⟩
    rw [this, sum_image (Fin.castLE_injective _).injOn]
  · refine sum_congr ?_ fun _ _ => rfl
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_outer, not_lt]

/-- The items of `A_C ∪ M_C` are collected in the first `k` steps. -/
theorem image_coll_lo :
    (G.stepsA σ C ∪ G.stepsM σ C).image (Fin.castLE l.isLt) ⊆
      ((G.coll σ C).filter (fun t => G.result (Fin.castLE l.isLt t) ≤ l)).image
        (fun t => G.result (Fin.castLE l.isLt t)) := by
  intro c hc
  simp only [coll, mem_image, mem_filter, mem_univ, true_and, mem_union, stepsA, stepsM] at hc ⊢
  obtain ⟨t, ⟨hT, hA⟩ | ⟨hT, p, hp, hpe⟩, rfl⟩ := hc
  · refine ⟨t, ⟨?_, ?_⟩, hA⟩ <;> rw [hA]
    · exact isItem_castLE _ hT
    · exact castLE_le t
  · have hlt : (p : ℕ) < l + 1 := Nat.lt_succ_of_lt (Fin.lt_def.mp (hp.trans_le (castLE_le t)))
    have hιp : Fin.castLE l.isLt ⟨p, hlt⟩ = p := rfl
    refine ⟨⟨p, hlt⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [hιp, hpe]
    · exact isItem_castLE _ hT
    · exact castLE_le t

/-- The part of `Φ_C`'s first sum over the items `≤ k` of `C` is at least
`∑_{t ∈ A_C ∪ M_C} (t(t) - ω)`: an item of `A_C ∪ M_C` is collected at a step `t_i ≤ i`,
so `v_{t_i} ≥ i(i)` by (D), and every other collected item `≤ k` of `C` (an item of `P_C`,
collected at a step `t > SG(t)`) contributes `v_t - ω ≥ 0` by (M). -/
theorem sum_coll_lo_ge :
    ∑ t ∈ G.stepsA σ C, (S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t) - G.ω l) +
      ∑ t ∈ G.stepsM σ C, (S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t) - G.ω l) ≤
    ∑ t ∈ (G.coll σ C).filter (fun t => G.result (Fin.castLE l.isLt t) ≤ l),
      (G.v t - G.ω l) := by
  set ι := Fin.castLE l.isLt
  have hdisj : Disjoint (G.stepsA σ C) (G.stepsM σ C) := by
    rw [disjoint_left]
    intro t hA hM
    exact ne_of_mem_stepsM hM (mem_filter.mp hA).2
  rw [← sum_union hdisj]
  -- index the right-hand side by items
  have h : ∑ t ∈ (G.coll σ C).filter (fun t => G.result (ι t) ≤ l), (G.v t - G.ω l) =
      ∑ c ∈ ((G.coll σ C).filter (fun t => G.result (ι t) ≤ l)).image
        (fun t => G.result (ι t)), (S c (G.collTime c) - G.ω l) := by
    rw [sum_image (fun a _ b _ h => Fin.castLE_injective _ (G.result_injective h))]
    refine sum_congr rfl fun t _ => ?_
    simp only [v, G.collTime_result]
  have h' : ∑ t ∈ G.stepsA σ C ∪ G.stepsM σ C, (S (ι t) (ι t) - G.ω l) =
      ∑ c ∈ (G.stepsA σ C ∪ G.stepsM σ C).image ι, (S c c - G.ω l) := by
    rw [sum_image (Fin.castLE_injective _).injOn]
  rw [h, h']
  refine (sum_le_sum fun c hc => ?_).trans (sum_le_sum_of_subset_of_nonneg image_coll_lo
    fun c hc hc' => ?_)
  · -- the collection time of `t` is at most `t` for `t ∈ A_C ∪ M_C`
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hc
    refine sub_le_sub_right (S.antitone _ ?_) _
    rcases mem_union.mp ht with hA | hM
    · rw [(mem_stepsA.mp hA).2]
    · exact (mem_stepsM.mp hM).2.le
  · -- any other collected item `c ≤ k` of `C` is not collected at its home step
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hc
    simp only [coll, mem_filter, mem_univ, true_and] at ht
    have hne : G.result (ι t) ≠ ι t := fun he => by
      refine hc' (mem_image.mpr ⟨t, mem_union_left _ (mem_filter.mpr ⟨?_, he⟩), he.symm⟩)
      rw [he] at ht
      exact mem_steps_of_isItem ht.1 t.isLt
    rw [G.collTime_result]
    exact sub_nonneg.mpr (G.ω_le (castLE_le t) hne)

/-- `eq:prop_generic_e_C`: the part of `Φ_C`'s first sum over `E_C` is at least
`∑_{e ∈ E_C} e(e) - |E_C| · ω`. -/
theorem sum_coll_hi_ge :
    ∑ j ∈ outer σ C, S j j - (outer σ C).card * G.ω l ≤
    ∑ t ∈ (G.coll σ C).filter (fun t => ¬ G.result (Fin.castLE l.isLt t) ≤ l),
      (G.v t - G.ω l) := by
  set ι := Fin.castLE l.isLt
  set hi := (G.coll σ C).filter (fun t => ¬ G.result (ι t) ≤ l) with hhi
  set img := hi.image (fun t => G.result (ι t)) with himg
  have hinj : Set.InjOn (fun t => G.result (ι t)) ↑hi :=
    (G.result_injective.comp (Fin.castLE_injective l.isLt)).injOn
  have hsub : img ⊆ outer σ C := fun c hc => by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hc
    simp only [hhi, coll, mem_filter, mem_univ, true_and, not_le] at ht
    exact mem_outer.mpr ⟨ht.1, ht.2⟩
  -- collected items of `E_C` are worth at least their diagonal value, by (D)
  have h1 : ∑ j ∈ img, S j j ≤ ∑ t ∈ hi, G.v t := by
    rw [himg, sum_image hinj]
    refine sum_le_sum fun t ht => ?_
    simp only [hhi, mem_filter, not_le] at ht
    exact S.antitone _ (Fin.le_def.mpr ((castLE_le t).trans ht.2.le))
  -- uncollected items of `E_C` are worth at most `ω`
  have h2 : ∑ j ∈ outer σ C \ img, S j j ≤ (outer σ C \ img).card * G.ω l := by
    rw [← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun j hj => ?_
    obtain ⟨hjO, hjimg⟩ := mem_sdiff.mp hj
    obtain ⟨hjI, hjk⟩ := mem_outer.mp hjO
    have hjl : l < j := Fin.lt_def.mpr hjk
    refine (S.antitone j hjl.le).trans (G.le_ω fun t htl hte => hjimg ?_)
    have hlt : (t : ℕ) < l + 1 := Nat.lt_succ_of_le htl
    refine mem_image.mpr ⟨⟨t, hlt⟩, ?_, hte⟩
    simp only [hhi, coll, mem_filter, mem_univ, true_and, not_le]
    exact ⟨hte ▸ hjI, hte ▸ hjl⟩
  have h3 := sum_sdiff (f := fun j => S j j) hsub
  simp only at h3
  have h4 := card_sdiff_add_card_eq_card hsub
  have h5 : img.card = hi.card := card_image_of_injOn hinj
  have h6 : ((outer σ C \ img).card : ℝ) * G.ω l + hi.card * G.ω l =
      (outer σ C).card * G.ω l := by
    rw [← add_mul, ← h5]; exact_mod_cast congrArg (fun m : ℕ => (m : ℝ) * G.ω l) h4
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith

/-- `eq:prop_generic_A_C`: `∑_{t ∈ A_C} (t(t) + ω (λ̂ - 1)/λ) ≤ λ̂ ∑_{t ∈ A_C} v_t`, by (A). -/
theorem sum_A_bound (hδ : 1 ≤ δ) :
    ∑ t ∈ G.stepsA σ C, S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t) +
      (G.stepsA σ C).card * (G.ω l * ((lamHat δ - 1) / δ)) ≤
        lamHat δ * ∑ t ∈ G.stepsA σ C, G.v t := by
  rw [mul_sum, ← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
  refine sum_le_sum fun t ht => ?_
  have hA := (mem_filter.mp ht).2
  have hω := G.ω_le_δ_mul hδ (castLE_le t)
  simp only [v, hA] at hω ⊢
  have hδ0 : 0 < δ := by linarith
  have h1 := one_le_lamHat hδ
  have : G.ω l * ((lamHat δ - 1) / δ) ≤
      (lamHat δ - 1) * S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t) := by
    rw [← mul_div_assoc, div_le_iff₀ hδ0]
    nlinarith [mul_le_mul_of_nonneg_right hω (sub_nonneg.mpr h1)]
  linarith

/-- `eq:prop_generic_M_C`: `∑_{t ∈ M_C} (v_t + ω (λ̂ - 1)) ≤ λ̂ ∑_{t ∈ M_C} v_t`, by (M). -/
theorem sum_M_bound (hδ : 1 ≤ δ) :
    ∑ t ∈ G.stepsM σ C, G.v t + (G.stepsM σ C).card * (G.ω l * (lamHat δ - 1)) ≤
      lamHat δ * ∑ t ∈ G.stepsM σ C, G.v t := by
  rw [mul_sum, ← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
  refine sum_le_sum fun t ht => ?_
  have hω : G.ω l ≤ G.v t := G.ω_le (castLE_le t) (ne_of_mem_stepsM ht)
  have h1 := one_le_lamHat hδ
  nlinarith [mul_le_mul_of_nonneg_right hω (sub_nonneg.mpr h1)]

/-- `eq:prop_generic_P_C`: `∑_{t ∈ P_C} (t(t) + v_t) ≤ λ̂ ∑_{t ∈ P_C} v_t`, by (P) and
`λ̂ ≥ 1 + 1/λ`. -/
theorem sum_P_bound (hδ : 1 ≤ δ) :
    ∑ t ∈ G.stepsP σ C, S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t) +
      ∑ t ∈ G.stepsP σ C, G.v t ≤ lamHat δ * ∑ t ∈ G.stepsP σ C, G.v t := by
  rw [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun t ht => ?_
  have hP := G.ineq_P (mem_filter.mp ht).2
  have hδ0 : 0 < δ := by linarith
  have hv : 0 ≤ G.v t := S.nonneg _ _
  have h2 := add_one_le_lamHat_mul hδ
  have : δ * (S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t) + G.v t) ≤ δ * (lamHat δ * G.v t) := by
    simp only [v] at hv ⊢
    nlinarith [mul_le_mul_of_nonneg_right h2 hv]
  exact le_of_mul_le_mul_left this hδ0

/-- `prop:generic`: a component with `|A_C| (λ̂ - 1)/λ + |M_C| (λ̂ - 1) + |P_C| ≥ |E_C|`
satisfies `eq:charging_scheme`. -/
theorem generic (hδ : 1 ≤ δ) {c : ℝ} (hc : 1 ≤ c) (hloc : EtaOptimal S c)
    (hcount : ((outer σ C).card : ℝ) ≤
      (G.stepsA σ C).card * ((lamHat δ - 1) / δ) + (G.stepsM σ C).card * (lamHat δ - 1) +
        (G.stepsP σ C).card) :
    LedgerIneq c (lamHat δ) G σ C := by
  unfold LedgerIneq Φ
  have hw0 := G.ω_nonneg l
  refine (dem_le_sum_items hloc).trans (mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans hc))
  rw [sum_items_eq]
  have hT1 := sum_steps_eq (G := G) (C := C)
    (fun t => S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t))
  have hT2 : lamHat δ * ∑ t ∈ steps σ C, G.v t = lamHat δ * (∑ t ∈ G.stepsA σ C, G.v t +
      ∑ t ∈ G.stepsM σ C, G.v t + ∑ t ∈ G.stepsP σ C, G.v t) := by
    rw [sum_steps_eq (G := G) (C := C) G.v]
  have hT3 := sum_steps_eq (G := G) (C := C) (fun t => G.v t - G.ω l)
  have hcard : ((steps σ C).card : ℝ) =
      (G.stepsA σ C).card + (G.stepsM σ C).card + (G.stepsP σ C).card := by
    exact_mod_cast card_steps_eq (G := G) (C := C)
  have hColl := sum_filter_add_sum_filter_not (G.coll σ C)
    (fun t => G.result (Fin.castLE l.isLt t) ≤ l) (fun t => G.v t - G.ω l)
  have hlo := sum_coll_lo_ge (G := G) (C := C)
  have hhi := sum_coll_hi_ge (G := G) (C := C)
  have hA := sum_A_bound (G := G) (C := C) hδ
  have hM := sum_M_bound (G := G) (C := C) hδ
  have hP := sum_P_bound (G := G) (C := C) hδ
  have hAv : ∑ t ∈ G.stepsA σ C, G.v t =
      ∑ t ∈ G.stepsA σ C, S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t) :=
    sum_congr rfl fun t ht => by simp only [v, (mem_filter.mp ht).2]
  have hcw : ((outer σ C).card : ℝ) * G.ω l ≤
      (G.stepsA σ C).card * (G.ω l * ((lamHat δ - 1) / δ)) +
      (G.stepsM σ C).card * (G.ω l * (lamHat δ - 1)) + (G.stepsP σ C).card * G.ω l := by
    have := mul_le_mul_of_nonneg_right hcount hw0
    convert this using 1
    ring
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at hT3 hColl hlo hhi ⊢
  rw [hcard] at hT3 ⊢
  linarith

end Greedy

end SwapGreedy
