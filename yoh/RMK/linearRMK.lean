/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä, Yoh Tanimoto
-/
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.ContinuousFunction.CompactlySupported
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner

/-!
#  Riesz–Markov–Kakutani representation theorem

This file will prove a version of the Riesz-Markov-Kakutani representation theorem.
The theorem is first proven for locally compact Hausdorff (T2) spaces.
A large part of the file is an adaptation of the `EEReal` version by Jesse Reimann, Kalle Kytölä
to `ℝ` version.

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of the space X, rather than the usual construction of open sets in the literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/


noncomputable section

open BoundedContinuousFunction NNReal ENNReal

open Set Function TopologicalSpace CompactlySupported


variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : ∀ (f : C_c(X, ℝ)), 0 ≤ f.1 → 0 ≤ Λ f)

/-- Under the assumption `hΛ`, `Λ` is monotone. -/
lemma Λ_mono {f g : C_c(X, ℝ)} (h : f.1 ≤ g.1) : Λ f ≤ Λ g := by
  have : 0 ≤ g.1 - f.1 := by exact sub_nonneg.mpr h
  calc Λ f ≤ Λ f + Λ (g - f) := by exact le_add_of_nonneg_right (hΛ (g - f) this)
  _ = Λ (f + (g - f)) := by rw [← LinearMap.map_add Λ f (g - f)]
  _ = Λ g := by simp only [add_sub_cancel]

lemma Λ_neg {f : C_c(X, ℝ)} : Λ (-f) = - Λ f := by
  simp only [map_neg]


/-! ### Construction of the content: -/

/-- Given a positive linear functional Λ on X, for `K ⊆ X` compact define
`λ(K) = inf {Λf | 1≤f on K}`. When X is a compact Hausdorff space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
def rieszContentAux : Compacts X → ℝ := fun K =>
  sInf (Λ '' { f : C_c(X, ℝ) | HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x)
  ∧ (∀ (x : X), x ∈ K → 1 ≤ f x) })

section RieszMonotone

/-- For any compact subset `K ⊆ X`, there exist some bounded continuous nonnegative
functions f on X such that `f ≥ 1` on K. -/
theorem rieszContentAux_image_nonempty (K : Compacts X) :
    (Λ '' { f : C_c(X, ℝ) | HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x) ∧ (∀ (x : X),
    x ∈ K → 1 ≤ f x) }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hV.1 isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hV.1)]
    exact closure_mono interior_subset
  obtain ⟨f, hf⟩ := exists_tsupport_one_of_isOpen_isClosed isOpen_interior
    hIsCompact_closure_interior (IsCompact.isClosed K.2) hV.2
  have hfHasCompactSupport : HasCompactSupport f :=
    IsCompact.of_isClosed_subset hV.1 (isClosed_tsupport f) (Set.Subset.trans hf.1 interior_subset)
  use ⟨f, hfHasCompactSupport⟩
  simp only [mem_setOf_eq]
  constructor
  · exact IsCompact.of_isClosed_subset hV.1 (isClosed_tsupport f)
      (_root_.subset_trans hf.1 interior_subset)
  constructor
  · intro x
    exact (Set.mem_Icc.mp (hf.2.2 x)).1
  · intro x hx
    apply le_of_eq
    rw [← ContinuousMap.one_apply x]
    exact (hf.2.1 hx).symm

/-- `rieszContentAux Λ hΛ` is nonnegative. -/
lemma rieszContentAux_nonneg {K : Compacts X} : 0 ≤ rieszContentAux Λ K := by
  apply le_csInf
  exact rieszContentAux_image_nonempty Λ K
  intro b
  simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
  intro f _ hf _ hb
  rw [← hb]
  exact hΛ f hf

/-- The image of `rieszContentAux Λ hΛ` is bounded below. This is only a technical lemma
used below. -/
lemma rieszContentAux_image_BddBelow (K : Compacts X) :
    BddBelow (Λ '' { f : C_c(X, ℝ) | HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x)
    ∧ (∀ (x : X), x ∈ K → 1 ≤ f x) }) := by
  use 0
  intro b
  simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
  intro f _ hf _ hb
  rw [← hb]
  exact hΛ f hf

/-- Riesz content λ (associated with a positive linear functional Λ) is
monotone: if `K₁ ⊆ K₂` are compact subsets in X, then `λ(K₁) ≤ λ(K₂)`. -/
theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentAux Λ K₁ ≤ rieszContentAux Λ K₂ := by
  apply csInf_le_csInf (rieszContentAux_image_BddBelow Λ hΛ K₁)
    (rieszContentAux_image_nonempty Λ K₂)
  simp only [image_subset_iff]
  intro f hf
  simp only [mem_setOf_eq] at hf
  simp only [mem_preimage, mem_image, mem_setOf_eq]
  use f
  constructor
  constructor
  · exact hf.1
  constructor
  · exact hf.2.1
  · intro x hx
    exact hf.2.2 x (Set.mem_of_subset_of_mem h hx)
  rfl

end RieszMonotone

section RieszSubadditive

/-- Any bounded continuous nonnegative f such that `f ≥ 1` on K gives an upper bound on the
content of K; namely `λ(K) ≤ Λ f`. -/
theorem rieszContentAux_le {K : Compacts X} {f : C_c(X, ℝ)}
    (h : HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x) ∧ ∀ (x : X), x ∈ K → 1 ≤ f x) :
    rieszContentAux Λ K ≤ Λ f := by
  apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ K)
  simp only [mem_image, mem_setOf_eq]
  use f

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a bounded continuous nonnegative
function f on X such that `f ≥ 1` on K and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : ℝ} (εpos : 0 < ε) :
    ∃ f : C_c(X, ℝ), HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x) ∧ (∀ x ∈ K, 1 ≤ f x)
    ∧ Λ f < rieszContentAux Λ K + ε := by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  use f
  simp only [mem_setOf_eq] at f_hyp
  constructor
  · exact f_hyp.1.1
  constructor
  · exact f_hyp.1.2.1
  constructor
  · exact f_hyp.1.2.2
  · rw [f_hyp.2]
    exact α_hyp

/-- The Riesz content λ associated to a given positive linear functional Λ is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
theorem rieszContentAux_sup_le {K₁ K₂ : Compacts X} :
    rieszContentAux Λ (K₁ ⊔ K₂) ≤ rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  apply le_of_forall_pos_lt_add'
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K₁⟩ := exists_lt_rieszContentAux_add_pos Λ K₁ (half_pos εpos)
  obtain ⟨f2, f_test_function_K₂⟩ := exists_lt_rieszContentAux_add_pos Λ K₂ (half_pos εpos)
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : ∀ x ∈ K₁ ⊔ K₂, 1 ≤ (f1 + f2) x := by
    rintro x (x_in_K₁ | x_in_K₂)
    · simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
      apply le_add_of_le_of_nonneg
      · exact f_test_function_K₁.2.2.1 x x_in_K₁
      · exact f_test_function_K₂.2.1 x
    · simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
      rw [add_comm]
      apply le_add_of_le_of_nonneg
      · exact f_test_function_K₂.2.2.1 x x_in_K₂
      · exact f_test_function_K₁.2.1 x
  --use that `Λf` is an upper bound for `λ(K₁⊔K₂)`
  set f := f1 + f2 with hf
  have f_HasCompactSupport : HasCompactSupport f := by
    exact HasCompactSupport.add f_test_function_K₁.1 f_test_function_K₂.1
  have f_nonneg : ∀ (x : X), 0 ≤ f x := by
    intro x
    rw [hf]
    simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
    exact add_nonneg (f_test_function_K₁.2.1 x) (f_test_function_K₂.2.1 x)
  apply lt_of_le_of_lt (rieszContentAux_le Λ hΛ
    (And.intro f_HasCompactSupport (And.intro f_nonneg f_test_function_union)))
  rw [hf]
  simp only [map_add]
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K₁.2.2.2 f_test_function_K₂.2.2.2)
    (le_of_eq _)
  rw [add_assoc, add_comm (ε / 2), add_assoc, add_halves ε, add_assoc]

end RieszSubadditive

section RieszAdditive

/-- `rieszContentAux` is additive: `λ(K₁ ∪ K₂) = λ(K₁) + λ(K₂)` for disjoint compact subsets
`K₁, K₂ ⊆ X`. -/
theorem rieszContentAux_eq_add [T2Space X] {K₁ K₂ : Compacts X} (h : Disjoint K₁ K₂) :
    rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  apply le_antisymm
  · exact rieszContentAux_sup_le Λ hΛ
  · apply le_csInf
    · exact rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)
    · intro b hb
      obtain ⟨f, hf⟩ := hb
      simp only [mem_setOf_eq] at hf
      have hDisjoint : Disjoint K₁.carrier K₂.carrier := by
        rw [disjoint_iff]
        rw [disjoint_iff] at h
        simp only [inf_eq_inter, bot_eq_empty]
        simp only [Compacts.carrier_eq_coe]
        rw [← TopologicalSpace.Compacts.coe_inf]
        rw [← Compacts.carrier_eq_coe]
        rw [h]
        exact rfl
-- need to take g with compact support
      obtain ⟨V, hV⟩ := exists_compact_superset (K₁ ⊔ K₂).2
-- This works because `T2Space` is an `R₁Space` and there is `instRegularSpace`.
      have hclosure_interior_diff_subset: closure (interior V \ K₁.1) ⊆ V := by
        nth_rw 2 [← IsClosed.closure_eq (IsCompact.isClosed hV.1)]
        apply closure_mono
        exact Set.Subset.trans (Set.diff_subset _ _) interior_subset
      have : (K₁ ⊔ K₂).1 = K₁.1 ∪ K₂.1 := by
        exact rfl
      obtain ⟨g, hg⟩ := exists_tsupport_one_of_isOpen_isClosed
        (IsOpen.sdiff isOpen_interior (IsCompact.isClosed K₁.2))
        (IsCompact.of_isClosed_subset hV.1 isClosed_closure hclosure_interior_diff_subset)
        (IsCompact.isClosed K₂.2)
        (Set.subset_diff.mpr (And.intro (Set.Subset.trans (Set.subset_union_right K₁.1 K₂.1) hV.2)
        (Disjoint.symm hDisjoint)))
      have hgHasCompactSupport : HasCompactSupport g := by
        exact IsCompact.of_isClosed_subset hV.1 (isClosed_tsupport g)
          (Set.Subset.trans hg.1 (Set.Subset.trans (Set.diff_subset (interior V) K₁.carrier)
          interior_subset))
      simp only [Compacts.carrier_eq_coe, mem_Icc] at hg
-- need to show that f * (1-g) has compact support
-- one way: ad hoc (boring)
-- another way: define C(X, ℝ) as a ring, C_c(X, ℝ) as a module and use (1-g)•f
-- problem: very few definitions in C(X, ℝ)
      have h1 : rieszContentAux Λ K₁ ≤
          Λ (((1 : C(X, ℝ)) - (⟨g, hgHasCompactSupport⟩ : C_c(X, ℝ)).1) • f) := by
        apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ K₁)
        simp only [mem_image, mem_setOf_eq]
        use (1 - g) • f
        constructor
        constructor
        exact HasCompactSupport.mul_left hf.1.1
        constructor
        · intro x
          simp only [CompactlySupportedContinuousMap.smulc_apply, ContinuousMap.sub_apply,
            ContinuousMap.one_apply]
          exact mul_nonneg (unitInterval.one_minus_nonneg ⟨(g x), hg.2.2 x⟩) (hf.1.2.1 x)
        · intro x hx
          simp only [CompactlySupportedContinuousMap.smulc_apply, ContinuousMap.sub_apply,
            ContinuousMap.one_apply]
          have hgx : g x = 0 := by
            apply Function.nmem_support.mp
            apply Set.not_mem_subset subset_closure
            rw [tsupport] at hg
            exact Set.not_mem_subset hg.1 (Set.not_mem_diff_of_mem hx)
          rw [hgx]
          simp only [sub_zero, mul_one, ge_iff_le, one_mul]
          exact hf.1.2.2 x ((Set.mem_union x K₁ K₂).mpr (Or.inl hx))
        · rfl
      have h2 : rieszContentAux Λ K₂ ≤ Λ (g • f) := by
        apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ K₂)
        simp only [mem_image, mem_setOf_eq]
        use g • f
        constructor
        constructor
        exact HasCompactSupport.mul_left hf.1.1
        constructor
        · intro x
          simp only [CompactlySupportedContinuousMap.smulc_apply]
          exact mul_nonneg (hg.2.2 x).1 (hf.1.2.1 x)
        · intro x hx
          simp only [CompactlySupportedContinuousMap.smulc_apply]
          have hgx : g x = 1 := by
            rw [hg.2.1 hx]
            simp only [Pi.one_apply]
          rw [hgx]
          simp only [sub_zero, mul_one, ge_iff_le, one_mul]
          exact hf.1.2.2 x ((Set.mem_union x K₁ K₂).mpr (Or.inr hx))
        · rfl
      have honef : (1 - g) • f + g • f = f := by
        ext x
        simp only [CompactlySupportedContinuousMap.coe_add,
          CompactlySupportedContinuousMap.coe_smulc, ContinuousMap.coe_sub, ContinuousMap.coe_one,
          Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
        ring
      have hb : b = Λ ((1 - g) • f + g • f) := by
        rw [honef]
        exact (hf.2).symm
      rw [hb]
      simp only [map_add, ge_iff_le]
      exact add_le_add h1 h2

end RieszAdditive

/-- `NNReal.toReal` as a continuous map. -/
def continuousToReal : C(ℝ≥0, ℝ) := ⟨NNReal.toReal, NNReal.continuous_coe⟩

/-- For `f : C_c(X, ℝ≥0)`, `continuousExtendToReal f` is the same function `f`
of type `C_c(X, ℝ)` -/
def continuousExtendToReal (f : C_c(X, ℝ≥0)) : C_c(X, ℝ) where
  toFun := NNReal.toReal ∘ f
  continuous_toFun :=  Continuous.comp continuousToReal.2 f.1.2
  has_compact_support' := by
    simp only
    apply HasCompactSupport.comp_left f.2
    exact rfl

/-- For `f : C_c(X, ℝ)`, `continuousRestrictionToReal f` is the truncated function
`Real.toNNReal ∘ f` of type `C_c(X, ℝ≥0)` -/
def continuousRestrictionToNNReal (f : C_c(X, ℝ)) : C_c(X, ℝ≥0) where
  toFun := Real.toNNReal ∘ f
  continuous_toFun := Continuous.comp continuous_real_toNNReal f.1.2
  has_compact_support' := by
    simp only
    apply HasCompactSupport.comp_left f.2
    exact Real.toNNReal_zero

/-- Only a technical lemma. For `f : C_c(X, ℝ≥0)`, it states that the function is nonnegative. -/
lemma restrictNonneg (f : C_c(X, ℝ≥0)) : 0 ≤ f.1 := by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
    CompactlySupportedContinuousMap.coe_toContinuousMap, zero_le]

/-- For `f : C_c(X, ℝ≥0)`, `RestrictNonneg Λ hΛ f` gives the same value as `Λ f` as `ℝ≥0`. -/
def RestrictNonneg (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : ∀ (f : C_c(X, ℝ)), 0 ≤ f.1 → 0 ≤ Λ f) :
  C_c(X, ℝ≥0) → ℝ≥0 :=
  fun f => ⟨Λ (continuousExtendToReal f), hΛ (continuousExtendToReal f) (restrictNonneg f)⟩

/-- `rieszContentAux` with the value of type `ℝ≥0`. -/
def rieszContentNonneg : Compacts X → ℝ≥0 := fun K =>
  sInf (RestrictNonneg Λ hΛ '' { f : C_c(X, ℝ≥0) | (∀ (x : X), x ∈ K → 1 ≤ f x) })

/-- The image of `rieszContentNonneg Λ hΛ` is nonempty. -/
theorem rieszContentNonneg_image_nonempty (K : Compacts X) :
    (RestrictNonneg Λ hΛ '' { f : C_c(X, ℝ≥0) | (∀ (x : X), x ∈ K → 1 ≤ f x) }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hV.1 isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hV.1)]
    exact closure_mono interior_subset
  obtain ⟨f, hf⟩ := exists_tsupport_one_of_isOpen_isClosed isOpen_interior
    hIsCompact_closure_interior (IsCompact.isClosed K.2) hV.2
  have hfHasCompactSupport : HasCompactSupport f :=
    IsCompact.of_isClosed_subset hV.1 (isClosed_tsupport f) (Set.Subset.trans hf.1 interior_subset)
  use (continuousRestrictionToNNReal ⟨f, hfHasCompactSupport⟩)
  simp only [mem_setOf_eq]
  intro x hx
  rw [continuousRestrictionToNNReal]
  simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, comp_apply,
    Real.one_le_toNNReal]
  rw [hf.2.1 hx]
  simp only [Pi.one_apply, le_refl]

/-- The image of `rieszContentNonneg Λ hΛ` is bounded below. -/
lemma rieszContentNonneg_image_BddBelow (K : Compacts X) :
    BddBelow (RestrictNonneg Λ hΛ '' { f : C_c(X, ℝ≥0) | (∀ (x : X), x ∈ K → 1 ≤ f x) }) := by
  use 0
  intro b _
  exact b.2

/-- `rieszContentAux` and `rieszContentNonneg` give the same value in types `ℝ` and `ℝ≥0`,
respectively. -/
lemma rieszContentAux_eq_rieszContentNonneg {K : Compacts X} :
    ⟨rieszContentAux Λ K, rieszContentAux_nonneg Λ hΛ⟩ = rieszContentNonneg Λ hΛ K  := by
  apply le_antisymm
  · rw [← NNReal.coe_le_coe]
    simp only [coe_mk]
    apply (csInf_le_iff (rieszContentAux_image_BddBelow Λ hΛ K)
      (rieszContentAux_image_nonempty Λ K)).mpr
    · intro b hb
      by_cases hbzero : 0 ≤ b
      · rw [← Real.coe_toNNReal b hbzero]
        rw [NNReal.coe_le_coe]
        apply (le_csInf_iff (rieszContentNonneg_image_BddBelow Λ hΛ K)
          (rieszContentNonneg_image_nonempty Λ hΛ K)).mpr
        intro c hc
        simp only [zero_le, implies_true, true_and, mem_image, mem_setOf_eq] at hc
        obtain ⟨f, hf⟩ := hc
        rw [RestrictNonneg] at hf
        rw [← hf.2, Real.toNNReal_le_iff_le_coe]
        simp only [coe_mk]
        rw [mem_lowerBounds] at hb
        apply hb
        simp only [mem_image, mem_setOf_eq]
        use continuousExtendToReal f
        constructor
        constructor
        · apply HasCompactSupport.of_support_subset_isCompact f.2
          rw [continuousExtendToReal]
          exact Set.Subset.trans (Function.support_comp_subset NNReal.coe_zero f) subset_closure
        constructor
        · intro x
          rw [continuousExtendToReal]
          simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, comp_apply,
            zero_le_coe]
        · intro x hx
          rw [continuousExtendToReal]
          simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, comp_apply,
            one_le_coe]
          exact hf.1 x hx
        rfl
      · push_neg at hbzero
        apply le_of_lt (lt_of_lt_of_le hbzero _)
        simp only [zero_le_coe]
  · apply (csInf_le_iff (rieszContentNonneg_image_BddBelow Λ hΛ K)
      (rieszContentNonneg_image_nonempty Λ hΛ K)).mpr
    intro b hb
    rw [mem_lowerBounds] at hb
    rw [← NNReal.coe_le_coe]
    simp only [coe_mk]
    apply (le_csInf_iff (rieszContentAux_image_BddBelow Λ hΛ K)
      (rieszContentAux_image_nonempty Λ K)).mpr
    intro c hc
    simp only [mem_image, mem_setOf_eq] at hc
    obtain ⟨f, hf⟩ := hc
    have hΛfpos : 0 ≤ Λ f := by
      apply hΛ
      exact hf.1.2.1
    rw [← Real.le_toNNReal_iff_coe_le _]
    · apply hb
      rw [← hf.2]
      simp only [mem_image, mem_setOf_eq]
      use continuousRestrictionToNNReal f
      constructor
      · intro x hx
        rw [continuousRestrictionToNNReal]
        simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, comp_apply,
          Real.one_le_toNNReal]
        exact hf.1.2.2 x hx
      · rw [continuousRestrictionToNNReal]
        rw [RestrictNonneg]
        rw [Real.toNNReal_of_nonneg hΛfpos, ← NNReal.coe_inj]
        simp only [coe_mk]
        rw [continuousExtendToReal]
        simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk]
        apply congr_arg
        ext x
        simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, comp_apply,
          Real.coe_toNNReal', max_eq_left_iff]
        exact hf.1.2.1 x
    · rw [← hf.2]
      exact hΛfpos

/-- `rieszContentNonneg` is monotone. -/
theorem rieszContentNonneg_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentNonneg Λ hΛ K₁ ≤ rieszContentNonneg Λ hΛ K₂ := by
  rw [← rieszContentAux_eq_rieszContentNonneg, ← rieszContentAux_eq_rieszContentNonneg]
  rw [← NNReal.coe_le_coe]
  simp only [coe_mk]
  exact rieszContentAux_mono Λ hΛ h

/-- `rieszContentNonneg` is additive. -/
theorem rieszContentNonneg_eq_add [T2Space X] {K₁ K₂ : Compacts X} (h : Disjoint K₁ K₂) :
    rieszContentNonneg Λ hΛ (K₁ ⊔ K₂) =
    rieszContentNonneg Λ hΛ K₁ + rieszContentNonneg Λ hΛ K₂ := by
  rw [← rieszContentAux_eq_rieszContentNonneg, ← rieszContentAux_eq_rieszContentNonneg,
    ← rieszContentAux_eq_rieszContentNonneg]
  rw [← NNReal.eq_iff]
  simp only [coe_mk, NNReal.coe_add]
  exact rieszContentAux_eq_add Λ hΛ h

/-- `rieszContentNonneg` is finitely subadditive. -/
theorem rieszContentNonneg_sup_le {K₁ K₂ : Compacts X} :
    rieszContentNonneg Λ hΛ (K₁ ⊔ K₂) ≤
    rieszContentNonneg Λ hΛ K₁ + rieszContentNonneg Λ hΛ K₂ := by
  rw [← rieszContentAux_eq_rieszContentNonneg, ← rieszContentAux_eq_rieszContentNonneg,
    ← rieszContentAux_eq_rieszContentNonneg]
  rw [← NNReal.coe_le_coe]
  simp only [coe_mk, NNReal.coe_add]
  exact rieszContentAux_sup_le Λ hΛ

/-- `rieszContent` has the value of `rieszContentNonneg` with the desired properties,
thus it is indeed a content. -/
def rieszContent : MeasureTheory.Content X where
  toFun := rieszContentNonneg Λ hΛ
  mono' := by
    intro K₁ K₂ h
    exact rieszContentNonneg_mono Λ hΛ h
  sup_disjoint' := by
    intro K₁ K₂ hDisjoint _ _
    have : Disjoint K₁ K₂ := by
        rw [disjoint_iff]
        rw [disjoint_iff] at hDisjoint
        simp only [inf_eq_inter, bot_eq_empty] at hDisjoint
        apply TopologicalSpace.Compacts.ext
        simp only [Compacts.coe_inf, Compacts.coe_bot]
        exact hDisjoint
    exact rieszContentNonneg_eq_add Λ hΛ this
  sup_le' := by
    intro K₁ K₂
    exact rieszContentNonneg_sup_le Λ hΛ

lemma rieszContent_neq_top {K : Compacts X} : rieszContent Λ hΛ K ≠ ⊤ := by
  simp only [ne_eq, coe_ne_top, not_false_eq_true]

variable [MeasurableSpace X] [BorelSpace X]

open BigOperators

lemma exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed [T2Space X]
    [LocallyCompactSpace X] {n : ℕ} {t : Set X} {s : Fin n → Set X}
    (hs : ∀ (i : Fin n), IsOpen (s i))
    (htcp : IsCompact t) (hst : t ⊆ ⋃ i, s i) :
    ∃ f : Fin n → C(X, ℝ), (∀ (i : Fin n), tsupport (f i) ⊆ s i) ∧ EqOn (∑ i, f i) 1 t
    ∧ ∀ (i : Fin n), ∀ (x : X), f i x ∈ Icc (0 : ℝ) 1 := by
  sorry

/-- `rieszContent` is promoted to a measure. -/
def μ := (MeasureTheory.Content.measure (rieszContent Λ hΛ))

/-- The Riesz-Markov-Kakutani theorem. -/
theorem RMK [Nonempty X] : ∀ (f : C_c(X, ℝ)), ∫ (x : X), f x ∂(μ Λ hΛ) = Λ f := by
  have RMK_le : ∀ (f : C_c(X, ℝ)), Λ f ≤ ∫ (x : X), f x ∂(μ Λ hΛ) := by
    intro f
    set L := Set.range f with hLdef
    have hL : IsCompact L := by exact HasCompactSupport.isCompact_range f.2 f.1.2
    have hLNonempty : Nonempty L := instNonemptyRange f
    have BddBelow_bbdAbove_L := Real.isBounded_iff_bddBelow_bddAbove.mp
      (Metric.isCompact_iff_isClosed_bounded.mp hL).2
    obtain ⟨a, ha⟩ := BddBelow_bbdAbove_L.1
    obtain ⟨b, hb⟩ := BddBelow_bbdAbove_L.2
    have hafx : ∀ (x : X), a ≤ f x := by
      intro x
      apply ha
      rw [hLdef]
      simp only [mem_range, exists_apply_eq_apply]
    have hfxb : ∀ (x : X), f x ≤ b:= by
      intro x
      apply hb
      rw [hLdef]
      simp only [mem_range, exists_apply_eq_apply]
    have hab : a ≤ b := by
      obtain ⟨c, hc⟩ := hLNonempty
      exact le_trans (mem_lowerBounds.mp ha c hc) (mem_upperBounds.mp hb c hc)
    have habnonneg : 0 ≤ |a| + b := by
      apply le_trans _ (add_le_add_right (neg_le_abs a) b)
      simp only [le_neg_add_iff_add_le, add_zero]
      exact hab
    apply le_iff_forall_pos_lt_add.mpr
    intro ε hε
    have hltε : ∃ (ε' : ℝ), 0 < ε' ∧
        ε' * (2 * (rieszContent Λ hΛ (⟨tsupport f, f.2⟩)).toReal + |a| + b + ε') < ε := by
      simp only [coe_toReal]
      set A := 2 * (rieszContent Λ hΛ (⟨tsupport f, f.2⟩)).toReal + |a| + b with hA
      simp only [coe_toReal] at hA
      use ε / (4 * A + 2 + 2 * ε)
      rw [← hA]
      have hAnonneg : 0 ≤ A := by
        rw [hA, add_assoc]
        apply add_nonneg _ habnonneg
        simp only [gt_iff_lt, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, zero_le_coe]
      constructor
      · apply div_pos hε
        linarith
      · rw [left_distrib]
        have h1 : ε / (4 * A + 2 + 2 * ε) * A < ε / 2 := by
          rw [← mul_div_right_comm, mul_div_assoc]
          nth_rw 3 [← mul_one ε]
          rw [mul_div_assoc]
          apply mul_lt_mul_of_pos_left _ hε
          apply (div_lt_div_iff _ two_pos).mpr
          · linarith
          · linarith
        have h2 : ε / (4 * A + 2 + 2 * ε) < ε / 2 := by
          apply div_lt_div_of_pos_left hε two_pos
          linarith
        have h3 : 0 < 4 * A + 2 + 2 * ε := by
          linarith
        have h4 : ε / (4 * A + 2 + 2 * ε) * (ε / (4 * A + 2 + 2 * ε)) < ε / 2 := by
          rw [lt_div_iff two_pos, mul_comm, ← mul_div_assoc, ← mul_div_assoc, div_lt_iff h3,
            ← mul_assoc, mul_comm, ← mul_assoc, ← mul_div_assoc, div_lt_iff h3, mul_assoc,
            mul_assoc]
          apply mul_lt_mul_of_pos_left _ hε
          have h41 : 2 < 4 * A + 2 + 2 * ε := by
            linarith
          have h42 : ε < 4 * A + 2 + 2 * ε := by
            linarith
          exact mul_lt_mul h41 (le_of_lt h42) hε (le_of_lt h3)
        nth_rw 7 [← add_halves' ε]
        exact add_lt_add h1 h4
    obtain ⟨ε', hε'⟩ := hltε
    apply lt_trans _ (add_lt_add_left hε'.2 _)
    simp only [coe_toReal]
    set δ := ε / 2 with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      exact div_pos hε two_pos
    set N := (b - a) / δ with hN
    have hNNonneg : 0 ≤ N :=
      by exact div_nonneg (sub_nonneg.mpr hab) (le_of_lt hδpos)
    set y : ℤ → ℝ := fun n => b + δ * (n - (⌈N⌉₊+1)) with hy
    have hy0 : y 0 < a := by
      rw [hy, hN]
      simp only [Int.cast_zero, Int.ceil_add_one, Int.cast_add, Int.cast_one, zero_sub, neg_add_rev]
      apply lt_tsub_iff_left.mp
      apply (lt_div_iff' hδpos).mp
      simp only [add_neg_lt_iff_lt_add]
      rw [neg_lt_iff_pos_add, add_assoc, ← neg_lt_iff_pos_add']
      apply lt_add_of_lt_add_right _ (Nat.le_ceil _)
      rw [neg_lt_iff_pos_add]
      apply pos_of_mul_pos_left _ (le_of_lt hδpos)
      rw [add_mul, add_mul, div_mul, div_mul, div_self (Ne.symm (ne_of_lt hδpos))]
      simp only [div_one, one_mul]
      linarith
    set E : ℤ → Set X := fun n => (f ⁻¹' Ioc (y n) (y (n+1))) ∩ (tsupport f) with hE
    have hEmeasurable : ∀ (n : ℤ), MeasurableSet (E n) := by
      intro n
      rw [hE]
      simp only
      apply MeasurableSet.inter
      · exact (ContinuousMap.measurable f.1) measurableSet_Ioc
      · exact measurableSet_closure
    set Erest : Fin (⌈N⌉₊ + 1) → Set X := fun n => E n with hErest
    have hErestsubtsupport : ∀ (n : Fin (⌈N⌉₊ + 1)), Erest n ⊆ tsupport f := by
      intro n
      rw [hErest]
      simp only
      rw [hE]
      simp only [inter_subset_right]
    have hrangefsubioc: range f ⊆ Ioc (y 0) (y (⌈N⌉₊ + 1)) := by
      intro z hz
      simp only [mem_Ioc]
      constructor
      · apply lt_of_lt_of_le hy0
        apply ha
        rw [hLdef]
        exact hz
      · rw [hy]
        simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, sub_self, mul_zero, add_zero]
        apply hb
        rw [hLdef]
        exact hz
    have hrangefsubiunion: range f ⊆ ⋃ n : Fin (⌈N⌉₊ + 1), Ioc (y n) (y (n+1)) := by
      have : y = fun (n : ℤ) => b - δ * ⌈N⌉₊ - δ + n • δ := by
        ext n
        rw [hy]
        simp only [zsmul_eq_mul]
        ring
      have : ⋃ n, Ioc (y n) (y (n+1)) = univ := by
        rw [this]
        simp only [Int.cast_add, Int.cast_one]
        exact iUnion_Ioc_add_zsmul hδpos (b - δ * ⌈N⌉₊ - δ)
      intro z hz
      have : z ∈ ⋃ n, Ioc (y n) (y (n+1)) := by
        rw [this]
        exact trivial
      obtain ⟨j, hj⟩ := mem_iUnion.mp this
      have hjnonneg : 0 ≤ j := by sorry
      have hjltceil : j < ⌈N⌉₊ := by sorry
      have hnltceil : j.toNat < ⌈N⌉₊ + 1 := by
        apply (Int.toNat_lt hjnonneg).mpr (lt_trans hjltceil _)
        simp only [Nat.cast_add, Nat.cast_one, lt_add_iff_pos_right, zero_lt_one]
      rw [mem_iUnion]
      use ⟨j.toNat, hnltceil⟩
      simp only
      rw [Int.toNat_of_nonneg hjnonneg]
      exact hj
    have htsupportsubErest : tsupport f ⊆ ⋃ j, Erest j := by
      intro x hx
      rw [hErest, hE]
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, exists_and_right]
      obtain ⟨j, hj⟩ := mem_iUnion.mp (Set.mem_of_subset_of_mem hrangefsubiunion
        (Set.mem_range_self x))
      constructor
      · use j
      · exact hx
    --   simp only [mem_iUnion]
    --   have hnonnegfxsuby0: 0 < (f x - y 0) / δ := by
    --     have : a ≤ f x := hafx x
    --     apply div_pos _ hδpos
    --     linarith
    --   have hfxsuby0ltnaddone : ⌈(f x - y 0) / δ - 1⌉ < ⌈N⌉ + 1 := by
    --     rw [Int.ceil_sub_one]
    --     apply sub_right_lt_of_lt_add
    --     apply (@Int.cast_lt ℝ).mp
    --     apply lt_of_lt_of_le (Int.ceil_lt_add_one _) _
    --     rw [hy]
    --     simp only [Int.cast_zero, zero_sub, neg_add_rev, Int.cast_add, Int.cast_one,
    --       add_le_add_iff_right]
    --     rw [_root_.sub_div, add_div, mul_comm, mul_div_assoc, div_self (Ne.symm (ne_of_lt hδpos))]
    --     simp only [mul_one, tsub_le_iff_right]
    --     rw [add_comm, add_assoc, add_assoc]
    --     simp only [neg_add_cancel_left, add_left_neg, add_zero]
    --     apply div_le_div_of_nonneg_right _ (le_of_lt hδpos)
    --     exact hfxb x
    --   have hfxsuby0ltnaddone' : ⌈(f x - y 0) / δ - 1⌉₊ < ⌈N⌉₊ + 1 := by
    --     apply (@Nat.cast_lt ℤ).mp
    --     simp only [Nat.cast_add, Nat.cast_one]
    --     rw [Int.ofNat_ceil_eq_ceil hNNonneg]
    --     by_cases hn : (f x - y 0) / δ - 1 ≤ 0
    --     · rw [Nat.ceil_eq_zero.mpr hn]
    --       simp only [CharP.cast_eq_zero]
    --       exact add_pos_of_nonneg_of_pos (Int.ceil_nonneg hNNonneg) one_pos
    --     · push_neg at hn
    --       rw [Int.ofNat_ceil_eq_ceil (le_of_lt hn)]
    --       exact hfxsuby0ltnaddone
    --   use ⟨⌈(f x - y 0) / δ - 1⌉₊, hfxsuby0ltnaddone'⟩
    --   constructor
    --   · simp only [mem_preimage, mem_Ioc]
    --     constructor
    --     · sorry
    --     · sorry
    --     -- rw [hy]
    --     -- simp only [Int.cast_zero, zero_sub, neg_add_rev, Int.cast_sub, Int.cast_natCast,
    --     --   Int.cast_one]
    --     -- constructor
    --     -- · apply add_lt_of_lt_sub_left
    --     --   rw [← lt_div_iff' hε]
    --     --   apply sub_right_lt_of_lt_add
    --     --   apply sub_right_lt_of_lt_add
    --     --   simp only [Int.cast_natCast]
    --     --   apply lt_of_lt_of_le (Int.ceil_lt_add_one _) _
    --     --   apply add_le_add_right _ 1
    --     --   rw [div_le_iff' hε, mul_add, mul_add, mul_add, ← mul_div_assoc, ← mul_div_assoc, mul_comm,
    --     --     mul_div_assoc, div_self (Ne.symm (ne_of_lt hε))]
    --     --   simp only [mul_one, neg_add_rev, neg_sub]
    --     --   rw [mul_comm, mul_div_assoc, div_self (Ne.symm (ne_of_lt hε))]
    --     --   linarith
    --     -- · apply le_add_of_sub_left_le
    --     --   rw [← div_le_iff' hε]
    --     --   apply le_sub_right_of_add_le
    --     --   apply le_trans _ (Int.le_ceil _)
    --     --   rw [le_div_iff' hε, mul_add, ← mul_div_assoc, mul_comm, mul_div_assoc,
    --     --     div_self (Ne.symm (ne_of_lt hε))]
    --     --   linarith
    --   · exact hx
    -- -- have htsupportsubErest : tsupport f ⊆ ⋃ n, Erest n := by
    -- --   intro x hx
    -- --   rw [hErest]
    -- --   simp only [mem_iUnion]
    -- --   sorry

    set SpecV := fun (n : Fin (⌈N⌉₊ + 1)) =>
      MeasureTheory.Content.outerMeasure_exists_open (rieszContent Λ hΛ)
      (ne_of_lt (lt_of_le_of_lt ((rieszContent Λ hΛ).outerMeasure.mono (hErestsubtsupport n))
      (MeasureTheory.Content.outerMeasure_lt_top_of_isCompact (rieszContent Λ hΛ) f.2)))
      (ne_of_gt (Real.toNNReal_pos.mpr (div_pos hε (Nat.cast_pos.mpr (Nat.add_one_pos ⌈N⌉₊)))))
    set V : Fin (⌈N⌉₊ + 1) → Opens X := fun n => Classical.choose (SpecV n) ⊓
      ⟨(f ⁻¹' Iio (y (n + 1) + ε)), IsOpen.preimage f.1.2 isOpen_Iio⟩ with hV
    have htsupportsubV : tsupport f ⊆ ⋃ n : Fin (⌈N⌉₊ + 1), V n := by
      apply Set.Subset.trans htsupportsubErest _
      apply Set.iUnion_mono
      intro n
      rw [hV]
      simp only [Nat.cast_succ, Opens.coe_inf, Opens.coe_mk, subset_inter_iff]
      constructor
      · simp only [Nat.cast_add, Nat.cast_one] at SpecV
        exact (Classical.choose_spec (SpecV n)).1
      · rw [hErest]
        simp only
        apply Set.Subset.trans (Set.inter_subset_left _ _) _
        intro z hz
        rw [Set.mem_preimage]
        rw [Set.mem_preimage] at hz
        exact lt_of_le_of_lt hz.2 (lt_add_of_pos_right (y (n + 1)) hε)
    obtain ⟨g, hg⟩ := exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed
      (fun n => (V n).2) f.2 htsupportsubV


    sorry
-- `K = range tsupport f`
-- we will show that `Λ f ≤ ∫ (x : X), f x ∂(μ Λ hΛ) + ε (2 μ K + |a| + b + ε)`
-- for arbitrary `0 < ε`.
-- ------ need that, if `0 ≤ f ≤ 1` and `tsupport f ⊆ V`, then `Λ f ≤ μ V`
-- calculate
-- need that, if `a ≤ f` on `E j`, then `a μ (E j) ≤ ∫ (E j), f d μ

  intro f
  apply le_antisymm
  · calc ∫ (x : X), f x ∂(μ Λ hΛ) = ∫ (x : X), -(-f) x ∂(μ Λ hΛ) := by simp only
      [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply, neg_neg]
    _ = - ∫ (x : X), (-f) x ∂(μ Λ hΛ) := by exact MeasureTheory.integral_neg' (-f)
    _ ≤ - Λ (-f) := by exact neg_le_neg (RMK_le (-f))
    _ = Λ (- -f) := by exact Eq.symm (Λ_neg Λ)
    _ = Λ f := by simp only [neg_neg]
  · exact RMK_le f
