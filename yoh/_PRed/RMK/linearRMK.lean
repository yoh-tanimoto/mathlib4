/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä, Yoh Tanimoto
-/
import Mathlib.Algebra.Order.Group.DenselyOrdered
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.ContinuousFunction.CompactlySupported
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

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

open BoundedContinuousFunction NNReal ENNReal BigOperators

open Set Function TopologicalSpace CompactlySupported


variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : ∀ (f : C_c(X, ℝ)), 0 ≤ f.1 → 0 ≤ Λ f)

section Positive
include hΛ

/-- Under the assumption `hΛ`, `Λ` is monotone. -/
lemma Λ_mono {f g : C_c(X, ℝ)} (h : f.1 ≤ g.1) : Λ f ≤ Λ g := by
  have : 0 ≤ g.1 - f.1 := by exact sub_nonneg.mpr h
  calc Λ f ≤ Λ f + Λ (g - f) := by exact le_add_of_nonneg_right (hΛ (g - f) this)
  _ = Λ (f + (g - f)) := by rw [← LinearMap.map_add Λ f (g - f)]
  _ = Λ g := by simp only [add_sub_cancel]

end Positive

lemma Λ_neg {f : C_c(X, ℝ)} : Λ (-f) = - Λ f := by
  simp only [map_neg]

lemma Λ_sum {ι : Type*} [Fintype ι] {f : ι → C_c(X, ℝ)} :
    Λ (∑ i , f i) = ∑ i, Λ (f i) := by
  exact map_sum Λ (fun x => f x) Finset.univ

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

section Positive
include hΛ

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

end Positive

end RieszMonotone

section RieszSubadditive

section Positive
include hΛ

/-- Any bounded continuous nonnegative f such that `f ≥ 1` on K gives an upper bound on the
content of K; namely `λ(K) ≤ Λ f`. -/
theorem rieszContentAux_le {K : Compacts X} {f : C_c(X, ℝ)}
    (h : HasCompactSupport f ∧ (∀ (x : X), 0 ≤ f x) ∧ ∀ (x : X), x ∈ K → 1 ≤ f x) :
    rieszContentAux Λ K ≤ Λ f := by
  apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ K)
  simp only [mem_image, mem_setOf_eq]
  use f

end Positive

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

section Positive
include hΛ

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

end Positive

end RieszSubadditive

section RieszAdditive

section Positive
include hΛ

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
        exact Set.Subset.trans (Set.diff_subset) interior_subset
      have : (K₁ ⊔ K₂).1 = K₁.1 ∪ K₂.1 := by
        exact rfl
      obtain ⟨g, hg⟩ := exists_tsupport_one_of_isOpen_isClosed
        (IsOpen.sdiff isOpen_interior (IsCompact.isClosed K₁.2))
        (IsCompact.of_isClosed_subset hV.1 isClosed_closure hclosure_interior_diff_subset)
        (IsCompact.isClosed K₂.2)
        (Set.subset_diff.mpr (And.intro (Set.Subset.trans (Set.subset_union_right) hV.2)
        (Disjoint.symm hDisjoint)))
      have hgHasCompactSupport : HasCompactSupport g := by
        exact IsCompact.of_isClosed_subset hV.1 (isClosed_tsupport g)
          (Set.Subset.trans hg.1 (Set.Subset.trans (Set.diff_subset)
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
          simp only [sub_zero, smul_eq_mul, one_mul, ge_iff_le]
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
          simp only [smul_eq_mul, one_mul, ge_iff_le]
          exact hf.1.2.2 x ((Set.mem_union x K₁ K₂).mpr (Or.inr hx))
        · rfl
      have honef : (1 - g) • f + g • f = f := by
        ext x
        simp only [CompactlySupportedContinuousMap.coe_add,
          CompactlySupportedContinuousMap.coe_smulc, ContinuousMap.sub_apply,
          ContinuousMap.one_apply, smul_eq_mul, Pi.add_apply]
        ring
      have hb : b = Λ ((1 - g) • f + g • f) := by
        rw [honef]
        exact (hf.2).symm
      rw [hb]
      simp only [map_add, ge_iff_le]
      exact add_le_add h1 h2

end Positive

end RieszAdditive

/-- `NNReal.toReal` as a continuous map. -/
def continuousToReal : C(ℝ≥0, ℝ) := ⟨NNReal.toReal, NNReal.continuous_coe⟩

/-- For `f : C_c(X, ℝ≥0)`, `continuousExtendToReal f` is the same function `f`
of type `C_c(X, ℝ)` -/
def continuousExtendToReal (f : C_c(X, ℝ≥0)) : C_c(X, ℝ) where
  toFun := NNReal.toReal ∘ f
  continuous_toFun :=  Continuous.comp continuousToReal.2 f.1.2
  hasCompactSupport' := by
    simp only
    apply HasCompactSupport.comp_left f.2
    exact rfl

lemma continuousExtendToReal_sum {ι : Type*} (s : Finset ι) (f : ι → C_c(X, ℝ≥0)) :
    continuousExtendToReal (∑ i ∈ s, f i) = ∑ i ∈ s, continuousExtendToReal (f i) := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  rw [continuousExtendToReal]
  simp_rw [continuousExtendToReal]
  simp only [CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_mk,
    ContinuousMap.coe_mk, comp_apply, Finset.sum_apply]
  exact NNReal.coe_sum

/-- For `f : C_c(X, ℝ)`, `continuousRestrictionToReal f` is the truncated function
`Real.toNNReal ∘ f` of type `C_c(X, ℝ≥0)` -/
def continuousRestrictionToNNReal (f : C_c(X, ℝ)) : C_c(X, ℝ≥0) where
  toFun := Real.toNNReal ∘ f
  continuous_toFun := Continuous.comp continuous_real_toNNReal f.1.2
  hasCompactSupport' := by
    simp only
    apply HasCompactSupport.comp_left f.2
    exact Real.toNNReal_zero

/-- Only a technical lemma. For `f : C_c(X, ℝ≥0)`, it states that the function is nonnegative. -/
lemma restrictNonneg (f : C_c(X, ℝ≥0)) : 0 ≤ f.1 := by
  intro x
  simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
    CompactlySupportedContinuousMap.coe_toContinuousMap, zero_le]

/-- For `f : C_c(X, ℝ≥0)`, `RestrictNonneg Λ hΛ f` gives the same value as `Λ f` as `ℝ≥0`. -/
def RestrictNonneg : C_c(X, ℝ≥0) → ℝ≥0 :=
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
  rw [NNReal.eq_iff]
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

lemma Real.le_of_forall_lt_one_lt_mul (a b : ℝ) (hb : 0 ≤ b) :
    (∀ (ε : ℝ), 1 < ε → a ≤  b * ε) → a ≤ b := by
  intro h
  by_cases hbzero : b = 0
  · rw [hbzero]
    rw [← zero_mul 2, ← hbzero]
    exact h 2 one_lt_two
  · apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    push_neg at hbzero
    have bpos : 0 < b := by
      exact lt_of_le_of_ne hb (id (Ne.symm hbzero))
    have bdiv : 1 < (b + ε) / b := by
      apply (one_lt_div bpos).mpr
      exact lt_add_of_pos_right b hε
    have : a ≤ b * ((b + ε) / b) := h ((b + ε) / b) bdiv
    rw [← mul_div_assoc, mul_comm, mul_div_assoc, div_self (ne_of_gt bpos), mul_one] at this
    exact this

open Pointwise

lemma rieszContentRegular : (rieszContent Λ hΛ).ContentRegular := by
  intro K
  simp only
  rw [rieszContent]
  simp only
  apply le_antisymm
  · apply le_iInf
    rw [← rieszContentAux_eq_rieszContentNonneg]
    simp only [le_iInf_iff, ENNReal.coe_le_coe]
    intro K' hK'
    rw [← rieszContentAux_eq_rieszContentNonneg]
    rw [← NNReal.coe_le_coe]
    simp only [coe_mk]
    exact rieszContentAux_mono Λ hΛ (Set.Subset.trans hK' interior_subset)
  · rw [iInf_le_iff]
    intro b hb
    rw [← rieszContentAux_eq_rieszContentNonneg]
    rw [ENNReal.le_coe_iff]
    have : b < ⊤ := by
      obtain ⟨F, hF⟩ := exists_compact_superset K.2
      exact lt_of_le_of_lt (le_iInf_iff.mp (hb ⟨F, hF.1⟩) hF.2) ENNReal.coe_lt_top
    use b.toNNReal
    constructor
    · exact Eq.symm (ENNReal.coe_toNNReal (ne_of_lt this))
    · apply NNReal.coe_le_coe.mp
      simp only [coe_mk]
      apply le_iff_forall_pos_le_add.mpr
      intro ε hε
      obtain ⟨f, hf⟩ := exists_lt_rieszContentAux_add_pos Λ K hε
      apply le_of_lt (lt_of_le_of_lt _ hf.2.2.2)
      have : 0 ≤ f.1 := by
        intro x
        simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
          CompactlySupportedContinuousMap.coe_toContinuousMap]
        exact hf.2.1 x
      apply Real.le_of_forall_lt_one_lt_mul
      · exact hΛ f this
      · intro α hα
        have : Λ f * α = Λ (α • f) := by
          simp only [map_smul, smul_eq_mul]
          exact mul_comm _ _
        rw [this]
        set K' := f ⁻¹' (Ici α⁻¹) with hK'
        have hKK' : K.carrier ⊆ interior K' := by
          rw [subset_interior_iff]
          use f ⁻¹' (Ioi α⁻¹)
          constructor
          · apply IsOpen.preimage f.1.2
            exact isOpen_Ioi
          constructor
          · intro x hx
            rw [Set.mem_preimage, Set.mem_Ioi]
            exact lt_of_lt_of_le (inv_lt_one hα) (hf.2.2.1 x hx)
          · rw [hK']
            intro x hx
            simp only [mem_preimage, mem_Ioi] at hx
            simp only [mem_preimage, mem_Ici]
            exact le_of_lt hx
        have hK'cp : IsCompact K' := by
          apply IsCompact.of_isClosed_subset hf.1
          · simp only [smul_eq_mul] at hK'
            exact IsClosed.preimage f.1.2 isClosed_Ici
          · rw [hK']
            apply Set.Subset.trans _ subset_closure
            intro x hx
            simp only [mem_preimage, mem_Ici] at hx
            simp only [mem_support]
            apply ne_of_gt
            exact (lt_of_lt_of_le (inv_pos_of_pos (lt_trans zero_lt_one hα)) hx)
        set hb' := hb ⟨K', hK'cp⟩
        simp only [Compacts.coe_mk, le_iInf_iff] at hb'
        have hbK' : b ≤ rieszContentNonneg Λ hΛ ⟨K', hK'cp⟩ := hb' hKK'
        rw [ENNReal.le_coe_iff] at hbK'
        obtain ⟨p, hp⟩ := hbK'
        rw [hp.1]
        simp only [toNNReal_coe]
        rw [← rieszContentAux_eq_rieszContentNonneg] at hp
        apply le_trans (NNReal.GCongr.toReal_le_toReal hp.2)
        simp only [coe_mk]
        rw [rieszContentAux]
        apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ _)
        simp only [mem_image, mem_setOf_eq]
        use α • f
        constructor
        constructor
        · simp only [CompactlySupportedContinuousMap.coe_smul]
          apply IsCompact.of_isClosed_subset hf.1 (isClosed_tsupport _)
            (closure_mono (Function.support_const_smul_subset _ _))
        constructor
        · intro x
          simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
          exact mul_nonneg (le_of_lt (lt_trans zero_lt_one hα)) (hf.2.1 x)
        · intro x hx
          simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
          apply (inv_pos_le_iff_one_le_mul' (lt_trans zero_lt_one hα)).mp
          rw [← Set.mem_Ici, ← Set.mem_preimage]
          exact hx
        · exact rfl

variable [MeasurableSpace X] [BorelSpace X]

lemma exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed [T2Space X]
    [LocallyCompactSpace X] {n : ℕ} {t : Set X} {s : Fin n → Set X}
    (hs : ∀ (i : Fin n), IsOpen (s i))
    (htcp : IsCompact t) (hst : t ⊆ ⋃ i, s i) :
    ∃ f : Fin n → C(X, ℝ), (∀ (i : Fin n), tsupport (f i) ⊆ s i) ∧
    (∀ (i : Fin n), HasCompactSupport (f i)) ∧ EqOn (∑ i, f i) 1 t
    ∧ ∀ (i : Fin n), ∀ (x : X), f i x ∈ Icc (0 : ℝ) 1 := by
  sorry

theorem MeasureTheory.integral_tsupport {M : Type*} [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup M]
    [NormedSpace ℝ M] {F : X → M} {ν : MeasureTheory.Measure X} :
    ∫ (x : X), F x ∂ν = ∫ (x : X) in tsupport F, F x ∂ν := by
  rw [← MeasureTheory.integral_univ]
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ
    (subset_univ _)
  intro x hx
  apply image_eq_zero_of_nmem_tsupport
  exact not_mem_of_mem_diff hx

/-- `rieszContent` is promoted to a measure. -/
def μ := (MeasureTheory.Content.measure (rieszContent Λ hΛ))

lemma leRieszMeasure_isCompact {f : C_c(X, ℝ)} (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1) {K : Compacts X}
    (h : tsupport f ⊆ K) : ENNReal.ofReal (Λ f) ≤ (μ Λ hΛ) K := by
  rw [μ]
  rw [MeasureTheory.Content.measure_eq_content_of_regular (rieszContent Λ hΛ)
    (rieszContentRegular Λ hΛ)]
  simp only
  rw [rieszContent]
  simp only
  rw [← rieszContentAux_eq_rieszContentNonneg, ← ENNReal.ofReal_eq_coe_nnreal]
  rw [ENNReal.ofReal_le_ofReal_iff (rieszContentAux_nonneg Λ hΛ)]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos Λ K hε
  apply le_of_lt (lt_of_le_of_lt _ hg.2.2.2)
  apply Λ_mono Λ hΛ
  intro x
  simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap]
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hf x).2 (hg.2.2.1 x (Set.mem_of_subset_of_mem h hx))
  · rw [image_eq_zero_of_nmem_tsupport hx]
    exact hg.2.1 x

lemma leRieszMeasure_isOpen {f : C_c(X, ℝ)} (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1) {V : Opens X}
    (h : tsupport f ⊆ V) :
    ENNReal.ofReal (Λ f) ≤ (μ Λ hΛ) V := by
  apply le_trans _ (MeasureTheory.measure_mono h)
  rw [← TopologicalSpace.Compacts.coe_mk (tsupport f) f.2]
  apply leRieszMeasure_isCompact Λ hΛ hf
  simp only [Compacts.coe_mk]
  exact subset_rfl

/-- The Riesz-Markov-Kakutani theorem. -/
theorem RMK [Nonempty X] : ∀ (f : C_c(X, ℝ)), ∫ (x : X), f x ∂(μ Λ hΛ) = Λ f := by
  have RMK_le : ∀ (f : C_c(X, ℝ)), Λ f ≤ ∫ (x : X), f x ∂(μ Λ hΛ) := by
    intro f
    set L := Set.range f with hLdef
    have hL : IsCompact L := by exact HasCompactSupport.isCompact_range f.2 f.1.2
    have hLNonempty : Nonempty L := instNonemptyRange f
    have BddBelow_bbdAbove_L := isBounded_iff_bddBelow_bddAbove.mp
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
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    have hltε : ∃ (ε' : ℝ), 0 < ε' ∧
        ε' * (2 * ((μ Λ hΛ) (tsupport f)).toReal + |a| + b + ε') < ε := by
      set A := 2 * ((μ Λ hΛ) (tsupport f)).toReal + |a| + b with hA
      use ε / (4 * A + 2 + 2 * ε)
      have hAnonneg : 0 ≤ A := by
        rw [hA, add_assoc]
        apply add_nonneg _ habnonneg
        simp only [gt_iff_lt, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, toReal_nonneg]
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
          rw [_root_.lt_div_iff two_pos, mul_comm, ← mul_div_assoc, ← mul_div_assoc, div_lt_iff h3,
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
    apply le_of_lt (lt_of_le_of_lt _ (add_lt_add_left hε'.2 _))
    set δ := ε' / 2 with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      exact div_pos hε'.1 two_pos
    set N := (b - a) / δ with hN
    have hNNonneg : 0 ≤ N :=
      by exact div_nonneg (sub_nonneg.mpr hab) (le_of_lt hδpos)
    set y : ℤ → ℝ := fun n => b + δ * (n - (⌈N⌉₊+1)) with hy
    have ymono : ∀ (j k : ℤ), y j < y k → j < k := by
      intro j k
      rw [hy]
      simp only [add_lt_add_iff_left]
      intro h
      apply (@Int.cast_lt ℝ).mp
      apply @lt_of_tsub_lt_tsub_right ℝ j k (⌈N⌉₊ + 1)
      exact lt_of_mul_lt_mul_left h (le_of_lt hδpos)
    have hy1leyn : ∀ (n : Fin (⌈N⌉₊ + 1)), y 1 ≤ y (n + 1) := by
      intro n
      rw [hy]
      simp only [Int.cast_one, sub_add_cancel_right, mul_neg, Int.cast_add, Int.cast_natCast,
        add_sub_add_right_eq_sub, add_lt_add_iff_left]
      rw [_root_.mul_sub]
      apply le_add_neg_iff_le.mp
      ring_nf
      simp only [one_div, gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_right]
      exact mul_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _)
    have hymono' : ∀ (m n : Fin (⌈N⌉₊ + 1)), m ≤ n → y m ≤ y n := by
      intro m n hmn
      rw [hy]
      simp only [Int.cast_natCast, add_le_add_iff_left]
      rw [_root_.mul_sub, _root_.mul_sub]
      simp only [tsub_le_iff_right, sub_add_cancel]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hδpos)
      rw [Nat.cast_le]
      simp only [Fin.val_fin_le]
      exact hmn
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
    set Erest : Fin (⌈N⌉₊ + 1) → Set X := fun n => E n with hErest
    have hErestdisjoint : PairwiseDisjoint univ Erest := by
      intro m _ n _ hmn
      apply Disjoint.preimage
      simp only [mem_preimage]
      by_cases hmltn : m < n
      · rw [Set.disjoint_left]
        intro x hx
        simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
        simp only [mem_Ioc, mem_setOf_eq] at hx
        left
        left
        apply le_trans hx.1.2
        have : m.1 + (1 : ℤ) = (m+1 : Fin (⌈N⌉₊ + 1)) := by
          rw [← Nat.cast_add_one, Nat.cast_inj]
          apply Eq.symm (Fin.val_add_one_of_lt _)
          exact lt_of_lt_of_le hmltn (Fin.le_last n)
        rw [this]
        apply hymono' _ _
        exact Fin.add_one_le_of_lt hmltn
      · rw [Set.disjoint_left]
        intro x hx
        simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
        simp only [mem_Ioc, mem_setOf_eq] at hx
        push_neg at hmltn
        set hnltm := lt_of_le_of_ne hmltn (Ne.symm hmn)
        left
        right
        apply lt_of_le_of_lt _ hx.1.1
        have : n.1 + (1 : ℤ) = (n+1 : Fin (⌈N⌉₊ + 1)) := by
          rw [← Nat.cast_add_one, Nat.cast_inj]
          apply Eq.symm (Fin.val_add_one_of_lt _)
          exact lt_of_lt_of_le hnltm (Fin.le_last m)
        rw [this]
        apply hymono' _ _
        exact Fin.add_one_le_of_lt hnltm
    have hErestdisjoint' : Pairwise (Disjoint on Erest) := by
      intro m n hmn
      apply Disjoint.preimage
      simp only [mem_preimage]
      by_cases hmltn : m < n
      · rw [Set.disjoint_left]
        intro x hx
        simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
        simp only [mem_Ioc, mem_setOf_eq] at hx
        left
        left
        apply le_trans hx.1.2
        have : m.1 + (1 : ℤ) = (m+1 : Fin (⌈N⌉₊ + 1)) := by
          rw [← Nat.cast_add_one, Nat.cast_inj]
          apply Eq.symm (Fin.val_add_one_of_lt _)
          exact lt_of_lt_of_le hmltn (Fin.le_last n)
        rw [this]
        apply hymono' _ _
        exact Fin.add_one_le_of_lt hmltn
      · rw [Set.disjoint_left]
        intro x hx
        simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
        simp only [mem_Ioc, mem_setOf_eq] at hx
        push_neg at hmltn
        set hnltm := lt_of_le_of_ne hmltn (Ne.symm hmn)
        left
        right
        apply lt_of_le_of_lt _ hx.1.1
        have : n.1 + (1 : ℤ) = (n+1 : Fin (⌈N⌉₊ + 1)) := by
          rw [← Nat.cast_add_one, Nat.cast_inj]
          apply Eq.symm (Fin.val_add_one_of_lt _)
          exact lt_of_lt_of_le hnltm (Fin.le_last m)
        rw [this]
        apply hymono' _ _
        exact Fin.add_one_le_of_lt hnltm
    have hErestmeasurable : ∀ (n : Fin (⌈N⌉₊ + 1)), MeasurableSet (Erest n) := by
      intro n
      rw [hErest]
      simp only
      apply MeasurableSet.inter
      · exact (ContinuousMap.measurable f.1) measurableSet_Ioc
      · exact measurableSet_closure
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
      have hjnonneg : 0 ≤ j := by
        apply (Int.add_le_add_iff_right 1).mp
        apply Int.le_of_sub_one_lt
        simp only [zero_add, sub_self]
        apply ymono
        apply lt_of_lt_of_le hy0
        simp only [mem_Ioc] at hj
        apply le_trans _ hj.2
        apply ha
        rw [hLdef]
        exact hz
      have hjltceil : j < ⌈N⌉₊ + 1 := by
        apply ymono
        simp only [mem_Ioc] at hj
        apply lt_of_lt_of_le hj.1 _
        rw [hy]
        simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, sub_self, mul_zero, add_zero]
        apply hb
        rw [hLdef]
        exact hz
      have hnltceil : j.toNat < ⌈N⌉₊ + 1 := by
        exact (Int.toNat_lt hjnonneg).mpr hjltceil
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
    have htsupporteqErest : tsupport f = ⋃ j, Erest j := by
      apply subset_antisymm
      · exact htsupportsubErest
      · exact Set.iUnion_subset hErestsubtsupport
    have hμsuppfeqμErest : (μ Λ hΛ) (tsupport f) = ∑ n, (μ Λ hΛ) (Erest n) := by
      rw [htsupporteqErest]
      rw [← MeasureTheory.measure_biUnion_finset]
      · simp only [Finset.mem_univ, iUnion_true]
      · simp only [Finset.coe_univ]
        exact hErestdisjoint
      · intro n _
        exact hErestmeasurable n
    set SpecV := fun (n : Fin (⌈N⌉₊ + 1)) =>
      MeasureTheory.Content.outerMeasure_exists_open (rieszContent Λ hΛ)
      (ne_of_lt (lt_of_le_of_lt ((rieszContent Λ hΛ).outerMeasure.mono (hErestsubtsupport n))
      (MeasureTheory.Content.outerMeasure_lt_top_of_isCompact (rieszContent Λ hΛ) f.2)))
      (ne_of_gt (Real.toNNReal_pos.mpr (div_pos hε'.1 (Nat.cast_pos.mpr (Nat.add_one_pos ⌈N⌉₊)))))
    set V : Fin (⌈N⌉₊ + 1) → Opens X := fun n => Classical.choose (SpecV n) ⊓
      ⟨(f ⁻¹' Iio (y (n + 1) + ε')), IsOpen.preimage f.1.2 isOpen_Iio⟩ with hV
    have hErestsubV : ∀ (n : Fin (⌈N⌉₊ + 1)), Erest n ⊆ V n := by
      intro n
      rw [hV]
      simp only [Nat.cast_succ, Opens.coe_inf, Opens.coe_mk, subset_inter_iff]
      constructor
      · simp only [Nat.cast_add, Nat.cast_one] at SpecV
        exact (Classical.choose_spec (SpecV n)).1
      · rw [hErest]
        simp only
        apply Set.Subset.trans (Set.inter_subset_left) _
        intro z hz
        rw [Set.mem_preimage]
        rw [Set.mem_preimage] at hz
        exact lt_of_le_of_lt hz.2 (lt_add_of_pos_right (y (n + 1)) hε'.1)
    have htsupportsubV : tsupport f ⊆ ⋃ n : Fin (⌈N⌉₊ + 1), V n := by
      apply Set.Subset.trans htsupportsubErest _
      apply Set.iUnion_mono
      exact hErestsubV
    obtain ⟨g, hg⟩ := exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed
      (fun n => (V n).2) f.2 htsupportsubV
    have hf : f = ∑ n, g n • f := by
      ext x
      simp only [CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_smulc,
        smul_eq_mul, Finset.sum_apply]
      rw [← Finset.sum_mul, ← Finset.sum_apply]
      by_cases hx : x ∈ tsupport f
      · rw [hg.2.2.1 hx]
        simp only [Pi.one_apply, one_mul]
      · rw [image_eq_zero_of_nmem_tsupport hx]
        simp only [Finset.sum_apply, mul_zero]
    have μtsupportflesumΛgn :
        (μ Λ hΛ (TopologicalSpace.Compacts.mk (tsupport f) f.2)) ≤
        ENNReal.ofReal (Λ (∑ n, ⟨g n, hg.2.1 n⟩)) := by
      rw [μ]
      rw [MeasureTheory.Content.measure_eq_content_of_regular (rieszContent Λ hΛ)
        (rieszContentRegular Λ hΛ) ⟨tsupport f, f.2⟩]
      rw [rieszContent]
      simp only [map_sum]
      apply ENNReal.coe_le_iff.mpr
      intro p hp
      rw [← ENNReal.ofReal_coe_nnreal] at hp
      rw [ENNReal.ofReal_eq_ofReal_iff] at hp
      rw [rieszContentNonneg]
      apply csInf_le (rieszContentNonneg_image_BddBelow Λ hΛ ⟨tsupport f, f.2⟩)
      rw [Set.mem_image]
      -- need to define g n as C(X, ℝ≥0)
      set nng : Fin (⌈N⌉₊ + 1) → C_c(X, ℝ≥0) :=
        fun n => ⟨⟨Real.toNNReal ∘ (g n), Continuous.comp continuous_real_toNNReal (g n).2⟩,
        @HasCompactSupport.comp_left _ _ _ _ _ _ Real.toNNReal (g n) (hg.2.1 n) Real.toNNReal_zero⟩
        with hnng
      use ∑ n, nng n
      constructor
      · intro x hx
        rw [CompactlySupportedContinuousMap.sum_apply Finset.univ (fun n => nng n) x]
        rw [hnng]
        simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, comp_apply]
        rw [← Real.toNNReal_sum_of_nonneg _]
        · simp only [Real.one_le_toNNReal]
          set hgx := hg.2.2.1 hx
          simp only [Finset.sum_apply, Pi.one_apply] at hgx
          rw [hgx]
        · intro n _
          exact (hg.2.2.2 n x).1
      · rw [RestrictNonneg]
        rw [NNReal.eq_iff]
        simp only [coe_mk]
        rw [continuousExtendToReal_sum, map_sum Λ _ Finset.univ, ← hp]
        apply Finset.sum_congr (Eq.refl _)
        intro n _
        rw [hnng, continuousExtendToReal]
        simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk]
        apply congr (Eq.refl _)
        simp only [CompactlySupportedContinuousMap.mk.injEq]
        ext x
        simp only [ContinuousMap.coe_mk, comp_apply, Real.coe_toNNReal', max_eq_left_iff]
        exact (hg.2.2.2 n x).1
      · rw [← map_sum Λ _ Finset.univ]
        apply hΛ
        intro x
        simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
          CompactlySupportedContinuousMap.coe_toContinuousMap,
          CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_mk,
          Finset.sum_apply]
        apply Finset.sum_nonneg
        intro n hn
        exact (hg.2.2.2 n x).1
      · exact p.2
    have μtsupportflesumΛgn' : (μ Λ hΛ (TopologicalSpace.Compacts.mk (tsupport f) f.2)).toReal ≤
        ∑ n, Λ ⟨g n, hg.2.1 n⟩ := by
      rw [← map_sum]
      apply ENNReal.toReal_le_of_le_ofReal _ μtsupportflesumΛgn
      apply hΛ
      intro x
      simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
        CompactlySupportedContinuousMap.coe_toContinuousMap,
        CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_mk,
        Finset.sum_apply]
      apply Finset.sum_nonneg
      intro n _
      exact (hg.2.2.2 n x).1
    have hErestx : ∀ (n : Fin (⌈N⌉₊ + 1)), ∀ (x : X), x ∈ Erest n → y n < f x := by
      intro n x hnx
      rw [hErest, hE] at hnx
      simp only [mem_inter_iff, mem_preimage, mem_Ioc] at hnx
      exact hnx.1.1
    have hgf : ∀ (n : Fin (⌈N⌉₊ + 1)), (g n • f).1 ≤ ((y (n + 1) + ε') • (⟨g n, hg.2.1 n⟩ : C_c(X, ℝ))).1 := by
      intro n x
      simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap,
        CompactlySupportedContinuousMap.smulc_apply, CompactlySupportedContinuousMap.coe_smul,
        CompactlySupportedContinuousMap.coe_mk, Pi.smul_apply, smul_eq_mul]
      by_cases hx : x ∈ tsupport (g n)
      · rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ (hg.2.2.2 n x).1
        have : x ∈ V n := Set.mem_of_subset_of_mem (hg.1 n) hx
        rw [hV] at this
        simp only [Nat.cast_add, Nat.cast_one] at this
        rw [TopologicalSpace.Opens.mem_mk] at this
        simp only [Opens.carrier_eq_coe, Opens.coe_inf, Opens.coe_mk, mem_inter_iff,
          SetLike.mem_coe, mem_preimage, mem_Iio] at this
        exact le_of_lt this.2
      · rw [image_eq_zero_of_nmem_tsupport hx]
        simp only [zero_mul, mul_zero, le_refl]
    have hΛgf : ∀ (n : Fin (⌈N⌉₊ + 1)), n ∈ Finset.univ →  Λ (g n • f)
        ≤ Λ ((y (n + 1) + ε') • (⟨g n, hg.2.1 n⟩ : C_c(X, ℝ))) := by
      intro n _
      exact Λ_mono Λ hΛ (hgf n)
    nth_rw 1 [hf]
    simp only [map_sum, CompactlySupportedContinuousMap.coe_sum,
      Finset.sum_apply, Pi.mul_apply]
    apply le_trans (Finset.sum_le_sum hΛgf)
    simp only [map_smul, smul_eq_mul]
    rw [← add_zero ε']
    simp_rw [← add_assoc, ← sub_self |a|, ← add_sub_assoc, _root_.sub_mul]
    simp only [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    have hy1a : 0 < y 1 + ε' + |a| := by
      rw [hy]
      simp only [Fin.val_zero, CharP.cast_eq_zero, zero_add, Int.cast_one, sub_add_cancel_right,
        mul_neg]
      rw [add_assoc, add_assoc, add_comm, add_assoc, lt_neg_add_iff_lt, ← lt_div_iff' hδpos]
      apply lt_trans (Nat.ceil_lt_add_one hNNonneg)
      rw [lt_div_iff' hδpos, hN, mul_add, mul_comm, div_mul, div_self (ne_of_gt hδpos)]
      simp only [div_one, mul_one]
      rw [hδ]
      apply lt_add_of_tsub_lt_right
      rw [add_sub_assoc, add_comm, ← add_sub_assoc]
      apply sub_right_lt_of_lt_add
      rw [sub_add]
      simp only [sub_self, sub_zero]
      apply lt_neg_add_iff_lt.mp
      rw [add_assoc, ← add_assoc]
      apply add_pos_of_pos_of_nonneg
      · simp only [lt_neg_add_iff_add_lt, add_zero, half_lt_self_iff]
        exact hε'.1
      · exact neg_le_iff_add_nonneg'.mp (neg_abs_le a)
    have hyna : ∀ (n : Fin (⌈N⌉₊ + 1)), 0 < y (n + 1) + ε' + |a| := by
      intro n
      by_cases hn : n = 0
      · rw [hn]
        exact hy1a
      · push_neg at hn
        have hnp : 0 < n := by
          exact Fin.pos_iff_ne_zero.mpr hn
        rw [← sub_add_cancel (y (n + 1)) (y 1), add_assoc, add_assoc]
        apply add_pos_of_nonneg_of_pos
        · exact sub_nonneg_of_le (hy1leyn n)
        · rw [← add_assoc]
          exact hy1a
    have hΛgnleμVn : ∀ (n : Fin (⌈N⌉₊ + 1)),
        ENNReal.ofReal (Λ (⟨g n, hg.2.1 n⟩)) ≤ (μ Λ hΛ) (V n) := by
      intro n
      apply leRieszMeasure_isOpen
      · simp only [CompactlySupportedContinuousMap.coe_mk]
        intro x
        exact hg.2.2.2 n x
      · simp only [CompactlySupportedContinuousMap.coe_mk]
        rw [← TopologicalSpace.Opens.carrier_eq_coe]
        exact hg.1 n

    have hμVnleμEnaddε : ∀ (n : Fin (⌈N⌉₊ + 1)),
        (μ Λ hΛ) (V n) ≤ (μ Λ hΛ) (Erest n) + ENNReal.ofReal (ε' / ((⌈N⌉₊ + 1 : ℕ))) := by
      intro n
      rw [μ]
      rw [← TopologicalSpace.Opens.carrier_eq_coe]
      rw [MeasureTheory.Content.measure_apply (rieszContent Λ hΛ) (V n).2.measurableSet]
      rw [TopologicalSpace.Opens.carrier_eq_coe]
      rw [MeasureTheory.Content.measure_apply (rieszContent Λ hΛ) (hErestmeasurable n)]
      set Un := Classical.choose (SpecV n) with hUn
      set SpecUn := Classical.choose_spec (SpecV n)
      have hVU : V n ≤ Un := by
        exact inf_le_left
      have hμVleμU :
          (rieszContent Λ hΛ).outerMeasure (V n) ≤ (rieszContent Λ hΛ).outerMeasure (Un) := by
        exact MeasureTheory.OuterMeasure.mono (rieszContent Λ hΛ).outerMeasure hVU
      apply le_trans hμVleμU
      rw [hUn]
      have hENNNR : ∀ (p : ℝ), ENNReal.ofReal p = p.toNNReal := by
        intro p
        rfl
      rw [hENNNR]
      exact SpecUn.2
    have hμErestlttop : ∀ (n : Fin (⌈N⌉₊ + 1)), (μ Λ hΛ) (Erest n) < ⊤ := by
      intro n
      apply lt_of_le_of_lt (MeasureTheory.measure_mono (hErestsubtsupport n))
      have : f = f.toFun := by
        exact rfl
      rw [μ, this,
        MeasureTheory.Content.measure_apply _ f.2.measurableSet]
      exact MeasureTheory.Content.outerMeasure_lt_top_of_isCompact _ f.2
    have hμsuppfeqμErest' : ((μ Λ hΛ) (tsupport f)).toReal = ∑ n, ((μ Λ hΛ) (Erest n)).toReal := by
      rw [← ENNReal.toReal_sum]
      exact congr rfl hμsuppfeqμErest
      intro n _
      rw [← lt_top_iff_ne_top]
      exact hμErestlttop n
    have hΛgnleμVn' : ∀ (n : Fin (⌈N⌉₊ + 1)),
        Λ (⟨g n, hg.2.1 n⟩) ≤ ((μ Λ hΛ) (V n)).toReal := by
      intro n
      apply (ENNReal.ofReal_le_iff_le_toReal _).mp (hΛgnleμVn n)
      rw [← lt_top_iff_ne_top]
      apply lt_of_le_of_lt (hμVnleμEnaddε n)
      rw [WithTop.add_lt_top]
      constructor
      · exact hμErestlttop n
      · exact ENNReal.ofReal_lt_top
    have hμVnleμEnaddε' : ∀ (n : Fin (⌈N⌉₊ + 1)),
        ((μ Λ hΛ) (V n)).toReal ≤ ((μ Λ hΛ) (Erest n)).toReal + (ε' / ((⌈N⌉₊ + 1 : ℕ))) := by
      intro n
      rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
      apply ENNReal.toReal_le_add (hμVnleμEnaddε n)
      · exact lt_top_iff_ne_top.mp (hμErestlttop n)
      · exact ENNReal.ofReal_ne_top
    have ynsubεmulμEnleintEnf :
        ∀ (n : Fin (⌈N⌉₊ + 1)), (y (n + 1) - ε') * ((μ Λ hΛ) (Erest n)).toReal
        ≤ ∫ x in (Erest n), f x ∂(μ Λ hΛ) := by
      intro n
      apply MeasureTheory.setIntegral_ge_of_const_le (hErestmeasurable n)
      · rw [μ]
        rw [MeasureTheory.Content.measure_apply _ (hErestmeasurable n)]
        rw [← lt_top_iff_ne_top]
        apply lt_of_le_of_lt (MeasureTheory.OuterMeasure.mono _ (hErestsubtsupport n))
        exact MeasureTheory.Content.outerMeasure_lt_top_of_isCompact _ f.2
      · intro x hx
        apply le_of_lt (lt_trans _ (hErestx n x hx))
        rw [hy]
        simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_add_right_eq_sub]
        rw [sub_add_eq_sub_sub]
        nth_rw 2 [_root_.mul_sub]
        rw [add_sub_assoc]
        simp only [mul_one, add_lt_add_iff_left, sub_lt_sub_iff_left]
        rw [hδ]
        linarith



      · apply MeasureTheory.Integrable.integrableOn
        rw [μ]
        exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    apply le_trans (tsub_le_tsub_left (mul_le_mul_of_nonneg_left μtsupportflesumΛgn' (abs_nonneg a)) _)
    rw [add_mul]
    simp only [add_sub_cancel_right]
    apply le_trans (tsub_le_tsub_right (Finset.sum_le_sum (fun n => (fun _ =>
      mul_le_mul_of_nonneg_left
      (le_trans (hΛgnleμVn' n) (hμVnleμEnaddε' n)) (le_of_lt (hyna n))))) _)
    simp_rw [mul_add _ ((μ Λ hΛ) _).toReal _]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    nth_rw 1 [← sub_add_cancel ε' ε']
    simp_rw [add_assoc _ _ |a|, ← add_assoc _ _ (ε' + |a|), Eq.symm (add_comm_sub _ ε' ε'),
      add_assoc _ ε' _, ← add_assoc ε' ε' |a|, Eq.symm (two_mul ε')]
    simp_rw [add_mul _ (2 * ε' + |a|) ((μ Λ hΛ) _).toReal]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hμsuppfeqμErest', add_mul (2 * ε') |a| _]
    simp only [Compacts.coe_mk]
    have hynleb : ∀ (n : Fin (⌈N⌉₊ + 1)), y (n + 1) ≤ b := by
      intro n
      rw [hy]
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_add_right_eq_sub,
        add_le_iff_nonpos_right]
      apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hδpos)
      simp only [tsub_le_iff_right, zero_add, Nat.cast_le]
      exact Fin.is_le n
    have hynleb' : ∀ (n : Fin (⌈N⌉₊ + 1)), y (n + 1) + (ε' + |a|) ≤ |a| + b + ε':= by
      intro n
      set h := hynleb n
      linarith
    rw [add_assoc, add_sub_assoc, add_sub_assoc, add_add_sub_cancel, ← add_assoc]
    apply le_trans ((add_le_add_iff_left _).mpr (mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum (fun n => fun _ => hynleb' n))
      (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    rw [mul_comm _ (|a| + b + ε'), mul_assoc (|a| + b + ε') _ _, ← mul_div_assoc]
    nth_rw 2 [mul_comm _ ε']
    rw [mul_div_assoc, div_self (ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) one_pos)),
      mul_one]
    rw [MeasureTheory.integral_tsupport, htsupporteqErest]
    nth_rw 3 [μ]
    have : f = f.toFun := by rfl
    rw [this]
    rw [MeasureTheory.integral_fintype_iUnion hErestmeasurable hErestdisjoint'
      fun n =>
      (MeasureTheory.Integrable.integrableOn (Continuous.integrable_of_hasCompactSupport f.1.2 f.2))]
    rw [add_assoc]
    apply add_le_add
    · apply Finset.sum_le_sum
      exact fun n => fun _ => ynsubεmulμEnleintEnf n
    · linarith
  intro f
  apply le_antisymm
  · calc ∫ (x : X), f x ∂(μ Λ hΛ) = ∫ (x : X), -(-f) x ∂(μ Λ hΛ) := by simp only
      [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply, neg_neg]
    _ = - ∫ (x : X), (-f) x ∂(μ Λ hΛ) := by exact MeasureTheory.integral_neg' (-f)
    _ ≤ - Λ (-f) := by exact neg_le_neg (RMK_le (-f))
    _ = Λ (- -f) := by exact Eq.symm (Λ_neg Λ)
    _ = Λ f := by simp only [neg_neg]
  · exact RMK_le f
