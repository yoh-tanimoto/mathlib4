import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.NumberTheory.NumberField.Embeddings

section Measurable

variable {R : Type*} [Lattice R] [Group R] [MeasurableSpace R] [MeasurableSup₂ R]
  [MeasurableInv R]

@[to_additive (attr := measurability)]
theorem measurable_mabs : Measurable fun x : R ↦ mabs x :=
  Measurable.sup measurable_id' measurable_inv

end Measurable

section InfinitePlace

variable {K : Type*} [Field K]

namespace NumberField.InfinitePlace

open NumberField IntermediateField Complex

theorem _root_.NumberField.is_primitive_element_of_infinitePlace_lt [NumberField K] (x : 𝓞 K)
    {w : InfinitePlace K} (h₁ : x ≠ 0) (h₂ : ∀ ⦃w'⦄, w' ≠ w → w' x < 1)
    (h₃ : IsReal w ∨ |(w.embedding x).re| < 1) : ℚ⟮(x:K)⟯ = ⊤ := by
  rw [Field.primitive_element_iff_algHom_eq_of_eval ℚ ℂ ?_ _ w.embedding.toRatAlgHom]
  · intro ψ hψ
    have h : 1 ≤ w x := ge_one_of_lt_one h₁ h₂
    have main : w = InfinitePlace.mk ψ.toRingHom := by
      erw [← norm_embedding_eq, hψ] at h
      contrapose! h
      exact h₂ h.symm
    rw [(mk_embedding w).symm, mk_eq_iff] at main
    by_cases hw : IsReal w
    · rw [conjugate_embedding_eq_of_isReal hw, or_self] at main
      exact congr_arg RingHom.toRatAlgHom main
    · refine congr_arg RingHom.toRatAlgHom (main.resolve_right fun h' ↦ ?_)
      have : (embedding w x).im = 0 := by
        erw [← conj_eq_iff_im, RingHom.congr_fun h' x]
        exact hψ.symm
      contrapose! h
      rw [← norm_embedding_eq, ← re_add_im (embedding w x), this, ofReal_zero, zero_mul,
        add_zero, norm_eq_abs, abs_ofReal]
      exact h₃.resolve_left hw
  . exact fun x ↦ IsAlgClosed.splits_codomain (minpoly ℚ x)

end InfinitePlace

section Algebra.Hom

@[simp]
theorem RingHom.toRatAlgHom_apply {R S : Type*} [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
  (f : R →+* S) (x : R) :
  RingHom.toRatAlgHom f x = f x := rfl

end Algebra.Hom



section Volume

open MeasureTheory MeasureTheory.Measure NNReal ENNReal

example (B : ℝ≥0) : volume {x : ℂ | |x.re| < 1 ∧ |x.im| < B^2} = 4*B^2 := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage]
  simp_rw [Set.preimage_setOf_eq, Complex.measurableEquivRealProd_symm_apply]
  rw [show {a : ℝ × ℝ | |a.1| < 1 ∧ |a.2| < B ^ 2} =
      Set.Ioo (-1:ℝ) (1:ℝ) ×ˢ Set.Ioo (- (B:ℝ) ^ 2) ((B:ℝ) ^ 2) by
        ext; rw [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo, abs_lt, abs_lt]]
  rw [volume_eq_prod, prod_prod, Real.volume_Ioo, Real.volume_Ioo, sub_neg_eq_add, sub_neg_eq_add,
    one_add_one_eq_two, ← two_mul, ofReal_mul zero_le_two, ofReal_pow (coe_nonneg B), ofReal_ofNat,
    ofReal_coe_nnreal, ← mul_assoc, show (2:ℝ≥0∞) * 2 = 4 by norm_num]
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt (measurable_abs.comp Complex.measurable_re) measurable_const
  · exact measurableSet_lt (measurable_abs.comp Complex.measurable_im) measurable_const

end Volume


#exit

section Convex

example (r : ℝ) : Convex ℝ {x : ℂ | |x.re| < 1} := by
  simp_rw [abs_lt]
  exact Convex.inter (convex_halfspace_re_gt _) (convex_halfspace_re_lt _)

end Convex

#exit

variable {A E : Type*} [Field A] [Field E] [Algebra E A] (F : IntermediateField E A)

-- attribute [local instance 1001] Algebra.id


-- set_option synthInstance.maxHeartbeats 150000 in
#synth Algebra F F -- Algebra A F ? -> Algebra A E ?

instance : Algebra F F := Algebra.id F

#synth Algebra F F


#exit


open NumberField

attribute [local instance 2000] inst_ringOfIntegersAlgebra Algebra.toSMul Algebra.toModule

attribute [local instance 909] Subalgebra.module'

variable {A : Type*} [Field A] [CharZero A]

example (F : Subfield A) (h : FiniteDimensional ℚ F) :
    haveI :  NumberField F := @NumberField.mk _ _ inferInstance h
    Algebra (𝓞 F) F := by
    let S := (𝓞 F)
    refine @Subalgebra.toAlgebra F ℤ F _ _ _ _ _ (𝓞 F)


set_option maxHeartbeats 200000 in
example (F : IntermediateField ℚ A) (h : FiniteDimensional ℚ F) :
    haveI : NumberField F := @NumberField.mk _ _ inferInstance h
    Algebra (𝓞 F) F := by
    refine @Subalgebra.toAlgebra F ℤ F _ _ _ _ ?_ (𝓞 F)


#exit
section

open Nat

example (n m : ℕ) (h : n ≤ m) :
    choose n (n / 2) ≤ choose m (m / 2) := by
  refine (Nat.choose_le_choose _ h).trans ?_
  exact choose_le_middle (n / 2) m

section

open FiniteDimensional

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [Nontrivial A]

noncomputable example (h : finrank K A = 1) : K ≃+* A := by
  refine RingEquiv.ofBijective (algebraMap K A) ⟨(algebraMap K A).injective, fun y ↦ ?_⟩
  simp_rw [Algebra.algebraMap_eq_smul_one]
  exact (finrank_eq_one_iff_of_nonzero' (1:A) one_ne_zero).mp h y

end
