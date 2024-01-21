import Mathlib.FieldTheory.IntermediateField
import Mathlib.Analysis.Convex.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

section Algebra.Hom

@[simp]
theorem RingHom.toRatAlgHom_apply {R S : Type*} [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
  (f : R →+* S) (x : R) :
  RingHom.toRatAlgHom f x = f x := rfl

end Algebra.Hom

section Complex

open  MeasureTheory MeasureTheory.Measure NNReal

example (r : ℝ≥0) (hr : 1 ≤ r) : r ≤ volume {x : ℂ | ‖x‖ < r ∧ |x.re| < 1} := by
  

  sorry



end Complex

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
