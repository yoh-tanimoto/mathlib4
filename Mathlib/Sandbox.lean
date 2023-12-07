import Mathlib

open FiniteDimensional

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [Nontrivial A]

noncomputable example (h : finrank K A = 1) : K ≃+* A := by
  refine RingEquiv.ofBijective (algebraMap K A) ⟨(algebraMap K A).injective, fun y ↦ ?_⟩
  simp_rw [Algebra.algebraMap_eq_smul_one]
  exact (finrank_eq_one_iff_of_nonzero' (1:A) one_ne_zero).mp h y
