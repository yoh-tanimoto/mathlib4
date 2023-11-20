import Mathlib.NumberTheory.NumberField.Discriminant

open NumberField

example {A : Type*} [Field A] [CharZero A] [IsAlgClosed A] (N : ℕ) :
    {K : { K : IntermediateField ℚ A // FiniteDimensional ℚ K } |
      haveI :  NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |discr K| ≤ N }.Finite := sorry
