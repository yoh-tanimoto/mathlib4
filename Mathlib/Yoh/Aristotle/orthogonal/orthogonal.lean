import Mathlib

variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (K : Submodule ℂ H) (h : IsClosed (K : Set H))

example : Kᗮᗮ = K := by sorry

abbrev l2 := lp (fun (_ : ℕ) => ℂ) 2

def Cc : Submodule ℂ l2 where
  carrier := { x : l2 | HasCompactSupport x }
  add_mem' := .add
  zero_mem' := .zero
  smul_mem' _ _ := .smul_left

#check Cc

#synth InnerProductSpace ℂ Cc

example : ∃ (K : Submodule ℂ Cc), (IsClosed (K : Set Cc)) ∧ Kᗮᗮ ≠ K := by sorry
