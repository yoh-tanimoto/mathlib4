import Mathlib

variable (H : Type)

example : ∃ (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (K : Submodule ℂ H),
    (IsClosed (K : Set H)) ∧ Kᗮᗮ ≠ K := by sorry
