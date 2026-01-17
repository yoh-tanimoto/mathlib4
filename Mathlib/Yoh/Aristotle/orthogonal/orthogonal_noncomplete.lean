import Mathlib

variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (K : Submodule ℂ H)
  (h : IsClosed (K : Set H))

example : Kᗮᗮ = K := by sorry
