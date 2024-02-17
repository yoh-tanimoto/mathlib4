/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.ZetaFunctions.HurwitzZetaEven
import Mathlib.NumberTheory.ZetaFunctions.HurwitzZetaOdd
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Hurwitz zeta function

-/

open Real Complex Classical

@[irreducible] noncomputable def hurwitzZeta (a : UnitAddCircle) (s : ℂ) :=
  if (a = 0 ∧ s = 0) then (-1 / 2)
  else (completedHurwitzZetaEven a s + completedHurwitzZetaOdd a s) * π ^ (s / 2) / Gamma (s / 2)

lemma differentiableAt_hurwitzZeta (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 1) (hs' : s ≠ 0 ∨ a ≠ 0) :
    DifferentiableAt ℂ (hurwitzZeta a) s := by
  have claim (t : ℂ) (ht : t ≠ 0 ∨ a ≠ 0) (ht' : t ≠ 1) : DifferentiableAt ℂ
      (fun u : ℂ ↦ (completedHurwitzZetaEven a u + completedHurwitzZetaOdd a u)
      * π ^ (u / 2) / Gamma (u / 2)) t := by
    apply DifferentiableAt.mul
    · refine DifferentiableAt.mul ?_ ((differentiableAt_id.div_const _).const_cpow ?_)
      · refine DifferentiableAt.add ?_ ?_
        · exact differentiableAt_completedHurwitzZetaEven a ht ht'
        · exact differentiable_completedHurwitzZetaOdd
      · exact Or.inl (ofReal_ne_zero.mpr pi_pos.ne')
    · exact differentiable_one_div_Gamma.differentiableAt.comp t (differentiableAt_id.div_const  _)
