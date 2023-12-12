/-
Copyright (c) 2019 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Sifted categories

A category `C` is sifted iff it is inhabited and the diagonal functor `D ⥤ D × D` is final.
These categories are important as colimits from them commute with finite products (in fact, in
many places in the literature this is the official definition).

As a concrete example, we show that categories with finite coproducts are sifted.

## References
- [nlab: Sifted Category](https://ncatlab.org/nlab/show/sifted+category)
-/

open CategoryTheory Functor Limits

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category `IsSiftedOrEmpty` if the diagonal functor `C → C × C` is final. -/
class IsSiftedOrEmpty : Prop where
  /-- The diagonal functor `C ⥤ C × C` is Final -/
  final_diag : Final (show C ⥤ (Discrete (Fin 2) ⥤ C) from Functor.const _)

class IsSifted extends IsSiftedOrEmpty C : Prop where
  [nonempty : Nonempty C]

instance [HasBinaryCoproducts C] : IsSiftedOrEmpty C where
  final_diag := {
    out := fun d => { iso_constant := sorry, is_nonempty := Nonempty.intro sorry }}

instance [HasFiniteCoproducts C] : IsSifted C :=
  { (inferInstance : IsSiftedOrEmpty C ) with nonempty := Nonempty.intro sorry }

end CategoryTheory
