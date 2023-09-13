/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tactic.CategoryTheory.Elementwise

#align_import category_theory.limits.shapes.types from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

/-!
# Special shapes for limits in `Type`.

The general shape (co)limits defined in `CategoryTheory.Limits.Types`
are intended for use through the limits API,
and the actual implementation should mostly be considered "sealed".

In this file, we provide definitions of the "standard" special shapes of limits in `Type`,
giving the expected definitional implementation:
* the terminal object is `PUnit`
* the binary product of `X` and `Y` is `X × Y`
* the product of a family `f : J → Type` is `Π j, f j`
* the coproduct of a family `f : J → Type` is `Σ j, f j`
* the binary coproduct of `X` and `Y` is the sum type `X ⊕ Y`
* the equalizer of a pair of maps `(g, h)` is the subtype `{x : Y // g x = h x}`
* the coequalizer of a pair of maps `(f, g)` is the quotient of `Y` by `∀ x : Y, f x ~ g x`
* the pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the subtype `{ p : X × Y // f p.1 = g p.2 }`
  of the product

We first construct terms of `IsLimit` and `LimitCone`, and then provide isomorphisms with the
types generated by the `HasLimit` API.

As an example, when setting up the monoidal category structure on `Type`
we use the `Types.terminalLimitCone` and `Types.binaryProductLimitCone` definitions.
-/


universe v v' u

open CategoryTheory Limits

namespace CategoryTheory.Limits.Types

example : HasProducts.{v} (Type v) := inferInstance
example [UnivLE.{v, u}] : HasProducts.{v} (Type u) := inferInstance

-- This shortcut instance is required in `Mathlib.CategoryTheory.Closed.Types`,
-- although I don't understand why, and wish it wasn't.
instance : HasProducts.{v} (Type v) := inferInstance

/-- A restatement of `Types.Limit.lift_π_apply` that uses `Pi.π` and `Pi.lift`. -/
@[simp 1001]
theorem pi_lift_π_apply [UnivLE.{v, u}] {β : Type v} (f : β → Type u) {P : Type u}
    (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
    (Pi.π f b : (piObj f) → f b) (@Pi.lift β _ _ f _ P s x) = s b x :=
  congr_fun (limit.lift_π (Fan.mk P s) ⟨b⟩) x
#align category_theory.limits.types.pi_lift_π_apply CategoryTheory.Limits.Types.pi_lift_π_apply

/-- A restatement of `Types.Limit.lift_π_apply` that uses `Pi.π` and `Pi.lift`,
with specialized universes. -/
theorem pi_lift_π_apply' {β : Type v} (f : β → Type v) {P : Type v}
    (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
    (Pi.π f b : (piObj f) → f b) (@Pi.lift β _ _ f _ P s x) = s b x :=
  by simp
#align category_theory.limits.types.pi_lift_π_apply' CategoryTheory.Limits.Types.pi_lift_π_apply'

/-- A restatement of `Types.Limit.map_π_apply` that uses `Pi.π` and `Pi.map`. -/
@[simp 1001]
theorem pi_map_π_apply [UnivLE.{v, u}] {β : Type v} {f g : β → Type u}
    (α : ∀ j, f j ⟶ g j) (b : β) (x) :
    (Pi.π g b : ∏ g → g b) (Pi.map α x) = α b ((Pi.π f b : ∏ f → f b) x) :=
  Limit.map_π_apply.{v, u} _ _ _
#align category_theory.limits.types.pi_map_π_apply CategoryTheory.Limits.Types.pi_map_π_apply

/-- A restatement of `Types.Limit.map_π_apply` that uses `Pi.π` and `Pi.map`,
with specialized universes. -/
theorem pi_map_π_apply' {β : Type v} {f g : β → Type v} (α : ∀ j, f j ⟶ g j) (b : β) (x) :
    (Pi.π g b : ∏ g → g b) (Pi.map α x) = α b ((Pi.π f b : ∏ f → f b) x) :=
   by simp
#align category_theory.limits.types.pi_map_π_apply' CategoryTheory.Limits.Types.pi_map_π_apply'

/-- The category of types has `PUnit` as a terminal object. -/
def terminalLimitCone : Limits.LimitCone (Functor.empty (Type u)) where
  -- porting note: tidy was able to fill the structure automatically
  cone :=
    { pt := PUnit
      π := (Functor.uniqueFromEmpty _).hom }
  isLimit :=
    { lift := fun _ _ => PUnit.unit
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by
        funext
        apply Subsingleton.elim }
#align category_theory.limits.types.terminal_limit_cone CategoryTheory.Limits.Types.terminalLimitCone

/-- The terminal object in `Type u` is `PUnit`. -/
noncomputable def terminalIso : ⊤_ Type u ≅ PUnit :=
  limit.isoLimitCone terminalLimitCone.{u, 0}
#align category_theory.limits.types.terminal_iso CategoryTheory.Limits.Types.terminalIso

/-- The terminal object in `Type u` is `PUnit`. -/
noncomputable def isTerminalPunit : IsTerminal (PUnit : Type u) :=
  terminalIsTerminal.ofIso terminalIso
#align category_theory.limits.types.is_terminal_punit CategoryTheory.Limits.Types.isTerminalPunit

-- porting note: the following three instances have been added to ease
-- the automation in a definition in `AlgebraicTopology.SimplicialSet`
noncomputable instance : Inhabited (⊤_ (Type u)) :=
  ⟨@terminal.from (Type u) _ _ (ULift (Fin 1)) (ULift.up 0)⟩

instance : Subsingleton (⊤_ (Type u)) := ⟨fun a b =>
  congr_fun (@Subsingleton.elim (_ ⟶ ⊤_ (Type u)) _
    (fun _ => a) (fun _ => b)) (ULift.up (0 : Fin 1))⟩

noncomputable instance : Unique (⊤_ (Type u)) := Unique.mk' _

/-- A type is terminal if and only if it contains exactly one element. -/
noncomputable def isTerminalEquivUnique (X : Type u) : IsTerminal X ≃ Unique X :=
  equivOfSubsingletonOfSubsingleton
    (fun h => ((Iso.toEquiv (terminalIsoIsTerminal h).symm).unique))
    (fun _ => IsTerminal.ofIso terminalIsTerminal (Equiv.toIso (Equiv.equivOfUnique _ _)))

/-- A type is terminal if and only if it is isomorphic to `PUnit`. -/
noncomputable def isTerminalEquivIsoPUnit (X : Type u) : IsTerminal X ≃ (X ≅ PUnit) := by
  calc
    IsTerminal X ≃ Unique X := isTerminalEquivUnique _
    _ ≃ (X ≃ PUnit.{u + 1}) := uniqueEquivEquivUnique _ _
    _ ≃ (X ≅ PUnit) := equivEquivIso

/-- The category of types has `PEmpty` as an initial object. -/
def initialColimitCocone : Limits.ColimitCocone (Functor.empty (Type u)) where
  -- porting note: tidy was able to fill the structure automatically
  cocone :=
    { pt := PEmpty
      ι := (Functor.uniqueFromEmpty _).inv }
  isColimit :=
    { desc := fun _ => by rintro ⟨⟩
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by funext x; cases x }
#align category_theory.limits.types.initial_colimit_cocone CategoryTheory.Limits.Types.initialColimitCocone

/-- The initial object in `Type u` is `PEmpty`. -/
noncomputable def initialIso : ⊥_ Type u ≅ PEmpty :=
  colimit.isoColimitCocone initialColimitCocone.{u, 0}
#align category_theory.limits.types.initial_iso CategoryTheory.Limits.Types.initialIso

/-- The initial object in `Type u` is `PEmpty`. -/
noncomputable def isInitialPunit : IsInitial (PEmpty : Type u) :=
  initialIsInitial.ofIso initialIso
#align category_theory.limits.types.is_initial_punit CategoryTheory.Limits.Types.isInitialPunit

open CategoryTheory.Limits.WalkingPair

-- We manually generate the other projection lemmas since the simp-normal form for the legs is
-- otherwise not created correctly.
/-- The product type `X × Y` forms a cone for the binary product of `X` and `Y`. -/
@[simps! pt]
def binaryProductCone (X Y : Type u) : BinaryFan X Y :=
  BinaryFan.mk _root_.Prod.fst _root_.Prod.snd
#align category_theory.limits.types.binary_product_cone CategoryTheory.Limits.Types.binaryProductCone

@[simp]
theorem binaryProductCone_fst (X Y : Type u) : (binaryProductCone X Y).fst = _root_.Prod.fst :=
  rfl
#align category_theory.limits.types.binary_product_cone_fst CategoryTheory.Limits.Types.binaryProductCone_fst

@[simp]
theorem binaryProductCone_snd (X Y : Type u) : (binaryProductCone X Y).snd = _root_.Prod.snd :=
  rfl
#align category_theory.limits.types.binary_product_cone_snd CategoryTheory.Limits.Types.binaryProductCone_snd

/-- The product type `X × Y` is a binary product for `X` and `Y`. -/
@[simps]
def binaryProductLimit (X Y : Type u) : IsLimit (binaryProductCone X Y) where
  lift (s : BinaryFan X Y) x := (s.fst x, s.snd x)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := funext fun x => Prod.ext (congr_fun (w ⟨left⟩) x) (congr_fun (w ⟨right⟩) x)
#align category_theory.limits.types.binary_product_limit CategoryTheory.Limits.Types.binaryProductLimit

/-- The category of types has `X × Y`, the usual cartesian product,
as the binary product of `X` and `Y`.
-/
@[simps]
def binaryProductLimitCone (X Y : Type u) : Limits.LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩
#align category_theory.limits.types.binary_product_limit_cone CategoryTheory.Limits.Types.binaryProductLimitCone

/-- The categorical binary product in `Type u` is cartesian product. -/
noncomputable def binaryProductIso (X Y : Type u) : Limits.prod X Y ≅ X × Y :=
  limit.isoLimitCone (binaryProductLimitCone X Y)
#align category_theory.limits.types.binary_product_iso CategoryTheory.Limits.Types.binaryProductIso

@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ _root_.Prod.fst = Limits.prod.fst :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.types.binary_product_iso_hom_comp_fst CategoryTheory.Limits.Types.binaryProductIso_hom_comp_fst

@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ _root_.Prod.snd = Limits.prod.snd :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.types.binary_product_iso_hom_comp_snd CategoryTheory.Limits.Types.binaryProductIso_hom_comp_snd

@[elementwise (attr := simp)]
theorem binaryProductIso_inv_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.fst = _root_.Prod.fst :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.types.binary_product_iso_inv_comp_fst CategoryTheory.Limits.Types.binaryProductIso_inv_comp_fst

@[elementwise (attr := simp)]
theorem binaryProductIso_inv_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.snd = _root_.Prod.snd :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.types.binary_product_iso_inv_comp_snd CategoryTheory.Limits.Types.binaryProductIso_inv_comp_snd

-- porting note: it was originally @[simps (config := { typeMd := reducible })]
-- We add the option `type_md` to tell `@[simps]` to not treat homomorphisms `X ⟶ Y` in `Type*` as
-- a function type
/-- The functor which sends `X, Y` to the product type `X × Y`. -/
@[simps]
def binaryProductFunctor : Type u ⥤ Type u ⥤ Type u where
  obj X :=
    { obj := fun Y => X × Y
      map := fun { Y₁ Y₂} f => (binaryProductLimit X Y₂).lift
        (BinaryFan.mk _root_.Prod.fst (_root_.Prod.snd ≫ f)) }
  map {X₁ X₂} f :=
    { app := fun Y =>
      (binaryProductLimit X₂ Y).lift (BinaryFan.mk (_root_.Prod.fst ≫ f) _root_.Prod.snd) }
#align category_theory.limits.types.binary_product_functor CategoryTheory.Limits.Types.binaryProductFunctor

/-- The product functor given by the instance `HasBinaryProducts (Type u)` is isomorphic to the
explicit binary product functor given by the product type.
-/
noncomputable def binaryProductIsoProd : binaryProductFunctor ≅ (prod.functor : Type u ⥤ _) := by
  refine' NatIso.ofComponents (fun X => _) (fun _ => _)
  · refine' NatIso.ofComponents (fun Y => _) (fun _ => _)
    · exact ((limit.isLimit _).conePointUniqueUpToIso (binaryProductLimit X Y)).symm
    · apply Limits.prod.hom_ext <;> simp <;> rfl
  · ext : 2
    apply Limits.prod.hom_ext <;> simp <;> rfl
#align category_theory.limits.types.binary_product_iso_prod CategoryTheory.Limits.Types.binaryProductIsoProd

/-- The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`. -/
@[simps!]
def binaryCoproductCocone (X Y : Type u) : Cocone (pair X Y) :=
  BinaryCofan.mk Sum.inl Sum.inr
#align category_theory.limits.types.binary_coproduct_cocone CategoryTheory.Limits.Types.binaryCoproductCocone

/-- The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`. -/
@[simps]
def binaryCoproductColimit (X Y : Type u) : IsColimit (binaryCoproductCocone X Y) where
  desc := fun s : BinaryCofan X Y => Sum.elim s.inl s.inr
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := funext fun x => Sum.casesOn x (congr_fun (w ⟨left⟩)) (congr_fun (w ⟨right⟩))
#align category_theory.limits.types.binary_coproduct_colimit CategoryTheory.Limits.Types.binaryCoproductColimit

/-- The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
def binaryCoproductColimitCocone (X Y : Type u) : Limits.ColimitCocone (pair X Y) :=
  ⟨_, binaryCoproductColimit X Y⟩
#align category_theory.limits.types.binary_coproduct_colimit_cocone CategoryTheory.Limits.Types.binaryCoproductColimitCocone

/-- The categorical binary coproduct in `Type u` is the sum `X ⊕ Y`. -/
noncomputable def binaryCoproductIso (X Y : Type u) : Limits.coprod X Y ≅ Sum X Y :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone X Y)
#align category_theory.limits.types.binary_coproduct_iso CategoryTheory.Limits.Types.binaryCoproductIso

--open CategoryTheory.Type

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inl_comp_hom (X Y : Type u) :
    Limits.coprod.inl ≫ (binaryCoproductIso X Y).hom = Sum.inl :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.types.binary_coproduct_iso_inl_comp_hom CategoryTheory.Limits.Types.binaryCoproductIso_inl_comp_hom

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inr_comp_hom (X Y : Type u) :
    Limits.coprod.inr ≫ (binaryCoproductIso X Y).hom = Sum.inr :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.types.binary_coproduct_iso_inr_comp_hom CategoryTheory.Limits.Types.binaryCoproductIso_inr_comp_hom

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inl_comp_inv (X Y : Type u) :
    ↾(Sum.inl : X ⟶ Sum X Y) ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inl :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.types.binary_coproduct_iso_inl_comp_inv CategoryTheory.Limits.Types.binaryCoproductIso_inl_comp_inv

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inr_comp_inv (X Y : Type u) :
    ↾(Sum.inr : Y ⟶ Sum X Y) ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inr :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.types.binary_coproduct_iso_inr_comp_inv CategoryTheory.Limits.Types.binaryCoproductIso_inr_comp_inv

open Function (Injective)

theorem binaryCofan_isColimit_iff {X Y : Type u} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      Injective c.inl ∧ Injective c.inr ∧ IsCompl (Set.range c.inl) (Set.range c.inr) := by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.left⟩,
        ← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.right⟩]
      dsimp [binaryCoproductCocone]
      refine'
        ⟨(h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inl_injective,
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inr_injective, _⟩
      erw [Set.range_comp, ← eq_compl_iff_isCompl, Set.range_comp _ Sum.inr, ←
        Set.image_compl_eq
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.bijective]
      simp
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine' ⟨BinaryCofan.IsColimit.mk _ _ _ _ _⟩
      · intro T f g x
        exact
          if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁).symm ⟨x, h⟩)
          else g ((Equiv.ofInjective _ h₂).symm ⟨x, (this x).resolve_left h⟩)
      · intro T f g
        funext x
        dsimp
        simp [h₁.eq_iff]
      · intro T f g
        funext x
        dsimp
        simp only [Set.mem_range, Equiv.ofInjective_symm_apply,
          dite_eq_right_iff, forall_exists_index]
        intro y e
        have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
        rw [disjoint_iff.mp h₃.1] at this
        exact this.elim
      · rintro T _ _ m rfl rfl
        funext x
        dsimp
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm
#align category_theory.limits.types.binary_cofan_is_colimit_iff CategoryTheory.Limits.Types.binaryCofan_isColimit_iff

/-- Any monomorphism in `Type` is a coproduct injection. -/
noncomputable def isCoprodOfMono {X Y : Type u} (f : X ⟶ Y) [Mono f] :
    IsColimit (BinaryCofan.mk f (Subtype.val : ↑(Set.range f)ᶜ → Y)) := by
  apply Nonempty.some
  rw [binaryCofan_isColimit_iff]
  refine' ⟨(mono_iff_injective f).mp inferInstance, Subtype.val_injective, _⟩
  symm
  rw [← eq_compl_iff_isCompl]
  exact Subtype.range_val
#align category_theory.limits.types.is_coprod_of_mono CategoryTheory.Limits.Types.isCoprodOfMono

/--
The category of types has `Π j, f j` as the product of a type family `f : J → TypeMax.{v, u}`.
-/
def productLimitCone {J : Type v} (F : J → TypeMax.{v, u}) :
    Limits.LimitCone (Discrete.functor F) where
  cone :=
    { pt := ∀ j, F j
      π := Discrete.natTrans (fun ⟨j⟩ f => f j) }
  isLimit :=
    { lift := fun s x j => s.π.app ⟨j⟩ x
      uniq := fun s m w => funext fun x => funext fun j => (congr_fun (w ⟨j⟩) x : _) }
#align category_theory.limits.types.product_limit_cone CategoryTheory.Limits.Types.productLimitCone

/-- The categorical product in `TypeMax.{v, u}` is the type theoretic product `Π j, F j`. -/
noncomputable def productIso {J : Type v} (F : J → TypeMax.{v, u}) : ∏ F ≅ ∀ j, F j :=
  limit.isoLimitCone (productLimitCone.{v, u} F)
#align category_theory.limits.types.product_iso CategoryTheory.Limits.Types.productIso

-- Porting note: was `@[elementwise (attr := simp)]`, but it produces a trivial lemma
-- It should produce the lemma below.
@[simp]
theorem productIso_hom_comp_eval {J : Type v} (F : J → TypeMax.{v, u}) (j : J) :
    ((productIso.{v, u} F).hom ≫ fun f => f j) = Pi.π F j :=
  rfl
#align category_theory.limits.types.product_iso_hom_comp_eval CategoryTheory.Limits.Types.productIso_hom_comp_eval

@[simp]
theorem productIso_hom_comp_eval_apply {J : Type v} (F : J → TypeMax.{v, u}) (j : J) (x) :
    ((productIso.{v, u} F).hom x) j = Pi.π F j x :=
  rfl
#align category_theory.limits.types.product_iso_hom_comp_eval_apply CategoryTheory.Limits.Types.productIso_hom_comp_eval_apply

@[elementwise (attr := simp)]
theorem productIso_inv_comp_π {J : Type v} (F : J → TypeMax.{v, u}) (j : J) :
    (productIso.{v, u} F).inv ≫ Pi.π F j = fun f => f j :=
  limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩
#align category_theory.limits.types.product_iso_inv_comp_π CategoryTheory.Limits.Types.productIso_inv_comp_π

namespace UnivLE

/--
A variant of `productLimitCone` using a `UnivLE` hypothesis rather than a function to `TypeMax`.
-/
noncomputable def productLimitCone {J : Type v} (F : J → Type u) [UnivLE.{v, u}] :
    Limits.LimitCone (Discrete.functor F) where
  cone :=
    { pt := Shrink (∀ j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ f => (equivShrink _).symm f j) }
  isLimit :=
    { lift := fun s x => (equivShrink _) (fun j => s.π.app ⟨j⟩ x)
      uniq := fun s m w => funext fun x => Shrink.ext <| funext fun j => by
        simpa using (congr_fun (w ⟨j⟩) x : _) }

/-- The categorical product in `Type u` indexed in `Type v`
is the type theoretic product `Π j, F j`, after shrinking back to `Type u`. -/
noncomputable def productIso {J : Type v} (F : J → Type u) [UnivLE.{v, u}] :
    (∏ F : Type u) ≅ Shrink.{u} (∀ j, F j) :=
  limit.isoLimitCone (productLimitCone.{v, u} F)

@[simp]
theorem productIso_hom_comp_eval {J : Type v} (F : J → Type u) [UnivLE.{v, u}] (j : J) :
    ((productIso.{v, u} F).hom ≫ fun f => (equivShrink _).symm f j) = Pi.π F j :=
  limit.isoLimitCone_hom_π (productLimitCone.{v, u} F) ⟨j⟩

-- Porting note:
-- `elementwise` seems to be broken. Applied to the previous lemma, it should produce:
@[simp]
theorem productIso_hom_comp_eval_apply {J : Type v} (F : J → Type u) [UnivLE.{v, u}] (j : J) (x) :
   (equivShrink _).symm ((productIso F).hom x) j = Pi.π F j x :=
  congr_fun (productIso_hom_comp_eval F j) x

@[elementwise (attr := simp)]
theorem productIso_inv_comp_π {J : Type v} (F : J → Type u) [UnivLE.{v, u}] (j : J) :
    (productIso.{v, u} F).inv ≫ Pi.π F j = fun f => ((equivShrink _).symm f) j :=
  limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩

end UnivLE

/-- The category of types has `Σ j, f j` as the coproduct of a type family `f : J → Type`.
-/
def coproductColimitCocone {J : Type u} (F : J → Type u) :
    Limits.ColimitCocone (Discrete.functor F) where
  cocone :=
    { pt := Σj, F j
      ι := Discrete.natTrans (fun ⟨j⟩ x => ⟨j, x⟩)}
  isColimit :=
    { desc := fun s x => s.ι.app ⟨x.1⟩ x.2
      uniq := fun s m w => by
        funext ⟨j, x⟩
        exact congr_fun (w ⟨j⟩) x }
#align category_theory.limits.types.coproduct_colimit_cocone CategoryTheory.Limits.Types.coproductColimitCocone

/-- The categorical coproduct in `Type u` is the type theoretic coproduct `Σ j, F j`. -/
noncomputable def coproductIso {J : Type u} (F : J → Type u) : ∐ F ≅ Σj, F j :=
  colimit.isoColimitCocone (coproductColimitCocone F)
#align category_theory.limits.types.coproduct_iso CategoryTheory.Limits.Types.coproductIso

@[elementwise (attr := simp)]
theorem coproductIso_ι_comp_hom {J : Type u} (F : J → Type u) (j : J) :
    Sigma.ι F j ≫ (coproductIso F).hom = fun x : F j => (⟨j, x⟩ : Σj, F j) :=
  colimit.isoColimitCocone_ι_hom (coproductColimitCocone F) ⟨j⟩
#align category_theory.limits.types.coproduct_iso_ι_comp_hom CategoryTheory.Limits.Types.coproductIso_ι_comp_hom

theorem coproductIso_ι_comp_hom_apply' {J : Type u} (F : J → Type u) (j : J) (x : F j) :
    (coproductIso F).hom (Sigma.ι F j x) = ⟨j, x⟩ :=
  coproductIso_ι_comp_hom_apply _ _ _

-- porting note: was @[elementwise (attr := simp)], but it produces a trivial lemma
-- removed simp attribute because it seems it never applies
theorem coproductIso_mk_comp_inv {J : Type u} (F : J → Type u) (j : J) :
    (↾fun x : F j => (⟨j, x⟩ : Σj, F j)) ≫ (coproductIso F).inv = Sigma.ι F j :=
  rfl
#align category_theory.limits.types.coproduct_iso_mk_comp_inv CategoryTheory.Limits.Types.coproductIso_mk_comp_inv

section Small

noncomputable def coproductEquiv {J : Type v} [Small.{u} J] (F : J → Type u) [HasCoproduct F] :
  ∐ F ≃ Σj, F j := calc
    ∐ F ≃ ∐ (F ∘ (equivShrink.{u} J).symm) := (Sigma.reindex _ _).symm.toEquiv
    _ ≃ Σj, (F ∘ (equivShrink.{u} J).symm) j := (coproductIso _).toEquiv
    _ ≃ Σj, F j := Equiv.sigmaCongrLeft _

attribute [local instance] ConcreteCategory.funLike
theorem forget_hom_Type (α β : Type u) (f : α ⟶ β) : FunLike.coe f = f := rfl

@[simp]
theorem coproductEquiv_ι {J : Type v} [Small.{u} J] (F : J → Type u) [HasCoproduct F] (j : J)
    (x : F j) : coproductEquiv F (Sigma.ι F j x) = ⟨j, x⟩ := by
  obtain ⟨j, rfl⟩ := (equivShrink.{u} J).symm.surjective j
  dsimp [coproductEquiv]
  rw [elementwise_of% Sigma.ι_reindex_inv (equivShrink.{u} J).symm F]
  erw [forget_hom_Type _ _ (Sigma.ι (F ∘ (equivShrink.{u} J).symm) j)]
  rw [coproductIso_ι_comp_hom_apply']

@[simp]
theorem mk_coproductEquiv_symm {J : Type v} [Small.{u} J] (F : J → Type u) [HasCoproduct F] (j : J)
    (x : F j) : (coproductEquiv F).symm ⟨j, x⟩ = Sigma.ι F j x := by
  rw [← coproductEquiv_ι, Equiv.symm_apply_apply]

noncomputable def Sigma.comp {J : Type v} [Small.{u} J] {F : J → Type u} [HasCoproduct F]
    (x : ∐ F) : J :=
  (coproductEquiv F x).1

noncomputable def Sigma.rep {J : Type v} [Small.{u} J] {F : J → Type u} [HasCoproduct F]
    (x : ∐ F) : F (Sigma.comp x) :=
  (coproductEquiv F x).2

lemma Sigma.ι_comp_rep {J : Type v} [Small.{u} J] {F : J → Type u} [HasCoproduct F]
    (x : ∐ F) : Sigma.ι F (Sigma.comp x) (Sigma.rep x) = x := by
  apply (coproductEquiv F).injective
  simp [comp, rep]

theorem coproductEquiv_map' {J : Type v} {K : Type v'} [Small.{u} J] [Small.{u} K]
    (F : J → Type u) (G : K → Type u) [HasCoproduct F] [HasCoproduct G] {p : J → K}
    (q : ∀ (j : J), F j ⟶ G (p j)) (x : ∐ F) :
    coproductEquiv G (Sigma.map' p q x) = _root_.Sigma.map p q (coproductEquiv F x) := by
  rw [←Sigma.ι_comp_rep x, elementwise_of% Sigma.ι_comp_map' p q]
  aesop_cat

lemma Sigma.ι_eq_iff {J : Type v} [Small.{u} J] {F : J → Type u} [HasCoproduct F]
    (j j' : J) (x : F j) (x' : F j') :
    Sigma.ι F j x = Sigma.ι F j' x' ↔ ∃ h : j = j', (eqToHom (h ▸ rfl) : F j ⟶ F j') x = x' :=
  ⟨fun h => by apply_fun coproductEquiv F at h; aesop_cat, by aesop_cat⟩

@[simp]
lemma Sigma.comp_ι {J : Type v} [Small.{u} J] {F : J → Type u} [HasCoproduct F] (j : J) (x : F j) :
    Sigma.comp (Sigma.ι F j x) = j := by
  simp [comp]

lemma Sigma.rep_ι {J : Type v} [Small.{u} J] {F : J → Type u} [HasCoproduct F] (j : J)
    (x : F j) : Sigma.rep (Sigma.ι F j x) = (eqToHom (by simp) : F j ⟶ F (Sigma.comp (Sigma.ι F j x))) x := by
  dsimp only [rep]
  have := coproductEquiv_ι F j x
  rw [Sigma.ext_iff] at this
  dsimp at this
  symm
  rw [eqToHom_eq_iff_heq]
  symm
  exact this.2

lemma Sigma.comp_map' {J : Type v} {K : Type v'} [Small.{u} J] [Small.{u} K]
    (F : J → Type u) (G : K → Type u) [HasCoproduct F] [HasCoproduct G] {p : J → K}
    (q : ∀ (j : J), F j ⟶ G (p j)) (x : ∐ F) : Sigma.comp (Sigma.map' p q x) = p (Sigma.comp x) := by
  simp only [comp, coproductEquiv_map']
  aesop_cat

lemma Sigma.rep_map' {J : Type v} {K : Type v'} [Small.{u} J] [Small.{u} K]
    (F : J → Type u) (G : K → Type u) [HasCoproduct F] [HasCoproduct G] {p : J → K}
    (q : ∀ (j : J), F j ⟶ G (p j)) (x : ∐ F) :
    Sigma.rep (Sigma.map' p q x) = (eqToHom (by rw [Sigma.comp_map']) : G (p (Sigma.comp x)) ⟶ G (Sigma.comp (Sigma.map' p q x))) (q (Sigma.comp x) (Sigma.rep x)) := by
  simp only [rep]
  symm
  rw [eqToHom_eq_iff_heq]
  have := coproductEquiv_map' _ _ q x
  rw [Sigma.ext_iff] at this
  symm
  exact this.2

-- theorem Sigma.exists_rep_of_nonempty {α : Type v} (f : α → Type u) [HasCoproduct f]
--     [∀ i, Nonempty (f i)] (x : ∐ f) : ∃ (i : α) (y : f i), Sigma.ι f i y = x := by
--   have : Small.{u} α := by
--     let inc : α → ∐ f := fun i => Sigma.ι f i (Classical.ofNonempty)
--     suffices Function.Injective inc from small_of_injective this
--     intros i j hij

--     --let proj : ∐ f

--   sorry

-- theorem Sigma.exists_rep {α : Type u} (f : α → Type u) (x : ∐ f) :
--     ∃ (i : α) (y : f i), Sigma.ι f i y = x := by
--   obtain ⟨i, y, h⟩ := Concrete.sigma.exists_rep f x
--   exact ⟨i, y, h⟩

-- theorem Sigma.exists_rep_of_small {α : Type v} [Small.{u} α] (f : α → Type u) [HasCoproduct f]
--     (x : ∐ f) : ∃ (i : α) (y : f i), Sigma.ι f i y = x := by
--   let f' : Shrink.{u} α → Type u := f ∘ (equivShrink _).symm
--   let w : ∀ j, f ((equivShrink _).symm j) ≅ f' j := fun j => Iso.refl _
--   let e : ∐ f' ≅ ∐ f := Sigma.whiskerEquiv _ w
--   obtain ⟨i, y, h⟩ := Sigma.exists_rep f' (e.toEquiv.symm x)
--   refine' ⟨(equivShrink α).symm i, y, _⟩
--   obtain rfl := e.toEquiv.eq_symm_apply.1 h
--   dsimp only [Function.comp_apply, Iso.toEquiv_fun, Sigma.whiskerEquiv_hom, Iso.refl_inv]
--   erw [← types_comp_apply (Sigma.ι _ _) (Sigma.map' _ _), colimit.ι_desc]
--   simp only [Cofan.mk_pt, Cofan.mk_ι_app, types_comp_apply, types_id_apply]

-- noncomputable def Sigma.comp {α : Type v} [Small.{u} α] {f : α → Type u} [HasCoproduct f]
--     (x : ∐ f) : α := (Sigma.exists_rep_of_small f x).choose

-- noncomputable def Sigma.rep {α : Type v} [Small.{u} α] {f : α → Type u} [HasCoproduct f]
--     (x : ∐ f) : f (comp x) := (Sigma.exists_rep_of_small f x).choose_spec.choose

-- lemma Sigma.ι_comp_rep {α : Type v} [Small.{u} α] {f : α → Type u} [HasCoproduct f]
--     (x : ∐ f) : Sigma.ι f (Sigma.comp x) (Sigma.rep x) = x :=
--   (Sigma.exists_rep_of_small f x).choose_spec.choose_spec

-- lemma Sigma.ι_eq {α : Type v} {f : α → Type u} [HasCoproduct f] {i i' : α} {y : f i}
--     {y' : f i'} (hi : i = i') (hy : (eqToHom (hi ▸ rfl) : f i ⟶ f i') y = y') :
--     Sigma.ι f i y = Sigma.ι f i' y' := by
--   aesop_cat

end Small
section Fork

variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

/--
Show the given fork in `Type u` is an equalizer given that any element in the "difference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
noncomputable def typeEqualizerOfUnique (t : ∀ y : Y, g y = h y → ∃! x : X, f x = y) :
    IsLimit (Fork.ofι _ w) :=
  Fork.IsLimit.mk' _ fun s => by
    refine' ⟨fun i => _, _, _⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_fun s.condition i
    · funext i
      exact (Classical.choose_spec (t (s.ι i) (congr_fun s.condition i))).1
    · intro m hm
      funext i
      exact (Classical.choose_spec (t (s.ι i) (congr_fun s.condition i))).2 _ (congr_fun hm i)
#align category_theory.limits.types.type_equalizer_of_unique CategoryTheory.Limits.Types.typeEqualizerOfUnique

/-- The converse of `type_equalizer_of_unique`. -/
theorem unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) :
    ∃! x : X, f x = y := by
  let y' : PUnit ⟶ Y := fun _ => y
  have hy' : y' ≫ g = y' ≫ h := funext fun _ => hy
  refine' ⟨(Fork.IsLimit.lift' t _ hy').1 ⟨⟩, congr_fun (Fork.IsLimit.lift' t y' _).2 ⟨⟩, _⟩
  intro x' hx'
  suffices (fun _ : PUnit => x') = (Fork.IsLimit.lift' t y' hy').1 by
    rw [← this]
  apply Fork.IsLimit.hom_ext t
  funext ⟨⟩
  apply hx'.trans (congr_fun (Fork.IsLimit.lift' t _ hy').2 ⟨⟩).symm
#align category_theory.limits.types.unique_of_type_equalizer CategoryTheory.Limits.Types.unique_of_type_equalizer

theorem type_equalizer_iff_unique :
    Nonempty (IsLimit (Fork.ofι _ w)) ↔ ∀ y : Y, g y = h y → ∃! x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩
#align category_theory.limits.types.type_equalizer_iff_unique CategoryTheory.Limits.Types.type_equalizer_iff_unique

/-- Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)`. -/
def equalizerLimit : Limits.LimitCone (parallelPair g h) where
  cone := Fork.ofι (Subtype.val : { x : Y // g x = h x } → Y) (funext Subtype.prop)
  isLimit :=
    Fork.IsLimit.mk' _ fun s =>
      ⟨fun i => ⟨s.ι i, by apply congr_fun s.condition i⟩, rfl, fun hm =>
        funext fun x => Subtype.ext (congr_fun hm x)⟩
#align category_theory.limits.types.equalizer_limit CategoryTheory.Limits.Types.equalizerLimit

variable (g h)

/-- The categorical equalizer in `Type u` is `{x : Y // g x = h x}`. -/
noncomputable def equalizerIso : equalizer g h ≅ { x : Y // g x = h x } :=
  limit.isoLimitCone equalizerLimit
#align category_theory.limits.types.equalizer_iso CategoryTheory.Limits.Types.equalizerIso

-- porting note: was @[elementwise], but it produces a trivial lemma
@[simp]
theorem equalizerIso_hom_comp_subtype : (equalizerIso g h).hom ≫ Subtype.val = equalizer.ι g h := by
  rfl
#align category_theory.limits.types.equalizer_iso_hom_comp_subtype CategoryTheory.Limits.Types.equalizerIso_hom_comp_subtype

@[elementwise (attr := simp)]
theorem equalizerIso_inv_comp_ι : (equalizerIso g h).inv ≫ equalizer.ι g h = Subtype.val :=
  limit.isoLimitCone_inv_π equalizerLimit WalkingParallelPair.zero
#align category_theory.limits.types.equalizer_iso_inv_comp_ι CategoryTheory.Limits.Types.equalizerIso_inv_comp_ι

end Fork

section Cofork

variable {X Y Z : Type u} (f g : X ⟶ Y)

/-- (Implementation) The relation to be quotiented to obtain the coequalizer. -/
inductive CoequalizerRel : Y → Y → Prop
  | Rel (x : X) : CoequalizerRel (f x) (g x)
#align category_theory.limits.types.coequalizer_rel CategoryTheory.Limits.Types.CoequalizerRel

/-- Show that the quotient by the relation generated by `f(x) ~ g(x)`
is a coequalizer for the pair `(f, g)`.
-/
def coequalizerColimit : Limits.ColimitCocone (parallelPair f g) where
  cocone :=
    Cofork.ofπ (Quot.mk (CoequalizerRel f g)) (funext fun x => Quot.sound (CoequalizerRel.Rel x))
  isColimit :=
    Cofork.IsColimit.mk _
      (fun s => Quot.lift s.π
        (fun a b (h : CoequalizerRel f g a b) => by
          cases h
          apply congr_fun s.condition))
      (fun s => rfl)
      (fun s m hm => funext (fun x => Quot.inductionOn x (congr_fun hm)))
#align category_theory.limits.types.coequalizer_colimit CategoryTheory.Limits.Types.coequalizerColimit

/-- If `π : Y ⟶ Z` is an equalizer for `(f, g)`, and `U ⊆ Y` such that `f ⁻¹' U = g ⁻¹' U`,
then `π ⁻¹' (π '' U) = U`.
-/
theorem coequalizer_preimage_image_eq_of_preimage_eq (π : Y ⟶ Z) (e : f ≫ π = g ≫ π)
    (h : IsColimit (Cofork.ofπ π e)) (U : Set Y) (H : f ⁻¹' U = g ⁻¹' U) : π ⁻¹' (π '' U) = U := by
  have lem : ∀ x y, CoequalizerRel f g x y → (x ∈ U ↔ y ∈ U) := by
    rintro _ _ ⟨x⟩
    change x ∈ f ⁻¹' U ↔ x ∈ g ⁻¹' U
    rw [H]
  -- porting note: tidy was able to fill the structure automatically
  have eqv : _root_.Equivalence fun x y => x ∈ U ↔ y ∈ U :=
    { refl := by tauto
      symm := by tauto
      trans := by tauto }
  ext
  constructor
  · rw [←
      show _ = π from
        h.comp_coconePointUniqueUpToIso_inv (coequalizerColimit f g).2
          WalkingParallelPair.one]
    rintro ⟨y, hy, e'⟩
    dsimp at e'
    replace e' :=
      (mono_iff_injective
            (h.coconePointUniqueUpToIso (coequalizerColimit f g).isColimit).inv).mp
        inferInstance e'
    exact (eqv.eqvGen_iff.mp (EqvGen.mono lem (Quot.exact _ e'))).mp hy
  · exact fun hx => ⟨_, hx, rfl⟩
#align category_theory.limits.types.coequalizer_preimage_image_eq_of_preimage_eq CategoryTheory.Limits.Types.coequalizer_preimage_image_eq_of_preimage_eq

/-- The categorical coequalizer in `Type u` is the quotient by `f g ~ g x`. -/
noncomputable def coequalizerIso : coequalizer f g ≅ _root_.Quot (CoequalizerRel f g) :=
  colimit.isoColimitCocone (coequalizerColimit f g)
#align category_theory.limits.types.coequalizer_iso CategoryTheory.Limits.Types.coequalizerIso

@[elementwise (attr := simp)]
theorem coequalizerIso_π_comp_hom :
    coequalizer.π f g ≫ (coequalizerIso f g).hom = Quot.mk (CoequalizerRel f g) :=
  colimit.isoColimitCocone_ι_hom (coequalizerColimit f g) WalkingParallelPair.one
#align category_theory.limits.types.coequalizer_iso_π_comp_hom CategoryTheory.Limits.Types.coequalizerIso_π_comp_hom

-- porting note: was @[elementwise], but it produces a trivial lemma
@[simp]
theorem coequalizerIso_quot_comp_inv :
    ↾Quot.mk (CoequalizerRel f g) ≫ (coequalizerIso f g).inv = coequalizer.π f g :=
  rfl
#align category_theory.limits.types.coequalizer_iso_quot_comp_inv CategoryTheory.Limits.Types.coequalizerIso_quot_comp_inv

end Cofork

section Pullback

-- #synth HasPullbacks.{u} (Type u)
instance : HasPullbacks.{u} (Type u) :=
  -- FIXME does not work via `inferInstance` despite `#synth HasPullbacks.{u} (Type u)` succeeding.
  -- https://github.com/leanprover-community/mathlib4/issues/5752
  -- inferInstance
  hasPullbacks_of_hasWidePullbacks.{u} (Type u)

open CategoryTheory.Limits.WalkingPair

open CategoryTheory.Limits.WalkingCospan

open CategoryTheory.Limits.WalkingCospan.Hom

variable {W X Y Z : Type u}

variable (f : X ⟶ Z) (g : Y ⟶ Z)

-- porting note: removed @[nolint has_nonempty_instance]
/-- The usual explicit pullback in the category of types, as a subtype of the product.
The full `LimitCone` data is bundled as `pullbackLimitCone f g`.
-/
abbrev PullbackObj : Type u :=
  { p : X × Y // f p.1 = g p.2 }
#align category_theory.limits.types.pullback_obj CategoryTheory.Limits.Types.PullbackObj

-- `PullbackObj f g` comes with a coercion to the product type `X × Y`.
example (p : PullbackObj f g) : X × Y :=
  p

/-- The explicit pullback cone on `PullbackObj f g`.
This is bundled with the `IsLimit` data as `pullbackLimitCone f g`.
-/
abbrev pullbackCone : Limits.PullbackCone f g :=
  PullbackCone.mk (fun p : PullbackObj f g => p.1.1) (fun p => p.1.2) (funext fun p => p.2)
#align category_theory.limits.types.pullback_cone CategoryTheory.Limits.Types.pullbackCone

/-- The explicit pullback in the category of types, bundled up as a `LimitCone`
for given `f` and `g`.
-/
@[simps]
def pullbackLimitCone (f : X ⟶ Z) (g : Y ⟶ Z) : Limits.LimitCone (cospan f g) where
  cone := pullbackCone f g
  isLimit :=
    PullbackCone.isLimitAux _ (fun s x => ⟨⟨s.fst x, s.snd x⟩, congr_fun s.condition x⟩)
      (by aesop) (by aesop) fun s m w =>
      funext fun x =>
        Subtype.ext <|
          Prod.ext (congr_fun (w WalkingCospan.left) x) (congr_fun (w WalkingCospan.right) x)
#align category_theory.limits.types.pullback_limit_cone CategoryTheory.Limits.Types.pullbackLimitCone

/-- The pullback cone given by the instance `HasPullbacks (Type u)` is isomorphic to the
explicit pullback cone given by `pullbackLimitCone`.
-/
noncomputable def pullbackConeIsoPullback : limit.cone (cospan f g) ≅ pullbackCone f g :=
  (limit.isLimit _).uniqueUpToIso (pullbackLimitCone f g).isLimit
#align category_theory.limits.types.pullback_cone_iso_pullback CategoryTheory.Limits.Types.pullbackConeIsoPullback

/-- The pullback given by the instance `HasPullbacks (Type u)` is isomorphic to the
explicit pullback object given by `PullbackObj`.
-/
noncomputable def pullbackIsoPullback : pullback f g ≅ PullbackObj f g :=
  (Cones.forget _).mapIso <| pullbackConeIsoPullback f g
#align category_theory.limits.types.pullback_iso_pullback CategoryTheory.Limits.Types.pullbackIsoPullback

@[simp]
theorem pullbackIsoPullback_hom_fst (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).fst = (pullback.fst : _ ⟶ X) p :=
  congr_fun ((pullbackConeIsoPullback f g).hom.w left) p
#align category_theory.limits.types.pullback_iso_pullback_hom_fst CategoryTheory.Limits.Types.pullbackIsoPullback_hom_fst

@[simp]
theorem pullbackIsoPullback_hom_snd (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).snd = (pullback.snd : _ ⟶ Y) p :=
  congr_fun ((pullbackConeIsoPullback f g).hom.w right) p
#align category_theory.limits.types.pullback_iso_pullback_hom_snd CategoryTheory.Limits.Types.pullbackIsoPullback_hom_snd

@[simp]
theorem pullbackIsoPullback_inv_fst :
    (pullbackIsoPullback f g).inv ≫ pullback.fst = fun p => (p.1 : X × Y).fst :=
  (pullbackConeIsoPullback f g).inv.w left
#align category_theory.limits.types.pullback_iso_pullback_inv_fst CategoryTheory.Limits.Types.pullbackIsoPullback_inv_fst

@[simp]
theorem pullbackIsoPullback_inv_snd :
    (pullbackIsoPullback f g).inv ≫ pullback.snd = fun p => (p.1 : X × Y).snd :=
  (pullbackConeIsoPullback f g).inv.w right
#align category_theory.limits.types.pullback_iso_pullback_inv_snd CategoryTheory.Limits.Types.pullbackIsoPullback_inv_snd

end Pullback

section Pushout

-- #synth HasPushouts.{u} (Type u)
instance : HasPushouts.{u} (Type u) :=
  -- FIXME does not work via `inferInstance` despite `#synth HasPushouts.{u} (Type u)` succeeding.
  -- https://github.com/leanprover-community/mathlib4/issues/5752
  -- inferInstance
  hasPushouts_of_hasWidePushouts.{u} (Type u)

end Pushout

end CategoryTheory.Limits.Types
