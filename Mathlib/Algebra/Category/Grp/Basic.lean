/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.category.Group.basic
! leanprover-community/mathlib commit 524793de15bc4c52ee32d254e7d7867c7176b3af
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Endomorphism

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

We introduce the bundled categories:
* `Grp`
* `AddGrp`
* `CommGrp`
* `AddCommGrp`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/


universe u v

open CategoryTheory

/-- The category of groups and group morphisms. -/
@[to_additive]
def Grp : Type (u + 1) :=
  Bundled Group
set_option linter.uppercaseLean3 false in
#align Group Grp
set_option linter.uppercaseLean3 false in
#align AddGroup AddGrp

/-- The category of additive groups and group morphisms -/
add_decl_doc AddGrp

namespace Grp

@[to_additive]
instance : BundledHom.ParentProjection
  (fun {α : Type _} (h : Group α) => h.toDivInvMonoid.toMonoid) := ⟨⟩

instance largeCategory : LargeCategory Grp := by
  dsimp only [Grp]
  infer_instance

instance concreteCategory : ConcreteCategory Grp := by
  dsimp only [Grp]
  infer_instance

attribute [to_additive] Grp.largeCategory Grp.concreteCategory

@[to_additive]
instance : CoeSort Grp (Type _) := by
  dsimp only [Grp]
  infer_instance

/-- Construct a bundled `Group` from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [Group X] : Grp :=
  Bundled.of X
set_option linter.uppercaseLean3 false in
#align Group.of Grp.of
set_option linter.uppercaseLean3 false in
#align AddGroup.of AddGrp.of

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
add_decl_doc AddGrp.of

/-- Typecheck a `MonoidHom` as a morphism in `Grp`. -/
@[to_additive]
def ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  f
set_option linter.uppercaseLean3 false in
#align Group.of_hom Grp.ofHom
set_option linter.uppercaseLean3 false in
#align AddGroup.of_hom AddGrp.ofHom

/-- Typecheck a `AddMonoidHom` as a morphism in `AddGroup`. -/
add_decl_doc AddGrp.ofHom

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : Grp} : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ConcreteCategory.hasCoeToFun

-- porting note: this was added to ease automation
@[to_additive (attr := simp)]
lemma id_apply {X : Grp} (x : X) :
  (𝟙 X) x = x := rfl

-- porting note: this was added to ease automation
@[to_additive (attr := simp)]
lemma comp_apply {X Y Z : Grp} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := rfl

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type _} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.of_hom_apply Grp.ofHom_apply
set_option linter.uppercaseLean3 false in
#align AddGroup.of_hom_apply AddGrp.ofHom_apply

@[to_additive]
instance (G : Grp) : Group G :=
  G.str

-- porting note: added to make `one_apply` work
@[to_additive]
instance (G : Grp) : Group ((forget Grp).obj G) :=
  G.str

-- porting note: simp attribute was removed to please the linter
@[to_additive]
theorem coe_of (R : Type u) [Group R] : ↑(Grp.of R) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.coe_of Grp.coe_of
set_option linter.uppercaseLean3 false in
#align AddGroup.coe_of AddGrp.coe_of

@[to_additive]
instance : Inhabited Grp :=
  ⟨Grp.of PUnit⟩

@[to_additive]
instance ofUnique (G : Type _) [Group G] [i : Unique G] : Unique (Grp.of G) :=
  i
set_option linter.uppercaseLean3 false in
#align Group.of_unique Grp.ofUnique
set_option linter.uppercaseLean3 false in
#align AddGroup.of_unique AddGrp.ofUnique

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance (G H : Grp) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : Grp) (g : G) : ((forget Grp).map (1 : G ⟶ H)) g = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align Group.one_apply Grp.one_apply
set_option linter.uppercaseLean3 false in
#align AddGroup.zero_apply AddGrp.zero_apply

@[to_additive (attr := ext)]
theorem ext (G H : Grp) (f₁ f₂ : G ⟶ H) (w : ∀ (x : ↑G), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.hom_ext _ _ w
set_option linter.uppercaseLean3 false in
#align Group.ext Grp.ext
set_option linter.uppercaseLean3 false in
#align AddGroup.ext AddGrp.ext

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ Grp MonCat :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align Group.has_forget_to_Mon Grp.hasForgetToMonCat
set_option linter.uppercaseLean3 false in
#align AddGroup.has_forget_to_AddMon AddGrp.hasForgetToAddMonCat

@[to_additive]
instance : Coe Grp.{u} MonCat.{u} where coe := (forget₂ Grp MonCat).obj

-- porting note: this was added to ease the port
/-- the morphism in `Grp` associated to a `MonoidHom` -/
@[to_additive]
def Hom.mk {X Y : Grp} (f : X →* Y) : X ⟶ Y := f

/-- the morphism in `AddGrp` associated to a `AddMonoidHom` -/
add_decl_doc AddGrp.Hom.mk

@[to_additive (attr := simp)]
lemma Hom.mk_apply {X Y : Grp} (f : X →* Y) (x : X) :
  (Hom.mk f) x = f x := rfl

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma Hom.map_mul {X Y : Grp} (f : X ⟶ Y) (x y : X) : f (x * y) = f x * f y := by
  apply MonoidHom.map_mul (show MonoidHom X Y from f)

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma Hom.map_one {X Y : Grp} (f : X ⟶ Y) : f (1 : X) = 1 := by
  apply MonoidHom.map_one (show MonoidHom X Y from f)

end Grp

/-- The category of commutative groups and group morphisms. -/
@[to_additive]
def CommGrp : Type (u + 1) :=
  Bundled CommGroup
set_option linter.uppercaseLean3 false in
#align CommGroup CommGrp
set_option linter.uppercaseLean3 false in
#align AddCommGroup AddCommGrp

/-- The category of additive commutative groups and group morphisms. -/
add_decl_doc AddCommGrp

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev Ab :=
  AddCommGrp
set_option linter.uppercaseLean3 false in
#align Ab Ab

namespace CommGrp

@[to_additive]
instance : BundledHom.ParentProjection @CommGroup.toGroup :=
  ⟨⟩

instance largeCategory : LargeCategory CommGrp := by
  dsimp only [CommGrp]
  infer_instance

instance concreteCategory : ConcreteCategory CommGrp := by
  dsimp only [CommGrp]
  infer_instance

attribute [to_additive] CommGrp.largeCategory CommGrp.concreteCategory

@[to_additive]
instance : CoeSort CommGrp (Type _) := by
  dsimp only [CommGrp]
  infer_instance

/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
@[to_additive]
def of (G : Type u) [CommGroup G] : CommGrp :=
  Bundled.of G
set_option linter.uppercaseLean3 false in
#align CommGroup.of CommGrp.of
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of AddCommGrp.of

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
add_decl_doc AddCommGrp.of

/-- Typecheck a `MonoidHom` as a morphism in `CommGroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  f
set_option linter.uppercaseLean3 false in
#align CommGroup.of_hom CommGrp.ofHom
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_hom AddCommGrp.ofHom

/-- Typecheck a `AddMonoidHom` as a morphism in `AddCommGroup`. -/
add_decl_doc AddCommGrp.ofHom

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance {X Y : CommGrp} : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ConcreteCategory.hasCoeToFun

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma id_apply {X : CommGrp} (x : X) :
  (𝟙 X) x = x := rfl

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma comp_apply {X Y Z : CommGrp} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := by apply CategoryTheory.comp_apply

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type _} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.of_hom_apply CommGrp.ofHom_apply
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_hom_apply AddCommGrp.ofHom_apply

@[to_additive]
instance commGroupInstance (G : CommGrp) : CommGroup G :=
  G.str
set_option linter.uppercaseLean3 false in
#align CommGroup.comm_group_instance CommGrp.commGroupInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.add_comm_group_instance AddCommGrp.addCommGroupInstance

-- porting note: simp attribute was removed to please the linter
@[to_additive]
theorem coe_of (R : Type u) [CommGroup R] : (CommGrp.of R : Type u) = R :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.coe_of CommGrp.coe_of
set_option linter.uppercaseLean3 false in
#align AddCommGroup.coe_of AddCommGrp.coe_of

@[to_additive]
instance : Inhabited CommGrp :=
  ⟨CommGrp.of PUnit⟩

@[to_additive]
instance ofUnique (G : Type _) [CommGroup G] [i : Unique G] : Unique (CommGrp.of G) :=
  i
set_option linter.uppercaseLean3 false in
#align CommGroup.of_unique CommGrp.ofUnique
set_option linter.uppercaseLean3 false in
#align AddCommGroup.of_unique AddCommGrp.ofUnique

-- porting note: this instance was not necessary in mathlib
@[to_additive]
instance (G H : CommGrp) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : CommGrp) (g : G) : (1 : G ⟶ H) g = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommGroup.one_apply CommGrp.one_apply
set_option linter.uppercaseLean3 false in
#align AddCommGroup.zero_apply AddCommGrp.zero_apply

@[to_additive (attr := ext)]
theorem ext (G H : CommGrp) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.hom_ext _ _ w
set_option linter.uppercaseLean3 false in
#align CommGroup.ext CommGrp.ext
set_option linter.uppercaseLean3 false in
#align AddCommGroup.ext AddCommGrp.ext

@[to_additive]
instance hasForgetToGroup : HasForget₂ CommGrp Grp :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align CommGroup.has_forget_to_Group CommGrp.hasForgetToGroup
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_forget_to_AddGroup AddCommGrp.hasForgetToAddGroup

@[to_additive]
instance : Coe CommGrp.{u} Grp.{u} where coe := (forget₂ CommGrp Grp).obj

@[to_additive hasForgetToAddCommMonCat]
instance hasForgetToCommMonCat : HasForget₂ CommGrp CommMonCat :=
  InducedCategory.hasForget₂ fun G : CommGrp => CommMonCat.of G
set_option linter.uppercaseLean3 false in
#align CommGroup.has_forget_to_CommMon CommGrp.hasForgetToCommMonCat
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_forget_to_AddCommMon AddCommGrp.hasForgetToAddCommMonCat

@[to_additive]
instance : Coe CommGrp.{u} CommMonCat.{u} where coe := (forget₂ CommGrp CommMonCat).obj

-- porting note: this was added to ease the port
/-- the morphism in `CommGrp` associated to a `MonoidHom` -/
@[to_additive]
def Hom.mk {X Y : CommGrp} (f : X →* Y) : X ⟶ Y := f

/-- the morphism in `AddCommGrp` associated to a `AddMonoidHom` -/
add_decl_doc AddCommGrp.Hom.mk

@[to_additive (attr := simp)]
lemma Hom.mk_apply {X Y : CommGrp} (f : X →* Y) (x : X) :
  (Hom.mk f) x = f x := rfl

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma Hom.map_mul {X Y : CommGrp} (f : X ⟶ Y) (x y : X) : f (x * y) = f x * f y := by
  apply MonoidHom.map_mul (show MonoidHom X Y from f)

-- porting note: added to ease automation
@[to_additive (attr := simp)]
lemma Hom.map_one {X Y : CommGrp} (f : X ⟶ Y) : f (1 : X) = 1 := by
  apply MonoidHom.map_one (show MonoidHom X Y from f)

-- Porting note: is this still relevant?
-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `MonoidHom.map_map` usable by `simp` here,
-- we had to mark all the concrete category `CoeSort` instances reducible.
-- Now, it just works.
@[to_additive]
example {R S : CommGrp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

end CommGrp

namespace AddCommGrp

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ULiftInstances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
def asHom {G : AddCommGrp.{0}} (g : G) : AddCommGrp.of ℤ ⟶ G :=
  zmultiplesHom G g
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom AddCommGrp.asHom

@[simp]
theorem asHom_apply {G : AddCommGrp.{0}} (g : G) (i : ℤ) : (asHom g) i = i • g :=
  rfl
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom_apply AddCommGrp.asHom_apply

theorem asHom_injective {G : AddCommGrp.{0}} : Function.Injective (@asHom G) := fun h k w => by
  convert congr_arg (fun k : AddCommGrp.of ℤ ⟶ G => (k : ℤ → G) (1 : ℤ)) w <;> simp
set_option linter.uppercaseLean3 false in
#align AddCommGroup.as_hom_injective AddCommGrp.asHom_injective

@[ext]
theorem int_hom_ext {G : AddCommGrp.{0}} (f g : AddCommGrp.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  @AddMonoidHom.ext_int G _ f g w
set_option linter.uppercaseLean3 false in
#align AddCommGroup.int_hom_ext AddCommGrp.int_hom_ext

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGrp.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by
    apply int_hom_ext
    simpa using h
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1
set_option linter.uppercaseLean3 false in
#align AddCommGroup.injective_of_mono AddCommGrp.injective_of_mono

end AddCommGrp

/-- Build an isomorphism in the category `Grp` from a `MulEquiv` between `Group`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toGrpIso {X Y : Grp} (e : X ≃* Y) : X ≅ Y where
  hom := Grp.Hom.mk e.toMonoidHom
  inv := Grp.Hom.mk e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_Group_iso MulEquiv.toGrpIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddGroup_iso AddEquiv.toAddGrpIso

/-- Build an isomorphism in the category `AddGroup` from an `AddEquiv` between `AddGroup`s. -/
add_decl_doc AddEquiv.toAddGrpIso

/-- Build an isomorphism in the category `CommGrp` from a `MulEquiv`
between `CommGroup`s. -/
@[to_additive (attr := simps)]
def MulEquiv.toCommGrpIso {X Y : CommGrp} (e : X ≃* Y) : X ≅ Y where
  hom := CommGrp.Hom.mk e.toMonoidHom
  inv := CommGrp.Hom.mk e.symm.toMonoidHom
set_option linter.uppercaseLean3 false in
#align mul_equiv.to_CommGroup_iso MulEquiv.toCommGrpIso
set_option linter.uppercaseLean3 false in
#align add_equiv.to_AddCommGroup_iso AddEquiv.toAddCommGrpIso

/-- Build an isomorphism in the category `AddCommGrp` from a `AddEquiv`
between `AddCommGroup`s. -/
add_decl_doc AddEquiv.toAddCommGrpIso

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `Grp`. -/
@[to_additive (attr := simp)]
def groupIsoToMulEquiv {X Y : Grp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.Group_iso_to_mul_equiv CategoryTheory.Iso.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddGroup_iso_to_add_equiv CategoryTheory.Iso.addGroupIsoToAddEquiv

/-- Build an `addEquiv` from an isomorphism in the category `AddGroup` -/
add_decl_doc addGroupIsoToAddEquiv

/-- Build a `MulEquiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive (attr := simps!)]
def commGroupIsoToMulEquiv {X Y : CommGrp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
set_option linter.uppercaseLean3 false in
#align category_theory.iso.CommGroup_iso_to_mul_equiv CategoryTheory.Iso.commGroupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.iso.AddCommGroup_iso_to_add_equiv CategoryTheory.Iso.addCommGroupIsoToAddEquiv

/-- Build an `AddEquiv` from an isomorphism\nin the category `AddCommGroup`. -/
add_decl_doc addCommGroupIsoToAddEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `Group`s are the same as (isomorphic to) isomorphisms
in `Grp` -/
@[to_additive]
def mulEquivIsoGroupIso {X Y : Grp.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toGrpIso
  inv i := i.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_Group_iso mulEquivIsoGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddGroup_iso addEquivIsoAddGroupIso

/-- "additive equivalences between `add_group`s are the same
as (isomorphic to) isomorphisms in `AddGroup` -/
add_decl_doc addEquivIsoAddGroupIso

/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms
in `CommGroup` -/
@[to_additive]
def mulEquivIsoCommGroupIso {X Y : CommGrp.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toCommGrpIso
  inv i := i.commGroupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align mul_equiv_iso_CommGroup_iso mulEquivIsoCommGroupIso
set_option linter.uppercaseLean3 false in
#align add_equiv_iso_AddCommGroup_iso addEquivIsoAddCommGroupIso

/-- additive equivalences between `AddCommGroup`s are
the same as (isomorphic to) isomorphisms in `AddCommGroup` -/
add_decl_doc addEquivIsoAddCommGroupIso

namespace CategoryTheory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : Grp.of (Aut α) ≅ Grp.of (Equiv.Perm α) where
  hom := Grp.Hom.mk
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv := Grp.Hom.mk
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }
set_option linter.uppercaseLean3 false in
#align category_theory.Aut.iso_perm CategoryTheory.Aut.isoPerm

/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv
set_option linter.uppercaseLean3 false in
#align category_theory.Aut.mul_equiv_perm CategoryTheory.Aut.mulEquivPerm

end CategoryTheory.Aut

@[to_additive]
instance Grp.forget_reflects_isos : ReflectsIsomorphisms (forget Grp.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget Grp).map f)
    let e : X ≃* Y := MulEquiv.mk i.toEquiv (by apply Grp.Hom.map_mul)
    exact IsIso.of_iso e.toGrpIso
set_option linter.uppercaseLean3 false in
#align Group.forget_reflects_isos Grp.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddGroup.forget_reflects_isos AddGrp.forget_reflects_isos

@[to_additive]
instance CommGrp.forget_reflects_isos : ReflectsIsomorphisms (forget CommGrp.{u}) where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommGrp).map f)
    let e : X ≃* Y := MulEquiv.mk i.toEquiv (by apply CommGrp.Hom.map_mul)
    exact IsIso.of_iso e.toCommGrpIso
set_option linter.uppercaseLean3 false in
#align CommGroup.forget_reflects_isos CommGrp.forget_reflects_isos
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget_reflects_isos AddCommGrp.forget_reflects_isos
