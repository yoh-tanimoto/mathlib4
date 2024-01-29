/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.KanExtension
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.EssentiallySmall

#align_import category_theory.limits.presheaf from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Colimit of representables

This file constructs an adjunction `yonedaAdjunction` between `(Cᵒᵖ ⥤ Type u)` and `ℰ` given a
functor `A : C ⥤ ℰ`, where the right adjoint sends `(E : ℰ)` to `c ↦ (A.obj c ⟶ E)` (provided `ℰ`
has colimits).

This adjunction is used to show that every presheaf is a colimit of representables. This result is
also known as the density theorem, the co-Yoneda lemma and the Ninja Yoneda lemma.

Further, the left adjoint `colimitAdj.extendAlongYoneda : (Cᵒᵖ ⥤ Type u) ⥤ ℰ` satisfies
`yoneda ⋙ L ≅ A`, that is, an extension of `A : C ⥤ ℰ` to `(Cᵒᵖ ⥤ Type u) ⥤ ℰ` through
`yoneda : C ⥤ Cᵒᵖ ⥤ Type u`. It is the left Kan extension of `A` along the yoneda embedding,
sometimes known as the Yoneda extension, as proved in `extendAlongYonedaIsoKan`.

`uniqueExtensionAlongYoneda` shows `extendAlongYoneda` is unique amongst cocontinuous functors
with this property, establishing the presheaf category as the free cocompletion of a small category.

We also give a direct pedestrian proof that every presheaf is a colimit of representables. This
version of the proof is valid for any category `C`, even if it is not small.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/

set_option autoImplicit true


namespace CategoryTheory

open Category Limits

universe v₁ v₂ u₁ u₂

section SmallCategory

variable {C : Type u₁} [SmallCategory C]

variable {ℰ : Type u₂} [Category.{u₁} ℰ]

variable (A : C ⥤ ℰ)

namespace ColimitAdj

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps!]
def restrictedYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type u₁ :=
  yoneda ⋙ (whiskeringLeft _ _ (Type u₁)).obj (Functor.op A)
#align category_theory.colimit_adj.restricted_yoneda CategoryTheory.ColimitAdj.restrictedYoneda

/--
The functor `restrictedYoneda` is isomorphic to the identity functor when evaluated at the yoneda
embedding.
-/
def restrictedYonedaYoneda : restrictedYoneda (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ≅ 𝟭 _ :=
  NatIso.ofComponents fun P =>
    NatIso.ofComponents (fun X => yonedaSectionsSmall X.unop _) @ fun X Y f =>
      funext fun x => by
        dsimp
        have : x.app X (CategoryStruct.id (Opposite.unop X)) =
            (x.app X (𝟙 (Opposite.unop X))) := rfl
        rw [this]
        rw [← FunctorToTypes.naturality _ _ x f (𝟙 _)]
        simp only [id_comp, Functor.op_obj, Opposite.unop_op, yoneda_obj_map, comp_id]
#align category_theory.colimit_adj.restricted_yoneda_yoneda CategoryTheory.ColimitAdj.restrictedYonedaYoneda

/-- (Implementation). The equivalence of homsets which helps construct the left adjoint to
`colimitAdj.restrictedYoneda`.
It is shown in `restrictYonedaHomEquivNatural` that this is a natural bijection.
-/
def restrictYonedaHomEquiv (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ)
    {c : Cocone ((CategoryOfElements.π P).leftOp ⋙ A)} (t : IsColimit c) :
    (c.pt ⟶ E) ≃ (P ⟶ (restrictedYoneda A).obj E) :=
  ((uliftTrivial _).symm ≪≫ t.homIso' E).toEquiv.trans
    { toFun := fun k =>
        { app := fun c p => k.1 (Opposite.op ⟨_, p⟩)
          naturality := fun c c' f =>
            funext fun p =>
              (k.2
                  (Quiver.Hom.op ⟨f, rfl⟩ :
                    (Opposite.op ⟨c', P.map f p⟩ : P.Elementsᵒᵖ) ⟶ Opposite.op ⟨c, p⟩)).symm }
      invFun := fun τ =>
        { val := fun p => τ.app p.unop.1 p.unop.2
          property := @fun p p' f => by
            simp_rw [← f.unop.2]
            apply (congr_fun (τ.naturality f.unop.1) p'.unop.2).symm }
      left_inv := by
        rintro ⟨k₁, k₂⟩
        ext
        dsimp
        congr 1
      right_inv := by
        rintro ⟨_, _⟩
        rfl }
#align category_theory.colimit_adj.restrict_yoneda_hom_equiv CategoryTheory.ColimitAdj.restrictYonedaHomEquiv

/--
(Implementation). Show that the bijection in `restrictYonedaHomEquiv` is natural (on the right).
-/
theorem restrictYonedaHomEquiv_natural (P : Cᵒᵖ ⥤ Type u₁) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂) {c : Cocone _}
    (t : IsColimit c) (k : c.pt ⟶ E₁) :
    restrictYonedaHomEquiv A P E₂ t (k ≫ g) =
      restrictYonedaHomEquiv A P E₁ t k ≫ (restrictedYoneda A).map g := by
  ext x X
  apply (assoc _ _ _).symm
#align category_theory.colimit_adj.restrict_yoneda_hom_equiv_natural CategoryTheory.ColimitAdj.restrictYonedaHomEquiv_natural

variable [HasColimits ℰ]

/--
The left adjoint to the functor `restrictedYoneda` (shown in `yonedaAdjunction`). It is also an
extension of `A` along the yoneda embedding (shown in `isExtensionAlongYoneda`), in particular
it is the left Kan extension of `A` through the yoneda embedding.
-/
noncomputable def extendAlongYoneda : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
  Adjunction.leftAdjointOfEquiv (fun P E => restrictYonedaHomEquiv A P E (colimit.isColimit _))
    fun P E E' g => restrictYonedaHomEquiv_natural A P E E' g _
#align category_theory.colimit_adj.extend_along_yoneda CategoryTheory.ColimitAdj.extendAlongYoneda

@[simp]
theorem extendAlongYoneda_obj (P : Cᵒᵖ ⥤ Type u₁) :
    (extendAlongYoneda A).obj P = colimit ((CategoryOfElements.π P).leftOp ⋙ A) :=
  rfl
#align category_theory.colimit_adj.extend_along_yoneda_obj CategoryTheory.ColimitAdj.extendAlongYoneda_obj

-- porting note: adding this lemma because lean 4 ext no longer applies all ext lemmas when
-- stuck (and hence can see through definitional equalities). The previous lemma shows that
-- `(extendAlongYoneda A).obj P` is definitionally a colimit, and the ext lemma is just
-- a special case of `CategoryTheory.Limits.colimit.hom_ext`.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext] lemma extendAlongYoneda_obj.hom_ext {P : Cᵒᵖ ⥤ Type u₁}
    {f f' : (extendAlongYoneda A).obj P ⟶ X}
    (w : ∀ j, colimit.ι ((CategoryOfElements.π P).leftOp ⋙ A) j ≫ f =
      colimit.ι ((CategoryOfElements.π P).leftOp ⋙ A) j ≫ f') : f = f' :=
CategoryTheory.Limits.colimit.hom_ext w

theorem extendAlongYoneda_map {X Y : Cᵒᵖ ⥤ Type u₁} (f : X ⟶ Y) :
    (extendAlongYoneda A).map f =
      colimit.pre ((CategoryOfElements.π Y).leftOp ⋙ A) (CategoryOfElements.map f).op := by
  ext J
  erw [colimit.ι_pre ((CategoryOfElements.π Y).leftOp ⋙ A) (CategoryOfElements.map f).op]
  dsimp only [extendAlongYoneda, restrictYonedaHomEquiv, IsColimit.homIso', IsColimit.homIso,
    uliftTrivial]
  -- porting note: in mathlib3 the rest of the proof was `simp, refl`; this is squeezed
  -- and appropriately reordered, presumably because of a non-confluence issue.
  simp only [Adjunction.leftAdjointOfEquiv_map, Iso.symm_mk, Iso.toEquiv_comp, Equiv.coe_trans,
    Equiv.coe_fn_mk, Iso.toEquiv_fun, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk,
    Iso.toEquiv_symm_fun, id.def, colimit.isColimit_desc, colimit.ι_desc, FunctorToTypes.comp,
    Cocone.extend_ι, Cocone.extensions_app, Functor.map_id, Category.comp_id, colimit.cocone_ι]
  simp only [Functor.comp_obj, Functor.leftOp_obj, CategoryOfElements.π_obj, colimit.cocone_x,
    Functor.comp_map, Functor.leftOp_map, CategoryOfElements.π_map, Opposite.unop_op,
    Adjunction.leftAdjointOfEquiv_obj, Function.comp_apply, Functor.map_id, comp_id,
    colimit.cocone_ι, Functor.op_obj]
  rfl
#align category_theory.colimit_adj.extend_along_yoneda_map CategoryTheory.ColimitAdj.extendAlongYoneda_map

/-- Show `extendAlongYoneda` is left adjoint to `restrictedYoneda`.

The construction of [MM92], Chapter I, Section 5, Theorem 2.
-/
noncomputable def yonedaAdjunction : extendAlongYoneda A ⊣ restrictedYoneda A :=
  Adjunction.adjunctionOfEquivLeft _ _
#align category_theory.colimit_adj.yoneda_adjunction CategoryTheory.ColimitAdj.yonedaAdjunction

/--
The initial object in the category of elements for a representable functor. In `isInitial` it is
shown that this is initial.
-/
def Elements.initial (A : C) : (yoneda.obj A).Elements :=
  ⟨Opposite.op A, 𝟙 _⟩
#align category_theory.colimit_adj.elements.initial CategoryTheory.ColimitAdj.Elements.initial

/-- Show that `Elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def isInitial (A : C) : IsInitial (Elements.initial A) where
  desc s := ⟨s.pt.2.op, comp_id _⟩
  uniq s m _ := by
    simp_rw [← m.2]
    dsimp [Elements.initial]
    simp
  fac := by rintro s ⟨⟨⟩⟩
#align category_theory.colimit_adj.is_initial CategoryTheory.ColimitAdj.isInitial

/--
`extendAlongYoneda A` is an extension of `A` to the presheaf category along the yoneda embedding.
`uniqueExtensionAlongYoneda` shows it is unique among functors preserving colimits with this
property (up to isomorphism).

The first part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 1 of <https://ncatlab.org/nlab/show/Yoneda+extension#properties>.
-/
noncomputable def isExtensionAlongYoneda :
    (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ⋙ extendAlongYoneda A ≅ A :=
  NatIso.ofComponents
    (fun X =>
      (colimit.isColimit _).coconePointUniqueUpToIso
        (colimitOfDiagramTerminal (terminalOpOfInitial (isInitial _)) _))
    (by
      intro X Y f
      -- porting note: this is slightly different to the `change` in mathlib3 which
      -- didn't work
      change (colimit.desc _ _ ≫ _) = colimit.desc _ _ ≫ _
      ext
      rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc]
      change (colimit.ι _ _ ≫ 𝟙 _) ≫ colimit.desc _ _ = _
      rw [comp_id, colimit.ι_desc]
      dsimp
      rw [← A.map_comp]
      congr 1)
#align category_theory.colimit_adj.is_extension_along_yoneda CategoryTheory.ColimitAdj.isExtensionAlongYoneda

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
noncomputable instance : PreservesColimits (extendAlongYoneda A) :=
  (yonedaAdjunction A).leftAdjointPreservesColimits

/-- Show that the images of `X` after `extendAlongYoneda` and `Lan yoneda` are indeed isomorphic.
This follows from `CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalence`.
-/
@[simps]
noncomputable def extendAlongYonedaIsoKanApp (X) :
    (extendAlongYoneda A).obj X ≅ ((lan yoneda : (_ ⥤ ℰ) ⥤ _).obj A).obj X :=
  let eq := CategoryOfElements.costructuredArrowYonedaEquivalence X
  { hom := colimit.pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) eq.functor
    inv := colimit.pre ((CategoryOfElements.π X).leftOp ⋙ A) eq.inverse
    hom_inv_id := by
      erw [colimit.pre_pre ((CategoryOfElements.π X).leftOp ⋙ A) eq.inverse]
      trans colimit.pre ((CategoryOfElements.π X).leftOp ⋙ A) (𝟭 _)
      congr
      · exact congr_arg Functor.op (CategoryOfElements.from_toCostructuredArrow_eq X)
      · ext
        simp only [colimit.ι_pre]
        erw [Category.comp_id]
        congr
    inv_hom_id := by
      erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) eq.functor]
      trans colimit.pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) (𝟭 _)
      congr
      · exact CategoryOfElements.to_fromCostructuredArrow_eq X
      · ext
        simp only [colimit.ι_pre]
        erw [Category.comp_id]
        congr }
set_option linter.uppercaseLean3 false in
#align category_theory.colimit_adj.extend_along_yoneda_iso_Kan_app CategoryTheory.ColimitAdj.extendAlongYonedaIsoKanApp

/-- Verify that `extendAlongYoneda` is indeed the left Kan extension along the yoneda embedding.
-/
@[simps!]
noncomputable def extendAlongYonedaIsoKan :
    extendAlongYoneda A ≅ (lan yoneda : (_ ⥤ ℰ) ⥤ _).obj A :=
  NatIso.ofComponents (extendAlongYonedaIsoKanApp A) (by
    intro X Y f; simp
    rw [extendAlongYoneda_map]
    erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A Y) (CostructuredArrow.map f)]
    erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A Y)
        (CategoryOfElements.costructuredArrowYonedaEquivalence Y).functor]
    congr 1
    apply CategoryOfElements.costructuredArrow_yoneda_equivalence_naturality)
set_option linter.uppercaseLean3 false in
#align category_theory.colimit_adj.extend_along_yoneda_iso_Kan CategoryTheory.ColimitAdj.extendAlongYonedaIsoKan

/-- extending `F ⋙ yoneda` along the yoneda embedding is isomorphic to `Lan F.op`. -/
noncomputable def extendOfCompYonedaIsoLan {D : Type u₁} [SmallCategory D] (F : C ⥤ D) :
    extendAlongYoneda (F ⋙ yoneda) ≅ lan F.op :=
  Adjunction.natIsoOfRightAdjointNatIso (yonedaAdjunction (F ⋙ yoneda))
    (Lan.adjunction (Type u₁) F.op)
    (isoWhiskerRight curriedYonedaLemma' ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u₁)).obj F.op : _))
set_option linter.uppercaseLean3 false in
#align category_theory.colimit_adj.extend_of_comp_yoneda_iso_Lan CategoryTheory.ColimitAdj.extendOfCompYonedaIsoLan

-- porting note: attaching `[simps!]` directly to the declaration causes a timeout.
attribute [simps!] extendOfCompYonedaIsoLan

end ColimitAdj

open ColimitAdj

/-- `F ⋙ yoneda` is naturally isomorphic to `yoneda ⋙ Lan F.op`. -/
@[simps!]
noncomputable def compYonedaIsoYonedaCompLan {D : Type u₁} [SmallCategory D] (F : C ⥤ D) :
    F ⋙ yoneda ≅ yoneda ⋙ lan F.op :=
  (isExtensionAlongYoneda (F ⋙ yoneda)).symm ≪≫ isoWhiskerLeft yoneda (extendOfCompYonedaIsoLan F)
set_option linter.uppercaseLean3 false in
#align category_theory.comp_yoneda_iso_yoneda_comp_Lan CategoryTheory.compYonedaIsoYonedaCompLan

/-- Since `extendAlongYoneda A` is adjoint to `restrictedYoneda A`, if we use `A = yoneda`
then `restrictedYoneda A` is isomorphic to the identity, and so `extendAlongYoneda A` is as well.
-/
noncomputable def extendAlongYonedaYoneda : extendAlongYoneda (yoneda : C ⥤ _) ≅ 𝟭 _ :=
  Adjunction.natIsoOfRightAdjointNatIso (yonedaAdjunction _) Adjunction.id restrictedYonedaYoneda
#align category_theory.extend_along_yoneda_yoneda CategoryTheory.extendAlongYonedaYoneda

-- Maybe this should be reducible or an abbreviation?
/-- A functor to the presheaf category in which everything in the image is representable (witnessed
by the fact that it factors through the yoneda embedding).
`coconeOfRepresentable` gives a cocone for this functor which is a colimit and has point `P`.
-/
def functorToRepresentables (P : Cᵒᵖ ⥤ Type u₁) : P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type u₁ :=
  (CategoryOfElements.π P).leftOp ⋙ yoneda
#align category_theory.functor_to_representables CategoryTheory.functorToRepresentables

/-- This is a cocone with point `P` for the functor `functorToRepresentables P`. It is shown in
`colimitOfRepresentable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
noncomputable def coconeOfRepresentable (P : Cᵒᵖ ⥤ Type u₁) : Cocone (functorToRepresentables P) :=
  Cocone.extend (colimit.cocone _) (extendAlongYonedaYoneda.hom.app P)
#align category_theory.cocone_of_representable CategoryTheory.coconeOfRepresentable

@[simp]
theorem coconeOfRepresentable_pt (P : Cᵒᵖ ⥤ Type u₁) : (coconeOfRepresentable P).pt = P :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.cocone_of_representable_X CategoryTheory.coconeOfRepresentable_pt

-- Marking this as a simp lemma seems to make things more awkward.
/-- An explicit formula for the legs of the cocone `coconeOfRepresentable`. -/
theorem coconeOfRepresentable_ι_app (P : Cᵒᵖ ⥤ Type u₁) (j : P.Elementsᵒᵖ) :
    (coconeOfRepresentable P).ι.app j = (yonedaSectionsSmall _ _).inv j.unop.2 :=
  colimit.ι_desc _ _
#align category_theory.cocone_of_representable_ι_app CategoryTheory.coconeOfRepresentable_ι_app

/-- The legs of the cocone `coconeOfRepresentable` are natural in the choice of presheaf. -/
theorem coconeOfRepresentable_naturality {P₁ P₂ : Cᵒᵖ ⥤ Type u₁} (α : P₁ ⟶ P₂) (j : P₁.Elementsᵒᵖ) :
    (coconeOfRepresentable P₁).ι.app j ≫ α =
      (coconeOfRepresentable P₂).ι.app ((CategoryOfElements.map α).op.obj j) := by
  ext T f
  simpa [coconeOfRepresentable_ι_app] using FunctorToTypes.naturality _ _ α f.op _
#align category_theory.cocone_of_representable_naturality CategoryTheory.coconeOfRepresentable_naturality

/-- The cocone with point `P` given by `coconeOfRepresentable` is a colimit:
that is, we have exhibited an arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
noncomputable def colimitOfRepresentable (P : Cᵒᵖ ⥤ Type u₁) :
    IsColimit (coconeOfRepresentable P) := by
  -- porting note:
  -- the `suffices` was not necessary in mathlib3; the function being `apply`ed has an
  -- `IsIso` input in square brackets; lean 3 was happy to give the user the input as a goal but
  -- lean 4 complains that typeclass inference can't find it.
  suffices IsIso (IsColimit.desc (colimit.isColimit (functorToRepresentables P))
    (coconeOfRepresentable P)) by
    apply IsColimit.ofPointIso (colimit.isColimit (functorToRepresentables P))
  change IsIso (colimit.desc _ (Cocone.extend _ _))
  rw [colimit.desc_extend, colimit.desc_cocone]
  infer_instance
#align category_theory.colimit_of_representable CategoryTheory.colimitOfRepresentable

/-- Given two functors L₁ and L₂ which preserve colimits, if they agree when restricted to the
representable presheaves then they agree everywhere.
-/
noncomputable def natIsoOfNatIsoOnRepresentables (L₁ L₂ : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ)
    [PreservesColimits L₁] [PreservesColimits L₂] (h : yoneda ⋙ L₁ ≅ yoneda ⋙ L₂) : L₁ ≅ L₂ := by
  apply NatIso.ofComponents _ _
  · intro P
    refine'
      (isColimitOfPreserves L₁ (colimitOfRepresentable P)).coconePointsIsoOfNatIso
        (isColimitOfPreserves L₂ (colimitOfRepresentable P)) _
    apply Functor.associator _ _ _ ≪≫ _
    exact isoWhiskerLeft (CategoryOfElements.π P).leftOp h
  · intro P₁ P₂ f
    apply (isColimitOfPreserves L₁ (colimitOfRepresentable P₁)).hom_ext
    intro j
    dsimp only [id.def, isoWhiskerLeft_hom]
    have :
      (L₁.mapCocone (coconeOfRepresentable P₁)).ι.app j ≫ L₁.map f =
        (L₁.mapCocone (coconeOfRepresentable P₂)).ι.app
          ((CategoryOfElements.map f).op.obj j) := by
      dsimp
      rw [← L₁.map_comp, coconeOfRepresentable_naturality]
      rfl
    erw [reassoc_of% this, IsColimit.ι_map_assoc, IsColimit.ι_map]
    dsimp
    rw [← L₂.map_comp, coconeOfRepresentable_naturality]
    rfl
#align category_theory.nat_iso_of_nat_iso_on_representables CategoryTheory.natIsoOfNatIsoOnRepresentables

variable [HasColimits ℰ]

/-- Show that `extendAlongYoneda` is the unique colimit-preserving functor which extends `A` to
the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
noncomputable def uniqueExtensionAlongYoneda (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (hL : yoneda ⋙ L ≅ A)
    [PreservesColimits L] : L ≅ extendAlongYoneda A :=
  natIsoOfNatIsoOnRepresentables _ _ (hL ≪≫ (isExtensionAlongYoneda _).symm)
#align category_theory.unique_extension_along_yoneda CategoryTheory.uniqueExtensionAlongYoneda

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. This is a special case of
`isLeftAdjointOfPreservesColimits` used to prove that.
-/
noncomputable def isLeftAdjointOfPreservesColimitsAux (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ)
    [PreservesColimits L] : IsLeftAdjoint L where
  right := restrictedYoneda (yoneda ⋙ L)
  adj := (yonedaAdjunction _).ofNatIsoLeft (uniqueExtensionAlongYoneda _ L (Iso.refl _)).symm
#align category_theory.is_left_adjoint_of_preserves_colimits_aux CategoryTheory.isLeftAdjointOfPreservesColimitsAux

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this is a (partial)
converse to `leftAdjointPreservesColimits`.
-/
noncomputable def isLeftAdjointOfPreservesColimits (L : (C ⥤ Type u₁) ⥤ ℰ) [PreservesColimits L] :
    IsLeftAdjoint L :=
  let e : _ ⥤ Type u₁ ≌ _ ⥤ Type u₁ := (opOpEquivalence C).congrLeft
  let _ := isLeftAdjointOfPreservesColimitsAux (e.functor ⋙ L : _)
  Adjunction.leftAdjointOfNatIso (e.invFunIdAssoc _)
#align category_theory.is_left_adjoint_of_preserves_colimits CategoryTheory.isLeftAdjointOfPreservesColimits

end SmallCategory

section ArbitraryUniverses

variable {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁)

/-- For a presheaf `P`, consider the forgetful functor from the category of representable
    presheaves over `P` to the category of presheaves. There is a tautological cocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representable is just that
    natural transformation. -/
@[simps]
def tautologicalCocone : Cocone (CostructuredArrow.proj yoneda P ⋙ yoneda) where
  pt := P
  ι := { app := fun X => X.hom }

/-- The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a colimit of
    representables. -/
def isColimitTautologicalCocone : IsColimit (tautologicalCocone P) where
  desc := fun s => by
    refine' ⟨fun X t => yonedaEquiv (s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm t))), _⟩
    intros X Y f
    ext t
    dsimp
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [yonedaEquiv_naturality', yonedaEquiv_symm_map]
    simpa using (s.ι.naturality
      (CostructuredArrow.homMk' (CostructuredArrow.mk (yonedaEquiv.symm t)) f.unop)).symm
  fac := by
    intro s t
    dsimp
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    dsimp only
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [Equiv.symm_apply_apply]
    rfl
  uniq := by
    intro s j h
    ext V x
    obtain ⟨t, rfl⟩ := yonedaEquiv.surjective x
    dsimp
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [Equiv.symm_apply_apply, ← yonedaEquiv_comp']
    exact congr_arg _ (h (CostructuredArrow.mk t))

lemma a : 0 = 0 := rfl

variable {I : Type v₁} [SmallCategory I] (α : I ⥤ C)

structure IsYonedaPreimage {F A : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A)
    (u : F.obj (Opposite.op X)) : Prop where
  (app : η.app _ u = yonedaEquiv s)

lemma IsYonedaPreimage.map₁ {F G A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {μ : G ⟶ A} {ε : F ⟶ G} (hε : ε ≫ μ = η)
    {X : C} {s : yoneda.obj X ⟶ A} {u : F.obj (Opposite.op X)} (h : IsYonedaPreimage η s u) :
    IsYonedaPreimage μ s (ε.app _ u) :=
  ⟨by rw [← elementwise_of% NatTrans.comp_app ε μ, hε, h.app]⟩

lemma IsYonedaPreimage.map₂ {F A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (hst : yoneda.map f ≫ t = s)
    {u : F.obj (Opposite.op Y)} (h : IsYonedaPreimage η t u) : IsYonedaPreimage η s (F.map f.op u) :=
  ⟨by rw [elementwise_of% η.naturality, h.app, yonedaEquiv_naturality, hst]⟩

def YonedaPreimage {F A : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) : Type v₁ :=
  Subtype (IsYonedaPreimage η s)

def YonedaPreimage.val {F A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} :
    YonedaPreimage η s → F.obj (Opposite.op X) :=
  Subtype.val

@[ext]
lemma YonedaPreimage.ext {F A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    {u v : YonedaPreimage η s} : u.val = v.val → u = v :=
  Subtype.ext

-- lemma YonedaPreimage.val_eqToHom {F A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}

lemma YonedaPreimage.app_val {F A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (p : YonedaPreimage η s) : η.app _ p.val = yonedaEquiv s :=
  p.prop.app

@[simp]
lemma YonedaPreimage.map_val {A : Cᵒᵖ ⥤ Type v₁} {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (p : YonedaPreimage η s) : yoneda.map p.val ≫ η = s := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_comp, yonedaEquiv_yoneda_map, p.app_val, Opposite.op_unop]

def YonedaPreimage.map₁ {F G A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {μ : G ⟶ A} {X : C}
    {s : yoneda.obj X ⟶ A} (u : YonedaPreimage η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) :
    YonedaPreimage μ s :=
  ⟨ε.app _ u.val, IsYonedaPreimage.map₁ hε u.2⟩

@[simp]
lemma YonedaPreimage.map₁_val {F G A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {μ : G ⟶ A} {X : C}
    (s : yoneda.obj X ⟶ A) (u : YonedaPreimage η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) :
    (u.map₁ ε hε).val = ε.app _ u.val :=
  rfl

def YonedaPreimage.map₂ {F A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {X Y : C} {s : yoneda.obj X ⟶ A}
  {t : yoneda.obj Y ⟶ A} (u : YonedaPreimage η t) (f : X ⟶ Y) (hst : yoneda.map f ≫ t = s) :
    YonedaPreimage η s :=
  ⟨F.map f.op u.val, IsYonedaPreimage.map₂ f hst u.2⟩

@[simp]
lemma YonedaPreimage.map₂_val {F A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (hst : yoneda.map f ≫ t = s)
    (u : YonedaPreimage η t) : (u.map₂ f hst).val = F.map f.op u.val :=
  rfl

-- lemma YonedaPreimage.map₂_val_eqToHom {F A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {X Y : C} (h : X = Y)
--     {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (u : YonedaPreimage η t) : (u.map₂ (eqToHom h) _).val = u.val := sorry

@[simp]
lemma YonedaPreimage_map₁_map₂ {F G A : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G) (hε : ε ≫ μ = η) {X Y : C}
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A}
    (f : X ⟶ Y) (hf : yoneda.map f ≫ t = s) (u : YonedaPreimage η t) :
    (u.map₁ ε hε).map₂ f hf = (u.map₂ f hf).map₁ ε hε :=
  YonedaPreimage.ext <| (elementwise_of% (ε.naturality f.op).symm) u.val

@[simps (config := { fullyApplied := false }) obj map]
def yonedaPreimageFunctor' {A F : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁ where
  obj s := YonedaPreimage η s.unop.hom
  map f u := u.map₂ f.unop.left f.unop.w

@[simps]
def yonedaPreimageFunctor'_map₁ {A F G : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G) (hε : ε ≫ μ = η) :
    yonedaPreimageFunctor' η ⟶ yonedaPreimageFunctor' μ where
  app s u := u.map₁ ε hε

@[simps]
def yonedaPreimageFunctor (A : Cᵒᵖ ⥤ Type v₁) : Over A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁ where
  obj η := yonedaPreimageFunctor' η.hom
  map ε := yonedaPreimageFunctor'_map₁ ε.left ε.w

def yonedaPreimageCostructuredArrow (A : Cᵒᵖ ⥤ Type v₁) (s t : CostructuredArrow yoneda A) :
    YonedaPreimage s.hom t.hom ≅ t ⟶ s :=
  ⟨fun p => CostructuredArrow.homMk p.val (by aesop_cat), fun f => ⟨f.left, ⟨by
    have := f.w
    dsimp at this
    rw [Category.comp_id] at this
    rw [← this, ← yonedaEquiv_naturality]
    dsimp
    have := congrFun (s.hom.naturality f.left.op) (𝟙 s.left)
    dsimp at this
    rw [← this, Category.comp_id]
  ⟩⟩, by aesop_cat, by aesop_cat⟩

@[simps!]
def yonedaCompYonedaPreimageFunctor (A : Cᵒᵖ ⥤ Type v₁) :
    CostructuredArrow.toOver yoneda A ⋙ yonedaPreimageFunctor A ≅ yoneda :=
  NatIso.ofComponents (fun s => by
    refine' NatIso.ofComponents (fun t => yonedaPreimageCostructuredArrow _ _ _) _
    aesop_cat
  ) (by aesop_cat)

lemma b : 0 = 0 := rfl

def YonedaCollection {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) (X : C) :
    Type v₁ :=
  Σ (s : A.obj (Opposite.op X)), F.obj (Opposite.op (CostructuredArrow.mk (yonedaEquiv.symm s)))

def YonedaCollection.mk {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    {X : C} (s : A.obj (Opposite.op X)) (x : F.obj (Opposite.op (CostructuredArrow.mk (yonedaEquiv.symm s)))) :
    YonedaCollection F X :=
  ⟨s, x⟩

def YonedaCollection.mk' {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    {X : C} (s : yoneda.obj X ⟶ A) (x : F.obj (Opposite.op (CostructuredArrow.mk s))) :
    YonedaCollection F X := ⟨yonedaEquiv s, F.map (eqToHom <| by rw [Equiv.symm_apply_apply]) x⟩

def YonedaCollection.fst {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    {X : C} (p : YonedaCollection F X) : A.obj (Opposite.op X) := p.1

def YonedaCollection.snd {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    {X : C} (p : YonedaCollection F X) :
    F.obj (Opposite.op (CostructuredArrow.mk (yonedaEquiv.symm p.fst))) := p.2

def YonedaCollection.fst' {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    {X : C} (p : YonedaCollection F X) : yoneda.obj X ⟶ A :=
  yonedaEquiv.symm p.fst

def YonedaCollection.snd' {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    {X : C} (p : YonedaCollection F X) : F.obj (Opposite.op (CostructuredArrow.mk p.fst')) :=
  p.snd

lemma YonedaCollection.fst_eq_yonedEquiv_fst' {A : Cᵒᵖ ⥤ Type v₁}
    {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁} {X : C} (p : YonedaCollection F X) :
    p.fst = yonedaEquiv p.fst' :=
  (Equiv.apply_symm_apply _ _).symm

@[simp]
lemma YonedaCollection.mk'_fst' {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    {X : C} (s : yoneda.obj X ⟶ A) (x : F.obj (Opposite.op (CostructuredArrow.mk s))) :
    (YonedaCollection.mk' s x).fst' = s :=
  Equiv.apply_symm_apply _ _

@[simp]
lemma YonedaCollection.mk'_snd' {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    {X : C} (s : yoneda.obj X ⟶ A) (x : F.obj (Opposite.op (CostructuredArrow.mk s))) :
    (YonedaCollection.mk' s x).snd' = F.map (eqToHom <| by rw [YonedaCollection.mk'_fst']) x := rfl

@[ext]
lemma YonedaCollection.ext' {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    {X : C} (p q : YonedaCollection F X) : (h : p.fst' = q.fst') → F.map (eqToHom <| by rw [h]) q.snd' = p.snd' → p = q := by
  -- TODO: Clean up this proof
  intro h h'
  rcases p with ⟨p, p'⟩
  rcases q with ⟨q, q'⟩
  obtain rfl : p = q := yonedaEquiv.symm.injective h
  apply Sigma.ext
  · rfl
  · rw [heq_eq_eq]
    convert h'.symm
    simp [snd']
    rfl

def YonedaCollection.map₁ {A : Cᵒᵖ ⥤ Type v₁} {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    (η : F ⟶ G) {X : C} : YonedaCollection F X → YonedaCollection G X := fun p =>
  YonedaCollection.mk' p.fst' (η.app _ p.snd')

@[simp]
lemma YonedaCollection.map₁_fst' {A : Cᵒᵖ ⥤ Type v₁} {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    (η : F ⟶ G) {X : C} (p : YonedaCollection F X) : (YonedaCollection.map₁ η p).fst' = p.fst' := by
  simp [map₁]

@[simp]
lemma YonedaCollection.map₁_snd' {A : Cᵒᵖ ⥤ Type v₁} {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    (η : F ⟶ G) {X : C} (p : YonedaCollection F X) :
    (YonedaCollection.map₁ η p).snd' = G.map (eqToHom (by rw [YonedaCollection.map₁_fst'])) (η.app _ p.snd') := by
  simp [map₁]

@[simp]
lemma YonedaCollection.map₁_fst {A : Cᵒᵖ ⥤ Type v₁} {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    (η : F ⟶ G) {X : C} (p : YonedaCollection F X) :
    (YonedaCollection.map₁ η p).fst = p.fst := by
  simp only [YonedaCollection.fst_eq_yonedEquiv_fst', map₁_fst']

def YonedaCollection.map₂ {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) {X Y : C}
    (f : X ⟶ Y) : YonedaCollection F Y → YonedaCollection F X := fun p =>
  YonedaCollection.mk' (yoneda.map f ≫ p.fst') $ F.map (Quiver.Hom.op (CostructuredArrow.homMk'' p.fst' f)) p.snd'

@[simp]
lemma YonedaCollection.map₂_fst' {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) {X Y : C}
    (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).fst' = yoneda.map f ≫ p.fst' :=
  by simp [map₂]

@[simp]
lemma YonedaCollection.map₂_fst {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) {X Y : C}
    (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).fst = A.map f.op p.fst := by
  simp only [YonedaCollection.fst_eq_yonedEquiv_fst', map₂_fst', yonedaEquiv_naturality]

@[simp]
lemma YonedaCollection.map₂_snd' {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) {X Y : C}
    (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).snd' = F.map (Quiver.Hom.op (CostructuredArrow.homMk'' p.fst' f) ≫ eqToHom (by rw [YonedaCollection.map₂_fst' F f])) p.snd' := by
  simp [map₂]

@[simp]
lemma bla {F : C ⥤ Type w} {X Y Z : C} (h₁ : X = Y) (h₂ : Y = Z) (x : F.obj X) :
  F.map (eqToHom h₂) (F.map (eqToHom h₁) x) = F.map (eqToHom (h₁.trans h₂)) x :=
  by aesop_cat

attribute [simp] CostructuredArrow.homMk''_id

@[simp]
lemma YonedaCollection.map₂_id {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁} {X : C} :
    YonedaCollection.map₂ F (𝟙 X) = id := by
  ext p
  · simp
  · simp

-- How does simp even know how to apply this
@[simp]
lemma blubb {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁} {X Y : C} {f : X ⟶ Y}
    {g g' : yoneda.obj Y ⟶ A} (h : g = g') {x : F.obj (Opposite.op (CostructuredArrow.mk g'))} :
  F.map (CostructuredArrow.homMk'' g f).op (F.map (eqToHom (by rw [h])) x) = F.map (eqToHom (by rw [h])) (F.map (CostructuredArrow.homMk'' g' f).op x)
   := by aesop_cat

attribute [simp] CostructuredArrow.homMk''_comp

@[simp]
lemma YonedaCollection.map₂_comp {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁} {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) : YonedaCollection.map₂ F (f ≫ g) = YonedaCollection.map₂ F f ∘ YonedaCollection.map₂ F g := by
  ext p
  · simp
  · simp

@[simp]
lemma YonedaCollection.map₁_map₂ {A : Cᵒᵖ ⥤ Type v₁} {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
  (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    YonedaCollection.map₂ G f (YonedaCollection.map₁ η p) = YonedaCollection.map₁ η (YonedaCollection.map₂ F f p) := by
  ext
  · simp
  · simp [FunctorToTypes.naturality]

@[simp]
lemma YonedaCollection.map₁_id {A : Cᵒᵖ ⥤ Type v₁} {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁} {X : C} :
  YonedaCollection.map₁ (𝟙 F) (X := X) = id := by aesop_cat

@[simp]
lemma YonedaCollection.map₁_comp {A : Cᵒᵖ ⥤ Type v₁} {F G H : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁}
    (η : F ⟶ G) (μ : G ⟶ H) {X : C} :
    YonedaCollection.map₁ (η ≫ μ) (X := X) = YonedaCollection.map₁ μ (X := X) ∘ YonedaCollection.map₁ η (X := X) := by
  ext
  · simp
  · simp [FunctorToTypes.naturality]

@[simps (config := { fullyApplied := false })]
def YonedaCollectionFunctor' (A : Cᵒᵖ ⥤ Type v₁) (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) :
    Cᵒᵖ ⥤ Type v₁ where
  obj X := YonedaCollection F X.unop
  map f := YonedaCollection.map₂ F f.unop

@[simps]
def YonedaCollectionMap {A : Cᵒᵖ ⥤ Type v₁} {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁} (η : F ⟶ G) :
    YonedaCollectionFunctor' A F ⟶ YonedaCollectionFunctor' A G where
  app X := YonedaCollection.map₁ η
  naturality := by
    intros
    ext
    simp

@[simps (config := { fullyApplied := false }) obj map]
def YonedaCollectionFunctor (A : Cᵒᵖ ⥤ Type v₁) : ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj := YonedaCollectionFunctor' A
  map η := YonedaCollectionMap η

@[simps (config := { fullyApplied := false }) app]
def YonedaCollectionFunctorToA (A : Cᵒᵖ ⥤ Type v₁) (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) :
    YonedaCollectionFunctor' A F ⟶ A where
  app X := YonedaCollection.fst

@[simps! (config := { fullyApplied := false }) obj map]
def YonedaCollectionTotal (A : Cᵒᵖ ⥤ Type v₁) :
    ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) ⥤ Over A :=
  (YonedaCollectionFunctor A).toOver _ (YonedaCollectionFunctorToA A) (by aesop_cat)

theorem c : 0 = 0 := rfl

def ax {A F : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) (X : C) :
    YonedaCollection (yonedaPreimageFunctor' η) X → F.obj (Opposite.op X) :=
  fun p => p.snd'.val

@[simp]
lemma ax_naturality₁ {A F G : Cᵒᵖ ⥤ Type v₁} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G) (hε : ε ≫ μ = η) (X : C) (p : YonedaCollection (yonedaPreimageFunctor' η) X) :
    ax μ X (p.map₁ (yonedaPreimageFunctor'_map₁ ε hε)) = ε.app _ (ax η X p) := by
  simp [ax]

@[simp]
lemma ax_naturality₂ {A F : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) (X Y : C) (f : X ⟶ Y) (p : YonedaCollection (yonedaPreimageFunctor' η) Y) :
    ax η X (YonedaCollection.map₂ (yonedaPreimageFunctor' η) f p) = F.map f.op (ax η Y p) := by
  simp [ax]

@[simp]
lemma app_ax {A F : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) (X : Cᵒᵖ) (p : YonedaCollection (yonedaPreimageFunctor' η) X.unop) :
    η.app X (ax η X.unop p) = p.fst := by
  simp [ax]
  have := p.snd'.app_val
  dsimp [-yonedaEquiv_apply] at this
  simp [-yonedaEquiv_apply, this, YonedaCollection.fst_eq_yonedEquiv_fst']

def back {A F : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) (X : C) :
    F.obj (Opposite.op X) → YonedaCollection (yonedaPreimageFunctor' η) X :=
  fun x => YonedaCollection.mk' (yonedaEquiv.symm (η.app _ x)) ⟨x, ⟨by aesop_cat⟩⟩

lemma ax_back {A F : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) (X : C) : ax η X ∘ back η X = id := by
  ext x
  dsimp [ax, back]
  aesop_cat

lemma back_ax {A F : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) (X : C) : back η X ∘ ax η X = id := by
  ext1 p
  simp [ax, back]
  refine' YonedaCollection.ext' _ _ _ _
  · have := p.snd'.app_val
    dsimp [-yonedaEquiv_apply] at this
    dsimp
    simp [-yonedaEquiv_apply, this]
  · apply YonedaPreimage.ext
    aesop_cat

@[simps]
def bij {A F : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) (X : C) :
    YonedaCollection (yonedaPreimageFunctor' η) X ≅ F.obj (Opposite.op X) where
  hom := ax η X
  inv := back η X
  hom_inv_id := back_ax η X
  inv_hom_id := ax_back η X

@[simps!]
def unit₀ {A F : Cᵒᵖ ⥤ Type v₁} (η : F ⟶ A) : YonedaCollectionFunctor' A (yonedaPreimageFunctor' η) ≅ F :=
  NatIso.ofComponents (fun X => bij η X.unop) (by aesop_cat)

@[simps!]
def unit_pt {A : Cᵒᵖ ⥤ Type v₁} (η : Over A) : (yonedaPreimageFunctor A ⋙ YonedaCollectionTotal A).obj η ≅ η :=
  Over.isoMk (unit₀ η.hom) (by aesop_cat)

def unit {A : Cᵒᵖ ⥤ Type v₁} : yonedaPreimageFunctor A ⋙ YonedaCollectionTotal A ≅ 𝟭 (Over A) :=
  NatIso.ofComponents unit_pt (by aesop_cat)

theorem d : 0 = 0 := rfl

@[simp]
lemma val_fst' {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) (X : C)
    (s : yoneda.obj X ⟶ A) (p : YonedaPreimage (YonedaCollectionFunctorToA A F) s) : p.val.fst' = s := by
  simpa [-yonedaEquiv_apply, YonedaCollection.fst_eq_yonedEquiv_fst'] using p.app_val

def cofo {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) (s : CostructuredArrow yoneda A) :
    F.obj (Opposite.op s) → YonedaPreimage (YonedaCollectionFunctorToA A F) s.hom :=
  fun x => ⟨YonedaCollection.mk' s.hom x, ⟨by simp [-yonedaEquiv_apply, YonedaCollection.fst_eq_yonedEquiv_fst']⟩⟩

--cofo G s.unop (η.app s x) = YonedaPreimage.map₁ (cofo F s.unop x) (NatTrans.mk fun X ↦ YonedaCollection.map₁ η) _

@[simp]
lemma cofo_naturality₁ {A : Cᵒᵖ ⥤ Type v₁} {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁} (η : F ⟶ G)
    (s : (CostructuredArrow yoneda A)ᵒᵖ) (x : F.obj s) : cofo G s.unop (η.app s x) = YonedaPreimage.map₁ (cofo F s.unop x) (YonedaCollectionMap η) (by aesop_cat) := by
  dsimp [cofo]
  apply YonedaPreimage.ext
  simp
  refine' YonedaCollection.ext' _ _ _ _
  · simp
  · simp
    erw [YonedaCollection.mk'_snd']
    erw [YonedaCollection.mk'_snd']
    exact FunctorToTypes.naturality _ _ _ _ _

-- F.map f ≫ (cobij F Y.unop).hom = (cobij F X.unop).hom ≫ fun u ↦ YonedaPreimage.map₂ u f.unop.left _
-- cofo F t.unop (F.map f x) = YonedaPreimage.map₂ (cofo F s.unop x) f.unop.left _

lemma bloink {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) (s t : CostructuredArrow yoneda A)
    (f : s ⟶ t) (x : F.obj (Opposite.op t)) : (F.map (CostructuredArrow.homMk'' t.hom f.left).op x) = F.map (eqToHom <| by simp [← CostructuredArrow.eq_mk]) (F.map f.op x) := by
  have : (CostructuredArrow.homMk'' t.hom f.left).op = f.op ≫ eqToHom (by simp [← CostructuredArrow.eq_mk]) := by
    apply Quiver.Hom.unop_inj
    aesop_cat
  erw [this]
  simp

@[simp]
lemma cofo_naturality₂ {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) (s t : (CostructuredArrow yoneda A)ᵒᵖ)
    (f : t ⟶ s) (x : F.obj t) : cofo F s.unop (F.map f x) = YonedaPreimage.map₂ (cofo F t.unop x) f.unop.left (by simp) := by
  simp [cofo]
  apply YonedaPreimage.ext
  rw [YonedaPreimage.map₂_val]
  refine' YonedaCollection.ext' _ _ _ _
  · simp only [Opposite.unop_op, YonedaCollectionFunctor'_obj, val_fst',
    YonedaCollectionFunctor'_map, Quiver.Hom.unop_op, YonedaCollection.map₂_fst', CommaMorphism.w,
    Functor.const_obj_obj, CostructuredArrow.right_eq_id, Functor.const_obj_map, comp_id]
  · erw [YonedaCollection.mk'_snd']
    erw [YonedaCollection.mk'_snd']
    erw [YonedaCollection.mk'_snd']
    simp only [Opposite.unop_op, YonedaCollectionFunctor'_obj, YonedaCollectionFunctor'_map,
      Quiver.Hom.unop_op, id_eq, eq_mpr_eq_cast, val_fst', blubb, bla]
    erw [bloink]
    simp

def coba {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) (s : CostructuredArrow yoneda A) :
    YonedaPreimage (YonedaCollectionFunctorToA A F) s.hom → F.obj (Opposite.op s) :=
  fun p => F.map (eqToHom (by simp [val_fst', ← CostructuredArrow.eq_mk])) p.val.snd'

lemma cofo_coba {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) (s : CostructuredArrow yoneda A) :
    cofo F s ∘ coba F s = id := by
  ext p
  dsimp [cofo, coba]
  change YonedaCollection.mk' _ _ = _
  refine' YonedaCollection.ext' _ _ _ _
  · simp
  · simp

lemma coba_cofo {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) (s : CostructuredArrow yoneda A) :
    coba F s ∘ cofo F s = id := by
  ext x
  dsimp [cofo, coba]
  erw [YonedaCollection.mk'_snd']
  simp

@[simps]
def cobij {A : Cᵒᵖ ⥤ Type v₁} (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) (s : CostructuredArrow yoneda A) :
    F.obj (Opposite.op s) ≅ YonedaPreimage (YonedaCollectionFunctorToA A F) s.hom where
  hom := cofo F s
  inv := coba F s
  hom_inv_id := coba_cofo F s
  inv_hom_id := cofo_coba F s

@[simps! (config := { fullyApplied := false }) hom]
def counit₀ (A : Cᵒᵖ ⥤ Type v₁) (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) :
    F ≅ yonedaPreimageFunctor' (YonedaCollectionFunctorToA A F) :=
  NatIso.ofComponents (fun s => cobij F s.unop) (by aesop_cat)

def counit {A : Cᵒᵖ ⥤ Type v₁} : 𝟭 ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) ≅ (YonedaCollectionTotal A ⋙ yonedaPreimageFunctor A) :=
  NatIso.ofComponents (counit₀ A) (by aesop_cat)

def OverEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type v₁) : Over A ≌ ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v₁) :=
  Equivalence.mk (yonedaPreimageFunctor A) (YonedaCollectionTotal A) (unit).symm (counit).symm

def ToOverCompOverEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type v₁) : CostructuredArrow.toOver yoneda A ⋙ (OverEquivPresheafCostructuredArrow A).functor ≅ yoneda :=
  yonedaCompYonedaPreimageFunctor A

open Functor

theorem final_toCostructuredArrow_comp_pre {c : Cocone (α ⋙ yoneda)} (hc : IsColimit c) :
    Final (c.toCostructuredArrow ⋙ CostructuredArrow.pre α yoneda c.pt) := by
  refine' cofinal_of_colimit_comp_coyoneda_iso_pUnit _ (fun d => _)
  refine' Types.isTerminalEquivIsoPUnit _ _
  suffices IsTerminal (colimit (c.toCostructuredArrow ⋙ CostructuredArrow.pre α _ _ ⋙ yoneda)) by
    let b := IsTerminal.isTerminalObj ((evaluation _ _).obj (Opposite.op d)) _ this
    apply IsTerminal.ofIso b
    let e := preservesColimitIso
      ((evaluation (CostructuredArrow yoneda c.pt)ᵒᵖ (Type v₁)).obj (Opposite.op d))
      (Cocone.toCostructuredArrow c ⋙ CostructuredArrow.pre α yoneda c.pt ⋙ yoneda)
    exact e
  refine' IsTerminal.isTerminalOfObj (OverEquivPresheafCostructuredArrow c.pt).inverse
    (colimit (c.toCostructuredArrow ⋙ CostructuredArrow.pre α _ _  ⋙ yoneda)) _
  apply IsTerminal.ofIso (Over.mkIdTerminal)
  let i := preservesColimitIso ((OverEquivPresheafCostructuredArrow c.pt).inverse) (Cocone.toCostructuredArrow c ⋙ CostructuredArrow.pre α yoneda c.pt ⋙ yoneda)
  refine' _ ≪≫ i.symm
  let j := ToOverCompOverEquivPresheafCostructuredArrow c.pt

  -- TODO: Extract this out
  let k : CostructuredArrow.toOver yoneda c.pt ≅ yoneda ⋙ (OverEquivPresheafCostructuredArrow c.pt).inverse := by
    calc
      CostructuredArrow.toOver yoneda c.pt ≅ CostructuredArrow.toOver yoneda c.pt ⋙ (OverEquivPresheafCostructuredArrow c.pt).functor ⋙ (OverEquivPresheafCostructuredArrow c.pt).inverse
        := isoWhiskerLeft (CostructuredArrow.toOver _ _) ((OverEquivPresheafCostructuredArrow c.pt).unitIso)
      _ ≅ yoneda ⋙ (OverEquivPresheafCostructuredArrow c.pt).inverse := isoWhiskerRight j (OverEquivPresheafCostructuredArrow c.pt).inverse

  let k' := isoWhiskerLeft (Cocone.toCostructuredArrow c ⋙ CostructuredArrow.pre α yoneda c.pt) k
  let k'' := HasColimit.isoOfNatIso k'
  refine' _ ≪≫ k''
  let u : colimit ((Cocone.toCostructuredArrow c ⋙ CostructuredArrow.pre α yoneda c.pt) ⋙ CostructuredArrow.toOver yoneda c.pt ⋙ Over.forget _) ≅ c.pt :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc
  let v := preservesColimitIso (Over.forget _) ((Cocone.toCostructuredArrow c ⋙ CostructuredArrow.pre α yoneda c.pt) ⋙ CostructuredArrow.toOver yoneda c.pt)
  let w := v ≪≫ u
  refine' Over.isoMk w.symm _
  apply hc.hom_ext
  intro i
  simp [preservesColimitIso, IsColimit.coconePointUniqueUpToIso]
  erw [colimit.ι_desc_assoc]
  simp

end ArbitraryUniverses


end CategoryTheory
