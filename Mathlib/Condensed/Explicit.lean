import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Topology.Category.Stonean.Limits
import Mathlib.Topology.Category.CompHaus.Limits
import Mathlib.Topology.Category.Profinite.EffectiveEpi

universe v v₁ u u₁ w

section isSheafForPullBackSieve

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

variable {C : Type u₁} [Category.{v₁} C]

variable {X : C} (S : Presieve X)

def isPullbackPresieve : Prop :=
  ∀ {Y Z} {f : Y ⟶ X} (_ : S f) {g : Z ⟶ X} (_ : S g),
  HasPullback f g

variable (P : Cᵒᵖ ⥤ Type max v₁ u₁)

variable (hS : isPullbackPresieve S) {S}
namespace Presieve

def FamilyOfElements.PullbackCompatible' (x : FamilyOfElements P S) : Prop :=
  ∀ ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : S f₁) (h₂ : S f₂),
    have := hS h₁ h₂
    P.map (pullback.fst : Limits.pullback f₁ f₂ ⟶ _).op (x f₁ h₁) = P.map pullback.snd.op (x f₂ h₂)

theorem pullbackCompatible_iff' (x : FamilyOfElements P S) :
    x.Compatible ↔ x.PullbackCompatible' hS := by
  constructor
  · intro t Y₁ Y₂ f₁ f₂ hf₁ hf₂
    apply t
    have := hS hf₁ hf₂
    apply pullback.condition
  · intro t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    have := hS hf₁ hf₂
    rw [← pullback.lift_fst _ _ comm, op_comp, FunctorToTypes.map_comp_apply, t hf₁ hf₂,
      ← FunctorToTypes.map_comp_apply, ← op_comp, pullback.lift_snd]

end Presieve

namespace Equalizer

namespace Presieve

/-- The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[simp] def SecondObj' : Type max v₁ u₁ :=
  ∏ fun fg : (ΣY, { f : Y ⟶ X // S f }) × ΣZ, { g : Z ⟶ X // S g } =>
    have := hS fg.1.2.2 fg.2.2.2
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of <https://stacks.math.columbia.edu/tag/00VL>. -/
noncomputable
def firstMap' : FirstObj P S ⟶ SecondObj' P hS :=
    Pi.lift fun fg =>
    have := hS fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map pullback.fst.op

/-- The map `pr₁*` of <https://stacks.math.columbia.edu/tag/00VL>. -/
noncomputable def secondMap' : FirstObj P S ⟶ SecondObj' P hS :=
  Pi.lift fun fg =>
    have := hS fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map pullback.snd.op

theorem w' : forkMap P S ≫ firstMap' P hS = forkMap P S ≫ secondMap' P hS := by
  dsimp
  ext fg
  simp only [firstMap', secondMap', forkMap]
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app]
  have := hS fg.1.2.2 fg.2.2.2
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp

/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap'` and `secondMap'`
map it to the same point.
-/
theorem compatible_iff' (x : FirstObj P S) :
    ((firstObjEqFamily P S).hom x).Compatible ↔ firstMap' P hS x = secondMap' P hS x := by
  rw [Presieve.pullbackCompatible_iff' _ hS]
  constructor
  . intro t
    apply Limits.Types.limit_ext
    rintro ⟨⟨Y, f, hf⟩, Z, g, hg⟩
    simpa [firstMap', secondMap'] using t hf hg
  · intro t Y Z f g hf hg
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap', secondMap'] using t ⟨⟨⟨Y, f, hf⟩, Z, g, hg⟩⟩

/-- `P` is a sheaf for `R`, iff the fork given by `w` is an equalizer.
See <https://stacks.math.columbia.edu/tag/00VM>.
-/
theorem sheaf_condition' : S.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w' P hS))) := by
  rw [Types.type_equalizer_iff_unique]
  erw [← Equiv.forall_congr_left (firstObjEqFamily P S).toEquiv.symm]
  simp_rw [← compatible_iff', ← Iso.toEquiv_fun, Equiv.apply_symm_apply]
  apply ball_congr
  intro x _
  apply exists_unique_congr
  intro t
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    funext Y f hf
    simpa [forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [forkMap]

end Presieve

end Equalizer

end CategoryTheory

end isSheafForPullBackSieve

section ProdCoprod

open CategoryTheory Opposite Limits

section ProdToCoprod

variable {C : Type _} [Category C] {α : Type} [Finite α]
  (Z : α → C) [HasFiniteProducts C]

@[simps!]
noncomputable
def oppositeCofan : Cofan (fun z => op (Z z)) :=
  Cofan.mk (op <| ∏ Z) fun i => (Pi.π _ i).op

@[simps]
noncomputable
def isColimitOppositeCofan : IsColimit (oppositeCofan Z) where
  desc := fun S =>
    let e : S.pt.unop ⟶ ∏ Z := Pi.lift fun j => (S.ι.app _).unop
    e.op
  fac := fun S j => by
    dsimp only [oppositeCofan_pt, Functor.const_obj_obj,
      oppositeCofan_ι_app, Discrete.functor_obj]
    simp only [← op_comp, limit.lift_π,
      Fan.mk_pt, Fan.mk_π_app, Quiver.Hom.op_unop]
  uniq := fun S m hm => by
    rw [← m.op_unop]
    congr 1
    apply limit.hom_ext
    intro j
    simpa using congr_arg Quiver.Hom.unop (hm j)

@[simp]
noncomputable
def ProdToCoprod : op (∏ Z) ≅ ∐ (fun z => op (Z z)) :=
  isColimitOppositeCofan Z |>.coconePointUniqueUpToIso <| colimit.isColimit _

end ProdToCoprod

section CoprodToProd

variable {C : Type _} [Category C] {α : Type} [Finite α]
  (Z : α → C) [HasFiniteCoproducts C]

@[simps!]
noncomputable
def oppositeFan : Fan (fun z => op (Z z)) := by
  refine' Fan.mk (op <| ∐ Z) fun i => (Sigma.ι _ i).op

@[simps!]
noncomputable
def isLimitOppositeFan : IsLimit (oppositeFan Z) where
  lift := fun S =>
    let e : ∐ Z ⟶ S.pt.unop := Sigma.desc fun j => (S.π.app _).unop
    e.op
  fac := fun S j => by
    dsimp only [oppositeFan_pt, Functor.const_obj_obj,
      oppositeFan_π_app, Discrete.functor_obj]
    simp only [← op_comp, colimit.ι_desc,
      Cofan.mk_pt, Cofan.mk_ι_app, Quiver.Hom.op_unop]
  uniq := fun S m hm => by
    rw [← m.op_unop]
    congr 1
    apply colimit.hom_ext
    intro j
    simpa using congr_arg Quiver.Hom.unop (hm j)

@[simp]
noncomputable
def CoprodToProd : op (∐ Z) ≅ ∏ (fun z => op (Z z)) :=
  isLimitOppositeFan Z |>.conePointUniqueUpToIso <| limit.isLimit _

lemma CoprodToProdInvComp.ι (b : α) : ((CoprodToProd Z).inv ≫ (Sigma.ι (fun a => Z a) b).op) =
    Pi.π (fun a => op (Z a)) b :=
  IsLimit.conePointUniqueUpToIso_inv_comp (isLimitOppositeFan Z) (limit.isLimit _) ⟨b⟩

variable {X : C} (π : (a : α) → Z a ⟶ X)

lemma descOpCompCoprodToProd {X : C} (π : (a : α) → Z a ⟶ X) :
    (Sigma.desc π).op ≫ (CoprodToProd Z).hom = Pi.lift (fun a => Quiver.Hom.op (π a)) := by
  refine' limit.hom_ext (fun a => _)
  simp only [CoprodToProd, Category.assoc, limit.conePointUniqueUpToIso_hom_comp, oppositeFan_pt,
    oppositeFan_π_app, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, ← op_comp, colimit.ι_desc]
  rfl

end CoprodToProd

end ProdCoprod


section ExtensiveRegular

section HasPullbackOfRightMono

open CategoryTheory Opposite CategoryTheory.Limits Functor

variable (C : Type u) [Category.{v, u} C]

class HasPullbackOfIsIsodesc : Prop where
    HasPullback : ∀ {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance [HasPullbackOfIsIsodesc C] {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :
    HasPullback f (i a) := HasPullbackOfIsIsodesc.HasPullback f i a

instance [HasPullbacks C] : HasPullbackOfIsIsodesc C := ⟨fun _ _ _ => inferInstance⟩

end HasPullbackOfRightMono

section Coverage
namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

open Sieve CategoryTheory.Limits Opposite

variable {C}

def ExtensiveSieve [HasFiniteCoproducts C] (B : C) := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C)
  (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }

def RegularSieve (B : C) := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
      (fun (_ : Unit) ↦ f) ∧ Epi f }

variable [HasFiniteCoproducts C] (C)

def Extensivity [HasPullbackOfIsIsodesc C] : Prop :=
  ∀ {α : Type} [Fintype α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X)
  {Y : C} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)),
     IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))

def EverythingIsProjective : Prop :=
  ∀ X : C, Projective X

def ExtensiveRegularCoverage [HasFiniteCoproducts C] [HasPullbackOfIsIsodesc C]
    (h_proj : EverythingIsProjective C) (h_ext : Extensivity C) : Coverage C where
  covering B :=   (ExtensiveSieve B) ∪ (RegularSieve B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · let Z' : α → C := fun a ↦ pullback f (π a)
      set π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst with hπ'
      set S' := @Presieve.ofArrows C _ _ α Z' π' with hS'
      use S'
      constructor
      · rw [Set.mem_union]
        apply Or.intro_left
        rw [ExtensiveSieve]
        constructor
        refine ⟨hα, Z', π', ⟨by simp only, ?_⟩⟩
        · rw [hπ']
          exact h_ext (fun x => π x) f h_iso
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩
        refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
        rw [hS]
        refine Presieve.ofArrows.mk a
    · set S' := Presieve.singleton (𝟙 Y) with hS'
      use S'
      constructor
      · apply Or.intro_right
        rw [RegularSieve]
        refine ⟨Y, 𝟙 _, by {rw [Presieve.ofArrows_pUnit (𝟙 Y)]}, instEpiIdToCategoryStruct Y⟩
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        cases hg
        simp only [Category.id_comp]
        use Z
        use @Projective.factorThru C _ Y X Z ?_ f π h_epi
        · use π
          constructor
          · cases hπ
            rw [Presieve.ofArrows_pUnit]
            exact Presieve.singleton.mk
          · have : Projective Y
            exact h_proj Y
            exact @Projective.factorThru_comp C _ Y X Z this f π h_epi
        · exact h_proj Y

def EpiPullbackOfEpi [HasPullbacks C] : Prop := ∀ {X Y Z : C} (f : Y ⟶ X) (π : Z ⟶ X) [Epi π],
    Epi (@pullback.fst _ _ _ _ _ f π _)

def ExtensiveRegularCoverage' [HasFiniteCoproducts C] [HasPullbacks C] (h_epi_epi : EpiPullbackOfEpi C)
    (h_ext : Extensivity C) : Coverage C where
  covering B := (ExtensiveSieve B) ∪ (RegularSieve B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · let Z' : α → C := fun a ↦ pullback f (π a)
      set π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst with hπ'
      set S' := @Presieve.ofArrows C _ _ α Z' π' with hS'
      use S'
      constructor
      · rw [Set.mem_union]
        apply Or.intro_left
        rw [ExtensiveSieve]
        constructor
        refine ⟨hα, Z', π', ⟨by simp only, ?_⟩⟩
        · rw [hπ']
          exact h_ext (fun x => π x) f h_iso
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩
        refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
        rw [hS]
        refine Presieve.ofArrows.mk a
    · set S' := Presieve.singleton (@pullback.fst _ _ _ _ _ f π _) with hS'
      use S'
      constructor
      · right
        rw [RegularSieve]
        refine' ⟨(pullback f π), _, by {rw [Presieve.ofArrows_pUnit _]}, h_epi_epi f π⟩
      · rw [hS', Presieve.FactorsThruAlong]
        rintro _ _ ⟨⟩
        refine' ⟨Z, pullback.snd, π, ⟨_, by rw [pullback.condition]⟩⟩
        rw [hπ]
        exact Presieve.ofArrows.mk ()

variable [HasPullbackOfIsIsodesc C] {C}

lemma isPullbackSieve_ExtensiveSieve {X : C} {S : Presieve X}
    (hS : S ∈ ExtensiveSieve X) : isPullbackPresieve S := by
  rcases hS with ⟨α, _, Z, π, hS, HIso⟩
  intro Y₁ Y₂ f hf g hg
  rw [hS] at hf hg
  cases' hg with b
  apply HasPullbackOfIsIsodesc.HasPullback f

def v {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) : α → Σ(Y : C), { f : Y ⟶ X // S f } :=
  fun a => ⟨Z a, π a, hS ▸ Presieve.ofArrows.mk a⟩

lemma vsurj {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) : Function.Surjective (v hS) := fun ⟨Y, ⟨f, hf⟩⟩ => by
  cases' (hS ▸ hf) with a h
  exact ⟨a, rfl⟩

lemma v.fst {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (a : α) : (v hS a).1 = Z a := rfl

lemma v.snd {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (a : α) : (v hS a).2.1 = π a := rfl

noncomputable
def FintypeT {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
     (hS: S = Presieve.ofArrows Z π) : Fintype (Σ(Y : C), { f : Y ⟶ X // S f }) := by
  classical
  exact Fintype.ofSurjective _ (vsurj hS)

lemma HasProductT {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
     (hS: S = Presieve.ofArrows Z π) : HasProduct
     fun (f : (Σ(Y : C), { f : Y ⟶ X // S f })) => (op f.1) := by
  suffices Finite (Σ(Y : C), { f : Y ⟶ X // S f }) by
    · infer_instance
  exact Fintype.finite <| FintypeT hS

noncomputable
def comparisoninv {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) (F : Cᵒᵖ ⥤ Type max u v) :
    haveI := HasProductT hS
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ X // S f })) => F.obj (op f.1)) ⟶
    ∏ fun a => F.obj (op (Z a)) :=
  haveI := HasProductT hS
  Pi.lift (fun a => Pi.π _ (v hS a) ≫ F.map (𝟙 _))

noncomputable
def fromFirst {α : Type} [Fintype α] {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} {S : Presieve X}
    (hS: S = Presieve.ofArrows Z π) {F : Cᵒᵖ ⥤ Type max u v} (hF : PreservesFiniteProducts F)
    (HIso : IsIso (Sigma.desc π)) :
    Equalizer.FirstObj F S ⟶ F.obj (op X) :=
  haveI : PreservesLimit (Discrete.functor fun a => op (Z a)) F := by
    haveI := (hF.preserves α); infer_instance
  comparisoninv hS F ≫ ((Limits.PreservesProduct.iso F (fun a => op <| Z a)).inv ≫
    F.map (CoprodToProd Z).inv ≫ F.map (inv (Sigma.desc π).op))

lemma piCompInvdesc {α : Type} [Fintype α] {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X)
    (HIso : IsIso (Sigma.desc π)) (a : α) : π a ≫ inv (Sigma.desc π) = Sigma.ι _ a := by
  simp

lemma PreservesProduct.isoInvCompMap {C : Type u} [Category C] {D : Type v} [Category D] (F : C ⥤ D)
    {J : Type w} {f : J → C} [HasProduct f] [HasProduct (fun j => F.obj (f j))]
    [PreservesLimit (Discrete.functor f) F] (j : J) :
    (PreservesProduct.iso F f).inv ≫ F.map (Pi.π _ j) = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (⟨j⟩ : Discrete J)

lemma isSheafForDagurSieveIsIsoFork {X : C} {S : Presieve X} (hS : S ∈ ExtensiveSieve X)
    {F : Cᵒᵖ ⥤ Type max u v}
    (hF : PreservesFiniteProducts F) :
    IsIso (Equalizer.forkMap F S) := by
  rcases hS with ⟨α, _, Z, π, hS, HIso⟩
  haveI : PreservesLimit (Discrete.functor fun a => op (Z a)) F := by
      haveI := (hF.preserves α); infer_instance
  refine' ⟨fromFirst hS hF HIso, _, _⟩
  · unfold fromFirst
    simp only [← Category.assoc]
    rw [Functor.map_inv, IsIso.comp_inv_eq, Category.id_comp, ← Functor.mapIso_inv,
      Iso.comp_inv_eq, Functor.mapIso_hom, Iso.comp_inv_eq, ← Functor.map_comp, descOpCompCoprodToProd]
    have : F.map (Pi.lift fun a => (π a).op) ≫ (PreservesProduct.iso F fun a => op (Z a)).hom =
      Pi.lift (fun a => F.map ((Sigma.ι Z a ≫ (Sigma.desc π)).op)) := by simp --this can be a general lemma
    erw [this]
    refine' funext (fun s => _)
    simp only [types_comp_apply, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    ext a
    rw [Types.Limit.lift_π_apply]
    dsimp [comparisoninv]
    simp_rw [v.fst]
    simp only [Functor.map_id, Category.comp_id]
    rw [Types.Limit.lift_π_apply]
    simp only [Fan.mk_pt, Equalizer.forkMap, Fan.mk_π_app, Types.pi_lift_π_apply, v.snd]
  · refine' Limits.Pi.hom_ext _ _ (fun f => _)
    dsimp [Equalizer.forkMap]
    rw [Category.id_comp, Category.assoc, limit.lift_π, Limits.Fan.mk_π_app]
    simp only
    obtain ⟨a, ha⟩ := vsurj hS f
    unfold fromFirst
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← op_inv, ← op_comp, ← ha, v.snd hS, piCompInvdesc,
      ← Functor.map_comp, CoprodToProdInvComp.ι, @PreservesProduct.isoInvCompMap _ _ _ _ F _ _ _ _ (_) a]
    simp only [comparisoninv, op_id, limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    erw [F.map_id, Category.comp_id]

lemma isSheafForExtensiveSieve {X : C} {S : Presieve X} (hS : S ∈ ExtensiveSieve X)
    {F : Cᵒᵖ ⥤ Type max u v}
    (hF : PreservesFiniteProducts F) :
    Presieve.IsSheafFor F S := by
  refine' (Equalizer.Presieve.sheaf_condition' F <| isPullbackSieve_ExtensiveSieve hS).2 _
  rw [Limits.Types.type_equalizer_iff_unique]
  dsimp [Equalizer.FirstObj]
  suffices IsIso (Equalizer.forkMap F S) by
    · intro y _
      refine' ⟨inv (Equalizer.forkMap F S) y, _, fun y₁ hy₁ => _⟩
      · change (inv (Equalizer.forkMap F S) ≫ (Equalizer.forkMap F S)) y = y
        rw [IsIso.inv_hom_id, types_id_apply]
      · replace hy₁ := congr_arg (inv (Equalizer.forkMap F S)) hy₁
        change ((Equalizer.forkMap F S) ≫ inv (Equalizer.forkMap F S)) _ = _ at hy₁
        rwa [IsIso.hom_inv_id, types_id_apply] at hy₁
  exact isSheafForDagurSieveIsIsoFork hS hF

end CategoryTheory

end Coverage

end ExtensiveRegular

section StoneanProjective -- This section is PR #5808

open CategoryTheory

namespace Stonean

/-- Every Stonean space is projective in `CompHaus` -/
instance (X : Stonean) : Projective X.compHaus where
  factors := by
    intro B C φ f _
    haveI : ExtremallyDisconnected X.compHaus.toTop := X.extrDisc
    have hf : f.1.Surjective
    · rwa [CompHaus.epi_iff_surjective] at *
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.continuous f.continuous hf
    use ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

end Stonean

namespace CompHaus

/-- If `X` is compact Hausdorff, `presentation X` is an extremally disconnected space
  equipped with an epimorphism down to `X`. It is a "constructive" witness to the
  fact that `CompHaus` has enough projectives.  -/
noncomputable
def presentation (X : CompHaus) : Stonean where
  compHaus := (projectivePresentation X).p
  extrDisc := by
    refine' CompactT2.Projective.extremallyDisconnected
      (@fun Y Z _ _ _ _ _ _ f g hfcont hgcont hgsurj => _)
    let g₁ : (CompHaus.of Y) ⟶ (CompHaus.of Z) := ⟨g, hgcont⟩
    let f₁ : (projectivePresentation X).p ⟶ (CompHaus.of Z) := ⟨f, hfcont⟩
    have hg₁ : Epi g₁ := (epi_iff_surjective _).2 hgsurj
    refine' ⟨Projective.factorThru f₁ g₁, (Projective.factorThru f₁ g₁).2, funext (fun _ => _)⟩
    change (Projective.factorThru f₁ g₁ ≫ g₁) _ = f _
    rw [Projective.factorThru_comp]
    rfl

/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentation.π (X : CompHaus) : X.presentation.compHaus ⟶ X :=
  (projectivePresentation X).f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance presentation.epi_π (X : CompHaus) : Epi (π X) :=
  (projectivePresentation X).epi

/--

               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y

If `Z` is extremally disconnected, X, Y are compact Hausdorff, if `f : X ⟶ Y` is an epi and
`e : Z ⟶ Y` is arbitrary, then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism
`Z ⟶ X`. It exists because `Z` is a projective object in `CompHaus`.
-/
noncomputable
def lift {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Z.compHaus ⟶ X :=
  Projective.factorThru e f

@[simp, reassoc]
lemma lift_lifts {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]

lemma Gleason (X : CompHaus.{u}) :
    Projective X ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    show ExtremallyDisconnected X.toStonean
    infer_instance
  · intro h
    let X' : Stonean := ⟨X⟩
    show Projective X'.compHaus
    apply Stonean.instProjectiveCompHausCategoryCompHaus

end CompHaus

end StoneanProjective

section OpenEmbedding

open CategoryTheory Limits

namespace Stonean

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso {X Y : Stonean} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.1
  invFun := f.2
  left_inv x := Iso.hom_inv_id_apply f x -- why doesn't `simp` work?
  right_inv x := Iso.inv_hom_id_apply f x -- why doesn't `simp` work?
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

/--
A coproduct cocone associated to the explicit finite coproduct with cone point `finiteCoproduct X`.
-/
@[simps]
def finiteCoproduct.explicitCocone {α : Type} [Fintype α] (Z : α → Stonean.{u}) :
    Limits.Cocone (Discrete.functor Z) where
  pt := finiteCoproduct Z
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι Z a

/--
The more explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def finiteCoproduct.isColimit' {α : Type} [Fintype α] (Z : α → Stonean.{u})  :
    Limits.IsColimit (finiteCoproduct.explicitCocone Z) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

/-- The isomorphism from the explicit finite coproducts to the abstract coproduct. -/
noncomputable
def coproductIsoCoproduct {α : Type} [Fintype α] (Z : α → Stonean.{u}) :
    finiteCoproduct Z ≅ ∐ Z :=
  Limits.IsColimit.coconePointUniqueUpToIso
    (finiteCoproduct.isColimit' Z) (Limits.colimit.isColimit _)

lemma finiteCoproduct.ιOpenEmbedding {α : Type} [Fintype α] (Z : α → Stonean.{u}) (a : α) :
    OpenEmbedding (finiteCoproduct.ι Z a) := by
  exact openEmbedding_sigmaMk (σ := fun a => (Z a))

lemma openEmbedding_ι {α : Type} [Fintype α] (Z : α → Stonean.{u}) (a : α) :
    OpenEmbedding (Sigma.ι Z a) := by
  refine' OpenEmbedding.of_comp _ (homeoOfIso (coproductIsoCoproduct Z).symm).openEmbedding _
  convert finiteCoproduct.ιOpenEmbedding Z a
  ext x
  change ((Sigma.ι Z a) ≫ (coproductIsoCoproduct Z).inv) x = _
  simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv,
    finiteCoproduct.explicitCocone_pt, finiteCoproduct.explicitCocone_ι, Discrete.natTrans_app]

end Stonean

end OpenEmbedding

section CompHausExplicitSheaves

open CategoryTheory CompHaus Opposite CategoryTheory.Limits Functor Presieve

namespace CompHaus

lemma extensivity_injective {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} {π : (a : α) → Z a ⟶ X} {Y : CompHaus.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (π a) ≫ finiteCoproduct.ι Z a )
  let σ := finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))
  let β := finiteCoproduct.desc _ π
  have comm : ζ ≫ β = σ ≫ f := by
     refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
     simp [← Category.assoc, finiteCoproduct.ι_desc, pullback.condition]
  intro R₁ R₂ hR
  have himage : (ζ ≫ β) R₁ = (ζ ≫ β) R₂ := by
    rw [comm]; change f (σ R₁) = f (σ R₂); rw [hR]
  replace himage := congr_arg (inv β) himage
  change ((ζ ≫ β ≫ inv β) R₁) = ((ζ ≫ β ≫ inv β) R₂) at himage
  rw [IsIso.hom_inv_id, Category.comp_id] at himage
  have Hfst : R₁.fst = R₂.fst := by
    suffices (ζ R₁).1 = R₁.1 ∧ (ζ R₂).1 = R₂.1 by
      · rw [← this.1, ← this.2, himage]
    constructor <;> rfl
  obtain ⟨a₁, r₁, h₁⟩ := finiteCoproduct.ι_jointly_surjective _ R₁
  obtain ⟨a₂, r₂, h₂⟩ := finiteCoproduct.ι_jointly_surjective _ R₂
  have ha₁ : a₁ = R₁.fst := (congrArg Sigma.fst h₁).symm
  have ha₂ : a₂ = R₂.fst := (congrArg Sigma.fst h₂).symm
  have ha : a₁ = a₂ := by rwa [ha₁, ha₂]
  have : R₁ ∈ Set.range (finiteCoproduct.ι _ a₂)
  · rw [← ha, h₁]
    simp only [Set.mem_range, exists_apply_eq_apply]
  obtain ⟨xr', hr'⟩ := this
  rw [← hr', h₂] at hR
  have hf : ∀ (a : α), Function.Injective
      ((finiteCoproduct.ι _ a) ≫ (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))))
  · intro a
    simp only [finiteCoproduct.ι_desc]
    intro x y h
    have h₁ := h
    apply_fun f at h
    change (pullback.fst f (π a) ≫ f) x = _ at h
    have h' := h.symm
    change (pullback.fst f (π a) ≫ f) y = _ at h'
    rw [pullback.condition] at h'
    have : Function.Injective (π a)
    · intro r s hrs
      rw [← finiteCoproduct.ι_desc_apply] at hrs
      have hrs' := hrs.symm
      rw [← finiteCoproduct.ι_desc_apply] at hrs'
      have : Function.Injective (finiteCoproduct.desc (fun a ↦ Z a) π)
      · apply Function.Bijective.injective
        exact ConcreteCategory.bijective_of_isIso _
      exact (finiteCoproduct.ι_injective _ a (this hrs')).symm
    have h₂ := this h'
    suffices : x.val = y.val
    · exact Subtype.ext this
    exact Prod.ext h₁ h₂.symm
  have := hf a₂ hR
  rw [← hr', h₂, this]

lemma extensivity_explicit {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} {π : (a : α) → Z a ⟶ X} {Y : CompHaus.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
     IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let β := finiteCoproduct.desc _ π
  apply isIso_of_bijective _
  refine' ⟨extensivity_injective f HIso, fun y => _⟩
  refine' ⟨⟨(inv β (f y)).1, ⟨⟨y, (inv β (f y)).2⟩, _⟩⟩, rfl⟩
  have inj : Function.Injective (inv β) := by --this should be obvious
    intros r s hrs
    convert congr_arg β hrs <;> change _ = (inv β ≫ β) _<;> simp only [IsIso.inv_hom_id]<;> rfl
  apply inj
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by
    · apply Eq.symm
      change (_ ≫ inv β) _ = _
      rw [this]
      rfl
  intro a
  simp only [IsIso.comp_inv_eq, finiteCoproduct.ι_desc]

lemma extensivity : Extensivity CompHaus := @fun α _ X Z i Y f H => by
  let θ := Sigma.mapIso (fun a => pullbackIsoPullback f (i a))
  suffices IsIso (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
    · apply IsIso.of_isIso_comp_left θ.hom
  let δ := coproductIsoCoproduct (fun a => CompHaus.pullback f (i a))
  suffices IsIso <| δ.hom ≫ (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
    · apply IsIso.of_isIso_comp_left δ.hom
  have HIso : IsIso (finiteCoproduct.desc _ i) := by
    suffices IsIso <| (coproductIsoCoproduct Z).inv ≫ (finiteCoproduct.desc _ i) by
      · apply IsIso.of_isIso_comp_left (coproductIsoCoproduct Z).inv
    convert H
    refine' Sigma.hom_ext _ _ (fun a => _)
    simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc,
      Discrete.functor_obj, finiteCoproduct.cocone_pt, finiteCoproduct.cocone_ι,
      Discrete.natTrans_app, finiteCoproduct.ι_desc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
  convert extensivity_explicit f HIso
  refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
  rw [finiteCoproduct.ι_desc, ← Category.assoc, ← Sigma.ι_comp_toFiniteCoproduct]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, pullbackIsoPullback, mapIso_hom,
    colim_map, colimit.map_desc, colimit.ι_desc, Cocones.precompose_obj_pt, Cofan.mk_pt,
    Cocones.precompose_obj_ι, NatTrans.comp_app, Discrete.functor_obj, const_obj_obj,
    Discrete.natIso_hom_app, Cofan.mk_ι_app, limit.conePointUniqueUpToIso_hom_comp,
    pullback.cone_pt, pullback.cone_π]

lemma epi_pullback_of_epi : EpiPullbackOfEpi CompHaus := by
  intro X Y Z f π hπ
  suffices : Epi ((pullbackIsoPullback f π).hom ≫ (Limits.pullback.fst : Limits.pullback f π ⟶ Y))
  · exact @epi_of_epi _ _ _ _ _ _ _ this
  rw [CompHaus.epi_iff_surjective] at hπ ⊢
  intro y
  obtain ⟨z,hz⟩ := hπ (f y)
  simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
    pullback.cone_π]
  exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

lemma extensiveRegular_generates_coherent :
    (ExtensiveRegularCoverage' CompHaus epi_pullback_of_epi extensivity).toGrothendieck =
    (coherentTopology CompHaus) := by
  ext X S
  constructor
  <;> intro h
  · dsimp [Coverage.toGrothendieck] at *
    induction h with
    | of Y T hT =>
      · apply Coverage.saturate.of
        dsimp [coherentCoverage]
        dsimp [ExtensiveRegularCoverage'] at hT
        apply Or.elim hT
        <;> intro h
        · obtain ⟨α, x, Xmap, π, h⟩ := h
          use α
          use x
          use Xmap
          use π
          refine' ⟨h.1,_⟩
          have he := (effectiveEpiFamily_tfae Xmap π).out 0 1
          rw [he]
          letI := h.2
          exact inferInstance
        · obtain ⟨Z, f, h⟩ := h
          use Unit
          use inferInstance
          use (fun _ ↦ Z)
          use (fun _ ↦ f)
          refine' ⟨h.1,_⟩
          have he := (effectiveEpiFamily_tfae (fun (_ : Unit) ↦ Z) (fun _ ↦ f)).out 0 1
          rw [he]
          rw [CompHaus.epi_iff_surjective _] at h ⊢
          intro x
          obtain ⟨y,hy⟩ := h.2 x
          use Sigma.ι (fun (_ : Unit) ↦ Z) Unit.unit y
          rw [← hy]
          suffices : (f : Z → Y) = Sigma.ι (fun (_ : Unit) ↦ Z) Unit.unit ≫ Sigma.desc (fun _ ↦ f)
          · rw [this]
            rfl
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    | top =>
      · apply Coverage.saturate.top
    | transitive Y T =>
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption
  · induction h with
    | of Y T hT =>
      · dsimp [coherentCoverage] at hT
        obtain ⟨I, hI, Xmap, f, ⟨h, hT⟩⟩ := hT
        have he := (effectiveEpiFamily_tfae Xmap f).out 0 1
        rw [he] at hT
        let φ := fun (i : I) ↦ Sigma.ι Xmap i
        let F := Sigma.desc f
        let Z := Sieve.generate T
        let Xs := (∐ fun (i : I) => Xmap i)
        let Zf : Sieve Y := Sieve.generate
          (Presieve.ofArrows (fun (_ : Unit) ↦ Xs) (fun (_ : Unit) ↦ F))
        apply Coverage.saturate.transitive Y Zf
        · apply Coverage.saturate.of
          dsimp [ExtensiveRegularCoverage']
          simp only [Set.mem_union, Set.mem_setOf_eq]
          right
          use Xs
          use F
        · intro R g hZfg
          dsimp at hZfg
          rw [Presieve.ofArrows_pUnit] at hZfg
          obtain ⟨W, ψ, σ, ⟨hW, hW'⟩⟩ := hZfg
          dsimp [Presieve.singleton] at hW
          induction hW
          rw [← hW', Sieve.pullback_comp Z]
          suffices : Sieve.pullback ψ ((Sieve.pullback F) Z) ∈ GrothendieckTopology.sieves
            (ExtensiveRegularCoverage' _ _ _).toGrothendieck R
          · exact this
          apply GrothendieckTopology.pullback_stable'
          dsimp [Coverage.toGrothendieck]
          suffices : Coverage.saturate (ExtensiveRegularCoverage' _ _ _) Xs (Z.pullback F)
          · exact this
          suffices : Sieve.generate (Presieve.ofArrows Xmap φ) ≤ Z.pullback F
          · apply Coverage.saturate_of_superset _ this
            apply Coverage.saturate.of
            dsimp [ExtensiveRegularCoverage']
            left
            refine' ⟨I, hI, Xmap, φ, ⟨rfl, _⟩⟩
            suffices : Sigma.desc φ = 𝟙 _
            · rw [this]
              exact inferInstance
            ext
            simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Category.comp_id]
          intro Q q hq
          simp only [Sieve.pullback_apply, Sieve.generate_apply]
          simp only [Sieve.generate_apply] at hq
          obtain ⟨E, e, r, hq⟩ := hq
          refine' ⟨E, e, r ≫ F, ⟨_, _⟩⟩
          · rw [h]
            induction hq.1
            dsimp
            simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
            exact Presieve.ofArrows.mk _
          · rw [← hq.2]
            rfl
    | top =>
      · apply Coverage.saturate.top
    | transitive Y T =>
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption

def MapToEqualizer (P : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) {W X B : CompHaus} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  fun t ↦ ⟨P.map f.op t, by
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _ ;
    simp_rw [← P.map_comp, ← op_comp, w] ⟩

def EqualizerCondition (P : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := ∀
  (X B : CompHaus) (π : X ⟶ B) (_ : Function.Surjective π),
  Function.Bijective (MapToEqualizer P π (CompHaus.pullback.fst π π) (CompHaus.pullback.snd π π)
      (CompHaus.pullback.condition _ _))

noncomputable
def EqualizerFirstObjIso (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) {B X : CompHaus} (π : X ⟶ B)
     : Equalizer.FirstObj F (Presieve.singleton π) ≅ F.obj (op X) :=
  CategoryTheory.Equalizer.firstObjEqFamily F (Presieve.singleton π) ≪≫
  { hom := fun e ↦ e π (Presieve.singleton_self π)
    inv := fun e _ _ h ↦ by
      induction h with
      | mk => exact e
    hom_inv_id := by
      funext _ _ _ h
      induction h with
      | mk => rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso_aux (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) {B X : CompHaus} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Limits.pullback π π)) :=
  Types.productIso.{u+1, u+1} _ ≪≫
  { hom := fun e ↦ e (⟨X, ⟨π, Presieve.singleton_self π⟩⟩, ⟨X, ⟨π, Presieve.singleton_self π⟩⟩)
    inv := fun x ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩ ↦ by
      induction h₁
      induction h₂
      exact x
    hom_inv_id := by
      funext _ ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩
      induction h₁
      induction h₂
      rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) {B X : CompHaus} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (CompHaus.pullback π π)) :=
  EqualizerSecondObjIso_aux F π ≪≫ (F.mapIso ((pullbackIsoPullback π π).op :
    op (Limits.pullback π π) ≅ op (CompHaus.pullback π π)))

lemma isSheafFor_of_Dagur {B : CompHaus} {S : Presieve B}
    (hS : S ∈ (ExtensiveRegularCoverage' CompHaus epi_pullback_of_epi extensivity).covering B)
    {F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)} (hFpfp : PreservesFiniteProducts F)
    (hFecs : EqualizerCondition F) :
    S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · exact isSheafForExtensiveSieve hSIso hFpfp
  · rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
    intro y h
    dsimp [RegularSieve] at hSSingle
    obtain ⟨X, π, ⟨hS, πsurj⟩⟩ := hSSingle
    rw [Presieve.ofArrows_pUnit] at hS
    subst hS
    rw [CompHaus.epi_iff_surjective] at πsurj
    specialize hFecs X B π πsurj
    have fork_comp : Equalizer.forkMap F (Presieve.singleton π) ≫ (EqualizerFirstObjIso F π).hom =
        F.map π.op
    · dsimp [EqualizerFirstObjIso, Equalizer.forkMap]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have fmap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.fst π π).op =
        Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom
    · dsimp [EqualizerSecondObjIso]
      have : CompHaus.pullback.fst π π = (pullbackIsoPullback π π).hom ≫ Limits.pullback.fst
      · simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
          pullback.cone_π]
      rw [this, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.fst.op =
          Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom
      · simp only [← Category.assoc]
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.firstMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have smap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.snd π π).op =
        Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom
    · dsimp [EqualizerSecondObjIso]
      have : CompHaus.pullback.snd π π = (pullbackIsoPullback π π).hom ≫ Limits.pullback.snd
      · simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
          pullback.cone_π]
      rw [this, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.snd.op =
          Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom
      · simp only [← Category.assoc]
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.secondMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have iy_mem : F.map (pullback.fst π π).op ((EqualizerFirstObjIso F π).hom y) =
        F.map (pullback.snd π π).op ((EqualizerFirstObjIso F π).hom y)
    · change ((EqualizerFirstObjIso F π).hom ≫ _) y = _
      apply Eq.symm -- how do I avoid this ugly hack?
      change ((EqualizerFirstObjIso F π).hom ≫ _) y = _
      rw [fmap_comp, smap_comp]
      dsimp
      rw [h]
    have uniq_F : ∃! x, F.map π.op x = (EqualizerFirstObjIso F π).hom y
    · rw [Function.bijective_iff_existsUnique] at hFecs
      specialize hFecs ⟨(EqualizerFirstObjIso F π).hom y, iy_mem⟩
      obtain ⟨x, hx⟩ := hFecs
      refine' ⟨x, _⟩
      dsimp [MapToEqualizer] at *
      refine' ⟨Subtype.ext_iff.mp hx.1,_⟩
      intro z hz
      apply hx.2
      rwa [Subtype.ext_iff]
    obtain ⟨x,hx⟩ := uniq_F
    dsimp at hx
    rw [← fork_comp] at hx
    use x
    dsimp
    constructor
    · apply_fun (EqualizerFirstObjIso F π).hom
      · exact hx.1
      · apply Function.Bijective.injective
        rw [← isIso_iff_bijective]
        exact inferInstance
    · intro z hz
      apply_fun (EqualizerFirstObjIso F π).hom at hz
      exact hx.2 z hz

theorem final (A : Type (u+2)) [Category.{u+1} A] {F : CompHaus.{u}ᵒᵖ ⥤ A}
    (hF : PreservesFiniteProducts F)
    (hF' : ∀ (E : A), EqualizerCondition (F ⋙ coyoneda.obj (op E))) :
  Presheaf.IsSheaf (coherentTopology CompHaus) F := by
  rw [← extensiveRegular_generates_coherent]
  refine' fun E => (Presieve.isSheaf_coverage _ _).2 _
  intro B S hS
  apply isSheafFor_of_Dagur hS
  · exact ⟨fun J inst => have := hF.1; compPreservesLimitsOfShape _ _⟩
  · exact hF' E

theorem final' (A : Type (u+2)) [Category.{u+1} A] {G : A ⥤ Type (u+1)}
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G]
    {F : CompHaus.{u}ᵒᵖ ⥤ A}
    (hF : PreservesFiniteProducts (F ⋙ G)) (hF' : EqualizerCondition (F ⋙ G)) :
    Presheaf.IsSheaf (coherentTopology CompHaus) F := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology CompHaus) F G,
    isSheaf_iff_isSheaf_of_type, ← extensiveRegular_generates_coherent, Presieve.isSheaf_coverage]
  intro B S' hS
  exact isSheafFor_of_Dagur hS hF hF'

end CompHaus

end CompHausExplicitSheaves

section ProfiniteExplicitSheaves

open CategoryTheory Profinite Opposite CategoryTheory.Limits Functor Presieve

namespace Profinite

lemma extensivity_injective {α : Type} [Fintype α] {X : Profinite.{u}}
    {Z : α → Profinite.{u}} {π : (a : α) → Z a ⟶ X} {Y : Profinite.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
    Function.Injective (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let ζ := finiteCoproduct.desc _ (fun a => pullback.snd f (π a) ≫ finiteCoproduct.ι Z a )
  let σ := finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))
  let β := finiteCoproduct.desc _ π
  have comm : ζ ≫ β = σ ≫ f := by
     refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
     simp [← Category.assoc, finiteCoproduct.ι_desc, pullback.condition]
  intro R₁ R₂ hR
  have himage : (ζ ≫ β) R₁ = (ζ ≫ β) R₂ := by
    rw [comm]; change f (σ R₁) = f (σ R₂); rw [hR]
  replace himage := congr_arg (inv β) himage
  change ((ζ ≫ β ≫ inv β) R₁) = ((ζ ≫ β ≫ inv β) R₂) at himage
  rw [IsIso.hom_inv_id, Category.comp_id] at himage
  have Hfst : R₁.fst = R₂.fst := by
    suffices (ζ R₁).1 = R₁.1 ∧ (ζ R₂).1 = R₂.1 by
      · rw [← this.1, ← this.2, himage]
    constructor <;> rfl
  obtain ⟨a₁, r₁, h₁⟩ := finiteCoproduct.ι_jointly_surjective _ R₁
  obtain ⟨a₂, r₂, h₂⟩ := finiteCoproduct.ι_jointly_surjective _ R₂
  have ha₁ : a₁ = R₁.fst := (congrArg Sigma.fst h₁).symm
  have ha₂ : a₂ = R₂.fst := (congrArg Sigma.fst h₂).symm
  have ha : a₁ = a₂ := by rwa [ha₁, ha₂]
  have : R₁ ∈ Set.range (finiteCoproduct.ι _ a₂)
  · rw [← ha, h₁]
    simp only [Set.mem_range, exists_apply_eq_apply]
  obtain ⟨xr', hr'⟩ := this
  rw [← hr', h₂] at hR
  have hf : ∀ (a : α), Function.Injective
      ((finiteCoproduct.ι _ a) ≫ (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))))
  · intro a
    simp only [finiteCoproduct.ι_desc]
    intro x y h
    have h₁ := h
    apply_fun f at h
    change (pullback.fst f (π a) ≫ f) x = _ at h
    have h' := h.symm
    change (pullback.fst f (π a) ≫ f) y = _ at h'
    rw [pullback.condition] at h'
    have : Function.Injective (π a)
    · intro r s hrs
      rw [← finiteCoproduct.ι_desc_apply] at hrs
      have hrs' := hrs.symm
      rw [← finiteCoproduct.ι_desc_apply] at hrs'
      have : Function.Injective (finiteCoproduct.desc (fun a ↦ Z a) π)
      · apply Function.Bijective.injective
        exact ConcreteCategory.bijective_of_isIso _
      exact (finiteCoproduct.ι_injective _ a (this hrs')).symm
    have h₂ := this h'
    suffices : x.val = y.val
    · exact Subtype.ext this
    exact Prod.ext h₁ h₂.symm
  have := hf a₂ hR
  rw [← hr', h₂, this]

lemma extensivity_explicit {α : Type} [Fintype α] {X : Profinite.{u}}
    {Z : α → Profinite.{u}} {π : (a : α) → Z a ⟶ X} {Y : Profinite.{u}} (f : Y ⟶ X)
    (HIso : IsIso (finiteCoproduct.desc _ π)) :
     IsIso (finiteCoproduct.desc _ ((fun a => pullback.fst f (π a)))) := by
  let β := finiteCoproduct.desc _ π
  apply isIso_of_bijective _
  refine' ⟨extensivity_injective f HIso, fun y => _⟩
  refine' ⟨⟨(inv β (f y)).1, ⟨⟨y, (inv β (f y)).2⟩, _⟩⟩, rfl⟩
  have inj : Function.Injective (inv β) := by --this should be obvious
    intros r s hrs
    convert congr_arg β hrs <;> change _ = (inv β ≫ β) _<;> simp only [IsIso.inv_hom_id]<;> rfl
  apply inj
  suffices ∀ a, π a ≫ inv β = finiteCoproduct.ι _ a by
    · apply Eq.symm
      change (_ ≫ inv β) _ = _
      rw [this]
      rfl
  intro a
  simp only [IsIso.comp_inv_eq, finiteCoproduct.ι_desc]

lemma extensivity : Extensivity Profinite := @fun α _ X Z i Y f H => by
  let θ := Sigma.mapIso (fun a => pullbackIsoPullback f (i a))
  suffices IsIso (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
    · apply IsIso.of_isIso_comp_left θ.hom
  let δ := coproductIsoCoproduct (fun a => Profinite.pullback f (i a))
  suffices IsIso <| δ.hom ≫ (θ.hom ≫ Sigma.desc fun x => Limits.pullback.fst) by
    · apply IsIso.of_isIso_comp_left δ.hom
  have HIso : IsIso (finiteCoproduct.desc _ i) := by
    suffices IsIso <| (coproductIsoCoproduct Z).inv ≫ (finiteCoproduct.desc _ i) by
      · apply IsIso.of_isIso_comp_left (coproductIsoCoproduct Z).inv
    convert H
    refine' Sigma.hom_ext _ _ (fun a => _)
    simp only [coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc,
      Discrete.functor_obj, finiteCoproduct.cocone_pt, finiteCoproduct.cocone_ι,
      Discrete.natTrans_app, finiteCoproduct.ι_desc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
  convert extensivity_explicit f HIso
  refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
  rw [finiteCoproduct.ι_desc, ← Category.assoc, ← Sigma.ι_comp_toFiniteCoproduct]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, pullbackIsoPullback, mapIso_hom,
    colim_map, colimit.map_desc, colimit.ι_desc, Cocones.precompose_obj_pt, Cofan.mk_pt,
    Cocones.precompose_obj_ι, NatTrans.comp_app, Discrete.functor_obj, const_obj_obj,
    Discrete.natIso_hom_app, Cofan.mk_ι_app, limit.conePointUniqueUpToIso_hom_comp,
    pullback.cone_pt, pullback.cone_π]

lemma epi_pullback_of_epi : EpiPullbackOfEpi Profinite := by
  intro X Y Z f π hπ
  suffices : Epi ((pullbackIsoPullback f π).hom ≫ (Limits.pullback.fst : Limits.pullback f π ⟶ Y))
  · exact @epi_of_epi _ _ _ _ _ _ _ this
  rw [Profinite.epi_iff_surjective] at hπ ⊢
  intro y
  obtain ⟨z,hz⟩ := hπ (f y)
  simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
    pullback.cone_π]
  exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

lemma extensiveRegular_generates_coherent :
    (ExtensiveRegularCoverage' Profinite epi_pullback_of_epi extensivity).toGrothendieck =
    (coherentTopology Profinite) := by
  ext X S
  constructor
  <;> intro h
  · dsimp [Coverage.toGrothendieck] at *
    induction h with
    | of Y T hT =>
      · apply Coverage.saturate.of
        dsimp [coherentCoverage]
        dsimp [ExtensiveRegularCoverage'] at hT
        apply Or.elim hT
        <;> intro h
        · obtain ⟨α, x, Xmap, π, h⟩ := h
          use α
          use x
          use Xmap
          use π
          refine' ⟨h.1,_⟩
          have he := (effectiveEpiFamily_tfae Xmap π).out 0 1
          rw [he]
          letI := h.2
          exact inferInstance
        · obtain ⟨Z, f, h⟩ := h
          use Unit
          use inferInstance
          use (fun _ ↦ Z)
          use (fun _ ↦ f)
          refine' ⟨h.1,_⟩
          have he := (effectiveEpiFamily_tfae (fun (_ : Unit) ↦ Z) (fun _ ↦ f)).out 0 1
          rw [he]
          rw [Profinite.epi_iff_surjective _] at h ⊢
          intro x
          obtain ⟨y,hy⟩ := h.2 x
          use Sigma.ι (fun (_ : Unit) ↦ Z) Unit.unit y
          rw [← hy]
          suffices : (f : Z → Y) = Sigma.ι (fun (_ : Unit) ↦ Z) Unit.unit ≫ Sigma.desc (fun _ ↦ f)
          · rw [this]
            rfl
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    | top =>
      · apply Coverage.saturate.top
    | transitive Y T =>
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption
  · induction h with
    | of Y T hT =>
      · dsimp [coherentCoverage] at hT
        obtain ⟨I, hI, Xmap, f, ⟨h, hT⟩⟩ := hT
        have he := (effectiveEpiFamily_tfae Xmap f).out 0 1
        rw [he] at hT
        let φ := fun (i : I) ↦ Sigma.ι Xmap i
        let F := Sigma.desc f
        let Z := Sieve.generate T
        let Xs := (∐ fun (i : I) => Xmap i)
        let Zf : Sieve Y := Sieve.generate
          (Presieve.ofArrows (fun (_ : Unit) ↦ Xs) (fun (_ : Unit) ↦ F))
        apply Coverage.saturate.transitive Y Zf
        · apply Coverage.saturate.of
          dsimp [ExtensiveRegularCoverage']
          simp only [Set.mem_union, Set.mem_setOf_eq]
          right
          use Xs
          use F
        · intro R g hZfg
          dsimp at hZfg
          rw [Presieve.ofArrows_pUnit] at hZfg
          obtain ⟨W, ψ, σ, ⟨hW, hW'⟩⟩ := hZfg
          dsimp [Presieve.singleton] at hW
          induction hW
          rw [← hW', Sieve.pullback_comp Z]
          suffices : Sieve.pullback ψ ((Sieve.pullback F) Z) ∈ GrothendieckTopology.sieves
            (ExtensiveRegularCoverage' _ _ _).toGrothendieck R
          · exact this
          apply GrothendieckTopology.pullback_stable'
          dsimp [Coverage.toGrothendieck]
          suffices : Coverage.saturate (ExtensiveRegularCoverage' _ _ _) Xs (Z.pullback F)
          · exact this
          suffices : Sieve.generate (Presieve.ofArrows Xmap φ) ≤ Z.pullback F
          · apply Coverage.saturate_of_superset _ this
            apply Coverage.saturate.of
            dsimp [ExtensiveRegularCoverage']
            left
            refine' ⟨I, hI, Xmap, φ, ⟨rfl, _⟩⟩
            suffices : Sigma.desc φ = 𝟙 _
            · rw [this]
              exact inferInstance
            ext
            simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Category.comp_id]
          intro Q q hq
          simp only [Sieve.pullback_apply, Sieve.generate_apply]
          simp only [Sieve.generate_apply] at hq
          obtain ⟨E, e, r, hq⟩ := hq
          refine' ⟨E, e, r ≫ F, ⟨_, _⟩⟩
          · rw [h]
            induction hq.1
            dsimp
            simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
            exact Presieve.ofArrows.mk _
          · rw [← hq.2]
            rfl
    | top =>
      · apply Coverage.saturate.top
    | transitive Y T =>
      · apply Coverage.saturate.transitive Y T
        · assumption
        · assumption

def MapToEqualizer (P : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {W X B : Profinite} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  fun t ↦ ⟨P.map f.op t, by
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _ ;
    simp_rw [← P.map_comp, ← op_comp, w] ⟩

def EqualizerCondition (P : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := ∀
  (X B : Profinite) (π : X ⟶ B) (_ : Function.Surjective π),
  Function.Bijective (MapToEqualizer P π (Profinite.pullback.fst π π) (Profinite.pullback.snd π π)
      (Profinite.pullback.condition _ _))

noncomputable
def EqualizerFirstObjIso (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {B X : Profinite} (π : X ⟶ B)
     : Equalizer.FirstObj F (Presieve.singleton π) ≅ F.obj (op X) :=
  CategoryTheory.Equalizer.firstObjEqFamily F (Presieve.singleton π) ≪≫
  { hom := fun e ↦ e π (Presieve.singleton_self π)
    inv := fun e _ _ h ↦ by
      induction h with
      | mk => exact e
    hom_inv_id := by
      funext _ _ _ h
      induction h with
      | mk => rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso_aux (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {B X : Profinite} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Limits.pullback π π)) :=
  Types.productIso.{u+1, u+1} _ ≪≫
  { hom := fun e ↦ e (⟨X, ⟨π, Presieve.singleton_self π⟩⟩, ⟨X, ⟨π, Presieve.singleton_self π⟩⟩)
    inv := fun x ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩ ↦ by
      induction h₁
      induction h₂
      exact x
    hom_inv_id := by
      funext _ ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩
      induction h₁
      induction h₂
      rfl
    inv_hom_id := by aesop }

noncomputable
def EqualizerSecondObjIso (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) {B X : Profinite} (π : X ⟶ B) :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Profinite.pullback π π)) :=
  EqualizerSecondObjIso_aux F π ≪≫ (F.mapIso ((pullbackIsoPullback π π).op :
    op (Limits.pullback π π) ≅ op (Profinite.pullback π π)))

lemma isSheafFor_of_Dagur {B : Profinite} {S : Presieve B}
    (hS : S ∈ (ExtensiveRegularCoverage' Profinite epi_pullback_of_epi extensivity).covering B)
    {F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} (hFpfp : PreservesFiniteProducts F)
    (hFecs : EqualizerCondition F) :
    S.IsSheafFor F := by
  cases' hS with hSIso hSSingle
  · exact isSheafForExtensiveSieve hSIso hFpfp
  · rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
    intro y h
    dsimp [RegularSieve] at hSSingle
    obtain ⟨X, π, ⟨hS, πsurj⟩⟩ := hSSingle
    rw [Presieve.ofArrows_pUnit] at hS
    subst hS
    rw [Profinite.epi_iff_surjective] at πsurj
    specialize hFecs X B π πsurj
    have fork_comp : Equalizer.forkMap F (Presieve.singleton π) ≫ (EqualizerFirstObjIso F π).hom =
        F.map π.op
    · dsimp [EqualizerFirstObjIso, Equalizer.forkMap]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have fmap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.fst π π).op =
        Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom
    · dsimp [EqualizerSecondObjIso]
      have : Profinite.pullback.fst π π = (pullbackIsoPullback π π).hom ≫ Limits.pullback.fst
      · simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
          pullback.cone_π]
      rw [this, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.fst.op =
          Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom
      · simp only [← Category.assoc]
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.firstMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have smap_comp : (EqualizerFirstObjIso F π).hom ≫ F.map (pullback.snd π π).op =
        Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom
    · dsimp [EqualizerSecondObjIso]
      have : Profinite.pullback.snd π π = (pullbackIsoPullback π π).hom ≫ Limits.pullback.snd
      · simp only [pullbackIsoPullback, limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt,
          pullback.cone_π]
      rw [this, op_comp, Functor.map_comp]
      suffices : (EqualizerFirstObjIso F π).hom ≫ F.map Limits.pullback.snd.op =
          Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso_aux F π).hom
      · simp only [← Category.assoc]
        rw [this]
      dsimp [EqualizerFirstObjIso, Equalizer.Presieve.secondMap, EqualizerSecondObjIso_aux]
      ext b
      simp only [types_comp_apply, Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    have iy_mem : F.map (pullback.fst π π).op ((EqualizerFirstObjIso F π).hom y) =
        F.map (pullback.snd π π).op ((EqualizerFirstObjIso F π).hom y)
    · change ((EqualizerFirstObjIso F π).hom ≫ _) y = _
      apply Eq.symm -- how do I avoid this ugly hack?
      change ((EqualizerFirstObjIso F π).hom ≫ _) y = _
      rw [fmap_comp, smap_comp]
      dsimp
      rw [h]
    have uniq_F : ∃! x, F.map π.op x = (EqualizerFirstObjIso F π).hom y
    · rw [Function.bijective_iff_existsUnique] at hFecs
      specialize hFecs ⟨(EqualizerFirstObjIso F π).hom y, iy_mem⟩
      obtain ⟨x, hx⟩ := hFecs
      refine' ⟨x, _⟩
      dsimp [MapToEqualizer] at *
      refine' ⟨Subtype.ext_iff.mp hx.1,_⟩
      intro z hz
      apply hx.2
      rwa [Subtype.ext_iff]
    obtain ⟨x,hx⟩ := uniq_F
    dsimp at hx
    rw [← fork_comp] at hx
    use x
    dsimp
    constructor
    · apply_fun (EqualizerFirstObjIso F π).hom
      · exact hx.1
      · apply Function.Bijective.injective
        rw [← isIso_iff_bijective]
        exact inferInstance
    · intro z hz
      apply_fun (EqualizerFirstObjIso F π).hom at hz
      exact hx.2 z hz

theorem final (A : Type (u+2)) [Category.{u+1} A] {F : Profinite.{u}ᵒᵖ ⥤ A}
    (hF : PreservesFiniteProducts F)
    (hF' : ∀ (E : A), EqualizerCondition (F ⋙ coyoneda.obj (op E))) :
  Presheaf.IsSheaf (coherentTopology Profinite) F := by
  rw [← extensiveRegular_generates_coherent]
  refine' fun E => (Presieve.isSheaf_coverage _ _).2 _
  intro B S hS
  apply isSheafFor_of_Dagur hS
  · exact ⟨fun J inst => have := hF.1; compPreservesLimitsOfShape _ _⟩
  · exact hF' E

theorem final' (A : Type (u+2)) [Category.{u+1} A] {G : A ⥤ Type (u+1)}
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G]
    {F : Profinite.{u}ᵒᵖ ⥤ A}
    (hF : PreservesFiniteProducts (F ⋙ G)) (hF' : EqualizerCondition (F ⋙ G)) :
    Presheaf.IsSheaf (coherentTopology Profinite) F := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology Profinite) F G,
    isSheaf_iff_isSheaf_of_type, ← extensiveRegular_generates_coherent, Presieve.isSheaf_coverage]
  intro B S' hS
  exact isSheafFor_of_Dagur hS hF hF'

end Profinite

end ProfiniteExplicitSheaves
