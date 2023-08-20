/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.UniformSpace.Equicontinuity

#align_import topology.algebra.continuous_monoid_hom from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `ContinuousMonoidHom A B`: The continuous homomorphisms `A →* B`.
* `ContinuousAddMonoidHom A B`: The continuous additive homomorphisms `A →+ B`.
-/


open Pointwise Function

variable (F A B C D E : Type _) [Monoid A] [Monoid B] [Monoid C] [Monoid D] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace E] [TopologicalGroup E]

/-- The type of continuous additive monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousAddMonoidHom A B)`,
you should parametrize over `(F : Type*) [ContinuousAddMonoidHomClass F A B] (f : F)`.

When you extend this structure, make sure to extend `ContinuousAddMonoidHomClass`. -/
structure ContinuousAddMonoidHom (A B : Type _) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun
#align continuous_add_monoid_hom ContinuousAddMonoidHom

/-- The type of continuous monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousMonoidHom A B)`,
you should parametrize over `(F : Type*) [ContinuousMonoidHomClass F A B] (f : F)`.

When you extend this structure, make sure to extend `ContinuousAddMonoidHomClass`. -/
@[to_additive "The type of continuous additive monoid homomorphisms from `A` to `B`."]
structure ContinuousMonoidHom extends A →* B where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun
#align continuous_monoid_hom ContinuousMonoidHom

section

/-- `ContinuousAddMonoidHomClass F A B` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `ContinuousAddMonoidHom`. -/
-- porting note : Changed A B to outParam to help synthesizing order
class ContinuousAddMonoidHomClass (A B : outParam (Type _)) [AddMonoid A] [AddMonoid B]
  [TopologicalSpace A] [TopologicalSpace B] extends AddMonoidHomClass F A B where
  /-- Proof of the continuity of the map. -/
  map_continuous (f : F) : Continuous f
#align continuous_add_monoid_hom_class ContinuousAddMonoidHomClass

/-- `ContinuousMonoidHomClass F A B` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `ContinuousMonoidHom`. -/
-- porting note : Changed A B to outParam to help synthesizing order
@[to_additive]
class ContinuousMonoidHomClass (A B : outParam (Type _)) [Monoid A] [Monoid B]
    [TopologicalSpace A] [TopologicalSpace B] extends MonoidHomClass F A B where
  /-- Proof of the continuity of the map. -/
  map_continuous (f : F) : Continuous f
#align continuous_monoid_hom_class ContinuousMonoidHomClass

end

/-- Reinterpret a `ContinuousMonoidHom` as a `MonoidHom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `ContinuousAddMonoidHom` as an `AddMonoidHom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) ContinuousMonoidHomClass.toContinuousMapClass
    [ContinuousMonoidHomClass F A B] : ContinuousMapClass F A B :=
  { ‹ContinuousMonoidHomClass F A B› with }
#align continuous_monoid_hom_class.to_continuous_map_class ContinuousMonoidHomClass.toContinuousMapClass
#align continuous_add_monoid_hom_class.to_continuous_map_class ContinuousAddMonoidHomClass.toContinuousMapClass

namespace ContinuousMonoidHom

variable {A B C D E}

@[to_additive]
instance ContinuousMonoidHom.ContinuousMonoidHomClass :
  ContinuousMonoidHomClass (ContinuousMonoidHom A B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := g
    congr

  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_continuous f := f.continuous_toFun

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`
directly. -/
@[to_additive
      "Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`."]
instance : CoeFun (ContinuousMonoidHom A B) fun _ => A → B :=
  FunLike.hasCoeToFun

@[to_additive (attr := ext)]
theorem ext {f g : ContinuousMonoidHom A B} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align continuous_monoid_hom.ext ContinuousMonoidHom.ext
#align continuous_add_monoid_hom.ext ContinuousAddMonoidHom.ext

/-- Reinterpret a `ContinuousMonoidHom` as a `ContinuousMap`. -/
@[to_additive "Reinterpret a `ContinuousAddMonoidHom` as a `ContinuousMap`."]
def toContinuousMap (f : ContinuousMonoidHom A B) : C(A, B) :=
  { f with }
#align continuous_monoid_hom.to_continuous_map ContinuousMonoidHom.toContinuousMap
#align continuous_add_monoid_hom.to_continuous_map ContinuousAddMonoidHom.toContinuousMap

@[to_additive]
theorem toContinuousMap_injective : Injective (toContinuousMap : _ → C(A, B)) := fun f g h =>
  ext <| by convert FunLike.ext_iff.1 h
#align continuous_monoid_hom.to_continuous_map_injective ContinuousMonoidHom.toContinuousMap_injective
#align continuous_add_monoid_hom.to_continuous_map_injective ContinuousAddMonoidHom.toContinuousMap_injective

-- porting note: Removed simps because given definition is not a constructor application
/-- Construct a `ContinuousMonoidHom` from a `Continuous` `MonoidHom`. -/
@[to_additive "Construct a `ContinuousAddMonoidHom` from a `Continuous` `AddMonoidHom`."]
def mk' (f : A →* B) (hf : Continuous f) : ContinuousMonoidHom A B :=
  { f with continuous_toFun := (hf : Continuous f.toFun)}
#align continuous_monoid_hom.mk' ContinuousMonoidHom.mk'
#align continuous_add_monoid_hom.mk' ContinuousAddMonoidHom.mk'

/-- Composition of two continuous homomorphisms. -/
@[to_additive (attr := simps!) "Composition of two continuous homomorphisms."]
def comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) : ContinuousMonoidHom A C :=
  mk' (g.toMonoidHom.comp f.toMonoidHom) (g.continuous_toFun.comp f.continuous_toFun)
#align continuous_monoid_hom.comp ContinuousMonoidHom.comp
#align continuous_add_monoid_hom.comp ContinuousAddMonoidHom.comp

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive (attr := simps!) "Product of two continuous homomorphisms on the same space."]
def prod (f : ContinuousMonoidHom A B) (g : ContinuousMonoidHom A C) :
    ContinuousMonoidHom A (B × C) :=
  mk' (f.toMonoidHom.prod g.toMonoidHom) (f.continuous_toFun.prod_mk g.continuous_toFun)
#align continuous_monoid_hom.prod ContinuousMonoidHom.prod
#align continuous_add_monoid_hom.sum ContinuousAddMonoidHom.sum

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive (attr := simps!) "Product of two continuous homomorphisms on different spaces."]
def prod_map (f : ContinuousMonoidHom A C) (g : ContinuousMonoidHom B D) :
    ContinuousMonoidHom (A × B) (C × D) :=
  mk' (f.toMonoidHom.prodMap g.toMonoidHom) (f.continuous_toFun.prod_map g.continuous_toFun)
#align continuous_monoid_hom.prod_map ContinuousMonoidHom.prod_map
#align continuous_add_monoid_hom.sum_map ContinuousAddMonoidHom.sum_map

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive (attr := simps!) "The trivial continuous homomorphism."]
def one : ContinuousMonoidHom A B :=
  mk' 1 continuous_const
#align continuous_monoid_hom.one ContinuousMonoidHom.one
#align continuous_add_monoid_hom.zero ContinuousAddMonoidHom.zero

@[to_additive]
instance : Inhabited (ContinuousMonoidHom A B) :=
  ⟨one A B⟩

/-- The identity continuous homomorphism. -/
@[to_additive (attr := simps!) "The identity continuous homomorphism."]
def id : ContinuousMonoidHom A A :=
  mk' (MonoidHom.id A) continuous_id
#align continuous_monoid_hom.id ContinuousMonoidHom.id
#align continuous_add_monoid_hom.id ContinuousAddMonoidHom.id

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by projection onto the first factor."]
def fst : ContinuousMonoidHom (A × B) A :=
  mk' (MonoidHom.fst A B) continuous_fst
#align continuous_monoid_hom.fst ContinuousMonoidHom.fst
#align continuous_add_monoid_hom.fst ContinuousAddMonoidHom.fst

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by projection onto the second factor."]
def snd : ContinuousMonoidHom (A × B) B :=
  mk' (MonoidHom.snd A B) continuous_snd
#align continuous_monoid_hom.snd ContinuousMonoidHom.snd
#align continuous_add_monoid_hom.snd ContinuousAddMonoidHom.snd

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by inclusion of the first factor."]
def inl : ContinuousMonoidHom A (A × B) :=
  prod (id A) (one A B)
#align continuous_monoid_hom.inl ContinuousMonoidHom.inl
#align continuous_add_monoid_hom.inl ContinuousAddMonoidHom.inl

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by inclusion of the second factor."]
def inr : ContinuousMonoidHom B (A × B) :=
  prod (one B A) (id B)
#align continuous_monoid_hom.inr ContinuousMonoidHom.inr
#align continuous_add_monoid_hom.inr ContinuousAddMonoidHom.inr

/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by the diagonal embedding."]
def diag : ContinuousMonoidHom A (A × A) :=
  prod (id A) (id A)
#align continuous_monoid_hom.diag ContinuousMonoidHom.diag
#align continuous_add_monoid_hom.diag ContinuousAddMonoidHom.diag

/-- The continuous homomorphism given by swapping components. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by swapping components."]
def swap : ContinuousMonoidHom (A × B) (B × A) :=
  prod (snd A B) (fst A B)
#align continuous_monoid_hom.swap ContinuousMonoidHom.swap
#align continuous_add_monoid_hom.swap ContinuousAddMonoidHom.swap

/-- The continuous homomorphism given by multiplication. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by addition."]
def mul : ContinuousMonoidHom (E × E) E :=
  mk' mulMonoidHom continuous_mul
#align continuous_monoid_hom.mul ContinuousMonoidHom.mul
#align continuous_add_monoid_hom.add ContinuousAddMonoidHom.add

/-- The continuous homomorphism given by inversion. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by negation."]
def inv : ContinuousMonoidHom E E :=
  mk' invMonoidHom continuous_inv
#align continuous_monoid_hom.inv ContinuousMonoidHom.inv
#align continuous_add_monoid_hom.neg ContinuousAddMonoidHom.neg

variable {A B C D E}

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive (attr := simps!) "Coproduct of two continuous homomorphisms to the same space."]
def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.prod_map g)
#align continuous_monoid_hom.coprod ContinuousMonoidHom.coprod
#align continuous_add_monoid_hom.coprod ContinuousAddMonoidHom.coprod

@[to_additive]
instance : CommGroup (ContinuousMonoidHom A E) where
  mul f g := (mul E).comp (f.prod g)
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one := one A E
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)
  inv f := (inv E).comp f
  mul_left_inv f := ext fun x => mul_left_inv (f x)

@[to_additive]
instance : TopologicalSpace (ContinuousMonoidHom A B) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

variable (A B C D E)

@[to_additive]
theorem inducing_toContinuousMap : Inducing (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨rfl⟩
#align continuous_monoid_hom.inducing_to_continuous_map ContinuousMonoidHom.inducing_toContinuousMap
#align continuous_add_monoid_hom.inducing_to_continuous_map ContinuousAddMonoidHom.inducing_toContinuousMap

@[to_additive]
theorem embedding_toContinuousMap :
    Embedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨inducing_toContinuousMap A B, toContinuousMap_injective⟩
#align continuous_monoid_hom.embedding_to_continuous_map ContinuousMonoidHom.embedding_toContinuousMap
#align continuous_add_monoid_hom.embedding_to_continuous_map ContinuousAddMonoidHom.embedding_toContinuousMap

@[to_additive]
theorem closedEmbedding_toContinuousMap [ContinuousMul B] [T2Space B] :
    ClosedEmbedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨embedding_toContinuousMap A B,
    ⟨by
      suffices
        Set.range (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) =
          ({ f | f '' {1} ⊆ {1}ᶜ } ∪
              ⋃ (x) (y) (U) (V) (W) (_ : IsOpen U) (_ : IsOpen V) (_ : IsOpen W) (_ :
                Disjoint (U * V) W),
                { f | f '' {x} ⊆ U } ∩ { f | f '' {y} ⊆ V } ∩ { f | f '' {x * y} ⊆ W } :
                  Set C(A , B))ᶜ by
        rw [this, compl_compl]
        refine' (ContinuousMap.isOpen_gen isCompact_singleton isOpen_compl_singleton).union _
        repeat' apply isOpen_iUnion; intro
        repeat' apply IsOpen.inter
        all_goals apply ContinuousMap.isOpen_gen isCompact_singleton; assumption
      simp_rw [Set.compl_union, Set.compl_iUnion, Set.image_singleton, Set.singleton_subset_iff,
        Set.ext_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
      refine' fun f => ⟨_, _⟩
      · rintro ⟨f, rfl⟩
        exact
          ⟨fun h => h (map_one f), fun x y U V W _hU _hV _hW h ⟨⟨hfU, hfV⟩, hfW⟩ =>
            h.le_bot ⟨Set.mul_mem_mul hfU hfV, (congr_arg (· ∈ W) (map_mul f x y)).mp hfW⟩⟩
      · rintro ⟨hf1, hf2⟩
        suffices ∀ x y, f (x * y) = f x * f y by
          refine'
            ⟨({ f with
                  map_one' := of_not_not hf1
                  map_mul' := this } :
                ContinuousMonoidHom A B),
              ContinuousMap.ext fun _ => rfl⟩
        intro x y
        contrapose! hf2
        obtain ⟨UV, W, hUV, hW, hfUV, hfW, h⟩ := t2_separation hf2.symm
        have hB := @continuous_mul B _ _ _
        obtain ⟨U, V, hU, hV, hfU, hfV, h'⟩ :=
          isOpen_prod_iff.mp (hUV.preimage hB) (f x) (f y) hfUV
        refine' ⟨x, y, U, V, W, hU, hV, hW, h.mono_left _, ⟨hfU, hfV⟩, hfW⟩
        rintro _ ⟨x, y, hx : (x, y).1 ∈ U, hy : (x, y).2 ∈ V, rfl⟩
        exact h' ⟨hx, hy⟩⟩⟩
#align continuous_monoid_hom.closed_embedding_to_continuous_map ContinuousMonoidHom.closedEmbedding_toContinuousMap
#align continuous_add_monoid_hom.closed_embedding_to_continuous_map ContinuousAddMonoidHom.closedEmbedding_toContinuousMap

variable {A B C D E}

@[to_additive]
instance [T2Space B] : T2Space (ContinuousMonoidHom A B) :=
  (embedding_toContinuousMap A B).t2Space

@[to_additive]
instance : TopologicalGroup (ContinuousMonoidHom A E) :=
  let hi := inducing_toContinuousMap A E
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prod_map hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

@[to_additive]
theorem continuous_of_continuous_uncurry {A : Type _} [TopologicalSpace A]
    (f : A → ContinuousMonoidHom B C) (h : Continuous (Function.uncurry fun x y => f x y)) :
    Continuous f :=
  (inducing_toContinuousMap _ _).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)
#align continuous_monoid_hom.continuous_of_continuous_uncurry ContinuousMonoidHom.continuous_of_continuous_uncurry
#align continuous_add_monoid_hom.continuous_of_continuous_uncurry ContinuousAddMonoidHom.continuous_of_continuous_uncurry

@[to_additive]
theorem continuous_comp [LocallyCompactSpace B] :
    Continuous fun f : ContinuousMonoidHom A B × ContinuousMonoidHom B C => f.2.comp f.1 :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    ContinuousMap.continuous_comp'.comp
      ((inducing_toContinuousMap A B).prod_map (inducing_toContinuousMap B C)).continuous
#align continuous_monoid_hom.continuous_comp ContinuousMonoidHom.continuous_comp
#align continuous_add_monoid_hom.continuous_comp ContinuousAddMonoidHom.continuous_comp

@[to_additive]
theorem continuous_comp_left (f : ContinuousMonoidHom A B) :
    Continuous fun g : ContinuousMonoidHom B C => g.comp f :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_comp_left.comp (inducing_toContinuousMap B C).continuous
#align continuous_monoid_hom.continuous_comp_left ContinuousMonoidHom.continuous_comp_left
#align continuous_add_monoid_hom.continuous_comp_left ContinuousAddMonoidHom.continuous_comp_left

@[to_additive]
theorem continuous_comp_right (f : ContinuousMonoidHom B C) :
    Continuous fun g : ContinuousMonoidHom A B => f.comp g :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_comp.comp (inducing_toContinuousMap A B).continuous
#align continuous_monoid_hom.continuous_comp_right ContinuousMonoidHom.continuous_comp_right
#align continuous_add_monoid_hom.continuous_comp_right ContinuousAddMonoidHom.continuous_comp_right

variable (E)

/-- `ContinuousMonoidHom _ f` is a functor. -/
@[to_additive "`ContinuousAddMonoidHom _ f` is a functor."]
def compLeft (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (ContinuousMonoidHom B E) (ContinuousMonoidHom A E) where
  toFun g := g.comp f
  map_one' := rfl
  map_mul' _g _h := rfl
  continuous_toFun := f.continuous_comp_left
#align continuous_monoid_hom.comp_left ContinuousMonoidHom.compLeft
#align continuous_add_monoid_hom.comp_left ContinuousAddMonoidHom.compLeft

variable (A) {E}

/-- `ContinuousMonoidHom f _` is a functor. -/
@[to_additive "`ContinuousAddMonoidHom f _` is a functor."]
def compRight {B : Type _} [CommGroup B] [TopologicalSpace B] [TopologicalGroup B]
    (f : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (ContinuousMonoidHom A B) (ContinuousMonoidHom A E) where
  toFun g := f.comp g
  map_one' := ext fun _a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right
#align continuous_monoid_hom.comp_right ContinuousMonoidHom.compRight
#align continuous_add_monoid_hom.comp_right ContinuousAddMonoidHom.compRight

variable (E)

lemma mylem {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (S : Set α) (T : Set β) (b : β) (h : b ∈ T) :
    ContinuousMap.const α b ∈ ContinuousMap.CompactOpen.gen S T := by
  rintro - ⟨-, -, rfl⟩
  exact h

theorem arzeli_ascoli {X Y : Type*} [TopologicalSpace X] [UniformSpace Y] [CompactSpace Y]
    (S : Set C(X, Y)) (hS1 : IsClosed (ContinuousMap.toFun '' S))
    (hS2 : Equicontinuous ((↑) : S → X → Y)) :
    IsCompact S := by
  let T := ContinuousMap.toFun '' S
  have h1 : IsClosed T
  · exact hS1
  have h2 : IsCompact T := h1.isCompact
  let f₀ : S ≃ T := Equiv.Set.image ContinuousMap.toFun S ContinuousMap.coe_injective
  suffices : Inducing f₀
  · let f : S ≃ₜ T := f₀.toHomeomorphOfInducing this
    rw [isCompact_iff_compactSpace] at h2 ⊢
    exact f.symm.compactSpace
  rw [inducing_subtype_val.inducing_iff]
  change Inducing (ContinuousMap.toFun ∘ Subtype.val)
  rw [inducing_iff_nhds]
  rintro ⟨ϕ, hϕ⟩
  apply le_antisymm
  · rw [←Filter.map_le_iff_le_comap]
    exact (ContinuousMap.continuous_coe.comp continuous_subtype_val).continuousAt
  · rw [inducing_subtype_val.nhds_eq_comap ⟨ϕ, hϕ⟩, ← Filter.map_le_iff_le_comap]
    conv_rhs => rw [TopologicalSpace.nhds_generateFrom]
    simp only [le_iInf_iff]
    rintro - ⟨hg, K, hK, U, hU, rfl⟩
    have key : ∃ V ∈ uniformity Y, ∀ x ∈ K, ∀ y : Y, (ϕ x, y) ∈ V → y ∈ U
    · obtain ⟨V, hV, hV'⟩ := Disjoint.exists_uniform_thickening (hK.image ϕ.2) hU.isClosed_compl
        (disjoint_compl_right_iff.mpr hg)
      refine' ⟨V, hV, _⟩
      intro x hx y hy
      contrapose! hV'
      rw [Set.not_disjoint_iff]
      refine' ⟨y, _, _⟩
      · simp only [Set.mem_iUnion]
        refine' ⟨ϕ x, ⟨x, hx, rfl⟩, hy⟩
      · simp only [Set.mem_iUnion]
        refine' ⟨y, hV', _⟩
        exact UniformSpace.mem_ball_self y hV
    obtain ⟨V, hV, hVU⟩ := key
    obtain ⟨W₀, hW₀, hW₀V⟩ := comp3_mem_uniformity hV -- three epsilon trick!
    let W := symmetrizeRel W₀
    have hW : W ∈ uniformity Y := symmetrize_mem_uniformity hW₀
    have hWV : compRel W (compRel W W) ⊆ V
    · refine' Set.Subset.trans _ hW₀V
      refine' compRel_mono _ (compRel_mono _ _) <;> exact symmetrizeRel_subset_self W₀
    obtain ⟨t, htK, htW⟩ := hK.elim_nhds_subcover
      (fun x => {x' | ∀ ψ : S, ((ψ : X → Y) x, (ψ : X → Y) x') ∈ W})
      (fun x hx => hS2 x W hW)
    intro F hF
    refine' ⟨⋂ x ∈ t, {ψ | (ϕ x, ψ x) ∈ W}, _, _⟩
    · rw [Filter.biInter_finset_mem]
      intro x hxt
      simp only
      change _ ∈ nhds ϕ.toFun
      let Z : Set Y := {y | (ϕ x, y) ∈ W}
      change {ψ | ψ x ∈ Z} ∈ nhds ϕ.toFun
      have key' := Set.singleton_pi' x (fun _ ↦ Z)
      rw [← key', set_pi_mem_nhds_iff]
      rintro - ⟨-, -⟩
      rw [mem_nhds_uniformity_iff_right]
      refine' Filter.mem_of_superset hW _
      intro a b c
      rwa [← a.eta, c] at b
      exact Set.finite_singleton x
    · rintro ⟨ψ, hψ⟩ h
      apply hF
      rintro - ⟨x, hx, rfl⟩
      refine' hVU x hx (ψ x) _
      specialize htW hx
      simp only [Set.mem_iUnion] at htW
      obtain ⟨x', hx', h'⟩ := htW
      have h1 := h' ⟨ϕ, hϕ⟩
      have h2 := h' ⟨ψ, hψ⟩
      simp only at h1 h2
      simp only [Set.mem_preimage, Set.mem_iInter] at h
      specialize h x' hx'
      simp only at h
      change (ϕ x', ψ x') ∈ W at h
      apply hWV
      refine' ⟨ϕ x', _, ψ x', h, h2⟩
      exact (symmetric_symmetrizeRel W₀).mk_mem_comm.mp h1

open BoundedContinuousFunction

-- not sure how to make this work, but it's just a side refactor
example {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : CompactSpace α]
    [inst_2 : PseudoMetricSpace β] [inst_3 : CompactSpace β] (A : Set (α →ᵇ β))
    (h1 : IsClosed A) (h2 : Equicontinuous ((↑) : A → α → β)) : IsCompact A := by
  let f : (α →ᵇ β) → C(α, β) := BoundedContinuousFunction.toContinuousMap
  let B := f '' A
  have hB1 : IsClosed B := sorry
  have hB2 : Equicontinuous ((↑) : B → α → β) := sorry
  have key := arzeli_ascoli B hB1 hB2
  have hf0 : Inducing f
  · rw [inducing_iff_nhds]
    intro g
    apply eq_of_forall_le_iff
    intro c
    rw [← Filter.tendsto_iff_comap, ← Filter.tendsto_id', tendsto_iff_tendstoUniformly]
    rw [ContinuousMap.tendsto_compactOpen_iff_forall]
    -- simp?

  have hf : Continuous f := sorry
  sorry

theorem mythm {X Y : Type*} [TopologicalSpace X] [Group X]
    [TopologicalGroup X] [LocallyCompactSpace X]
    [UniformSpace Y] [CommGroup Y] [UniformGroup Y] [T2Space Y] [CompactSpace Y]
    (U : Set X) (V : Set Y)
    (hUc : IsCompact U) (hVc : IsCompact V)
    (hVo : V ∈ nhds (1 : Y))
    (h : EquicontinuousAt (fun f : {f : X →* Y | f '' U ⊆ V} ↦ (f : X → Y)) 1) :
    LocallyCompactSpace (ContinuousMonoidHom X Y) := by
  replace h := equicontinuous_of_equicontinuousAt_one _ h
  apply TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
  let S : Set (ContinuousMonoidHom X Y) := toContinuousMap ⁻¹' (ContinuousMap.CompactOpen.gen U V)
  let S' : Set C(X, Y) := toContinuousMap '' S
  let S'' : Set (X → Y) := ContinuousMap.toFun '' S'
  have h2 : ∀ f : X → Y, f ∈ S'' ↔ f '' U ⊆ V ∧ ∀ x y, f (x * y) = f x * f y
  · intro f
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨hf, map_mul f⟩
    · rintro ⟨hf, hf₀⟩
      suffices : Continuous f
      · exact ⟨⟨f, this⟩, ⟨⟨MonoidHom.mk' f hf₀, this⟩, hf, rfl⟩, rfl⟩
      exact h.continuous ⟨MonoidHom.mk' f hf₀, hf⟩
  have h3 : S'' = (⋂ (x ∈ U), {f | f x ∈ V}) ∩ ⋂ (x : X) (y : X), {f | f (x * y) = f x * f y}
  · simp only [Set.image_subset_iff] at h2
    ext f
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    exact h2 f
  have h4 : IsClosed S''
  · rw [h3]
    apply IsClosed.inter
    · apply isClosed_biInter
      intros x hx
      exact Set.singleton_pi' x (fun _ ↦ V) ▸ isClosed_set_pi (fun _ _ ↦ hVc.isClosed)
    · apply isClosed_iInter
      intro x
      apply isClosed_iInter
      intro y
      let g : (X → Y) → Y := fun f ↦ (f (x * y))⁻¹ * (f x * f y)
      have hg : Continuous g := by continuity
      have key : g ⁻¹' {1} = {f | f (x * y) = f x * f y}
      · ext f
        exact inv_mul_eq_one
      rw [← key]
      exact isClosed_singleton.preimage hg
  have h9 : IsCompact S'
  · refine' arzeli_ascoli S' h4 _
    rw [equicontinuous_iff_range] at h ⊢
    have key1 : Set.range (fun f : {f : X →* Y | f '' U ⊆ V} ↦ (f : X → Y)) = S''
    · ext f
      rw [h2]
      constructor
      · rintro ⟨⟨f, hf⟩, rfl⟩
        exact ⟨hf, map_mul f⟩
      · rintro ⟨hf, hf₀⟩
        exact ⟨⟨MonoidHom.mk' f hf₀, hf⟩, rfl⟩
    have key2 : Set.range (fun f : S' ↦ (f : X → Y)) = S''
    · ext f
      constructor
      · rintro ⟨f, rfl⟩
        exact ⟨f, f.2, rfl⟩
      · rintro ⟨f, hf, rfl⟩
        exact ⟨⟨f, hf⟩, rfl⟩
    convert h <;> exact key2.trans key1.symm
  have h6 : IsCompact S
  · exact (inducing_toContinuousMap X Y).isCompact_iff.mp h9
  have hS : (interior S).Nonempty
  · let T := toContinuousMap ⁻¹' ContinuousMap.CompactOpen.gen U (interior V)
    have h1 : T ⊆ S := fun f hf x hx => interior_subset (hf hx)
    have h2 : IsOpen T := isOpen_induced (ContinuousMap.isOpen_gen hUc isOpen_interior)
    have h3 : T.Nonempty
    · use 1
      apply mylem
      exact mem_interior_iff_mem_nhds.mpr hVo
    exact h3.mono (interior_maximal h1 h2)
  exact ⟨⟨S, h6⟩, hS⟩

instance {X : Type*} [Group X] [TopologicalSpace X] [TopologicalGroup X] [LocallyCompactSpace X] :
    LocallyCompactSpace (ContinuousMonoidHom X circle) := by
  have : UniformGroup circle := ⟨sorry⟩
  obtain ⟨U, hUc, hUo⟩ := exists_compact_mem_nhds (1 : X)
  obtain ⟨V, hVc, hVo⟩ := exists_compact_mem_nhds (1 : circle)
  apply mythm U V hUc hVc hVo
  sorry
  -- need to specify V more precisely, and prove equicontinuity

end ContinuousMonoidHom



/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → circle`. -/
def PontryaginDual :=
  ContinuousMonoidHom A circle
#align pontryagin_dual PontryaginDual

-- porting note: `deriving` doesn't derive these instances
instance : TopologicalSpace (PontryaginDual A) :=
  (inferInstance : TopologicalSpace (ContinuousMonoidHom A circle))

instance : T2Space (PontryaginDual A) :=
  (inferInstance : T2Space (ContinuousMonoidHom A circle))

instance [ContinuousMul A] [LocallyCompactSpace A] : LocallyCompactSpace (PontryaginDual A) :=
  (inferInstance : LocallyCompactSpace (ContinuousMonoidHom A circle))

-- porting note: instance is now noncomputable
noncomputable instance : CommGroup (PontryaginDual A) :=
  (inferInstance : CommGroup (ContinuousMonoidHom A circle))

instance : TopologicalGroup (PontryaginDual A) :=
  (inferInstance : TopologicalGroup (ContinuousMonoidHom A circle))

-- porting note: instance is now noncomputable
noncomputable instance : Inhabited (PontryaginDual A) :=
  (inferInstance : Inhabited (ContinuousMonoidHom A circle))


variable {A B C D E}

namespace PontryaginDual

open ContinuousMonoidHom

noncomputable instance : ContinuousMonoidHomClass (PontryaginDual A) A circle :=
  ContinuousMonoidHom.ContinuousMonoidHomClass

/-- `PontryaginDual` is a functor. -/
noncomputable def map (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (PontryaginDual B) (PontryaginDual A) :=
  f.compLeft circle
#align pontryagin_dual.map PontryaginDual.map

@[simp]
theorem map_apply (f : ContinuousMonoidHom A B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl
#align pontryagin_dual.map_apply PontryaginDual.map_apply

@[simp]
theorem map_one : map (one A B) = one (PontryaginDual B) (PontryaginDual A) :=
  ext fun x => ext (fun _y => OneHomClass.map_one x)
#align pontryagin_dual.map_one PontryaginDual.map_one

@[simp]
theorem map_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ext fun _x => ext fun _y => rfl
#align pontryagin_dual.map_comp PontryaginDual.map_comp


@[simp]
nonrec theorem map_mul (f g : ContinuousMonoidHom A E) : map (f * g) = map f * map g :=
  ext fun x => ext fun y => map_mul x (f y) (g y)
#align pontryagin_dual.map_mul PontryaginDual.map_mul

variable (A B C D E)

/-- `ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`. -/
noncomputable def mapHom [LocallyCompactSpace E] :
    ContinuousMonoidHom (ContinuousMonoidHom A E)
      (ContinuousMonoidHom (PontryaginDual E) (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp
#align pontryagin_dual.map_hom PontryaginDual.mapHom

end PontryaginDual
