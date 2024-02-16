/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Covering
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.UniformSpace.Equicontinuity

#align_import topology.algebra.continuous_monoid_hom from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!

# Pontryagin Duals

This file defines the pontryagin dual.

## Main definitions

* `ContinuousMonoidHom A B`: The continuous homomorphisms `A →* B`.
* `ContinuousAddMonoidHom A B`: The continuous additive homomorphisms `A →+ B`.
-/


open Pointwise Function

namespace ContinuousMonoidHom

-- better proof in tb_ascoli branch
theorem arzela_ascoli {X Y : Type*} [TopologicalSpace X] [UniformSpace Y] [CompactSpace Y]
    (S : Set C(X, Y)) (hS1 : IsCompact (ContinuousMap.toFun '' S))
    (hS2 : Equicontinuous ((↑) : S → X → Y)) :
    IsCompact S := by
  suffices : Inducing (Equiv.Set.image (↑) S DFunLike.coe_injective)
  · rw [isCompact_iff_compactSpace] at hS1 ⊢
    exact (Equiv.toHomeomorphOfInducing _ this).symm.compactSpace
  rw [inducing_subtype_val.inducing_iff, inducing_iff_nhds]
  refine' fun ϕ ↦ le_antisymm (Filter.map_le_iff_le_comap.mp
    (ContinuousMap.continuous_coe.comp continuous_subtype_val).continuousAt) _
  rw [inducing_subtype_val.nhds_eq_comap ϕ, ← Filter.map_le_iff_le_comap]
  conv_rhs => rw [TopologicalSpace.nhds_generateFrom]
  simp only [le_iInf_iff]
  rintro - ⟨hg, K, hK, U, hU, rfl⟩
  obtain ⟨V, hV, hV'⟩ := Disjoint.exists_uniform_thickening (hK.image ϕ.1.2) hU.isClosed_compl
    (disjoint_compl_right_iff.mpr hg)
  obtain ⟨W, hW, hW₀, hWV⟩ := comp_comp_symm_mem_uniformity_sets hV
  obtain ⟨t, -, htW⟩ := hK.elim_nhds_subcover
    (fun x ↦ {x' | ∀ ψ : S, ((ψ : X → Y) x, (ψ : X → Y) x') ∈ W}) (fun x _ ↦ hS2 x W hW)
  rw [Filter.le_principal_iff, Filter.mem_map]
  refine' ⟨⋂ x ∈ t, {ψ | (ϕ.1 x, ψ x) ∈ W}, _, _⟩
  · rw [Filter.biInter_finset_mem]
    rintro x -
    rw [nhds_pi, Filter.mem_pi]
    refine' ⟨{x}, Set.finite_singleton x, fun i ↦ {y | (ϕ.1 i, y) ∈ W}, fun _ ↦ _, by simp⟩
    rw [nhds_eq_comap_uniformity, Filter.mem_comap]
    exact ⟨W, hW, fun _ x ↦ x⟩
  · rintro ψ h - ⟨x, hx, rfl⟩
    simp only [Set.mem_preimage, Set.mem_iInter] at h
    specialize htW hx
    simp only [Set.mem_iUnion] at htW
    obtain ⟨x', hx', h'⟩ := htW
    contrapose! hV'
    simp only [Set.not_disjoint_iff, Set.mem_iUnion]
    refine' ⟨ψ.1 x, _, ⟨ψ.1 x, hV', UniformSpace.mem_ball_self (ψ.1 x) hV⟩⟩
    exact ⟨ϕ.1 x, ⟨x, hx, rfl⟩, hWV ⟨ψ.1 x', ⟨ϕ.1 x', hW₀.mk_mem_comm.mp (h' ϕ), h x' hx'⟩, h' ψ⟩⟩

open BoundedContinuousFunction

theorem MonoidHom.isClosed_range (X Y : Type*)
    [TopologicalSpace X] [Group X] [TopologicalGroup X]
    [TopologicalSpace Y] [Group Y] [TopologicalGroup Y] [T1Space Y] :
    IsClosed (Set.range ((↑) : (X →* Y) → (X → Y))) := by
  have key : Set.range ((↑) : (X →* Y) → (X → Y)) = ⋂ (x) (y), {f | f x * f y * (f (x * y))⁻¹ = 1}
  · ext f
    simp_rw [mul_inv_eq_one, eq_comm, Set.mem_iInter]
    exact ⟨fun ⟨g, h⟩ ↦ h ▸ map_mul g, fun h ↦ ⟨MonoidHom.mk' f h, rfl⟩⟩
  rw [key]
  exact isClosed_iInter (fun _ ↦ isClosed_iInter
    (fun _ ↦ isClosed_singleton.preimage (by continuity)))

theorem mythm {X Y : Type*}
    [TopologicalSpace X] [Group X] [TopologicalGroup X]
    [UniformSpace Y] [CommGroup Y] [UniformGroup Y] [T1Space Y] [CompactSpace Y]
    (U : Set X) (V : Set Y)
    (hUc : IsCompact U) (hVc : IsClosed V)
    (hVo : V ∈ nhds (1 : Y))
    (h : EquicontinuousAt (fun f : {f : X →* Y | U ⊆ f ⁻¹' V} ↦ (f : X → Y)) 1) :
    LocallyCompactSpace (ContinuousMonoidHom X Y) := by
  apply TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
  let S1 : Set (X →* Y) := {f | U ⊆ f ⁻¹' V}
  let S2 : Set (ContinuousMonoidHom X Y) := {f | U ⊆ f ⁻¹' V}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X → Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 → X → Y) := equicontinuous_of_equicontinuousAt_one _ h
  have hS : S4 = (↑) '' S1
  · ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 → X → Y)
  · rw [equicontinuous_iff_range, ← Set.image_eq_range] at h ⊢
    rwa [← hS] at h
  have hS2 : (interior S2).Nonempty
  · let T : Set (ContinuousMonoidHom X Y) := {f | f '' U ⊆ interior V}
    have h1 : T ⊆ S2 := fun f hf ↦ Set.image_subset_iff.mp (Set.Subset.trans hf interior_subset)
    have h2 : IsOpen T := isOpen_induced (ContinuousMap.isOpen_gen hUc isOpen_interior)
    have h3 : T.Nonempty := ⟨1, fun _ ⟨_, _, h⟩ ↦ h ▸ mem_interior_iff_mem_nhds.mpr hVo⟩
    exact h3.mono (interior_maximal h1 h2)
  suffices : IsClosed S4
  · exact ⟨⟨S2, (inducing_toContinuousMap X Y).isCompact_iff.mpr
      (arzela_ascoli S3 this.isCompact h)⟩, hS2⟩
  replace hS : S4 = Set.pi U (fun _ ↦ V) ∩ Set.range ((↑) : (X →* Y) → (X → Y))
  · rw [hS]
    ext f
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨g, hg, hf⟩ ↦ hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ ↦ ⟨g, hf ▸ hg, hf⟩⟩
  rw [hS]
  exact (isClosed_set_pi (fun _ _ ↦ hVc)).inter (MonoidHom.isClosed_range X Y)

theorem mythm' {X Y : Type*}
    [TopologicalSpace X] [Group X] [TopologicalGroup X] [LocallyCompactSpace X]
    [UniformSpace Y] [CommGroup Y] [UniformGroup Y] [T1Space Y] [CompactSpace Y]
    (V : ℕ → Set Y)
    (hV : ∀ {n x}, x ∈ V n → x * x ∈ V n → x ∈ V (n + 1))
    (hVc : IsClosed (V 0)) (hVo : Filter.HasBasis (nhds 1) (fun _ ↦ True) V) :
    LocallyCompactSpace (ContinuousMonoidHom X Y) := by
  obtain ⟨U0, hU0c, hU0o⟩ := exists_compact_mem_nhds (1 : X)
  let U_aux : ℕ → {S : Set X | S ∈ nhds 1} :=
    Nat.rec ⟨U0, hU0o⟩ <| fun _ S ↦ let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : ℕ → Set X := fun n ↦ (U_aux n).1
  have hU1 : ∀ n, U n ∈ nhds 1 := fun n ↦ (U_aux n).2
  have hU2 : ∀ n, U (n + 1) * U (n + 1) ⊆ U n :=
    fun n ↦ (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : ∀ n, U (n + 1) ⊆ U n :=
    fun n x hx ↦ hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  apply mythm (U 0) (V 0) hU0c hVc (hVo.mem_of_mem trivial)
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine' fun n _ ↦ Filter.eventually_iff_exists_mem.mpr ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ ↦ _⟩
  rw [Set.mem_setOf_eq, map_one, div_one]
  suffices : U n ⊆ f ⁻¹' V n
  · exact this hx
  clear x hx
  induction' n with n ih
  · exact hf
  · exact fun x hx ↦ hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))

open Pointwise

-- PR # 7596
lemma coveringmap : IsCoveringMap expMapCircle := sorry

lemma basis0 :
    Filter.HasBasis (nhds (0 : ℝ)) (fun _ ↦ True) (fun n : ℕ ↦ Set.Icc (- (n + 1 : ℝ)⁻¹) (n + 1 : ℝ)⁻¹) := by
  have key := nhds_basis_zero_abs_sub_lt ℝ
  have : ∀ ε : ℝ, {b | |b| < ε} = Set.Ioo (-ε) ε
  · simp [Set.ext_iff, abs_lt]
  simp only [this] at key
  refine' key.to_hasBasis (fun ε hε ↦ _) (fun n _ ↦ ⟨(n + 1)⁻¹, by positivity, Set.Ioo_subset_Icc_self⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  rw [one_div] at hn
  exact ⟨n, trivial, Set.Icc_subset_Ioo (neg_lt_neg hn) hn⟩

lemma basis1 :
    Filter.HasBasis (nhds (0 : ℝ)) (fun _ ↦ True) (fun n : ℕ ↦ Set.Icc (-(2 ^ n : ℝ)⁻¹) (2 ^ n : ℝ)⁻¹) := by
  have h1 : ∀ n : ℕ, (2 ^ n : ℝ)⁻¹ ≤ (n + 1 : ℝ)⁻¹ := fun n ↦
    inv_le_inv_of_le (by positivity) (mod_cast Nat.lt_two_pow n)
  have h2 : ∀ n, 0 < (2 ^ n : ℝ)⁻¹ := fun n ↦ by positivity
  refine' basis0.to_subset _ _
  · exact fun n _ ↦ Set.Icc_subset_Icc (neg_le_neg (h1 n)) (h1 n)
  · exact fun n _ ↦ Icc_mem_nhds (neg_neg_of_pos (h2 n)) (h2 n)

lemma smul_Icc {a b c : ℝ} (ha : 0 < a) : a • Set.Icc b c = Set.Icc (a • b) (a • c) := by
  ext x
  simp [Set.mem_smul_set]
  refine' ⟨_, fun ⟨h1, h2⟩ ↦ ⟨x / a,
    ⟨(le_div_iff' ha).mpr h1, (div_le_iff' ha).mpr h2⟩, mul_div_cancel' x ha.ne'⟩⟩
  rintro ⟨y, ⟨h1, h2⟩, rfl⟩
  exact ⟨(mul_le_mul_left ha).mpr h1, (mul_le_mul_left ha).mpr h2⟩

instance : UniformGroup circle := by
  convert topologicalGroup_is_uniform_of_compactSpace circle
  exact unique_uniformity_of_compact rfl rfl

instance {X : Type*} [TopologicalSpace X] [Group X] [TopologicalGroup X] [LocallyCompactSpace X] :
    LocallyCompactSpace (ContinuousMonoidHom X circle) := by
  let Vn : ℕ → Set circle := fun n ↦ expMapCircle '' Set.Icc (-(2 ^ n : ℝ)⁻¹) (2 ^ n : ℝ)⁻¹
  have key0 : Filter.HasBasis (nhds 1) (fun _ ↦ True) Vn
  · rw [← expMapCircle_zero, ← coveringmap.isLocalHomeomorph.map_nhds_eq 0]
    exact basis1.map expMapCircle
  refine' mythm' Vn _ (isCompact_Icc.image coveringmap.continuous).isClosed key0
  intro n x h2 h1
  have h3 : ∀ t, t < Real.pi → Set.Icc (-t) t ⊆ Set.Ioc (-Real.pi) Real.pi
  · intro t ht
    by_cases h : -t ≤ t
    · exact (Set.Icc_subset_Ioc_iff h).mpr ⟨neg_lt_neg ht, ht.le⟩
    · rw [Set.Icc_eq_empty h]
      apply Set.empty_subset
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpow : (2 ^ n : ℝ)⁻¹ ≤ 1 := inv_le_one (one_le_pow_of_one_le one_le_two n)
  have h3 : x ∈ Vn (n + 1)
  · obtain ⟨s, hs, h1⟩ := h1
    obtain ⟨t, ht, h2⟩ := h2
    refine' ⟨t, _, h2⟩
    rw [← h2, ← expMapCircle_add] at h1
    have := (Set.Icc_add_Icc_subset _ _ _ _ (Set.add_mem_add ht ht))
    rw [← neg_add] at this
    have key := invOn_arg_expMapCircle.1.injOn (h3 _ ?_ hs) (h3 _ ?_ this) h1
    rw [key] at hs
    rw [← two_smul ℝ, ← Set.mem_inv_smul_set_iff₀, smul_Icc, smul_neg, ← smul_inv₀,
        smul_eq_mul, ← pow_succ] at hs
    exact hs
    · exact inv_pos.mpr two_pos
    · exact two_ne_zero
    · linarith
    · linarith
  exact h3

end ContinuousMonoidHom

variable (A B C E) [Monoid A] [Monoid B] [Monoid C] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace E]
  [TopologicalGroup E]

/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → circle`. -/
def PontryaginDual :=
  ContinuousMonoidHom A circle
#align pontryagin_dual PontryaginDual

-- porting note: `deriving` doesn't derive these instances
instance : TopologicalSpace (PontryaginDual A) :=
  (inferInstance : TopologicalSpace (ContinuousMonoidHom A circle))

instance : T2Space (PontryaginDual A) :=
  (inferInstance : T2Space (ContinuousMonoidHom A circle))

instance {X : Type*} [Group X] [TopologicalSpace X] [TopologicalGroup X] [LocallyCompactSpace X] :
    LocallyCompactSpace (PontryaginDual X) :=
  (inferInstance : LocallyCompactSpace (ContinuousMonoidHom X circle))

-- porting note: instance is now noncomputable
noncomputable instance : CommGroup (PontryaginDual A) :=
  (inferInstance : CommGroup (ContinuousMonoidHom A circle))

instance : TopologicalGroup (PontryaginDual A) :=
  (inferInstance : TopologicalGroup (ContinuousMonoidHom A circle))

-- porting note: instance is now noncomputable
noncomputable instance : Inhabited (PontryaginDual A) :=
  (inferInstance : Inhabited (ContinuousMonoidHom A circle))

variable {A B C E}

namespace PontryaginDual

open ContinuousMonoidHom

instance : FunLike (PontryaginDual A) A circle :=
  ContinuousMonoidHom.funLike

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

variable (A B C E)

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
