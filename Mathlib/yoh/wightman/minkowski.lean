import Mathlib

abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)


namespace Minkowski

/-- The Minkowski metric as a two-variable function. -/
def MinkowskiMetric.fun : R2 → R2 → ℝ := fun x y => (x 0) * (y 0) - (x 1) * (y 1)

lemma H1 : ∀ (m₁ m₂ : R2) (n : R2),
    MinkowskiMetric.fun (m₁ + m₂) n = MinkowskiMetric.fun m₁ n + MinkowskiMetric.fun m₂ n := by
  intro m₁ m₂ n
  dsimp [MinkowskiMetric.fun]
  ring

lemma H2 :  ∀ (c : ℝ) (m : R2) (n : R2),
    MinkowskiMetric.fun (c • m) n = c • MinkowskiMetric.fun m n := by
  intro R m n
  dsimp [MinkowskiMetric.fun]
  ring

lemma H3 : ∀ (m : R2) (n₁ n₂ : R2),
    MinkowskiMetric.fun m (n₁ + n₂) = MinkowskiMetric.fun m n₁ + MinkowskiMetric.fun m n₂ := by
  intro m n₁ n₂
  dsimp [MinkowskiMetric.fun]
  ring

lemma H4 : ∀ (c : ℝ) (m : R2) (n : R2),
    MinkowskiMetric.fun m (c • n) = c • MinkowskiMetric.fun m n := by
  intro c m n
  dsimp [MinkowskiMetric.fun]
  ring

/-- The Minkowski metric as a bilinear form. -/
def MinkowskiMetric : LinearMap.BilinForm ℝ R2 :=
  LinearMap.mk₂' ℝ ℝ MinkowskiMetric.fun H1 H2 H3 H4

scoped[Minkowski] notation "⟪" x ", " y "⟫M" => MinkowskiMetric x y
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

scoped[Minkowski] notation "‖" x "‖M" => MinkowskiMetric x x
local notation "‖" x "‖" => @inner ℝ _ _ x x

/-- The full Poincaré group, the group of affine equivalences preserving  -/
noncomputable def Poincare : Subgroup (R2 ≃ᵃ[ℝ] R2) where
  carrier := {g : (R2 ≃ᵃ[ℝ] R2) | ∀ (x y : R2), ‖x-y‖M = ‖g x - g y‖M }
  mul_mem' := by
    intro g1 g2 hg1 hg2
    simp only [Set.mem_setOf_eq] at hg1
    simp only [Set.mem_setOf_eq] at hg2
    simp only [Set.mem_setOf_eq, AffineEquiv.coe_mul, Function.comp_apply]
    intro x y
    exact Eq.trans (hg2 x y) (hg1 (g2 x) (g2 y))
  one_mem' := by
    simp only [Set.mem_setOf_eq, AffineEquiv.coe_one, id_eq, forall_const]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp only [Set.mem_setOf_eq]
    intro x y
    calc ‖x - y‖M
      = ‖(g * g⁻¹) x - (g * g⁻¹) y‖M := by simp only [mul_right_inv, AffineEquiv.coe_one, id_eq]
    _ = ‖g (g⁻¹ x) - g (g⁻¹ y)‖M := by exact rfl
    _ = ‖g⁻¹ x - g⁻¹ y‖M := by exact Eq.symm (hg (g⁻¹ x) (g⁻¹ y))

@[coe]
noncomputable def toAffineEquiv (g : Poincare) : R2 ≃ᵃ[ℝ] R2 :=
  { g with
    toFun := g.1
    linear := g.1.linear
    map_vadd' := g.1.map_vadd'
    left_inv := g.1.left_inv'
    right_inv := g.1.right_inv'
  }

noncomputable instance : CoeOut Poincare (R2 ≃ᵃ[ℝ] R2) :=
  ⟨toAffineEquiv⟩

instance : CoeFun (Poincare) fun _ => R2 → R2 where
  coe := fun (f : Poincare) => f.1

variable (g : Poincare) (x : R2)
variable (g : R2 ≃ᵃ[ℝ] R2) (x : R2)

#check LinearMap.det g.linear.toLinearMap

def IsSpacelike (x : R2) : Prop := ‖x‖M < 0
def IsTimelike (x : R2) : Prop := ‖x‖M > 0
def IsLightlike (x : R2) : Prop := ‖x‖M = 0

def IsSpacelikeSeparated (A B: Set R2) : Prop := ∀ (x y : R2), x ∈ A → y ∈ B → ‖x - y‖M < 0
def IsTimelikeSeparated (A B: Set R2) : Prop := ∀ (x y : R2), x ∈ A → y ∈ B → ‖x - y‖M > 0
def IsLightlikeSeparated (A B: Set R2) : Prop := ∀ (x y : R2), x ∈ A → y ∈ B → ‖x - y‖M = 0

/-- The future light cone. -/
def V_f : Set R2 := {x : R2 | IsTimelike x ∧ (x 0) > 0}

lemma isTimelike_neg_of_isTimelike {x : R2} (h : IsTimelike x) : IsTimelike (-x) := by
  rw [IsTimelike]
  simp only [map_neg, LinearMap.neg_apply, neg_neg, gt_iff_lt]
  exact h

lemma isTimelike_neg_iff_isTimelike {x : R2} : IsTimelike x ↔ IsTimelike (-x) := by
  constructor
  · exact isTimelike_neg_of_isTimelike
  · nth_rw 2 [← neg_neg x]
    exact isTimelike_neg_of_isTimelike



lemma in_V_f_or_neg_V_f_of_isTimelike {x : R2} (h : IsTimelike x) : x ∈ V_f ∨ -x ∈ V_f := by
  rw [V_f]
  simp only [gt_iff_lt, Set.mem_setOf_eq, PiLp.neg_apply, Left.neg_pos_iff]
  rw [← isTimelike_neg_iff_isTimelike]
  rw [← and_or_left]
  constructor
  · exact h
  rw [IsTimelike, MinkowskiMetric] at h
  simp only [LinearMap.mk₂'_apply, gt_iff_lt] at h
  rw [MinkowskiMetric.fun, ← sq, ← sq, sub_pos, sq_lt_sq, lt_abs] at h
  rcases h with hp | hn
  · left
    exact lt_of_le_of_lt (abs_nonneg (x 1)) hp
  · right
    apply neg_of_neg_pos
    exact lt_of_le_of_lt (abs_nonneg (x 1)) hn

lemma isTimelike_poincare_isTimelike {x : R2} (h : IsTimelike x) {g : Poincare} :
    IsTimelike (g.1.linear x) := by
  rw [IsTimelike]
  rw [IsTimelike] at h
  rw [← sub_zero x] at h
  rw [← sub_zero x, ← vsub_eq_sub, ← LinearEquiv.coe_coe, ← AffineEquiv.linear_toAffineMap]
  rw [AffineMap.linearMap_vsub]
  simp only [AffineEquiv.coe_toAffineMap, vsub_eq_sub]
  rw [← g.2 x 0]
  exact h


/-- The orthochronous Poincaré group, the linear part preserves the future light cone. -/
noncomputable def PoincareO : Subgroup Poincare where
  carrier := {g : Poincare | ∀ (x y : R2), x ∈ V_f → (g.1.linear x) ∈ V_f }
-- mathematically the definition is ok, but need to know the structure of the Poincare group
  mul_mem' := by
    intro g1 g2 hg1 hg2
    simp only [forall_const, Set.mem_setOf_eq, Submonoid.coe_mul, Subgroup.coe_toSubmonoid]
    simp only [forall_const, Set.mem_setOf_eq] at hg1
    simp only [forall_const, Set.mem_setOf_eq] at hg2
    intro x hx
    rw [AffineEquiv.mul_def, AffineEquiv.trans]
    simp only [LinearEquiv.trans_apply]
    exact hg1 _ (hg2 x hx)
  one_mem' := by
    simp only [forall_const, Set.mem_setOf_eq, OneMemClass.coe_one]
    intro x hx
    rw [AffineEquiv.one_def]
    simp only [AffineEquiv.linear_refl, LinearEquiv.refl_apply]
    exact hx
  inv_mem' := by
    intro g hg
    simp only [forall_const, Set.mem_setOf_eq] at hg
    simp only [forall_const, Set.mem_setOf_eq, InvMemClass.coe_inv]
    intro x hx
    rw [V_f] at hx
    simp only [gt_iff_lt, Set.mem_setOf_eq] at hx
    have : IsTimelike (g⁻¹.1.linear x) := isTimelike_poincare_isTimelike hx.1
    rcases in_V_f_or_neg_V_f_of_isTimelike this with hf | hp
    · exact hf
    · rw [V_f]
      simp only [gt_iff_lt, Set.mem_setOf_eq]
      rw [V_f] at hp
      simp only [gt_iff_lt, Set.mem_setOf_eq] at hp
      simp only [InvMemClass.coe_inv, PiLp.neg_apply, Left.neg_pos_iff] at hp
      have : (g.1)⁻¹.linear = (g.1.linear)⁻¹ := by
        exact rfl
      rw [this]
      rw [this] at hp
      rw [← Left.neg_pos_iff] at hp
      have hgnegginvf : g.1.linear (-(g.1.linear)⁻¹ x) ∈ V_f := by
        exact hg (-(g.1.linear)⁻¹ x) hp
      simp only [map_neg] at hgnegginvf
      rw [V_f] at hgnegginvf
      simp only [gt_iff_lt, Set.mem_setOf_eq, PiLp.neg_apply, Left.neg_pos_iff] at hgnegginvf
      have : g.1.linear ((g.1.linear)⁻¹ x) = x := by
        calc g.1.linear ((g.1.linear)⁻¹ x) = (g.1.linear * g.1.linear⁻¹) x := by rfl
          _ = id x := by simp only [mul_right_inv, LinearEquiv.coe_one, id_eq]
          _ = x := by exact rfl
      rw [this] at hgnegginvf
      exfalso
      exact LT.lt.false (lt_trans hx.2 hgnegginvf.2)

/-- The proper Poincaré group, the linear part has determinant 1. -/
noncomputable def PoincareP : Subgroup Poincare where
  carrier := {g : Poincare | LinearMap.det g.1.linear.toLinearMap = 1 }
  mul_mem' := by
    intro g1 g2 hg1 hg2
    simp only [Set.mem_setOf_eq, Submonoid.coe_mul, Subgroup.coe_toSubmonoid]
    simp only [Set.mem_setOf_eq] at hg1
    simp only [Set.mem_setOf_eq] at hg2
    rw [← AffineEquiv.coe_linear, AffineEquiv.mul_def, AffineEquiv.coe_trans_to_affineMap]
    rw [AffineMap.comp]
    simp only [AffineEquiv.linear_toAffineMap]
    rw [LinearMap.det_comp, hg1, hg2]
    simp only [mul_one]
  one_mem' := by
    simp only [Set.mem_setOf_eq, OneMemClass.coe_one]
    rw [AffineEquiv.one_def]
    simp only [AffineEquiv.linear_refl, LinearEquiv.refl_toLinearMap, LinearMap.det_id]
  inv_mem' := by
    simp only [Set.mem_setOf_eq, InvMemClass.coe_inv, Subtype.forall]
    intro g _ hgdet
    have (a : R2 ≃ᵃ[ℝ] R2) : a⁻¹.linear = (a.linear)⁻¹ := rfl
    rw [this g]
    rw [← LinearEquiv.coe_det]
    rw [← LinearEquiv.coe_det] at hgdet
    simp only [map_inv, Units.val_inv_eq_inv_val, hgdet, inv_one]

/-- The proper orthochronous Poincaré group. -/
noncomputable def PoincarePO : Subgroup Poincare := PoincareP ⊓ PoincareO

-- todo action on the functions.
-- euclidean group (just pararell)
