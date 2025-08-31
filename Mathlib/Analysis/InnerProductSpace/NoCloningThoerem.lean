import Mathlib

open Complex TensorProduct ENNReal
open scoped ComplexInnerProductSpace

abbrev i := fun _ : (Fin 4) ↦ ℂ

abbrev H2 := lp (fun _ : (Fin 2) ↦ ℂ) 2
abbrev H4 := lp (fun _ : (Fin 2) × (Fin 2) ↦ ℂ) 2

variable (U : H4 →L[ℂ] H4)

abbrev e : H2 := ⟨fun (i : (Fin 2)) ↦ if i = 0 then (1 : ℂ) else (0 : ℂ), Memℓp.all _⟩

lemma norm_e : ‖e‖ = 1 := by
  rw [lp.norm_eq_tsum_rpow (by exact Nat.ofNat_pos')]
  simp only [Fin.isValue, toReal_ofNat, Real.rpow_ofNat, one_div]
  rw [tsum_fintype]
  simp

@[simp]
lemma inner_H2 (x y : H2) : ⟪x, y⟫ = ⟪x 0, y 0⟫ + ⟪x 1, y 1⟫ := by
  rw [lp.inner_eq_tsum, tsum_fintype]
  simp

lemma norm_eq_inner_H2 (x : H2) : ‖x‖ ^ 2  = ⟪x, x⟫ := by
  rw [inner_self_eq_norm_sq_to_K x]
  rfl

@[simp]
lemma norm_H2 (x : H2) : ‖x‖ ^ 2 = ⟪x 0, x 0⟫ + ⟪x 1, x 1⟫ := by
  rw [norm_eq_inner_H2 x, lp.inner_eq_tsum, tsum_fintype]
  simp

@[simp]
lemma inner_H4 (x y : H4) :
    ⟪x, y⟫ = ⟪x (0, 0), y (0, 0)⟫ + ⟪x (0, 1), y (0, 1)⟫
    + ⟪x (1, 0), y (1, 0)⟫ + ⟪x (1, 1), y (1, 1)⟫ := by
  rw [lp.inner_eq_tsum, tsum_fintype, Fintype.sum_prod_type]
  simp
  ring

def tensor (x y : H2) : H4 := ⟨fun ((i, j) : (Fin 2) × (Fin 2)) ↦ (x i) * (y j), Memℓp.all _⟩

@[simp]
lemma tensor_apply (x y : H2) (i j : Fin 2) : (tensor x y) (i, j) = (x i) * (y j) := by
  rfl

@[simp]
lemma inner_tensor_H4 (x1 x2 y1 y2 : H2) :
    ⟪tensor x1 x2, tensor y1 y2⟫ = ⟪x1, y1⟫ * ⟪x2, y2⟫ := by
  simp
  ring

@[simp]
lemma inner_tensor_H4' (x y : H2) :
    ⟪tensor x x, tensor y y⟫ = ⟪x, y⟫ ^ 2 := by
  simp
  ring

theorem NoCloning :
    ¬ (∃ U ∈ unitary (H4 →L[ℂ] H4), ∀ (x : H2), ‖x‖ = 1 → U (tensor x e) = (tensor x x)) := by
  by_contra! h
  obtain ⟨U, Uunit, Uclone⟩ := h
  have Uclone_star (x : H2) (hx : ‖x‖ = 1) : tensor x e = star U (tensor x x) := by
    calc
      tensor x e = (1 : H4 →L[ℂ] H4) (tensor x e) := by rfl
      _ = (1 : unitary (H4 →L[ℂ] H4)).1 (tensor x e) := by rfl
      _ = ((star U) * U) (tensor x e) := by
        rw [← unitary.star_mul_self ⟨U, Uunit⟩]; rfl
      _ = (star U) (U (tensor x e)) := rfl
      _ = (star U) (tensor x x) := by congr; exact Uclone x hx
  have inner_xeye_eq (x y : H2) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
      ⟪tensor x e, tensor y e⟫ = ⟪x, y⟫ ^ 2 := by
    rw [Uclone_star x hx, Uclone_star y hy]
    rw [unitary.inner_map_map ⟨star U, unitary.star_mem_iff.mpr Uunit⟩]
    simp only [inner_H4, Fin.isValue, tensor_apply, RCLike.inner_apply, map_mul, inner_H2]
    ring
  have inner_xy_eq_sq (x y : H2) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫ = ⟪x, y⟫ ^ 2 := by
    rw [← inner_xeye_eq x y hx hy]
    simp
  have zero_or_one (x y : H2) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫ = 0 ∨ ⟪x, y⟫ = 1 := by
    exact eq_zero_or_one_of_sq_eq_self (inner_xy_eq_sq x y hx hy).symm
  let x : H2 := ⟨fun i ↦ 1 / (Real.sqrt 2), Memℓp.all _⟩
  have inner_xe : ⟪x, e⟫ = 1 / (Real.sqrt 2) := by
    simp [x]
  have norm_sq_x : ‖x‖ ^ 2 = (1 : ℂ) := by
    rw [norm_H2 x]
    simp [x]
    field_simp
    ring_nf
    rw [sq, ← Complex.ofReal_mul (√2) (√2)]
    simp
  have norm_x : ‖x‖ = 1 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_eq_one, sq_eq_one_iff] at norm_sq_x
    apply Or.elim norm_sq_x
    · exact fun h ↦ h
    · by_contra! h
      have : 0 ≤ ‖x‖ := norm_nonneg x
      rw [h.1, Left.nonneg_neg_iff] at this
      linarith
  have xe_zero_or_one := zero_or_one x e norm_x norm_e
  apply Or.elim xe_zero_or_one
  · intro h
    rw [inner_xe] at h
    simp only [one_div, inv_eq_zero, Complex.ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero,
      OfNat.ofNat_ne_zero] at h
  · intro h
    rw [inner_xe] at h
    simp only [one_div, inv_eq_one, Complex.ofReal_eq_one, Real.sqrt_eq_one,
      OfNat.ofNat_ne_one] at h
