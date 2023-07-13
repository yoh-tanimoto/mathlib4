import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

open MatrixGroups Matrix SpecialLinearGroup

instance (n R : Type _) [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R] :
    TopologicalSpace (SpecialLinearGroup n R) := by
  apply TopologicalSpace.induced (β := n → (n → R))
  · exact (fun A i j ↦ A i j)
    -- exact (fun A ↦ (fun i ↦ (fun j ↦ A i j)))
  · infer_instance

lemma mem_center_SpecialLinearGroup_two_iff {A : SL(2,ℝ)} :
    A ∈ Subgroup.center SL(2,ℝ) ↔ A = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∨ A = (-1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Subgroup.mem_center_iff]
    rw [coe_mk]
    swap
    · simp    
    constructor
    swap
    intro h hg
    --apply h
    · sorry
    intro h
    

    --have h₁ :  ↑A = 1 ∨ ↑A = -1 → (∀ (g : SL(2, ℝ)), g * A = A * g) := by
    left

    --have h₂ :  (∀ (g : SL(2, ℝ)), g * A = A * g) → (↑A = 1 ∨ ↑A = -1) := by sorry
    rw [h₂ ]
    

    --rw [← coe_one]
    --rw [ext_iff]
    let S : SL(2, ℝ) := ⟨!![1, 1; 0, 1], by sorry⟩
    let T : SL(2, ℝ) := ⟨!![1, 0; 1, 1], by sorry⟩
    let a b : ℝ
    --have h₁ : (∀ (g : SL(2, ℝ)), g * S = S * g) := by
      --rw [ext_iff]
      --sorry
    --have h₂ : (∀ (g : SL(2, ℝ)), g * T = T * g) := by
      --sorry
    --have h₀ : A 1 1 = A 2 2 := by
      --sorry
    --have h : A 1 2 = 0 := by
      --sorry
    


    --Matrix.ext i j


    
    have h₁ : (∀ (g : SL(2, ℝ)), g * S = S * g) := by
      sorry
    have h₂ : (∀ (g : SL(2, ℝ)), g * T = T * g) := by
      sorry
  -- Try using `Subgroup.mem_center_iff` (maybe can `rw`?)
  -- and then special matrices are:

#check !![1, 1; 0, 1]


variable (n R : Type _) [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]

def ProjectiveLinearGroup := (SpecialLinearGroup n R)⧸Subgroup.center (SpecialLinearGroup n R)

scoped[MatrixGroups] notation "PSL(" n ", " R ")" => ProjectiveLinearGroup (Fin n) R

instance: Group (ProjectiveLinearGroup n R) := by
  unfold ProjectiveLinearGroup
  infer_instance

instance : TopologicalSpace (ProjectiveLinearGroup n R) := by
  unfold ProjectiveLinearGroup
  apply TopologicalSpace.coinduced (QuotientGroup.mk (s := Subgroup.center (SpecialLinearGroup n R) ))
  infer_instance

variable (G : Subgroup (ProjectiveLinearGroup n ℝ)) [DiscreteTopology G]

#check Subgroup.mem_center_iff
#check !![1, 1; 0, 1]