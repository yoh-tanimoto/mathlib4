import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

open MatrixGroups Matrix

instance (n R : Type _) [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R] :
    TopologicalSpace (SpecialLinearGroup n R) := by
  apply TopologicalSpace.induced (β := n → (n → R))
  · exact (fun A i j ↦ A i j)
    -- exact (fun A ↦ (fun i ↦ (fun j ↦ A i j)))
  · infer_instance

lemma mem_center_SpecialLinearGroup_two_iff {A : SL(2,ℝ)} :
    A ∈ Subgroup.center SL(2,ℝ) ↔ A = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∨ A = (-1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  -- Try using `Subgroup.mem_center_iff` (maybe can `rw`?)
  -- and then special matrices are:
  let S : SL(2, ℝ) := ⟨!![1, 1; 0, 1], by sorry⟩
  let T : SL(2, ℝ) := ⟨!![1, 0; 1, 1], by sorry⟩
  sorry

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
