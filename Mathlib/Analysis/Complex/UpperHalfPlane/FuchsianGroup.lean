import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

open MatrixGroups Matrix

instance (n R : Type _) [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R] :
    TopologicalSpace (SpecialLinearGroup n R) := by
  apply TopologicalSpace.induced (β := n → (n → R))
  · exact (fun A i j ↦ A i j)
    -- exact (fun A ↦ (fun i ↦ (fun j ↦ A i j)))
  · infer_instance

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