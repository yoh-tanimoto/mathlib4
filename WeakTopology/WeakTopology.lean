import Mathlib

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]


open NormedSpace


theorem norm_topology_le_weak_topology :
(UniformSpace.toTopologicalSpace : TopologicalSpace E) ≤
  (WeakSpace.instTopologicalSpace : TopologicalSpace (WeakSpace 𝕜 E)) := by
  apply Continuous.le_induced
  refine continuous_pi ?h.h
  intro y
  simp
  have : (fun x => ((topDualPairing 𝕜 E) y) x) = (fun x => y x) := by
   ext x
   exact topDualPairing_apply y x
  rw [this]
  exact ContinuousLinearMap.continuous y
