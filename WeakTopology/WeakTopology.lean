import Mathlib

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]


open NormedSpace

theorem norm_topology_le_weak_topology :
    (UniformSpace.toTopologicalSpace : TopologicalSpace E) ≤
      (WeakSpace.instTopologicalSpace : TopologicalSpace (WeakSpace 𝕜 E)) :=
      sorry
