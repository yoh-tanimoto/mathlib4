import Mathlib

variable  (𝕜 : Type u_8) (E : Type u_9) [CommSemiring 𝕜]
 [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
 [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

abbrev E_w : Type u_9 := WeakSpace 𝕜 E

#check E_w
#check WeakSpace.map
-- this only shows that any linear map from E to F is
-- continuous from E_w to F_w. this should be generalized to F

-- todo
-- E_w is weaker than the original topology
-- any continuous map from E to any X is continuous from E_w to X
-- for any continuous linear functional ℓ and a convergent net/sequence x n,
-- n → x n is convergent in E_w
-- in particular, in InnerProductSpace
