import Mathlib

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]


open NormedSpace Filter Set

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


theorem weak_convergence_of_norm_convergence
 (x : ℕ → E) (p : E) (hx : Tendsto x atTop (nhds p)) :
 Tendsto (fun n ↦ (x n : (WeakSpace 𝕜 E))) atTop (nhds (p : (WeakSpace 𝕜 E))) := by
 sorry
-- the statement is wrong, as x is always interpreted as E, not WeakSpace.

lemma tendsto_continuous_tendsto {X Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
 {F : Filter X} {f : X → Y} {g : Y → Z}
 (y : Y) (hf : Tendsto f F (nhds y)) (hg : Continuous g) :
 Tendsto (g ∘ f) F (nhds (g y))  := by
  exact Tendsto.comp (Continuous.tendsto hg y) hf

theorem functional_convergence_of_norm_convergence
 (x : ℕ → E) (p : E) (hx : Tendsto x atTop (nhds p)) :
 ∀ (y : E →L[𝕜] 𝕜), Tendsto (fun n => y (x n)) atTop (nhds (y p)) := by
 intro y
 exact Tendsto.comp (Continuous.tendsto (ContinuousLinearMap.continuous y) p) hx


variable (x : E)
#check (x : WeakSpace 𝕜 E)
variable (z : WeakSpace 𝕜 E)
#check (z : E)
#check (id z : WeakSpace 𝕜 E)   -- id p : WeakSpace 𝕜 E -- :)
-- thanks to Kalle Kytölä
#check nhds (id z : WeakSpace 𝕜 E)

def Rdisc := TopCat.discrete.obj ℝ
lemma isDiscreteRdisc: DiscreteTopology (Rdisc) :=
  ⟨rfl⟩

variable (a : ℝ)
#check (a : Rdisc)
variable (b : Rdisc)
#check (b : ℝ)
#check (id a : Rdisc)
#check (id b : ℝ)


variable (A : Set ℝ)
#check (A : Set Rdisc)
variable (B : Set Rdisc)
#check (B : Set ℝ)
#check (id B : Set ℝ)
#check (id A : Set Rdisc)

#check isDiscreteRdisc

example : IsOpen B := by
 exact (forall_open_iff_discrete.mpr isDiscreteRdisc) B

example : IsOpen (id A : Set Rdisc) := by
 exact (forall_open_iff_discrete.mpr isDiscreteRdisc) (A : Set Rdisc)



variable (y : E →L[𝕜] 𝕜)
variable (z : WeakDual 𝕜 E)
#check nhds (y : WeakDual 𝕜 E)
#check nhds z


theorem norm_convergence_of_weak_convergence
 (x : ℕ → (WeakSpace 𝕜 E)) (p : (WeakSpace 𝕜 E)) (hx : Tendsto x atTop (nhds p)) :
 Tendsto (fun n ↦ (x n : E)) atTop (nhds (p : E)) := by
 exact hx
-- something is wrong. the statement is not interpreted as intended
-- because this second claim cannot be true
