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
 Tendsto (fun n ↦ (id (x n) : (WeakSpace 𝕜 E))) atTop (nhds (p : (WeakSpace 𝕜 E))) := by
 refine tendsto_atTop_nhds.mpr ?_
 intro U hpU hU
 have hUnorm : IsOpen (id U : Set E) := by
  exact norm_topology_le_weak_topology (id U : Set E) hU
 rw [tendsto_atTop_nhds] at hx
 exact hx (id U : Set E) hpU hUnorm

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
#check IsOpen[UniformSpace.toTopologicalSpace : TopologicalSpace E]
-- how can one use the notation IsOpen[s] in the definition of
-- ≤ between TopologicalSpace?


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


theorem disc_topology_le_dist_topology (U : Set ℝ) : IsOpen U → IsOpen (id U : Set Rdisc):= by
 exact fun a => trivial

theorem dist_convergence_of_disc_convergence
 (x : ℕ → Rdisc) (p : ℝ) (hx : Tendsto x atTop (nhds p)) :
 Tendsto (fun n ↦ (id (x n) : ℝ)) atTop (nhds (p : ℝ)) := by
 refine tendsto_atTop_nhds.mpr ?_
 intro U hpU hU
 have hU' : IsOpen (id U : Set ℝ) := by exact hU
 have hUnorm : IsOpen (id U : Set Rdisc) := by
  exact TopologicalSpace.le_def.mp disc_topology_le_dist_topology (id U) hU'
 rw [tendsto_atTop_nhds] at hx
 exact hx U hpU hUnorm
