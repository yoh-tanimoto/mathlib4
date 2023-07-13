import TopologicalEntropy.Orbits
import Mathlib.Topology.Bases
import Mathlib.Topology.SubsetProperties
import Mathlib.Topology.Separation
import Mathlib.Tactic

open Orbits

namespace InvariantSubset

variable {X : Type _}

/-- A subset F is T-invariant if, for any x ∈ F, T(x) ∈ F. Written with preimages. -/
def IsInvariant (T : X → X) (F : Set X) : Prop :=
  F ⊆ T ⁻¹' F

theorem inv_def' {T : X → X} {F : Set X} (F_inv : IsInvariant T F) {x : X} (x_in_F : x ∈ F) :
  T x ∈ F :=
F_inv x_in_F

theorem iter_of_inv_in_inv {T : X → X} {F : Set X} (F_inv : IsInvariant T F) (n : ℕ) :
  F ⊆ T^[n] ⁻¹' F :=
by
  induction' n with n hn
  . rw [Function.iterate_zero T, Set.preimage_id]
  . rw [Function.iterate_succ T _, Set.preimage_comp]
    exact Set.Subset.trans F_inv (Set.preimage_mono hn)

theorem iter_of_inv_in_inv' {T : X → X} {F : Set X} (F_inv : IsInvariant T F) 
(n : ℕ) {x : X} (x_in_F : x ∈ F) :
  T^[n] x ∈ F :=
(iter_of_inv_in_inv F_inv n) x_in_F

theorem univ_is_inv (T : X → X) :
  IsInvariant T Set.univ :=
by 
  unfold IsInvariant
  rw [Set.preimage_univ]

theorem empty_is_inv (T : X → X) :
  IsInvariant T ∅ :=
by 
  unfold IsInvariant
  rw [Set.preimage_empty]

theorem inter_of_inv_is_inv {T : X → X} {F G : Set X} (F_inv : IsInvariant T F) (G_inv : IsInvariant T G) :
  IsInvariant T (F ∩ G) :=
by
  unfold IsInvariant
  rw [Set.preimage_inter]
  exact Set.inter_subset_inter F_inv G_inv

theorem iInter_of_inv_is_inv {T : X → X} {ι : Sort _} {s : ι → Set X} (h : ∀ i : ι, IsInvariant T (s i)) :
  IsInvariant T (⋂ i : ι, s i) :=
by
  unfold IsInvariant
  rw [Set.preimage_iInter]
  exact Set.iInter_mono h

theorem sInter_of_inv_is_inv {T : X → X} {A : Set (Set X)} (h : ∀ F : Set X, F ∈ A → IsInvariant T F) :
  IsInvariant T (⋂₀ A) :=
by
  unfold IsInvariant
  intro x x_in_sInter
  simp
  intro F F_in_A
  exact h F F_in_A (Set.mem_sInter.1 x_in_sInter F F_in_A)

theorem union_of_inv_is_inv {T : X → X} {F G : Set X} (F_inv : IsInvariant T F) (G_inv : IsInvariant T G) :
  IsInvariant T (F ∪ G) :=
by
  unfold IsInvariant
  rw [Set.preimage_union]
  exact Set.union_subset_union F_inv G_inv

theorem iUnion_of_inv_is_inv {T : X → X} {ι : Sort _} {s : ι → Set X} (h : ∀ i : ι, IsInvariant T (s i)) :
  IsInvariant T (⋃ i : ι, s i) :=
by
  unfold IsInvariant
  rw [Set.preimage_iUnion]
  exact Set.iUnion_mono h

theorem sUnion_of_inv_is_inv {T : X → X} {A : Set (Set X)} (h : ∀ F : Set X, F ∈ A → IsInvariant T F) :
  IsInvariant T (⋃₀ A) :=
by
  unfold IsInvariant
  intro x x_in_sUnion
  rcases x_in_sUnion with ⟨F, F_in_A, x_in_F⟩
  simp
  use F
  exact ⟨F_in_A, inv_def' (h F F_in_A) x_in_F⟩

/--
Definition of the set of points whose forward orbit stays in F. This is the largest invariant subset 
contained in F.--/
def interOfPreorbit (T : X → X) (F : Set X) : Set X :=
  ⋂ n : ℕ, T^[n] ⁻¹' F

theorem interOfPreorbit_sub_self (T : X → X) (F : Set X) :
  interOfPreorbit T F ⊆ F :=
Set.iInter_subset (fun n : ℕ => T^[n] ⁻¹' F) 0

theorem interOfPreorbit_is_inv (T : X → X) (F : Set X) :
  IsInvariant T (interOfPreorbit T F) :=
by
  unfold IsInvariant
  unfold interOfPreorbit
  rw [Set.preimage_iInter]
  apply Set.iInter_mono'
  intro n
  use n + 1
  rw [Function.iterate_add T n 1, Function.iterate_one, Set.preimage_comp]

theorem interOfPreorbit_is_largest_inv {T : X → X} {F G : Set X} (G_inv : IsInvariant T G) (G_sub_F : G ⊆ F) :
    G ⊆ interOfPreorbit T F :=
by
  apply Set.subset_iInter_iff.2
  intro n
  exact subset_trans (iter_of_inv_in_inv G_inv n) (Set.preimage_mono G_sub_F)

theorem interOfPreorbit_of_inv {T : X → X} {F : Set X} (F_inv : IsInvariant T F) :
    interOfPreorbit T F = F :=
by
  apply Set.Subset.antisymm
  . exact interOfPreorbit_sub_self T F
  . exact interOfPreorbit_is_largest_inv F_inv (subset_refl F)

theorem image_of_inv_is_inv {T : X → X} {F : Set X} (F_inv : IsInvariant T F) :
  IsInvariant T (T '' F) :=
by
  apply Set.Subset.trans _ (Set.subset_preimage_image T F)
  rw [Set.image_subset_iff]
  exact F_inv

theorem preimage_of_inv_is_inv {T : X → X} {F : Set X} (F_inv : IsInvariant T F) :
  IsInvariant T (T ⁻¹' F) :=
by
  apply Set.preimage_mono
  exact F_inv

/--The orbit of a point is the smallest invariant subset containing this point.-/

theorem orbit_is_inv (T : X → X) (x : X) :
  IsInvariant T (orbit T x) :=
by
  intro y y_in_orbit_x
  cases' y_in_orbit_x with n TnTx_eq_y
  use n + 1
  rw [TnTx_eq_y, ← Function.Commute.iterate_self T n x]
  exact Function.iterate_add_apply T n 1 x

theorem orbit_in_inv {F : Set X} (F_inv : IsInvariant T F) {x : X} (x_in_F : x ∈ F) :
  orbit T x ⊆ F :=
by
  intro y y_in_orbit
  cases' y_in_orbit with n Tnx_eq_y
  rw [Tnx_eq_y]
  apply iter_of_inv_in_inv F_inv n
  exact x_in_F

section InvariantClosed

variable {X : Type _} [TopologicalSpace X]

/-- A subset F is said to be invariant and closed if it is closed and sub-invariant
(its image is included in itself). Invariant closed sets are the closed subsets of
a topology on X. We prove the stability under finite unions and arbitrary intersections.
  In addition, invariant_closed is stated as a class, of which we give two instances
for now : the empty set and the universe. --/
def IsInvariantClosed (T : X → X) (F : Set X) : Prop :=
  IsInvariant T F ∧ IsClosed F

theorem univ_is_invclos (T : X → X) :
  IsInvariantClosed T Set.univ :=
⟨ univ_is_inv T, isClosed_univ ⟩

theorem empty_is_invclos (T : X → X) :
  IsInvariantClosed T ∅ :=
⟨ empty_is_inv T, isClosed_empty ⟩

theorem inter_of_invclos_is_invclos {T : X → X} {F G : Set X} (F_invclos : IsInvariantClosed T F) 
(G_invclos : IsInvariantClosed T G) :
  IsInvariantClosed T (F ∩ G) :=
⟨ inter_of_inv_is_inv F_invclos.1 G_invclos.1, IsClosed.inter F_invclos.2 G_invclos.2 ⟩

theorem iInter_of_invclos_is_invclos {ι : Sort _} {s : ι → Set X}
(h : ∀ i : ι, IsInvariantClosed T (s i)) :
  IsInvariantClosed T (⋂ i : ι, s i) :=
⟨ iInter_of_inv_is_inv fun i : ι => (h i).1, isClosed_iInter fun i : ι => (h i).2 ⟩

theorem sInter_of_invclos_is_invclos {T : X → X} {A : Set (Set X)}
(h : ∀ F : Set X, F ∈ A → IsInvariantClosed T F) :
  IsInvariantClosed T (⋂₀ A) :=
by
  apply And.intro
  . exact sInter_of_inv_is_inv (fun F : Set X => fun F_in_A : F ∈ A  => (h F F_in_A).1)
  . exact isClosed_sInter (fun F : Set X => fun F_in_A : F ∈ A  => (h F F_in_A).2)

theorem union_of_invclos_is_invclos {T : X → X} {F G : Set X} (F_invclos : IsInvariantClosed T F) 
(G_invclos : IsInvariantClosed T G) :
  IsInvariantClosed T (F ∪ G) :=
⟨ union_of_inv_is_inv F_invclos.1 G_invclos.1, IsClosed.union F_invclos.2 G_invclos.2 ⟩


/-- Closed T-invariant subsets are the closed set of a topology, the topology of invariants.--/
def topologyOfInvariants (T : X → X) : TopologicalSpace X :=
  by
  apply TopologicalSpace.ofClosed {F : Set X | IsInvariantClosed T F} (empty_is_invclos T)
  · simp
    intro A h
    exact sInter_of_invclos_is_invclos h
  · simp
    intro F F_invclos G G_invclos
    exact union_of_invclos_is_invclos F_invclos G_invclos

theorem interOfPreorbit_of_clos_is_invclos {T : X → X} (T_cont : Continuous T) {F : Set X} (F_clos : IsClosed F) :
    IsInvariantClosed T (interOfPreorbit T F) :=
by
  apply And.intro
  . exact interOfPreorbit_is_inv T F
  . apply isClosed_sInter
    simp [-Set.preimage_iterate_eq]
    exact fun n : ℕ => IsClosed.preimage (Continuous.iterate T_cont n) F_clos

theorem orbit_clos_is_invclos (T_cont : Continuous T) (x : X) :
  IsInvariantClosed T (closure (orbit T x)) :=
by
  apply And.intro
  . exact Set.Subset.trans (closure_mono (orbit_is_inv T x)) (Continuous.closure_preimage_subset T_cont (orbit T x))
  . exact isClosed_closure

theorem orbit_clos_in_inv_clos {T : X → X} {F : Set X} (F_invclos : IsInvariantClosed T F) 
{x : X} (x_in_F : x ∈ F) :
  closure (orbit T x) ⊆ F :=
closure_minimal (orbit_in_inv F_invclos.1 x_in_F) F_invclos.2

end InvariantClosed

section InvariantCompact

variable {X : Type _} [TopologicalSpace X] (T : X → X)

/-- Invariant compact subsets.--/
def IsInvariantCompact (T : X → X) (F : Set X) : Prop :=
  IsInvariant T F ∧ IsCompact F

theorem univ_is_inv_comp [CompactSpace X] (T : X → X) :
  IsInvariantCompact T Set.univ :=
⟨ univ_is_inv T, isCompact_univ ⟩

theorem empty_set_is_inv_comp (T : X → X) :
  IsInvariantCompact T ∅ :=
⟨ empty_is_inv T, isCompact_empty ⟩

theorem invcomp_inter_invclos_is_invcomp {T : X → X} {F G : Set X} (F_invcomp : IsInvariantCompact T F)
(G_invclos : IsInvariantClosed T G) :
  IsInvariantCompact T (F ∩ G) :=
⟨ inter_of_inv_is_inv F_invcomp.1 G_invclos.1, IsCompact.inter_right F_invcomp.2 G_invclos.2 ⟩

theorem invclos_inter_invcomp_is_invcomp {T : X → X} {F G : Set X} (F_invclos : IsInvariantClosed T F)
(G_invcomp : IsInvariantCompact T G) :
  IsInvariantCompact T (F ∩ G) :=
⟨ inter_of_inv_is_inv F_invclos.1 G_invcomp.1, IsCompact.inter_left G_invcomp.2 F_invclos.2 ⟩

theorem invclos_sub_comp_is_invcomp {T : X → X} {F G : Set X} (F_invclos : IsInvariantClosed T F) 
(G_comp : IsCompact G) (F_sub_G : F ⊆ G) :
  IsInvariantCompact T F :=
⟨ F_invclos.1, isCompact_of_isClosed_subset G_comp F_invclos.2 F_sub_G ⟩ 

theorem invclos_of_comp_is_invcomp [CompactSpace X] {T : X → X} {F : Set X} (F_invclos : IsInvariantClosed T F) :
  IsInvariantCompact T F :=
invclos_sub_comp_is_invcomp F_invclos isCompact_univ (Set.subset_univ F)

theorem inv_comp_of_separated_is_inv_clos [T2Space X] {T : X → X} {F : Set X} (F_invcomp : IsInvariantCompact T F) :
  IsInvariantClosed T F :=
⟨ F_invcomp.1, IsCompact.isClosed F_invcomp.2⟩ 

theorem interOfPreorbit_of_clos_comp_is_invcomp {T : X → X} (T_cont : Continuous T) {F : Set X}
(F_clos : IsClosed F) (F_comp : IsCompact F) :
  IsInvariantCompact T (interOfPreorbit T F) :=
invclos_sub_comp_is_invcomp (interOfPreorbit_of_clos_is_invclos T_cont F_clos) 
  F_comp (interOfPreorbit_sub_self T F)

theorem image_of_invcomp_is_invcomp {T : X → X} (T_cont : Continuous T) {F : Set X} (F_invcomp : IsInvariantCompact T F) :
  IsInvariantCompact T (T '' F) :=
⟨ image_of_inv_is_inv F_invcomp.1, IsCompact.image F_invcomp.2 T_cont⟩  

#lint

end InvariantCompact