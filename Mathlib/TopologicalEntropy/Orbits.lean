import Mathlib.Tactic

namespace Orbits

variable {X : Type _} (T : X → X)

/- Orbit of a point x under T.
  Deviation from [K] : we define the orbit as starting from time 0, in accordance with common definitions
involving the action of (semi-)groups. We do not define trajectories.
  When we need orbits starting from time 1, we make them start from T x instead of x. -/
/-- Forward orbit of a point under a transformation.--/
def orbit (x : X) : Set X :=
  {y : X | ∃ n : ℕ, y = T^[n] x}

theorem image_of_orbit_eq_orbit_of_image (x : X) (n : ℕ) :
  T^[n] '' (orbit T x) = orbit T (T^[n] x) :=
by
  ext y
  apply Iff.intro
  · intro h
    rcases h with ⟨z, ⟨k, h_k⟩, Tnz_eq_y⟩
    use k
    rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, ← h_k, Tnz_eq_y]
  · intro h
    cases' h with k Tnkx_eq_y
    use (T^[k]) x
    apply And.intro
    . use k
    . rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, Tnkx_eq_y]

/--
The Orbit relation : x R y if y is in the orbit of T x, so if there exists a positive n such that 
y = T^n (x). Warning: this relation is not, in general, reflexive.--/
def trajectoryRelation : Set (X × X) :=
  {xy : X × X | xy.2 ∈ orbit T (T xy.1)}

/--
A point x is T-periodic if (x,x) is in the diagonal of the relation, so if x R x. The next lemma 
shall show that this definition is equivalent with the usual one.--/
def isPeriodic (x : X) : Prop :=
  (x, x) ∈ trajectoryRelation T

theorem isPeriodic_iff (x : X) :
    isPeriodic T x ↔ ∃ n ≥ 1, x = (T^[n]) x :=
by
  apply Iff.intro
  · intro x_is_periodic
    cases' x_is_periodic with n h_n
    use n + 1
    simp
    simp at h_n
    exact h_n
  · intro h_n
    rcases h_n with ⟨n, n_spos, Tnx_eq_x⟩
    use n.pred
    simp
    rw [← Function.iterate_succ_apply, Nat.succ_pred_eq_of_pos n_spos]
    exact Tnx_eq_x

#lint

end Orbits

