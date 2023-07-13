import Mathlib.Tactic
import Mathlib.Topology.UniformSpace.Compact

namespace RefinedUniformity

open UniformSpace

/--Shorthand for the space of uniform neighborhoods--/
notation "𝓤" => uniformity

theorem uniformContinuous_ite {X : Type _} [UniformSpace X] (T : X → X) (n : ℕ) :
  UniformContinuous T → UniformContinuous T^[n] :=
by
  intro T_uni_cont
  induction' n with n hn
  · exact uniformContinuous_id
  · rw [Function.iterate_succ]
    exact UniformContinuous.comp hn T_uni_cont

theorem prod_map_ite {X Y : Type _} (S : X → X) (T : Y → Y) (n : ℕ) :
  (Prod.map S T)^[n] = Prod.map S^[n] T^[n] :=
by
  induction' n with n hn
  · simp 
    exact Prod.map_id
  · rw [Function.iterate_succ, hn, Prod.map_comp_map, ← Function.iterate_succ, 
      ← Function.iterate_succ]

theorem prod_map_comp_swap {X : Type _} (f g : X → X) :
  Prod.map f g ∘ Prod.swap = Prod.swap ∘ Prod.map g f := by rfl

/-- Definition of a refined uniformity.--/
def refinedUni {X : Type _} (T : X → X) (U : Set (X × X)) (n : ℕ) : Set (X × X) :=
  ⋂ (k : ℕ) (_ : k < n), (Prod.map T T)^[k] ⁻¹' U

theorem refinedUni_iff {X : Type _} (T : X → X) (U : Set (X × X)) (n : ℕ) (x y : X) :
    y ∈ ball x (refinedUni T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U :=
  by
  simp [refinedUni, ball, -Set.preimage_iterate_eq]
  apply Iff.intro
  · intro h k k_lt_n
    specialize h k k_lt_n
    rw [prod_map_ite T T k] at h 
    exact h
  · intro h k k_lt_n
    specialize h k k_lt_n
    rw [prod_map_ite T T k]
    simp
    exact h

theorem refinedUni_is_uniformity {X : Type _} [UniformSpace X] [CompactSpace X] (T : X → X)
(T_cont : Continuous T) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
  refinedUni T U n ∈ 𝓤 X :=
by
  have : refinedUni T U n = ⋂ (k : ℕ) (_ : k ∈ Set.Ico 0 n), (Prod.map T T)^[k] ⁻¹' U := by
    simp [-Set.preimage_iterate_eq]; rfl
  rw [this]; clear this
  apply (Filter.biInter_mem (Set.finite_Ico 0 n)).2
  intro k _
  rw [prod_map_ite T T k]
  apply uniformContinuous_def.1
  swap; exact U_uni
  apply uniformContinuous_ite T k
  exact CompactSpace.uniformContinuous_of_continuous T_cont

theorem refined_of_open_isOpen {X : Type _} [TopologicalSpace X] (T : X → X) (T_cont : Continuous T)
{U : Set (X × X)} (U_open : IsOpen U) (n : ℕ) :
  IsOpen (refinedUni T U n) :=
by
  have : refinedUni T U n = ⋂ (k : ℕ) (_ : k ∈ Set.Ico 0 n), (Prod.map T T)^[k] ⁻¹' U := by
    simp [-Set.preimage_iterate_eq]; rfl
  rw [this]; clear this
  apply isOpen_biInter (Set.finite_Ico 0 n)
  intro k _
  apply continuous_def.1 _ U U_open
  rw [prod_map_ite]
  apply Continuous.prod_map
  repeat' exact Continuous.iterate T_cont k

theorem refined_of_symm_is_symm {X : Type _} (T : X → X) {U : Set (X × X)} (U_symm : SymmetricRel U)
(n : ℕ) :
  SymmetricRel (refinedUni T U n) :=
by
  ext xy
  simp [refinedUni, -Set.preimage_iterate_eq]
  constructor
  · intro h k k_lt_n
    specialize h k k_lt_n
    change ((Prod.map T T)^[k] ∘ Prod.swap) xy ∈ U at h
    rw [prod_map_ite, prod_map_comp_swap] at h 
    change Prod.map (T^[k]) (T^[k]) xy ∈ Prod.swap ⁻¹' U at h 
    unfold SymmetricRel at U_symm 
    rw [U_symm, ← prod_map_ite] at h 
    exact h
  · intro h k k_le_n
    specialize h k k_le_n
    change ((Prod.map T T)^[k] ∘ Prod.swap) xy ∈ U
    rw [prod_map_ite, prod_map_comp_swap]
    change Prod.map T^[k] T^[k] xy ∈ Prod.swap ⁻¹' U
    unfold SymmetricRel at U_symm 
    rw [U_symm, ← prod_map_ite]
    exact h

theorem refined_of_comp_is_comp {X : Type _} (T : X → X) {U V : Set (X × X)} (h : compRel V V ⊆ U)
    (n : ℕ) : compRel (refinedUni T V n) (refinedUni T V n) ⊆ refinedUni T U n :=
  by
  simp [refinedUni, -Set.preimage_iterate_eq]
  intro k k_lt_n xy xy_in_comp
  simp [compRel, -Set.preimage_iterate_eq] at xy_in_comp 
  simp [-Set.preimage_iterate_eq]
  rcases xy_in_comp with ⟨z, hz1, hz2⟩
  specialize hz1 k k_lt_n
  specialize hz2 k k_lt_n
  rw [prod_map_ite] at *
  apply ball_mono h ((T^[k]) xy.1)
  exact mem_ball_comp hz1 hz2

theorem mono_time {X : Type _} (T : X → X) (U : Set (X × X)) {m n : ℕ} (m_le_n : m ≤ n) :
    refinedUni T U n ⊆ refinedUni T U m :=
  by
  apply Set.iInter_mono
  intro k
  apply Set.iInter_mono'
  intro k_lt_m
  use LT.lt.trans_le k_lt_m m_le_n

theorem mono_uni {X : Type _} (T : X → X) {U V : Set (X × X)} (U_sub_V : U ⊆ V) (n : ℕ) :
  refinedUni T U n ⊆ refinedUni T V n :=
by
  apply Set.iInter_mono
  intro k
  apply Set.iInter_mono
  intro _
  exact Set.preimage_mono U_sub_V

@[simp]
theorem time_zero_univ {X : Type _} (T : X → X) (U : Set (X × X)) :
  refinedUni T U 0 = Set.univ :=
by simp [refinedUni]

@[simp]
theorem time_one_id {X : Type _} (T : X → X) (U : Set (X × X)) :
  refinedUni T U 1 = U :=
by simp [refinedUni]

theorem inter_of_refined_ball_nonempty {X : Type _} (T : X → X) (n : ℕ) {U V : Set (X × X)}
(V_symm : SymmetricRel V) (V_comp : compRel V V ⊆ U) (x y : X) :
  (ball x (refinedUni T V n) ∩ ball y (refinedUni T V n)).Nonempty →
    x ∈ ball y (refinedUni T U n) :=
by
  intro hxy
  rcases hxy with ⟨z, z_in_Bx, z_in_By⟩
  rw [mem_ball_symmetry (refined_of_symm_is_symm T V_symm n)] at z_in_Bx 
  apply ball_mono (refined_of_comp_is_comp T V_comp n) y
  exact mem_ball_comp z_in_By z_in_Bx

#lint

end RefinedUniformity

