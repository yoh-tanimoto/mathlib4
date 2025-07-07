import Mathlib

open Polynomial Classical

variable (d : ℕ)
variable (a : EuclideanSpace ℝ (Fin d)→ ℝ)
variable (δ : ℝ) (hδ : δ > 0)
variable (c_del : ℝ) (hc_del : c_del ≥ 0)
variable {K : ℝ}
variable {M₀ : ℝ}
noncomputable def b (d : ℕ) (a : EuclideanSpace ℝ (Fin d)→ ℝ) (δ : ℝ) : (EuclideanSpace ℝ (Fin d)) → ℝ := fun x ↦ Real.exp ((d + δ) * Real.log (1 + ‖x‖)) * a x

lemma mn (m : ℤ) (hn : m < (1 : ℝ)) : m < 1 := by
  rw [←Int.cast_one] at hn
  exact Int.cast_lt.mp hn

example (m : ℤ) (h0 : 0 ≤ m) (h1 : m < (1 : ℝ)) : m = 0 := by
 have : m < 1 := by exact mn m h1
 linarith

-- -- the orthonormal basis on R^d
-- noncomputable def ZdBasis {d : ℕ} := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))
-- the orthonormal basis on R^2.
-- no implicit variable d
noncomputable def Z2Basis := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))
-- Z^d as the module on Z spanned by the orthonormal basis
-- seems that there is a problem of implicit variable
-- noncomputable def Zd {d : ℕ} := Submodule.span ℤ (Set.range (OrthonormalBasis.toBasis ZdBasis))
-- -- Z^2 as the module on Z spanned by the orthonormal basis
-- -- no implicit variable d
noncomputable def Z2 := Submodule.span ℤ (Set.range (OrthonormalBasis.toBasis Z2Basis))

example (ι : Fin d) : (EuclideanSpace.basisFun (Fin d) ℝ) ι ∈ Set.range (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin d) ℝ)) := by
 simp

variable (v : (EuclideanSpace ℝ (Fin d)))
variable (v2 : (EuclideanSpace ℝ (Fin 2)))
variable (ι : Fin (FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin d))))

-- -- the ι-th coordinate of the vector v in the basis ZdBasis
-- #check ZdBasis.repr v ι

#check DiscreteTopology Z2

-- want to prove that the ι-th coordinate of v is an integer.
-- the definition of Z2 says that it is a Z module spanned by
-- the set of vectors in Z2Basis. Is there a theorem that
-- v is a Z-combination of the basis vectors?


def isInteger (x : ℝ) := Int.floor x = x

lemma IsInteger_EqFloor (x : ℝ) : x = Int.floor x → ∃ (n : ℤ), x = n := by
 intro hx
 use Int.floor x

example (n : ℤ) (hn : n < (1 : ℝ)) : n < 1 := by
 rw [WithBot.coe_lt_one] at hn
-- exact hn
 sorry

example (n : ℤ) (hn : (n : ℝ) < 1) : n < 1 := by
 refine WithBot.coe_lt_coe.mp ?_
-- in the assumption, 1 is ℝ but here the right-hand side is ℕ
-- exact hn
 sorry
example (n m: ℤ) (hn : (n : ℝ) < m) : n < m := by
 exact WithBot.coe_lt_coe.mp hn
-- in the assumption, 1 is ℝ but here the right-hand side is ℕ
-- exact hn
 sorry


lemma Eq_Int_dist_lt_one (x y : ℝ) (hx : isInteger x) (hy : isInteger y) : |x - y| < 1 → x = y := by
 intro h
 have hxy : |⌊x⌋ - ⌊y⌋| < 1 := by
  rw [← hx , ← hy, abs_sub_lt_iff] at h
  refine abs_sub_lt_iff.mpr ?_
  constructor
  refine WithBot.coe_lt_one.mp ?_


  sorry
 rw [Int.abs_lt_one_iff, sub_eq_zero] at hxy
 rw [← hx, ← hy, hxy]

lemma IsIntegerLimitSeqInteger (x : ℕ → ℝ) (p : ℝ) (hxint : ∀ (n : ℕ), x n = Int.floor (x n)) (hxconv : Filter.Tendsto x Filter.atTop (nhds p))
 : ∃ (m : ℤ), p = m := by
 rw [Metric.tendsto_nhds] at hxconv
 simp at hxconv
 obtain ⟨N, hN⟩ := hxconv (1/2) one_half_pos
 obtain ⟨m, hm⟩ := IsInteger_EqFloor (x N) (hxint N)
 use m
 apply eq_of_forall_dist_le
 intro ε hε
 sorry


lemma IsInteger_componentsZ2 : v2 ∈ Z2 → ∀ (ι : Fin (FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin 2)))),
 ∃ (n : ℤ), (OrthonormalBasis.toBasis Z2Basis).repr v2 ι = n := by
 intro hv ι
 have hv2floor: (Zspan.floor (OrthonormalBasis.toBasis Z2Basis) v2) = v2 := by
  apply Zspan.floor_eq_self_of_mem
  exact hv
 apply IsInteger_EqFloor
 have : ((OrthonormalBasis.toBasis Z2Basis).repr (Zspan.floor (OrthonormalBasis.toBasis Z2Basis) v2)) ι = ⌊((OrthonormalBasis.toBasis Z2Basis).repr v2) ι⌋ := by
  simp
 rw [← this]
 rw [hv2floor]

-- want to prove that a bounded set of Z2 is finite,
-- by showing that it is discrete and compact.
-- problem: I don't know how to characterize Zd in
lemma IsFiniteBoundedSetZ2 (M : ℝ) (hM : M > 0) : Set.Finite {x ∈ Z2 | ‖x‖ ≤ M} := by
 have hComp : IsCompact {x ∈ Z2 | ‖x‖ ≤ M} := by
  refine Metric.isCompact_of_isClosed_isBounded ?hc ?hb
  have hBall : {x ∈ Z2 | dist x 0 ≤ M} = Z2.carrier ∩ Metric.closedBall 0 M := by
   exact rfl
  have Z2Closed: IsClosed Z2.carrier := by
   refine IsSeqClosed.isClosed ?hs
   unfold IsSeqClosed
   intro x p hx
   sorry
  have BallDef : {x : (EuclideanSpace ℝ (Fin 2))| dist x 0 ≤ M} = {x : (EuclideanSpace ℝ (Fin 2))| ‖x‖ ≤ M} := by
   simp
  have BallClosed : IsClosed {x : (EuclideanSpace ℝ (Fin 2))| ‖x‖ ≤ M} := by
   rw [← BallDef]
   exact Metric.isClosed_ball
  exact IsClosed.inter Z2Closed BallClosed
  --use IsClosedBall
  -- unfold IsSeqClosed
  -- intro x p hx hxp
  refine isBounded_iff_forall_norm_le.mpr ?hb.a
  use M
  simp
 refine IsCompact.finite hComp ?hs'
 apply DiscreteTopology.of_subset
 have hDisc : DiscreteTopology Z2 := by
  exact Zspan.instDiscreteTopologySubtypeMemSubmoduleIntInstSemiringIntToAddCommMonoidToAddCommGroupIntModuleInstMembershipSetLikeSpanRangeCoeBasisRealSemiringToModuleNormedFieldToSeminormedAddCommGroupInstFunLikeInstTopologicalSpaceSubtypeToTopologicalSpaceToUniformSpaceToPseudoMetricSpace
     (OrthonormalBasis.toBasis Z2Basis)
 exact hDisc
 intro x hx
 exact hx.1

namespace MeasureTheory.Measure
open InnerProductSpace.Core

-- -- the counting measure on the lattice Z^d
-- noncomputable def countZd : Measure (EuclideanSpace ℝ (Fin d)) :=
--  sum (fun x ↦ if x ∈ Zd then dirac x else 0)

-- the counting measure on the lattice Z^2
noncomputable def countZ2 : Measure (EuclideanSpace ℝ (Fin 2)) :=
 sum (fun x ↦ if x ∈ Z2 then dirac x else 0)

-- -- n-times convolution with itself
-- noncomputable def convolution_self : ℕ → ((EuclideanSpace ℝ (Fin d) → ℝ) → (EuclideanSpace ℝ (Fin d) → ℝ))
--   | 0 => fun f ↦ (fun x ↦ 1)
--   | n + 1 => fun f ↦ (convolution f ((convolution_self n) f) (ContinuousLinearMap.lsmul ℝ ℝ) (countZd d))

-- n-times convolution with itself on Z2
noncomputable def convolution_self2 : ℕ → ((EuclideanSpace ℝ (Fin 2) → ℝ) → (EuclideanSpace ℝ (Fin 2) → ℝ))
  | 0 => fun f ↦ (fun x ↦ 1)
  | n + 1 => fun f ↦ (convolution f ((convolution_self2 n) f) (ContinuousLinearMap.lsmul ℝ ℝ) countZ2)


variable (P1 : ∀ (x : EuclideanSpace ℝ (Fin d)), a x > 0)
variable (P2 : ∀ (x : EuclideanSpace ℝ (Fin d)), a x ≤ c_del * Real.exp (-2 * (d + δ) * Real.log (1 + ‖x‖)))
variable (P3 : ∀ (x y : EuclideanSpace ℝ (Fin d)) (hP3 : ‖y‖ ≤ 2 * NNReal.sqrt d),  b d a δ (x + y) / b d a δ x ≤ K)
variable (P4 : ∃ (c ε : ℝ) (hP4 : ε > 0), ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin d)), (convolution_self d n) (b d a δ) (x) ≤ c^n * (b d a δ (ε • x)))
variable (P5 : ∀ (x x' : EuclideanSpace ℝ (Fin d)) (hP5 : M₀ ≤ ‖x‖ ∧ ‖x‖ ≤ ‖x'‖), b d a δ x ≥ b d a δ x')


lemma A2_1 : ∀ (p : ℝ[X]), ∃ (N : ℝ), ∀ (x : ℝ), x ≥ N → |p.eval x| < Real.exp x := by
 intro p
 have h1 : Filter.Tendsto (fun x ↦ eval x p / Real.exp x) Filter.atTop (nhds 0) := by
  exact Polynomial.tendsto_div_exp_atTop p
 rw [tendsto_nhds] at h1
 have h2 : (fun x ↦ eval x p / Real.exp x) ⁻¹' (Metric.ball (0 : ℝ) 1) ∈ Filter.atTop := by
  apply h1
  apply Metric.isOpen_ball
  apply Metric.mem_ball_self
  norm_num
 rw [Filter.mem_atTop_sets] at h2
 obtain ⟨N, hN⟩ := h2
 use N
 intro x
 have h21 (a : ℝ): a - 0 = a := by ring
 have h3 (a : ℝ): a ∈ Metric.ball (0 : ℝ) 1 ↔ |a| < 1 := by
  constructor
  intro h31
  have h32 : |a - 0| < 1 := by exact h31
  rw [← h21 a]
  exact h32
  intro h33
  rw [← h21 a] at h33
  exact h33
 intro hx
 have h4 : eval x p / Real.exp x  ∈ Metric.ball (0 : ℝ)  1:= by
  apply hN
  exact hx
 rw [h3] at h4
 rw [abs_div] at h4
 rw [div_lt_iff] at h4
 rw [one_mul] at h4
 rw [← abs_of_pos (Real.exp_pos x)]
 exact h4
 rw [abs_of_pos]
 exact Real.exp_pos x
 exact Real.exp_pos x


lemma IsFiniteBoundedIntervalIntegers : ∀ (p q : ℤ) (h : p < q), Set.Finite {n : ℤ | p ≤ n ∧ n ≤ q} := by
 intro p q hpq
 have hpq' : (p : ℤ) < (q : ℤ) := by
  exact hpq
 have h : {n : ℤ | p ≤ n ∧ n ≤ q} = Set.uIcc (p : ℤ) (q : ℤ) := by
  rw [Set.uIcc_of_lt hpq']
  rfl
 rw [h]
 exact Set.finite_interval (p : ℤ) (q : ℤ)

lemma IsFiniteBoundedSetIntegers : ∀ (M : ℝ) (hM : 1 ≤ M), Set.Finite {n : ℤ | |n| ≤ M} := by
 intro M
 have h : {n : ℤ | |n| ≤ M} = {n : ℤ | - ⌊M⌋ ≤ n ∧ n ≤ ⌊M⌋} := by
  ext n
  constructor
  intro hn
  simp at hn
  simp
  rw [← abs_le]
  refine Int.le_floor.mpr ?h.mp.a
  have : |(n : ℝ)| = |n| := by exact Int.cast_abs.symm
  rw [← this]
  exact hn
  intro hn
  simp at hn
  simp
  rw [abs_le]
  refine and_comm.mpr ?h.mpr.a
  constructor
  rw [← Int.le_floor]
  exact hn.2
  rw [neg_le] at hn
  rw [Int.le_floor] at hn
  rw [neg_le]
  have : -(n : ℝ) = (-n : ℤ) := by exact (Int.cast_neg n).symm
  rw [this]
  exact hn.1
 rw [h]
 intro hM
 apply IsFiniteBoundedIntervalIntegers
 rw [← Int.floor_pos] at hM
 exact neg_lt_self hM

lemma A2_2 : ∀ (M : ℝ) (hM : 1 ≤ M), Set.Finite {x : EuclideanSpace ℝ (Fin d)| x ∈ Zd ∧ ‖x‖ ≤ M} := by
 intro M hM
 have hxleMi : {x : EuclideanSpace ℝ (Fin d)| x ∈ Zd ∧ ‖x‖ ≤ M} ⊆ {x : EuclideanSpace ℝ (Fin d)| x ∈ Zd ∧ ∀ (ι : (Fin d)), |x ι| ≤ M} := by
-- this is a subset of all x with |x_i| < M
  simp
  intro x hxZd hx_M
  constructor
  exact hxZd
  intro ι
  have : |x ι| ≤ ‖x‖ := by
   rw [EuclideanSpace.norm_eq]
   refine Real.le_sqrt_of_sq_le ?h
   rw [← Real.norm_eq_abs (x ι)]
   have hnorm : ∀ (ι : (Fin d)) (hiota : ι ∈ Finset.univ), 0 ≤ ‖x ι‖ := by
    exact fun ι hiota => norm_nonneg (x ι)
   have hnorm2 : ∀ (ι : (Fin d)) (hiota : ι ∈ Finset.univ), 0 ≤ ‖x ι‖^2 := by
    exact fun ι hiota => sq_nonneg ‖x ι‖
   exact Finset.single_le_sum hnorm2 (Finset.mem_univ ι)
  exact le_trans this hx_M

 have hleMifin : Set.Finite {x : EuclideanSpace ℝ (Fin d)| x ∈ Zd ∧ ∀ (ι : (Fin d)), |x ι| ≤ M} := by
-- the latter is a finite set : M^d
  simp

  sorry
 exact Set.Finite.subset hleMifin hxleMi


lemma A2 : ∃ (M' : ℝ), ∀ (x : EuclideanSpace ℝ (Fin d)), x ∈ Zd → (b d a δ (M' • x) ≤ b d a δ x) := by
 sorry
-- use by_cases
-- for x large, this is ok by P5. use M₀
-- for x small, there are finitely many such x.
-- for each of such x, there is large enough Mx' by P2 P3.
-- for x = 0, trivial. use M₀

--  have hx_nonneg : ‖x‖ ≥ 0 := by exact norm_nonneg x
--  by_cases hx_M : ‖x‖ ≥ M₀
