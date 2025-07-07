import Mathlib
import Mathlib.Yoh.Lattice.Defs

-- main depenency : Mathlib/Algebra/Module/ZLattice/Basic

open Polynomial Classical Filter

section Lattice

-- the orthonormal basis on R^d
noncomputable def RdBasis {d : SpaceDimension} := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))
-- noncomputable def ZdBasis {d : SpaceDimension} :=
--  Basis.restrictScalars ℤ (OrthonormalBasis.toBasis (@RdBasis d))


end Lattice





variable {d : SpaceDimension}

#check Set.range (OrthonormalBasis.toBasis (@RdBasis d))
-- #check @ZdBasis d
-- #check Set.range (@ZdBasis d)
#check (Submodule.span ℤ (Set.range (OrthonormalBasis.toBasis (@RdBasis d)))).carrier

-- Problem! Zd defined here is a subset of R^d,
-- while Z2Basis is a subset of Submodule Z of R2Basis


-- Z^d as the module on Z spanned by the orthonormal basis
-- seems that there is a problem of implicit variable
-- noncomputable def Z2 {d : ℕ} := Submodule.span ℤ (Set.range (OrthonormalBasis.toBasis R2Basis))
-- Z^2 as the module on Z spanned by the orthonormal basis
-- no implicit variable d

-- a subset of Rd
noncomputable def Zd := Submodule.span ℤ (Set.range (@RdBasis d))

--noncomputable def Zd' := Submodule.span ℤ (Set.range (@ZdBasis d))
-- noncomputable def Zd'' := AddSubgroup.closure (Set.range (@RdBasis d))

#check @Zd d
--#check @Zd' d
-- #check @Zd'' d

variable (w : EuclideanSpace ℝ (Fin d)) (h : w ∈ (@Zd d))



-- want to prove that the ι-th coordinate of v is an integer.
-- the definition of Z2 says that it is a Z module spanned by
-- the set of vectors in R2Basis. Is there a theorem that
-- v is a Z-combination of the basis vectors?


-- def isInteger (x : ℝ) := ∃ (n : ℤ), x = n
-- -- Int.floor x = x


-- lemma IsInteger_EqFloor (x : ℝ) : isInteger x → Int.floor x = x := by
--  intro hx
--  unfold isInteger at hx
--  obtain ⟨n, hn⟩ := hx
--  calc (Int.floor x : ℝ) = (Int.floor (n : ℝ) : ℝ) := by rw [hn]
--  _ = n := by simp
--  _ = x := by exact hn.symm


-- lemma IsZeroIntLessThanOne (m : ℤ) (h0 : 0 ≤ m) (h1 : m < (1 : ℝ)) : m = 0 := by
--  have : m < 1 := by
--   rw [←Int.cast_one] at h1
--   exact Int.cast_lt.mp h1
--  linarith
-- -- thanks to David Renshaw on Zulip

-- lemma Eq_Int_dist_lt_one (x y : ℝ) (hx : isInteger x) (hy : isInteger y) : |x - y| < 1 → x = y := by
--  intro h
--  rw [← IsInteger_EqFloor x hx, ← IsInteger_EqFloor y hy] at h
--  rw [← Int.cast_sub, ← Int.cast_abs] at h
--  have : |⌊x⌋ - ⌊y⌋| = 0 := by
--   exact IsZeroIntLessThanOne |⌊x⌋ - ⌊y⌋| (abs_nonneg (⌊x⌋ - ⌊y⌋)) h
--  rw [abs_eq_zero, sub_eq_zero] at this
--  rw [← IsInteger_EqFloor x hx, ← IsInteger_EqFloor y hy]
--  exact congrArg Int.cast this

-- lemma IsIntegerLimitSeqInteger (x : ℕ → ℝ) (p : ℝ) (hxint : ∀ (n : ℕ), isInteger (x n)) (hxconv : Tendsto x atTop (nhds p))
--  : isInteger p := by
--  rw [Metric.tendsto_nhds] at hxconv
--  simp at hxconv
--  obtain ⟨N1, hN1⟩ := hxconv (1/2) one_half_pos
--  obtain ⟨m, hm⟩ := hxint N1
--  unfold isInteger
--  use m
--  apply eq_of_forall_dist_le
--  intro ε hε
--  obtain ⟨N2, hN2⟩ := hxconv (min ε (1/2)) (lt_min hε one_half_pos)
--  have hxN1 : dist (x N1) p < (1/2) := by
--   exact hN1 N1 (le_refl N1)
--  have hxN2 : dist (x N2) p < (1/2) := by
--   exact (lt_min_iff.mp (hN2 N2 (le_refl N2))).2
--  have hx12 : dist (x N1) (x N2) < 1 :=
--   calc dist (x N1) (x N2) ≤ dist (x N1) p + dist p (x N2) := by exact dist_triangle (x N1) p (x N2)
--   _ = dist (x N1) p + dist (x N2) p := by nth_rw 2 [dist_comm]
--   _ < (1/2) + dist (x N2) p := by exact add_lt_add_right hxN1 (dist (x N2) p)
--   _ < (1/2) + (1/2) := by exact add_lt_add_left hxN2 (1/2)
--   _ = 1 := by norm_num
--  rw [Real.dist_eq] at hx12
--  have hm2 : x N1 = x N2 := by
--   exact Eq_Int_dist_lt_one (x N1) (x N2) (hxint N1) (hxint N2) hx12
--  have hm3 : m = x N2 :=
--   calc m = x N1 := by exact hm.symm
--   _ = x N2 := by exact hm2
--  have : dist p m < ε :=
--   calc dist p (m : ℝ) = dist (m : ℝ) p := by exact dist_comm p (m : ℝ)
--   _ = dist (x N2) p := by rw [hm3]
--   _ < min ε (1/2) := by exact hN2 N2 (le_refl N2)
--   _ ≤ ε := by simp
--  exact le_of_lt this

-- lemma IsInteger_iff_setrangeZR (s : ℝ) : s ∈ Set.range ⇑(algebraMap ℤ ℝ) ↔ ∃ (n : ℤ), s = n := by
--  constructor
--  · simp
--    intro n hn
--    use n
--    exact hn.symm
--  · intro hs
--    obtain ⟨n, hn⟩ := hs
--    use n
--    exact hn.symm


-- lemma IsInteger_componentsZ2
--   (v : R2) : v ∈ Z2.carrier ↔ ∀ (i : Fin 2), isInteger (v i) := by
--  constructor
--  · intro hv i
--    have : v i ∈ Set.range ⇑(algebraMap ℤ ℝ) := by
--     exact (Basis.mem_span_iff_repr_mem ℤ (OrthonormalBasis.toBasis R2Basis) v).mp hv i
--    unfold isInteger
--    obtain ⟨n, hn⟩ := this
--    use n
--    simp at hn
--    exact hn.symm
--  · intro hv
--    unfold Z2
--    apply (Basis.mem_span_iff_repr_mem ℤ (OrthonormalBasis.toBasis R2Basis) v).mpr
--    intro i
--    rw [IsInteger_iff_setrangeZR _]
--    exact hv i


open MeasureTheory.Measure MeasureTheory
open InnerProductSpace.Core

-- -- the counting measure on the lattice Z^d
-- noncomputable def countZ2 : Measure (R2) :=
--  sum (fun x ↦ if x ∈ Z2 then dirac x else 0)

-- the counting measure on the lattice Z^2
noncomputable def countZd : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
 sum (fun x ↦ if x ∈ Zd then dirac x else 0)

-- -- n-times convolution with itself
-- noncomputable def convolution_self : ℕ → ((R2 → ℝ) → (R2 → ℝ))
--   | 0 => fun f ↦ (fun x ↦ 1)
--   | n + 1 => fun f ↦ (convolution f ((convolution_self n) f) (ContinuousLinearMap.lsmul ℝ ℝ) (countZ2 d))

-- n-times convolution with itself on Z2
noncomputable def convolution_self :
    ℕ → ((EuclideanSpace ℝ (Fin d) → ℝ) → (EuclideanSpace ℝ (Fin d) → ℝ))
  | 0 => fun _ ↦ (fun _ ↦ 1)
  | n + 1 => fun f ↦
    (convolution f ((convolution_self n) f) (ContinuousLinearMap.lsmul ℝ ℝ) countZd)


-- lemma A2_1 : ∀ (p : ℝ[X]), ∃ (N : ℝ), ∀ (x : ℝ), x ≥ N → |p.eval x| < Real.exp x := by
--  intro p
--  have h1 : Tendsto (fun x ↦ eval x p / Real.exp x) atTop (nhds 0) := by
--   exact Polynomial.tendsto_div_exp_atTop p
--  rw [tendsto_nhds] at h1
--  have h2 : (fun x ↦ eval x p / Real.exp x) ⁻¹' (Metric.ball (0 : ℝ) 1) ∈ atTop := by
--   apply h1
--   apply Metric.isOpen_ball
--   apply Metric.mem_ball_self
--   norm_num
--  rw [mem_atTop_sets] at h2
--  obtain ⟨N, hN⟩ := h2
--  use N
--  intro x
--  have h21 (a : ℝ): a - 0 = a := by ring
--  have h3 (a : ℝ): a ∈ Metric.ball (0 : ℝ) 1 ↔ |a| < 1 := by
--   constructor
--   intro h31
--   have h32 : |a - 0| < 1 := by exact h31
--   rw [← h21 a]
--   exact h32
--   intro h33
--   rw [← h21 a] at h33
--   exact h33
--  intro hx
--  have h4 : eval x p / Real.exp x  ∈ Metric.ball (0 : ℝ)  1:= by
--   apply hN
--   exact hx
--  rw [h3] at h4
--  rw [abs_div] at h4
--  rw [div_lt_iff] at h4
--  rw [one_mul] at h4
--  rw [← abs_of_pos (Real.exp_pos x)]
--  exact h4
--  rw [abs_of_pos]
--  exact Real.exp_pos x
--  exact Real.exp_pos x


-- lemma IsFiniteBoundedIntervalIntegers : ∀ (p q : ℤ) (h : p < q), Set.Finite {n : ℤ | p ≤ n ∧ n ≤ q} := by
--  intro p q hpq
--  have hpq' : (p : ℤ) < (q : ℤ) := by
--   exact hpq
--  have h : {n : ℤ | p ≤ n ∧ n ≤ q} = Set.uIcc (p : ℤ) (q : ℤ) := by
--   rw [Set.uIcc_of_lt hpq']
--   rfl
--  rw [h]
--  exact Set.finite_interval (p : ℤ) (q : ℤ)

-- lemma IsFiniteBoundedSetIntegers : ∀ (M : ℝ) (hM : 1 ≤ M), Set.Finite {n : ℤ | |n| ≤ M} := by
--  intro M
--  have h : {n : ℤ | |n| ≤ M} = {n : ℤ | - ⌊M⌋ ≤ n ∧ n ≤ ⌊M⌋} := by
--   ext n
--   constructor
--   intro hn
--   simp at hn
--   simp
--   rw [← abs_le]
--   refine Int.le_floor.mpr ?h.mp.a
--   have : |(n : ℝ)| = |n| := by exact Int.cast_abs.symm
--   rw [← this]
--   exact hn
--   intro hn
--   simp at hn
--   simp
--   rw [abs_le]
--   refine and_comm.mpr ?h.mpr.a
--   constructor
--   rw [← Int.le_floor]
--   exact hn.2
--   rw [neg_le] at hn
--   rw [Int.le_floor] at hn
--   rw [neg_le]
--   have : -(n : ℝ) = (-n : ℤ) := by exact (Int.cast_neg n).symm
--   rw [this]
--   exact hn.1
--  rw [h]
--  intro hM
--  apply IsFiniteBoundedIntervalIntegers
--  rw [← Int.floor_pos] at hM
--  exact neg_lt_self hM



-- -- lemma A2_2 : ∀ (M : ℝ) (hM : 1 ≤ M), Set.Finite {x : R2| x ∈ Z2 ∧ ‖x‖ ≤ M} := by
-- --  intro M hM
-- --  have hxleMi : {x : R2| x ∈ Z2 ∧ ‖x‖ ≤ M} ⊆ {x : R2| x ∈ Z2 ∧ ∀ (ι : (Fin 2)), |x ι| ≤ M} := by
-- -- -- this is a subset of all x with |x_i| < M
-- --   simp
-- --   intro x hxZ2 hx_M
-- --   constructor
-- --   exact hxZ2
-- --   intro ι
-- --   have : |x ι| ≤ ‖x‖ := by
-- --    rw [EuclideanSpace.norm_eq]
-- --    refine Real.le_sqrt_of_sq_le ?h
-- --    rw [← Real.norm_eq_abs (x ι)]
-- --    have hnorm : ∀ (ι : (Fin 2)) (hiota : ι ∈ Finset.univ), 0 ≤ ‖x ι‖ := by
-- --     exact fun ι hiota => norm_nonneg (x ι)
-- --    have hnorm2 : ∀ (ι : (Fin 2)) (hiota : ι ∈ Finset.univ), 0 ≤ ‖x ι‖^2 := by
-- --     exact fun ι hiota => sq_nonneg ‖x ι‖
-- --    exact Finset.single_le_sum hnorm2 (Finset.mem_univ ι)
-- --   exact le_trans this hx_M

-- --  have hleMifin : Set.Finite {x : R2| x ∈ Z2 ∧ ∀ (ι : (Fin 2)), |x ι| ≤ M} := by
-- -- -- the latter is a finite set : M^d
-- --   simp

-- --  exact Set.Finite.subset hleMifin hxleMi

-- theorem norm_sq_eq {𝕜 : Type u_8} [RCLike 𝕜] {n : Type u_9} [Fintype n] (x : EuclideanSpace 𝕜 n)
--  : ‖x‖ ^ 2 = Finset.sum Finset.univ fun (i : n) => ‖x i‖ ^ 2 := by
--  have : ‖x‖ = Real.sqrt (Finset.sum Finset.univ fun (i : n) => ‖x i‖ ^ 2) := by
--   exact EuclideanSpace.norm_eq x
--  rw [← sq_eq_sq, Real.sq_sqrt] at this
--  exact this
--  have : ∀ (i : n), 0 ≤ ‖x i‖ ^ 2 := by
--   intro i
--   exact sq_nonneg _
--  apply Finset.sum_nonneg
--  intro i hi
--  exact this i
--  exact norm_nonneg _
--  exact Real.sqrt_nonneg _

-- theorem single_le_norm --{𝕜 : Type u_8} [IsROrC 𝕜]
-- {n : Type u_9} [Fintype n] (i : n) (x : EuclideanSpace ℝ n)
--  : |x i| ≤ ‖x‖ := by
--  rw [← Real.norm_eq_abs, ← (abs_of_nonneg (norm_nonneg _)), ← (abs_of_nonneg (norm_nonneg x))]
--  rw [← sq_le_sq, norm_sq_eq]
--  have hnorm : ∀ k ∈ Finset.univ, 0 ≤ ‖x k‖ ^ 2 := by
--   intro k hk
--   exact sq_nonneg _
--  apply (Finset.single_le_sum hnorm (Finset.mem_univ i))

-- -- Bounded sets in Z2 are finite

-- lemma A2_2 (M : ℝ) (hM : M > 0) : Set.Finite {x ∈ Z2 | ‖x‖ ≤ M} := by
--  have hComp : IsCompact {x ∈ Z2 | ‖x‖ ≤ M} := by
--   refine Metric.isCompact_of_isClosed_isBounded ?hc ?hb
--   have hBall : {x ∈ Z2 | dist x 0 ≤ M} = Z2.carrier ∩ Metric.closedBall 0 M := by
--    exact rfl
--   have Z2Closed: IsClosed Z2.carrier := by
--    apply (isSeqClosed_iff_isClosed).mp
--    unfold IsSeqClosed
--    intro x p hx hxtop
--    have hxint : ∀ (n : ℕ), ∀ (i : Fin 2), isInteger ((x n) i) := by
--     intro n i
--     exact (IsInteger_componentsZ2 (x n)).mp (hx n) i
--    rw [IsInteger_componentsZ2 p]
--    have hpint : ∀ (i : Fin 2), isInteger (p i) := by
--     intro i
--     have hxiconvpi : Tendsto (fun n => (x n) i) atTop (nhds (p i)) := by
--      exact Tendsto.comp (Continuous.tendsto (ContinuousLinearMap.continuous (EuclideanSpace.proj i)) p) hxtop
--     apply IsIntegerLimitSeqInteger
--     · intro n
--       exact hxint n i
--     · exact hxiconvpi
--    intro i
--    exact hpint i
--   have BallDef : {x : (R2)| dist x 0 ≤ M} = {x : (R2)| ‖x‖ ≤ M} := by
--    simp
--   have BallClosed : IsClosed {x : (R2)| ‖x‖ ≤ M} := by
--    rw [← BallDef]
--    exact Metric.isClosed_ball
--   exact IsClosed.inter Z2Closed BallClosed
--   refine isBounded_iff_forall_norm_le.mpr ?hb.a
--   use M
--   simp
--  refine IsCompact.finite hComp ?hs'
--  apply DiscreteTopology.of_subset
--  have hDisc : DiscreteTopology Z2 := by
--   exact Zspan.instDiscreteTopologySubtypeMemSubmoduleIntInstSemiringIntToAddCommMonoidToAddCommGroupIntModuleInstMembershipSetLikeSpanRangeCoeBasisRealSemiringToModuleNormedFieldToSeminormedAddCommGroupInstFunLikeInstTopologicalSpaceSubtypeToTopologicalSpaceToUniformSpaceToPseudoMetricSpace
--      (OrthonormalBasis.toBasis R2Basis)
--  exact hDisc
--  intro x hx
--  exact hx.1

-- lemma A2_3 : ∀ (t : ℝ), 0 < t →
-- ∃ (S : ℝ), M₀ ≤ S ∧ ∀ (s : ℝ), S ≤ s →
-- c_δ * Real.exp (- (2 + δ) * Real.log (1 + s)) < t:= by
--  intro t ht
--  have A2_3_1: Tendsto (fun (s : ℝ) => 1 + s) atTop atTop := by
--   exact Filter.tendsto_atTop_add_const_left _ _ Filter.tendsto_id
--  have A2_3_2: Tendsto (fun (s : ℝ) => Real.log (1 + s)) atTop atTop := by
--   exact Tendsto.comp (Real.tendsto_log_atTop) A2_3_1
--  have A2_3_3: Tendsto (fun (s : ℝ) => - (2 + δ) * Real.log (1 + s)) atTop atBot := by
--   apply Filter.Tendsto.neg_const_mul_atTop _ A2_3_2
--   rw [Left.neg_neg_iff]
--   exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg 2) hδ
--  have A2_3_4: Tendsto (fun (s : ℝ) => Real.exp (- (2 + δ) * Real.log (1 + s))) atTop (nhds 0) := by
--   apply Tendsto.comp (Real.tendsto_exp_atBot) A2_3_3
--  rw [Metric.tendsto_nhds] at A2_3_4
--  obtain ⟨V, hV⟩ := Filter.Eventually.exists_mem (A2_3_4 (t / c_δ) (div_pos ht hc_δ))
--  simp at hV
--  obtain ⟨S', hS⟩ := hV.1
--  let S := max M₀ S'
--  use S
--  constructor
--  · exact le_max_left _ _
--  intro s hs
--  rw [← (lt_div_iff' hc_δ)]
--  simp
--  apply hV.2 s (hS s _)
--  apply le_trans (le_max_right _ _) hs

-- lemma A2_4 (x : R2) : 0 < b a δ x := by
--  unfold b
--  exact mul_pos (Real.exp_pos _) (P1 x)

-- lemma A2_5 (x : R2) : x ∈ Z2 ∧ x ≠ 0 → 1 ≤ ‖x‖ := by
--  intro hx
--  rw [← norm_ne_zero_iff, ne_eq _ _] at hx
--  have : ∃ (i : Fin 2), x i ≠ 0 := by
--   by_contra! hxn
--   have hxi0 : (fun i => ‖x i‖ ^ 2) = 0 := by
--    ext i
--    simp
--    exact hxn i
--   have : ‖x‖ = 0 := by
--    rw [EuclideanSpace.norm_eq x, hxi0]
--    simp
--   exact hx.2 this
--  obtain ⟨i ,hi⟩ := this
--  have hxiz : isInteger (x i) := by
--   apply (IsInteger_componentsZ2 x).mp
--   exact hx.1
--  obtain ⟨n, hn⟩ := hxiz
--  have hqnz : (1 : ℤ) ≤ |(n : ℝ)| := by
--   rw [← Int.cast_abs, Int.cast_le]
--   by_contra! hnle
--   rw [Int.abs_lt_one_iff] at hnle
--   rw [hnle, Int.cast_zero] at hn
--   contradiction
--  have : |(n : ℝ)| ≤ ‖x‖ := by
--   rw [← hn]
--   exact single_le_norm i x
--  rw [← Int.cast_abs] at this
--  rw [← Int.cast_abs, Int.cast_one] at hqnz
--  linarith

-- lemma A2_6 (s t : ℝ) : 0 < s ∧ 0 < t ∧ s ≤ t →
--  c_δ * Real.exp (- (2 + δ) * Real.log (1 + t)) ≤ c_δ * Real.exp (- (2 + δ) * Real.log (1 + s)) := by
--   intro hst
--   have hs : 0 < 1 + s := by exact add_pos zero_lt_one hst.left
--   have ht : 0 < 1 + t := by exact add_pos zero_lt_one hst.right.left
--   have : -(2 + δ) < 0 := by linarith
--   rw [mul_le_mul_left hc_δ, Real.exp_le_exp, mul_le_mul_left_of_neg this]
--   rw [Real.log_le_log_iff hs ht]
--   linarith


-- lemma A2 : ∃ (M' : ℝ), ∀ (x : R2), x ∈ Z2 → (b a δ (M' • x) ≤ b a δ x) := by
--  have hb1 (x : R2) : (2 + δ) * Real.log (1 + ‖x‖) + (-2 * (2 + δ) * Real.log (1 + ‖x‖)) = (- (2 + δ) * Real.log (1 + ‖x‖)):= by ring
--  have hb2 (x : R2) : b a δ x ≤ c_δ * Real.exp (- (2 + δ) * Real.log (1 + ‖x‖)) := by
--   unfold b
--   calc Real.exp ((2 + δ) * Real.log (1 + ‖x‖)) * a x ≤ Real.exp ((2 + δ) * Real.log (1 + ‖x‖)) * (c_δ * Real.exp (-2 * (2 + δ) * Real.log (1 + ‖x‖)))
--    := by exact (mul_le_mul_left (Real.exp_pos ((2 + δ) * Real.log (1 + ‖x‖)))).mpr (P2 x)
--   _ = c_δ * (Real.exp ((2 + δ) * Real.log (1 + ‖x‖)) * Real.exp (-2 * (2 + δ) * Real.log (1 + ‖x‖)))
--    := by ring
--   _ = c_δ * Real.exp ((2 + δ) * Real.log (1 + ‖x‖) + (-2 * (2 + δ) * Real.log (1 + ‖x‖))) := by rw [(Real.exp_add ((2 + δ) * Real.log (1 + ‖x‖)) (-2 * (2 + δ) * Real.log (1 + ‖x‖))).symm]
--   _ = c_δ * Real.exp (-(2 + δ) * Real.log (1 + ‖x‖))
--    := by rw [hb1]
--  have hb3 (x : R2) : x ∈ Z2 ∧ x ≠ 0 → ∃ (M1 : ℝ), M₀ ≤ M1 ∧ ∀ (M : ℝ), M1 ≤ M → b a δ (M • x) ≤ b a δ x := by
--   intro hx
--   obtain ⟨S, hS⟩ := A2_3 δ hδ c_δ hc_δ M₀ (b a δ x) (A2_4 a δ P1 x)
--   let M1 := max S M₀
--   use M1
--   constructor
--   · exact le_max_right _ _
--   intro M hM
--   have hM1 : 0 < M :=
--    calc 0 < M₀ := by linarith
--    _ ≤ M1 := by exact le_max_right _ _
--    _ ≤ M := by exact hM
--   have hM2 : M ≤ M * ‖x‖ := by
--    nth_rw 1 [← one_mul M]
--    nth_rw 1 [mul_comm]
--    rw [mul_le_mul_left hM1]
--    exact A2_5 x hx
--   have hM3 : 0 < M * ‖x‖ := by
--    linarith
--   calc b a δ (M • x) ≤ c_δ * Real.exp (- (2 + δ) * Real.log (1 + ‖M • x‖)) := by exact hb2 (M • x)
--   _ = c_δ * Real.exp (- (2 + δ) * Real.log (1 + ‖M‖ * ‖x‖)) := by rw [norm_smul _ _]
--   _ = c_δ * Real.exp (- (2 + δ) * Real.log (1 + |M| * ‖x‖)) := by simp
--   _ = c_δ * Real.exp (- (2 + δ) * Real.log (1 + M * ‖x‖)) := by rw [abs_of_pos hM1]
--   _ ≤ c_δ * Real.exp (- (2 + δ) * Real.log (1 + M)) := by exact A2_6 δ hδ c_δ hc_δ M (M * ‖x‖) (And.intro hM1 (And.intro hM3 hM2))
--   _ ≤ b a δ x := by exact le_of_lt (hS.2 M (le_trans (le_max_left _ _) hM))

--  let S := {x : R2 | x ∈ Z2 ∧ ‖x‖ ≤ M₀ ∧ x ≠ 0}
--  have hxS (x : R2) : x ∈ S → x ∈ Z2 ∧ ‖x‖ ≤ M₀ ∧ x ≠ 0 := by
--   exact fun a => a
--  have hxS' (x : R2) : x ∈ S → x ∈ Z2 ∧ x ≠ 0 := by
--   intro hx
--   constructor
--   exact (hxS x hx).1
--   exact (hxS x hx).2.2
--  let S' := {x : R2 | x ∈ Z2 ∧ ‖x‖ ≤ M₀}
--  have hSS' : S ⊆ S' := by
--   intro x hx
--   exact And.intro hx.1 hx.2.1
--  let hS' := A2_2 M₀ (lt_trans zero_lt_one hM₀)
--  let hS := Set.Finite.subset hS' hSS'
--  have hSne : Set.Nonempty S := by
--   use EuclideanSpace.single 0 1
--   constructor
--   · apply (IsInteger_componentsZ2 (EuclideanSpace.single 0 1)).mpr
--     intro i
--     by_cases hi : i = 0
--     · simp
--       rw [hi]
--       simp
--       use 1
--       simp
--     · simp
--       push_neg at hi
--       have : (if i = 0 then (1 : ℝ) else 0) = 0 := by
--        simp
--        push_neg
--        exact hi
--       rw [this]
--       use 0
--       simp
--   rw [← norm_ne_zero_iff]
--   rw [EuclideanSpace.norm_single]
--   simp
--   linarith
--  obtain ⟨x₀, hx₀⟩ := Set.Finite.exists_maximal_wrt (fun (x : R2) => if hf : x ∈ S then Classical.choose (hb3 x (hxS' x hf)) else 0) S hS hSne
--  let M' := Classical.choose (hb3 x₀ (hxS' x₀ hx₀.1))
--  let hM' := Classical.choose_spec (hb3 x₀ (hxS' x₀ hx₀.1))
--  have hM'1 : M' = choose (_ : ∃ M1, M₀ ≤ M1 ∧ ∀ (M : ℝ), M1 ≤ M → b a δ (M • x₀) ≤ b a δ x₀) := by
--   rfl
--  use M'
--  intro x hx
--  by_cases hxnorm : ‖x‖ > M₀
--  · have : 1 < M' := by
--     apply lt_of_lt_of_le hM₀
--     exact (Classical.choose_spec (hb3 x₀ (hxS' x₀ hx₀.1))).1
--    apply P5 x (M' • x)
--    constructor
--    · exact le_of_lt hxnorm
--    · rw [norm_smul, Real.norm_eq_abs, (abs_of_pos (lt_trans zero_lt_one this))]
--      nth_rw 1 [← mul_one ‖x‖, mul_comm _ 1]
--      exact mul_le_mul (le_of_lt this) (le_refl _) (norm_nonneg x) (le_of_lt (lt_trans zero_lt_one this))
--  push_neg at hxnorm
--  by_cases hxzero : ‖x‖ = 0
--  · rw [norm_eq_zero] at hxzero
--    rw [hxzero, smul_zero]
--  · push_neg at hxzero
--    rw [norm_ne_zero_iff] at hxzero
--    let Mx := Classical.choose (hb3 x (And.intro hx hxzero))
--    let hMx := Classical.choose_spec (hb3 x (And.intro hx hxzero))
--    have hM1 : Mx = Classical.choose (hb3 x (And.intro hx hxzero)) := by
--     rfl
--    have hM₀M : M₀ ≤ Mx := by
--     exact hMx.1
--    have hMM : Mx ≤ M' := by
--     have hxinS : x ∈ S := by
--      exact And.intro hx (And.intro hxnorm hxzero)
--     have : M' ≤ Mx → M' = Mx := by
--      let hX := hx₀.2 x hxinS
--      rw [dif_pos hx₀.1, dif_pos hxinS] at hX
--      exact hX
--     by_contra! P
--     push_neg
--     have eP : M' = Mx := by exact this (le_of_lt P)
--     linarith
--    have hMM' : ‖Mx • x‖ ≤ ‖M' • x‖ := by
--     rw [norm_smul, norm_smul]
--     apply mul_le_mul
--     rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos, abs_of_pos]
--     exact hMM
--     exact lt_of_lt_of_le (lt_trans zero_lt_one hM₀) (le_trans hM₀M hMM)
--     exact lt_of_lt_of_le (lt_trans zero_lt_one hM₀) hM₀M
--     exact le_refl _
--     exact norm_nonneg _
--     exact norm_nonneg _
--    have hMxx : M₀ ≤ ‖Mx • x‖ := by
--     nth_rw 1 [← mul_one M₀]
--     rw [norm_smul, Real.norm_eq_abs, abs_of_pos, mul_comm, mul_comm Mx ‖x‖]
--     apply mul_le_mul
--     exact A2_5 x (And.intro hx hxzero)
--     exact hM₀M
--     exact le_of_lt (lt_trans zero_lt_one hM₀)
--     exact norm_nonneg x
--     exact lt_of_lt_of_le (lt_trans zero_lt_one hM₀) hM₀M
--    calc
--     b a δ (M' • x) ≤ b a δ (Mx • x) := by exact P5 (Mx • x) (M' • x) (And.intro hMxx hMM')
--     _ ≤ b a δ x := by exact hMx.2 Mx (le_refl _)
