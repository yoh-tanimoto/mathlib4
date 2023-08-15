
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Embedding.Basic
import Mathlib.Algebra.Hom.Ring
import Mathlib.Tactic.ClearExcept
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Basic

open BigOperators

/--
Given a finite type and a finset , returns the finite set of all functions with range contained in
that finset
-/
def function_finset (A : Type) (B : Type) [DecidableEq A] [Fintype A] (S : Finset B) : Finset (A -> B) :=
  Fintype.piFinset (fun _ => S)

-- TODO generalize to dependent piFinset
@[simp]
lemma Fin.cons_mem_piFinset_iff {F} {n : ℕ} (a : (Fin n → F)) (b: F) (S : Finset F) :
    @Fin.cons _ (fun _ => F) b a ∈ Fintype.piFinset (fun _ => S)
    ↔
    a ∈ Fintype.piFinset (fun _ => S)
    ∧
    b ∈ S := by
  simp only [Fintype.mem_piFinset]
  constructor
  · intros ha_1
    constructor
    · exact fun a_1 ↦ ha_1 (succ a_1)
    · exact ha_1 0
  · intro ha1 a1
    cases Fin.eq_zero_or_eq_succ a1
    · simp_all only [cons_zero]
    · rename_i h
      unhygienic with_reducible aesop_destruct_products
      aesop_subst h_1
      simp_all only [cons_succ]

@[simp]
lemma Fin.cons_comp_succ {F} {n : ℕ} (a : (Fin n → F)) (b : F) :
    @Fin.cons _ (fun _ => F) b a ∘ Fin.succ = a := by
  apply Eq.refl

lemma and_or_and_not_iff (p q : Prop) : ((p ∧ q) ∨ (p ∧ ¬ q)) ↔ p := by
  tauto

lemma and_and_and_not_iff (p q : Prop) : ((p ∧ q) ∧ (p ∧ ¬ q)) ↔ false := by
  tauto

lemma mk_prod_of_proj (A B : Type) (ab : A × B) : (ab.fst, ab.snd) = ab := by
  exact rfl

lemma Finsupp.cons_sum (n : ℕ) (σ: Fin n →₀ ℕ) {i : ℕ} : (Finsupp.sum σ (fun _ e ↦ e)) + i = Finsupp.sum (Finsupp.cons i σ) fun _ e ↦ e := by

  rw [eq_comm]
  simp_rw [add_comm]

  convert Fin.sum_cons i σ
  · rw [Finsupp.sum_fintype]
    congr
    simp
  · rw [Finsupp.sum_fintype]
    simp

lemma MvPolynomial.support_nonempty_iff {F σ} [Field F] (p : MvPolynomial σ F) :
    (MvPolynomial.support p).Nonempty ↔ p ≠ 0 := by
  rw [ne_eq, ←MvPolynomial.support_eq_empty, Finset.nonempty_iff_ne_empty]

lemma MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le {F} [Field F] (n: ℕ)
  (p : MvPolynomial (Fin (Nat.succ n)) F)
  (i : ℕ)
  (hi : (Polynomial.coeff ((MvPolynomial.finSuccEquiv F n) p) i) ≠ 0) :
    MvPolynomial.totalDegree (Polynomial.coeff ((MvPolynomial.finSuccEquiv F n) p) i) + i
      ≤ MvPolynomial.totalDegree p := by
  have hp'_sup : (Polynomial.coeff ((MvPolynomial.finSuccEquiv F n) p) i).support.Nonempty := by
    rw [MvPolynomial.support_nonempty_iff]
    exact hi
  -- Let sigma be a monomial index of (Polynomial.coeff ((MvPolynomial.finSuccEquiv F n) p) i) of
  -- maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (MvPolynomial.support _) hp'_sup
                          (fun s => Finsupp.sum s fun _ e => e)
  -- Then cons i σ is a monomial index of p with total degree equal to the desired bound
  let σ' : Fin (n+1) →₀ ℕ := Finsupp.cons i σ
  convert MvPolynomial.le_totalDegree (p := p) (s := σ') _
  · rw [MvPolynomial.totalDegree, hσ2, Finsupp.cons_sum]
  · rw [←MvPolynomial.support_coeff_finSuccEquiv]
    exact hσ1

/-- MvPolynomials over a type of variables are always constant -/
lemma MvPolynomial.eq_C_of_empty {F σ} [Field F] [h : IsEmpty σ]
  (p : MvPolynomial σ F) : p = C (p.coeff 0) := by
  ext m
  have m0 : m = 0 := by
    ext a
    by_contra
    exact IsEmpty.false a
  rw [m0]
  simp

-- Following the wikipedia proof
-- I don't think that the wikipedia proof technique of starting at n=1 is necessary, so I start at n = 0
lemma schwartz_zippel (F : Type) [Field F] [DecidableEq F] (n : ℕ)
  (p : MvPolynomial (Fin (n)) F) (hp : p ≠ 0) (S : Finset F) :
  (Finset.filter (fun f => MvPolynomial.eval f p = 0) (function_finset (Fin (n)) F S)).card * S.card
    ≤ (p.totalDegree) * S.card ^ (n)
:= by
  revert p hp S
  induction n with
  | zero =>
    intros p hp S
    convert Nat.zero_le (MvPolynomial.totalDegree p * Finset.card S ^ Nat.zero)
    simp only [Nat.zero_eq, Fin.forall_fin_zero_pi, mul_eq_zero, Finset.card_eq_zero]
    left
    convert Finset.filter_False (function_finset (Fin 0) F S)
    simp only [iff_false]
    -- Because p is a polynomial over the (empty) type Fin 0 of variables, it is constant
    have p_const := MvPolynomial.eq_C_of_empty p
    rw [p_const]
    simp only [Nat.zero_eq, MvPolynomial.eval_C, iff_false, ne_eq]
    contrapose! hp
    rw [hp] at p_const
    rw [p_const]
    simp only [Nat.zero_eq, map_zero]
    done
    -- Now, assume that the theorem holds for all polynomials in n variables.
  | succ n ih =>
    intros p hp S
    -- We can then consider p to be a polynomial in x_1
    set p' : Polynomial (MvPolynomial (Fin n) F) := MvPolynomial.finSuccEquiv F n p with hp'
    -- since p is not identically zero, there is some i such that p_i' is not identically zero
    -- take the largest such i
    set i := p'.natDegree with hi
    set p_i' := Polynomial.coeff p' i with hp_i'
    have h0 : (p'.coeff i).totalDegree + i ≤ (p.totalDegree) := by
      apply MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le
      rw [←Polynomial.leadingCoeff]
      rw [Polynomial.leadingCoeff_ne_zero]
      exact Iff.mpr (AddEquivClass.map_ne_zero_iff (MvPolynomial.finSuccEquiv F n)) hp
    have h1 : Polynomial.coeff p' i ≠ 0 := by
      rw [hi]
      rw [←Polynomial.leadingCoeff]
      rw [Polynomial.leadingCoeff_ne_zero]
      exact Iff.mpr (AddEquivClass.map_ne_zero_iff (MvPolynomial.finSuccEquiv F n)) hp
    -- We use the inductive hypothesis on p_i'
    replace ih := ih p_i' h1 S
    -- We then split the set of possible zeros into a union of two cases:
    -- In the first case, p_i' evaluates to 0.
    have h_first_half :
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      ≤
      (MvPolynomial.totalDegree p - i) * (Finset.card S) ^ n := by
      -- In this case, we bound the size of the set by the inductive hypothesis
      calc
      _ ≤ (MvPolynomial.totalDegree p_i') * (Finset.card S) ^ n := by
        convert ih
        rw [mul_comm, ←Finset.card_product, eq_comm]
        apply Finset.card_congr (fun ab _ => (@Fin.cons _ (fun _ => F)) ab.fst ab.snd )
        · intro ab ha
          rcases ab with ⟨a, b⟩
          rw [Finset.mem_product, Finset.mem_filter] at ha
          rcases ha with ⟨a_mem_S, b_mem_ffS, eval_b_zero⟩
          rw [Finset.mem_filter]
          simp only []
          unfold function_finset
          rw [Fin.cons_mem_piFinset_iff]
          constructor
          · exact ⟨b_mem_ffS, a_mem_S⟩
          · rw [Fin.cons_comp_succ]
            exact eval_b_zero
        · intros ab1 ab2 _ _ hmkeq
          simp only [Fin.cons_eq_cons] at hmkeq
          exact Iff.mpr Prod.ext_iff hmkeq
        · unfold function_finset
          intros b hb
          use (Equiv.piFinSucc n F).toFun b
          rw [exists_prop]
          constructor
          · simp only [Equiv.toFun_as_coe_apply, Equiv.piFinSucc_apply, Finset.mem_product, Finset.mem_filter, Fintype.mem_piFinset]
            simp only [Finset.mem_filter, Fintype.mem_piFinset] at hb
            rcases hb with ⟨hb, hb'⟩
            constructor
            · exact hb 0
            · constructor
              · intro a
                apply hb
              · exact hb'
          · simp only [Equiv.toFun_as_coe_apply, Equiv.piFinSucc_apply]
            -- The below is a simp lemma, so why does the above simp not close?
            refine Fin.cons_self_tail b
      _ ≤ _ := by
        apply Nat.mul_le_mul_right
        exact Nat.le_sub_of_add_le h0
    save
    -- In the second case p_i' does not evaluate to zero.
    have h_second_half :
      Finset.card
          (Finset.filter
            (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
            (function_finset (Fin (Nat.succ n)) F S))
      ≤
      (i) * (Finset.card S) ^ n := by
      clear h_first_half
      -- In this case, given r on which p_i' does not evaluate to zero, p' mapped over the
      -- evaluation
      -- on r of p_i' is a nonzero univariate polynomial of degree i.
      -- There can therefore only be at most i zeros per r value.
      rw [←Finset.card_map (Equiv.toEmbedding (Equiv.piFinSucc n F))]
      rw [Finset.map_filter]
      rw [Finset.card_eq_sum_ones]
      rw [Finset.sum_finset_product_right _
            (s := (Finset.filter (fun r ↦ (MvPolynomial.eval (r)) p_i' ≠ 0)
              (function_finset (Fin (n)) F S)))
            (t := fun r => Finset.filter (fun f => (MvPolynomial.eval ((Equiv.piFinSucc n F).invFun (f, r))) p = 0) S)] -- Note that ((Equiv.piFinSucc n F).invFun (f, r)) can be more simply written with Fin.cons
      · unfold function_finset
        simp_rw [←Finset.card_eq_sum_ones]
        apply le_trans (Finset.sum_le_sum (g := fun _ => i) _)
        · rw [Finset.sum_const, smul_eq_mul, mul_comm]
          apply Nat.mul_le_mul_left
          apply le_trans (Finset.card_filter_le _ _)
          apply le_of_eq
          rw [Fintype.card_piFinset]
          simp only [Finset.prod_const, Finset.card_fin]
        · intros r hr
          simp only [Equiv.invFun_as_coe, Equiv.piFinSucc_symm_apply]
          simp_rw [MvPolynomial.eval_eq_eval_mv_eval']
          rw [←hp']
          simp only [←hp',
            Fintype.mem_piFinset, Finset.mem_filter] at hr
          -- hr2 is in wikipedia P_i(r_2, ... , r_n) ≠ 0
          rcases hr with ⟨hr1, hr2⟩
          -- my pr is wikis P(x_1, r_2, ... r_n) = ∑ x_1^i P_i(r_2, ... r_n)
          save
          set p_r := (Polynomial.map (MvPolynomial.eval r) p') with hp_r
          have : p_r.natDegree = i := by
            rw [←hi] at hr2
            rw [hp_r]
            rw [hi]
            apply Polynomial.natDegree_map_of_leadingCoeff_ne_zero
            -- rw [Polynomial.natDegree_map_eq_iff (f := MvPolynomial.eval r) p']
            unfold Polynomial.leadingCoeff
            exact hr2
          rw [←hi, ←this]
          apply le_trans _ (Polynomial.card_roots' _)
          apply le_trans _ (Multiset.toFinset_card_le _)
          apply Finset.card_le_of_subset
          rw [Finset.subset_iff]
          intro x
          rw [Finset.mem_filter,
            Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, and_imp]
          intros XS hxr
          rw [Polynomial.IsRoot.def]
          rw [hxr]
          -- rw [refl]
          simp only [←hp_r, and_true]
          intro hpr_zero
          contrapose! hr2
          rw [←hp'] at *
          rw [hpr_zero] at this
          rw [Polynomial.natDegree_zero] at this
          rw [←hi, ←this]
          have bar : p_r.coeff 0 = 0 := by simp [hpr_zero]
          rw [←bar]
          simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom, Polynomial.coeff_map]
      · -- Note Polynomial.coeff_natDegree, MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom, are triggering but I don't want them
        unfold function_finset
        simp only [
          Equiv.piFinSucc_symm_apply, Finset.mem_map_equiv, Fintype.mem_piFinset, Function.comp_apply, Fin.cons_comp_succ,
          Prod.forall, Finset.mem_filter, Equiv.invFun_as_coe]
        intros a b
        -- TODO write unfold_projs tactic in Lean 4

        constructor
        · intro hfr
          rcases hfr with ⟨hfr1, hfr2, hfr3⟩
          constructor
          · constructor
            · intro n'
              refine hfr1 (Fin.succ n')
            · exact hfr3
          · constructor
            · refine hfr1 0
            · exact hfr2
        · intro hab
          rcases hab with ⟨⟨hab1, hab1'⟩, hab2, hab3⟩
          rw [←Fintype.mem_piFinset]
          simp only [Fin.cons_mem_piFinset_iff]
          constructor
          · simp [hab1, hab2]
          · exact { left := hab3, right := hab1' }


    -- Putting these results together, we take a union bound over these two cases to finish the
    -- induction
    calc
      -- Pr[A]
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      * Finset.card S
      =
      -- Pr [A ∩ B] + Pr [A ∩ Bᶜ]
      (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (Nat.succ n)) F S))
      )
      * Finset.card S := by
        congr
        rw [←Finset.card_union_add_card_inter]
        rw [Finset.filter_union_right]
        -- todo note filter_or is the symm of this. Golf that proof.
        -- Also if filter and exists, maybe so should filter_inter_right
        rw [←Finset.filter_and]
        simp only [ne_eq, and_or_and_not_iff, and_and_and_not_iff]
        simp only [Finset.filter_False, Finset.card_empty, add_zero]
      -- Pr [B] + Pr [A ∩ Bᶜ]
      _ ≤ (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (function_finset (Fin (Nat.succ n)) F S))
      )
      * Finset.card S := by
        apply Nat.mul_le_mul_right
        rw [add_le_add_iff_right]
        apply Finset.card_le_of_subset
        apply Finset.monotone_filter_right
        rw [Pi.le_def]
        intro i
        aesop
      _ ≤ ((MvPolynomial.totalDegree p - i) * (Finset.card S) ^ n
          +
          (i) * (Finset.card S) ^ n
          )
      * Finset.card S := by
        apply Nat.mul_le_mul_right
        apply add_le_add
        exact h_first_half
        exact h_second_half
      _ ≤
      MvPolynomial.totalDegree p * Finset.card S ^ Nat.succ n := by
        rw [Nat.pow_succ]
        rw [←mul_assoc]
        apply Nat.mul_le_mul_right
        rw [←add_mul]
        apply Nat.mul_le_mul_right
        apply le_of_eq
        apply Nat.sub_add_cancel
        apply le_of_add_le_right h0
