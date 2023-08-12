
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
-- import Mathlib.Data.Polynomial.Degree
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
-- import Mathlib.Tactic.DefeqTransformations

open BigOperators

-- open_locale classical

-- example (A B : Type) (f g : A -> B) (h :  f = g) (x : A) : f x = g x :=
-- begin
--   exact congr_fun h x
-- end

/--
Given a finite type and a finset , returns the finite set of all functions with range contained in
that finset
-/
def function_finset (A : Type) (B : Type) [DecidableEq A] [Fintype A] (S : Finset B) : Finset (A -> B) :=
  Fintype.piFinset (fun _ => S)




-- lemma Fin.elim_succ {F: Type}
--   {n: ℕ}
--   {S: F → Prop}
--   (a: F)
--   (b: Fin n → F)
--   (hab1: ∀ (n' : Fin n), S (b n'))
--   (hab2: S a)
--   (n': Fin (n + 1)) :
--     S ((@Fin.cons n (fun _ => F) (a : F) b n') : F) := by
--   apply?


lemma cases_fin_succ (n : ℕ) (a: Fin (n + 1)) : a = 0 ∨ ∃ b : Fin n, a = Fin.succ b := by
  exact Fin.eq_zero_or_eq_succ a

@[simp]
lemma Fin.cons_mem_piFinset_iff {n : ℕ} (a : (Fin n → F)) (b: F)  (S : Finset F) :
    @Fin.cons _ (fun _ => F) b a ∈ Fintype.piFinset (fun _ => S)
    ↔
    a ∈ Fintype.piFinset (fun _ => S)
    ∧
    b ∈ S := by
  simp only [Fintype.mem_piFinset]
  simp at *
  constructor
  · intros ha_1
    constructor
    · intro a_1
      have foo := ha_1 (Fin.succ a_1)
      simp at foo
      exact foo
    · have foo := ha_1 0
      simp at foo
      exact foo
  · intro ha1 a1
    have foo := Fin.eq_zero_or_eq_succ a1
    cases foo
    · simp_all only [cons_zero]
    · rename_i h
      unhygienic with_reducible aesop_destruct_products
      aesop_subst h_1
      simp_all only [cons_succ]




@[simp]
lemma Fin.cons_comp_succ {n : ℕ} (a : (Fin n → F)) (b : F) :
    @Fin.cons _ (fun _ => F) b a ∘ Fin.succ = a := by
  apply Eq.refl

lemma and_or_and_not_iff (p q : Prop) : ((p ∧ q) ∨ (p ∧ ¬ q)) ↔ p := by
  tauto

lemma and_and_and_not_iff (p q : Prop) : ((p ∧ q) ∧ (p ∧ ¬ q)) ↔ false := by
  tauto

lemma mk_prod_of_proj (A B : Type) (ab : A × B) : (ab.fst, ab.snd) = ab := by
  exact rfl

lemma foos (a b : ℕ) (aa : a ≤ b ) (shj : b ≤ a) : a = b := by
  exact Nat.le_antisymm aa shj

lemma Finsupp.cons_sum (n : ℕ) (σ: Fin n →₀ ℕ) : (Finsupp.sum σ (fun _ e ↦ e)) + i = Finsupp.sum (Finsupp.cons i σ) fun _ e ↦ e := by

  rw [eq_comm]
  simp_rw [add_comm]

  convert Fin.sum_cons i σ
  · rw [Finsupp.sum_fintype]
    congr
    simp
  · rw [Finsupp.sum_fintype]

    simp


lemma MvPolynomial.support_nonempty_iff [Field F] (p : MvPolynomial σ F) :
  Finset.Nonempty (MvPolynomial.support p) ↔ p ≠ 0 := by
  simp
  rw [←MvPolynomial.support_eq_empty]
  rw [Finset.nonempty_iff_ne_empty]

lemma foosdad [Field F] (n: ℕ)
  (p : MvPolynomial (Fin (Nat.succ n)) F)
  (i : ℕ)
  (hi : (Polynomial.coeff ((MvPolynomial.finSuccEquiv F n) p) i) ≠ 0)
-- hp: p ≠ 0
-- S: Finset F
-- p': Polynomial (MvPolynomial (Fin n) F) := ↑
-- hp': p' = ↑(MvPolynomial.finSuccEquiv F n) p
-- i: ℕ := Polynomial.natDegree p'
-- hi: i = Polynomial.natDegree p'
-- p_i': MvPolynomial (Fin n) F := Polynomial.coeff p' i
-- hp_i': p_i' = Polynomial.coeff p' i
:
    MvPolynomial.totalDegree (Polynomial.coeff ((MvPolynomial.finSuccEquiv F n) p) i) + i ≤ MvPolynomial.totalDegree p := by


  have hp'_sup : (Polynomial.coeff ((MvPolynomial.finSuccEquiv F n) p) i).support.Nonempty := by
    rw [MvPolynomial.support_nonempty_iff]
    exact hi
  -- Let sigma be a monomial index of (Polynomial.coeff ((MvPolynomial.finSuccEquiv F n) p) i) of maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (MvPolynomial.support _) hp'_sup (fun s => Finsupp.sum s fun _ e => e)

  let σ' : Fin (n+1) →₀ ℕ := Finsupp.cons i σ
  -- let σ' : Fin (n+1) →₀ ℕ := Finsupp.ofSupportFinite σ'_ (by exact Set.toFinite (Function.support σ'_))



  convert MvPolynomial.le_totalDegree (p := p) (s := σ') _
  · unfold MvPolynomial.totalDegree
    rw [hσ2]
    simp
    rw [Finsupp.cons_sum]
    -- rw
  · rw [←MvPolynomial.support_coeff_finSuccEquiv]
    exact hσ1
  -- aesop?
  -- unfold MvPolynomial.totalDegree
  -- simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom, bot_eq_zero', gt_iff_lt, add_pos_iff,
  --   Finset.lt_sup_iff, MvPolynomial.mem_support_iff, ne_eq]




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
    simp
    left
    convert Finset.filter_False (function_finset (Fin 0) F S)
    simp
    -- Because p is a polynomial over an empty set of variables, it is constant
    have p_const : (p : MvPolynomial (Fin Nat.zero) F)
        = ((MvPolynomial.C (p.coeff 0)) : MvPolynomial (Fin Nat.zero) F) := by
        ext m
        have m0 : m = 0 := by
          ext a
          by_contra
          exact Fin.elim0 a
        rw [m0]
        simp
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
      apply foosdad
      rw [←Polynomial.leadingCoeff]
      rw [Polynomial.leadingCoeff_ne_zero]
      exact Iff.mpr (AddEquivClass.map_ne_zero_iff (MvPolynomial.finSuccEquiv F n)) hp
      -- unfold_let i
      -- sorry

    have h1 : Polynomial.coeff p' i ≠ 0 := by
      rw [hi]
      rw [←Polynomial.leadingCoeff]
      rw [Polynomial.leadingCoeff_ne_zero]
      exact Iff.mpr (AddEquivClass.map_ne_zero_iff (MvPolynomial.finSuccEquiv F n)) hp

    -- done

    replace ih := ih p_i' h1 S


    have h_p_i'_deg_le : MvPolynomial.totalDegree p_i' ≤ (MvPolynomial.totalDegree p - i) := by
      exact Nat.le_sub_of_add_le h0

    -- Pr[B] ≤ (d - i)/|S|
    have h_first_half :
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (function_finset (Fin (Nat.succ n)) F S))
      ≤
      (MvPolynomial.totalDegree p - i) * (Finset.card S) ^ n := by
      calc
      _ ≤ (MvPolynomial.totalDegree p_i') * (Finset.card S) ^ n := by
        convert ih
        rw [mul_comm, <-Finset.card_product]
        apply Eq.symm
        -- -- Potential golf: apply ext next
        -- convert Finset.card_map (Equiv.toEmbedding (Equiv.piFinSucc n F))
        -- rw [Finset.map_filter]
        -- simp only [
        --   Equiv.piFinSucc_symm_apply, Finset.mem_map_equiv, Function.comp_apply, Prod.forall]
        -- done
        -- --
        apply Finset.card_congr
          (fun ab _ => (@Fin.cons _ (fun _ => F)) ab.fst ab.snd )
        · intro ab ha
          rcases ab with ⟨a, b⟩
          rw [Finset.mem_product, Finset.mem_filter] at ha
          rcases ha with ⟨a_mem_S, b_mem_ffS, eval_b_zero⟩
          rw [Finset.mem_filter]
          simp only []
          unfold function_finset
          rw [Fin.cons_mem_piFinset_iff]
          constructor
          · constructor
            · exact b_mem_ffS
            · exact a_mem_S
          · rw [Fin.cons_comp_succ]
            exact eval_b_zero
        · intros ab1 ab2 _ _ hmkeq
          simp only [Fin.cons_eq_cons] at hmkeq
          rcases hmkeq with ⟨abfst, absnd⟩
          exact Prod.ext abfst absnd
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
        exact h_p_i'_deg_le
    save
    have h_second_half :
      Finset.card
          (Finset.filter
            (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
            (function_finset (Fin (Nat.succ n)) F S))
      ≤
      (i) * (Finset.card S) ^ n := by
      -- Use polynomial.card_roots or card_roots'
      clear h_first_half
      -- rw [←Finset.card_congr
      --     (fun (ab : F × (Fin n → F)) _ => mk_fin_succ_function ab.snd ab.fst)]
      rw [←Finset.card_map (Equiv.toEmbedding (Equiv.piFinSucc n F))]
      rw [Finset.map_filter]
      rw [Finset.card_eq_sum_ones]
      rw [Finset.sum_finset_product_right _
            (s := (Finset.filter (fun r ↦ (MvPolynomial.eval (r)) p_i' ≠ 0)
              (function_finset (Fin (n)) F S)))
            (t := fun r => Finset.filter (fun f => (MvPolynomial.eval ((Equiv.piFinSucc n F).invFun (f, r))) p = 0) S)]
      -- Note that ((Equiv.piFinSucc n F).invFun (f, r)) can be more simply written with Fin.cons
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
          -- apply le_trans _ (Polynomial.card_roots' (p'))
          simp_rw [MvPolynomial.eval_eq_eval_mv_eval']
          rw [←hp']
          -- simp_rw [] at hr
          simp only [←hp',
            Fintype.mem_piFinset, Finset.mem_filter] at hr
          -- hr2 is in wikipedia P_i(r_2, ... , r_n) ≠ 0
          rcases hr with ⟨hr1, hr2⟩
          -- my pr is wikis P(x_1, r_2, ... r_n) = ∑ x_1^i P_i(r_2, ... r_n)
          save
          set p_r := (Polynomial.map (MvPolynomial.eval r) p') with hp_r
          have : p_r.natDegree = i := by
            rw [<-hi] at hr2
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
          simp only [<-hp_r, and_true]
          intro hpr_zero
          contrapose! hr2
          rw [<-hp'] at *
          rw [hpr_zero] at this
          rw [Polynomial.natDegree_zero] at this
          rw [<-hi, <-this]
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
            -- intro n'
            -- clear hab3 hab1' h_p_i'_deg_le ih h1 h0 p_i' i p' hp p
            -- apply @Fin.elim_succ F n (· ∈ S) a b hab1 hab2 n'
          · exact { left := hab3, right := hab1' }



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
        rw [<-Finset.card_union_add_card_inter]
        rw [Finset.filter_union_right]
        -- todo note filter_or is the symm of this. Golf that proof.
        -- Also if filter and exists, maybe so should filter_inter_right
        rw [<-Finset.filter_and]
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
        rw [<-add_mul]
        apply Nat.mul_le_mul_right
        apply le_of_eq
        apply Nat.sub_add_cancel
        apply le_of_add_le_right h0
