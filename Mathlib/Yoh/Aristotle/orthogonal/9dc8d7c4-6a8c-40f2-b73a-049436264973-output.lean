/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9dc8d7c4-6a8c-40f2-b73a-049436264973

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- example : Kᗮᗮ = K

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (K : Submodule ℂ H) (h : IsClosed (K : Set H))

noncomputable section AristotleLemmas

#check Submodule.orthogonal_orthogonal
#check Submodule.orthogonal_orthogonal_eq_closure

#print InnerProductSpace
#synth InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 3))
#print EuclideanSpace

variable [CompleteSpace H]

abbrev l2 := lp (fun (_ : ℕ) => ℂ) 2

def y_seq (n : ℕ) : ℂ := (n + 1 : ℂ)⁻¹

lemma y_mem_l2 : Memℓp y_seq 2 := by
  -- The sum of 1/n^2 converges, so the sequence y_seq is in ℓ^2.
  have h_summable : Summable (fun n : ℕ => (1 : ℝ) / (n + 1) ^ 2) := by
    simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
  norm_num [ Memℓp ];
  -- Since the norm squared of y_seq n is 1/(n+1)^2, and we know that the sum of 1/(n+1)^2 converges, it follows that the sum of ‖y_seq n‖^2 also converges.
  have h_norm_sq : ∀ n : ℕ, ‖y_seq n‖^2 = 1 / (n + 1 : ℝ)^2 := by
    unfold y_seq; norm_num [ EuclideanSpace.norm_eq ] ;
    exact fun n => by norm_cast;
  simpa only [ h_norm_sq ] using h_summable

def y : l2 := ⟨y_seq, y_mem_l2⟩

-- Define V as the span of finite support vectors
def V_sub : Submodule ℂ l2 := Submodule.span ℂ (Set.range (fun i => lp.single 2 i (1 : ℂ)))

-- Define H as the subtype
abbrev H_counter := ↥V_sub

-- Define the functional f on H_counter
def f : H_counter →L[ℂ] ℂ :=
  (InnerProductSpace.toDual ℂ l2 y).comp V_sub.subtypeL

-- Define K as the kernel of f
def K_counter : Submodule ℂ H_counter := LinearMap.ker f

-- K is closed
lemma K_counter_closed : IsClosed (K_counter : Set H_counter) := by
  exact IsClosed.preimage f.continuous isClosed_singleton

lemma K_counter_ne_top : K_counter ≠ ⊤ := by
  simp +decide [ K_counter, Submodule.eq_top_iff' ];
  refine' ⟨ _, _, _, _ ⟩;
  exact fun n => if n = 0 then 1 else 0;
  all_goals norm_num [ f ];
  all_goals norm_num [ l2, y ];
  all_goals norm_num [ lp, y_seq ];
  all_goals norm_num [ Memℓp, y_seq ];
  exact ⟨ _, hasSum_single 0 <| by norm_num ⟩;
  · exact Submodule.subset_span ⟨ 0, by ext n; aesop ⟩;
  · unfold y_seq; norm_num [ inner ];
    aesop

lemma mem_V_sub_finite_support (u : l2) (hu : u ∈ V_sub) : Set.Finite {n | u n ≠ 0} := by
  -- V_sub is the span of singletons.
  -- Any element in the span is a finite linear combination of singletons.
  -- Each singleton has finite support.
  -- The sum of functions with finite support has finite support.
  -- Scalar multiplication preserves finite support.
  have h_finite : ∀ u ∈ V_sub, Set.Finite {n : ℕ | u.val n ≠ 0} := by
    intro u hu;
    -- Since $u \in V_sub$, it can be written as a finite linear combination of the basis vectors $e_n$.
    obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, ∀ n, u.val n ≠ 0 → n ∈ s := by
      have h_finite : ∀ u ∈ V_sub, ∃ s : Finset ℕ, ∀ n, u.val n ≠ 0 → n ∈ s := by
        intro u hu
        have h_finite_support : ∀ u ∈ Submodule.span ℂ (Set.range (fun i => lp.single 2 i (1 : ℂ))), ∃ s : Finset ℕ, ∀ n, u.val n ≠ 0 → n ∈ s := by
          intro u hu;
          rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hu;
          obtain ⟨ c, rfl ⟩ := hu; use c.support; intro n hn; contrapose! hn; simp_all +decide [ Finsupp.sum ] ;
          rw [ Finset.sum_apply, Finset.sum_eq_single n ] <;> aesop
        exact h_finite_support u hu;
      exact h_finite u hu;
    exact Set.Finite.subset ( Finset.finite_toSet s ) hs;
  exact h_finite u hu

#check lp.hasSum_single

lemma y_not_mem_V_sub : y ∉ V_sub := by
  intro hy;
  -- Since $y$ is in the span of the standard basis vectors, it must have finite support.
  have h_finite_support : Set.Finite {n : ℕ | y n ≠ 0} := by
    exact?;
  refine h_finite_support.not_infinite <| Set.infinite_of_forall_exists_gt ?_;
  intro n; use n + 1; simp +decide [ y_seq ] ;
  exact inv_ne_zero ( Nat.cast_add_one_ne_zero _ )

#check lp.ext
#check lp.single

lemma exists_scalar_of_ker_le_ker {E : Type*} [AddCommGroup E] [Module ℂ E] (f g : E →ₗ[ℂ] ℂ) (h : LinearMap.ker f ≤ LinearMap.ker g) : ∃ c : ℂ, g = c • f := by
  -- Since $f$ is non-zero, there exists some $x \in E$ such that $f(x) \neq 0$.
  by_cases hf_zero : f = 0
  generalize_proofs at *; (
  -- Since $f$ is zero, its kernel is the entire space $E$. Therefore, $g$ must also be zero on the entire space $E$, implying $g = 0$.
  use 0
  simp [hf_zero];
  exact LinearMap.ext fun x => by simpa [ hf_zero ] using h ( by simp +decide [ hf_zero ] ) ;);
  -- Since $f$ is non-zero, there exists some $x \in E$ such that $f(x) \neq 0$. Let $x$ be such that $f(x) = 1$.
  obtain ⟨x, hx⟩ : ∃ x : E, f x = 1 := by
    exact ( LinearMap.surjective_of_ne_zero hf_zero ) 1 |> fun ⟨ x, hx ⟩ => ⟨ x, hx ⟩
  generalize_proofs at *; (
  use g x
  ext y
  by_cases hy : f y = 0
  generalize_proofs at *; (
  have := h ( show y ∈ LinearMap.ker f from hy ) ; aesop;);
  have := h ( show f ( y - ( f y ) • x ) = 0 from by simp +decide [ hx, hy, smul_smul ] ) ; simp_all +decide [ sub_eq_iff_eq_add ] ; ring;)

lemma K_counter_perp_eq_bot : K_counterᗮ = ⊥ := by
  refine' Submodule.eq_bot_iff _ |>.2 fun x => _;
  unfold K_counter;
  intro hx;
  simp_all +decide [ Submodule.mem_orthogonal ];
  -- Since $x \in V_sub$, we can write it as a finite linear combination of the basis vectors.
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, ∀ n ∉ s, x.val n = 0 := by
    have := mem_V_sub_finite_support x.val x.2;
    exact ⟨ this.toFinset, fun n hn => Classical.not_not.1 fun hnn => hn <| this.mem_toFinset.2 hnn ⟩;
  contrapose! hx;
  -- Let $a$ be a vector in $V_sub$ such that $a$ is orthogonal to $y$ but not to $x$.
  obtain ⟨a, ha⟩ : ∃ a : l2, a ∈ V_sub ∧ ∑' n, starRingEnd ℂ (y_seq n) * a n = 0 ∧ ∑' n, starRingEnd ℂ (x.val n) * a n ≠ 0 := by
    -- Let $a$ be a vector in $V_sub$ such that $a$ is orthogonal to $y$ but not to $x$. We can construct such a vector by choosing $a$ to be a linear combination of the basis vectors $e_i$ for $i \in s$.
    obtain ⟨i, hi⟩ : ∃ i ∈ s, x.val i ≠ 0 := by
      exact not_forall_not.mp fun h => hx <| Subtype.ext <| by ext n; by_cases hn : n ∈ s <;> aesop;
    -- Let $a$ be a vector in $V_sub$ such that $a$ is orthogonal to $y$ but not to $x$. We can construct such a vector by choosing $a$ to be a linear combination of the basis vectors $e_i$ for $i \in s$ and $e_j$ for some $j \notin s$.
    obtain ⟨j, hj⟩ : ∃ j ∉ s, y_seq j ≠ 0 := by
      exact ⟨ s.sup id + 1, fun h => not_lt_of_ge ( Finset.le_sup ( f := id ) h ) ( Nat.lt_succ_self _ ), by exact inv_ne_zero ( Nat.cast_add_one_ne_zero _ ) ⟩;
    refine' ⟨ lp.single 2 i ( -y_seq j / y_seq i ) + lp.single 2 j 1, _, _, _ ⟩ <;> simp_all +decide [ lp.single_apply ];
    · -- Since $lp.single 2 i (-y_seq j / y_seq i)$ and $lp.single 2 j 1$ are both in $V_sub$, their sum is also in $V_sub$.
      have h_sum : lp.single 2 i (-y_seq j / y_seq i) ∈ V_sub ∧ lp.single 2 j 1 ∈ V_sub := by
        -- Since $lp.single 2 i (-y_seq j / y_seq i)$ and $lp.single 2 j 1$ are both in the range of the function that maps $i$ to $lp.single 2 i 1$, they are in $V_sub$.
        have h_single_i : lp.single 2 i (-y_seq j / y_seq i) ∈ V_sub := by
          have h_single_i : lp.single 2 i 1 ∈ V_sub := by
            exact Submodule.subset_span ⟨ i, rfl ⟩;
          convert Submodule.smul_mem _ ( -y_seq j / y_seq i ) h_single_i using 1 ; ext n ; by_cases hn : n = i <;> simp +decide [ hn ]
        have h_single_j : lp.single 2 j 1 ∈ V_sub := by
          exact Submodule.subset_span ⟨ j, by aesop ⟩
        exact ⟨h_single_i, h_single_j⟩;
      exact Submodule.add_mem _ h_sum.1 h_sum.2;
    · rw [ tsum_eq_sum ];
      any_goals exact { i, j };
      · by_cases hij : i = j <;> simp_all +decide [ div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm ];
        unfold y_seq; norm_num [ Complex.ext_iff ] ;
        norm_num [ Complex.normSq ] ; ring;
        nlinarith [ inv_pos.mpr ( by linarith : 0 < ( 1 + j : ℝ ) ), inv_pos.mpr ( by linarith : 0 < ( 1 + i : ℝ ) ), mul_inv_cancel₀ ( by linarith : ( 1 + j : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by linarith : ( 1 + i : ℝ ) ≠ 0 ) ];
      · intro n hn; rw [ Pi.single_apply, Pi.single_apply ] ; aesop;
    · rw [ tsum_eq_sum ];
      any_goals exact { i, j };
      · rw [ Finset.sum_pair ] <;> simp_all +decide [ Pi.single_apply ];
        · split_ifs <;> simp_all +decide [ div_eq_mul_inv ];
          exact inv_ne_zero ( Nat.cast_add_one_ne_zero _ );
        · grind;
      · intro n hn; by_cases hi : n = i <;> by_cases hj : n = j <;> aesop;
  refine' ⟨ a, a.2, ha.1, _, _ ⟩ <;> simp_all +decide [ inner, tsum_mul_left, tsum_mul_right ];
  · convert ha.2.1 using 1;
    exact tsum_congr fun n => mul_comm _ _;
  · -- Since the sum of the product of x and the conjugate of a is non-zero, the sum of the product of x and a must also be non-zero.
    have h_conj : ∑' n, (x.val n) * (starRingEnd ℂ (a.val n)) = starRingEnd ℂ (∑' n, (starRingEnd ℂ (x.val n)) * (a.val n)) := by
      rw [ Complex.conj_tsum ];
      norm_num [ mul_comm ];
    aesop

lemma K_counter_perp_eq_bot' : K_counterᗮ = ⊥ := by
  -- Apply the lemma that states the orthogonal complement of K_counter is the bottom subspace.
  apply K_counter_perp_eq_bot

theorem counterexample_exists : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (K : Submodule ℂ H) (h : IsClosed (K : Set H)), Kᗮᗮ ≠ K := by
  use H_counter, inferInstance, inferInstance, K_counter, K_counter_closed
  rw [K_counter_perp_eq_bot, Submodule.bot_orthogonal_eq_top]
  exact K_counter_ne_top.symm

end AristotleLemmas

example : Kᗮᗮ = K := by
  -- Since K is closed, it is complete.
  have h_complete : CompleteSpace K := by
    exact h.completeSpace_coe;
  exact?

abbrev l2 := lp (fun (_ : ℕ) => ℂ) 2

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Type mismatch
  HasCompactSupport.smul_left
has type
  HasCompactSupport ?m.42 → HasCompactSupport (?m.41 • ?m.42)
but is expected to have type
  x✝ ∈ {x : ↥l2 | HasCompactSupport (↑x : (i : ℕ) → (fun (x : ℕ) => ℂ) i)} →
    x✝¹ • x✝ ∈ {x : ↥l2 | HasCompactSupport (↑x : (i : ℕ) → (fun (x : ℕ) => ℂ) i)}-/
def Cc : Submodule ℂ l2 where
  carrier := { x : l2 | HasCompactSupport x }
  add_mem' := .add
  zero_mem' := .zero
  smul_mem' _ _ := .smul_left

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `Cc`-/
#check Cc

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `Cc`-/
#synth InnerProductSpace ℂ Cc

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  AddCommMonoid Cc

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
example : ∃ (K : Submodule ℂ Cc), (IsClosed (K : Set Cc)) ∧ Kᗮᗮ ≠ K := by sorry