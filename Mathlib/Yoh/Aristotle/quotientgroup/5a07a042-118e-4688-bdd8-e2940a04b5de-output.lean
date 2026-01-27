/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5a07a042-118e-4688-bdd8-e2940a04b5de

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem QuotientGroup.map_injective {G : Type*} {H : Type*} [Group G] [Group H] (N : Subgroup G)
    [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    Function.Surjective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```



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

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
A homomorphism from ZMod 2 to ZMod 4 mapping 1 to 2.
-/
def counter_f : Multiplicative (ZMod 2) →* Multiplicative (ZMod 4) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun x => if x = 0 then 0 else 2
      map_zero' := by
        decide +revert
      map_add' := by
        decide +revert }

/-
The value of `counter_f` at `x` is `0` if `x=0` and `2` otherwise (in additive notation).
-/
lemma counter_f_apply (x : ZMod 2) :
  counter_f (Multiplicative.ofAdd x) = Multiplicative.ofAdd (if x = 0 then 0 else 2) := by
    exact?

/-
The kernel of `counter_f` is the trivial subgroup.
-/
lemma counter_f_ker_eq_bot : counter_f.ker = ⊥ := by
  -- By definition of `counter_f`, its kernel consists of all elements `g` in `Multiplicative (ZMod 2)` such that `counter_f g = 1`.
  ext g
  simp [counter_f_apply];
  fin_cases g <;> simp +decide [ counter_f_apply ]

/-
`counter_f` is not surjective.
-/
lemma counter_f_not_surjective : ¬ Function.Surjective counter_f := by
  native_decide +revert

/-
The induced map between quotients by trivial subgroups is surjective if and only if the original homomorphism is surjective.
-/
lemma map_bot_bot_surjective_iff {G H : Type*} [Group G] [Group H] (f : G →* H) :
  Function.Surjective (QuotientGroup.map (⊥ : Subgroup G) (⊥ : Subgroup H) f (bot_le)) ↔ Function.Surjective f := by
    norm_num [ Function.Surjective ];
    constructor <;> intro h <;> contrapose! h;
    · obtain ⟨ b, hb ⟩ := h; use QuotientGroup.mk b; intro x; simp_all +decide [ QuotientGroup.eq ] ;
      rcases QuotientGroup.mk_surjective x with ⟨ x, rfl ⟩ ; simp_all +decide [ QuotientGroup.eq ] ;
      exact fun h => hb x ( by rw [ inv_mul_eq_one ] at h; exact h );
    · rcases h with ⟨ b, hb ⟩ ; obtain ⟨ b, rfl ⟩ := QuotientGroup.mk_surjective b; exact ⟨ b, fun a ha => hb ( QuotientGroup.mk a ) <| by aesop ⟩ ;

/-
The theorem `QuotientGroup.map_injective` is false, as shown by the counterexample `counter_f`.
-/
theorem quotient_map_injective_is_false : ¬ ∀ {G : Type} {H : Type} [Group G] [Group H] (N : Subgroup G) [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M), Function.Surjective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M := by
  by_contra! h;
  -- Apply the theorem `h` to our counterexample: G = ZMod 2, H = ZMod 4, f = `counter_f`, N = ⊥, M = ⊥.
  specialize h (⊥ : Subgroup (Multiplicative (ZMod 2))) (⊥ : Subgroup (Multiplicative (ZMod 4))) counter_f; simp_all +decide [ map_bot_bot_surjective_iff ];
  exact h <| counter_f_ker_eq_bot.symm ▸ rfl

/-
The induced map between quotient groups is injective if and only if the kernel of the map contains the kernel of the quotient map (corrected version of the user's theorem).
-/
theorem QuotientGroup.map_injective_corrected {G : Type*} {H : Type*} [Group G] [Group H] (N : Subgroup G)
    [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    Function.Injective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M := by
      refine' ⟨ fun h_inj => _, fun h_eq => _ ⟩;
      · refine' le_antisymm h _;
        intro x hx; have := @h_inj ( QuotientGroup.mk x ) ( QuotientGroup.mk 1 ) ; simp_all +decide [ QuotientGroup.eq ] ;
      · intro x y hxy;
        obtain ⟨ x, rfl ⟩ := QuotientGroup.mk_surjective x; obtain ⟨ y, rfl ⟩ := QuotientGroup.mk_surjective y; simp_all +decide [ QuotientGroup.eq ] ;

end AristotleLemmas

theorem QuotientGroup.map_injective {G : Type*} {H : Type*} [Group G] [Group H] (N : Subgroup G)
    [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    Function.Surjective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  use ULift ( Multiplicative ( ZMod 2 ) ), ULift ( Multiplicative ( ZMod 4 ) );
  refine' ⟨ inferInstance, inferInstance, ⊥, _, ⊥, _, _ ⟩ <;> norm_num [ Function.Surjective ];
  all_goals try infer_instance;
  refine' ⟨ _, Or.inr ⟨ _, _ ⟩ ⟩
  all_goals generalize_proofs at *;
  refine' { .. } <;> norm_num [ MonoidHom.ext_iff ];
  refine' fun x => if x = 1 then 1 else ⟨ Multiplicative.ofAdd 2 ⟩;
  grind;
  native_decide +revert;
  · refine' ⟨ QuotientGroup.mk ⟨ Multiplicative.ofAdd 1 ⟩, _ ⟩ ; simp +decide [ QuotientGroup.map ];
    rintro ⟨ x ⟩ ; fin_cases x <;> simp +decide [ QuotientGroup.lift ] ;
    · erw [ QuotientGroup.eq ] ; simp +decide [ QuotientGroup.mk' ] ;
    · erw [ QuotientGroup.eq ] ; simp +decide [ QuotientGroup.lift ] ;
  · simp +decide [ SetLike.ext_iff ]

-/
theorem QuotientGroup.map_injective {G : Type*} {H : Type*} [Group G] [Group H] (N : Subgroup G)
    [nN : N.Normal] (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    Function.Surjective (QuotientGroup.map N M f h) ↔ N = Subgroup.comap f M := by
  sorry