import Mathlib
import Mathlib.Yoh.Lattice.Defs

open Polynomial Filter QuotientAddGroup Submodule MeasureTheory MeasureTheory.Measure
  NNReal BigOperators Function

namespace ZMod

variable (P : ℝ) {N : ℕ} [nzN : NeZero N]
-- `N⁻¹` : the lattice spacing
-- `P` : the period of the lattice


/-- The `AddMonoidHom` from `ZMod N` to `ℝ / P ℤ` sending `j mod N` to `P * j / N mod P`. -/
noncomputable def toScaledAddCircle : ZMod N →+ AddCircle P :=
  lift N ⟨AddMonoidHom.mk' (fun j ↦ ↑(P * j / N : ℝ)) (by simp only [Int.cast_add]; ring_nf; simp),
    by simp⟩

-- adapt APIs for `toAddCircle` to `toScaledAddCircle`

lemma toScaledAddCircle_intCast (j : ℤ) :
    toScaledAddCircle P (j : ZMod N) = ↑(P * j / N) := by
  simp [toScaledAddCircle]

lemma toScaledAddCircle_natCast (j : ℕ) :
    toScaledAddCircle P (j : ZMod N) = ↑(P * j / N) := by
  simpa using toScaledAddCircle_intCast P (N := N) j

/--
Explicit formula for `toScaledAddCircle j`. Note that this is "evil" because it uses `ZMod.val`.
Where possible, it is recommended to lift `j` to `ℤ` and use `toScaledAddCircle_intCast` instead. -/
lemma toScaledAddCircle_apply (j : ZMod N) :
    toScaledAddCircle P j = ↑(P * j.val / N) := by
  rw [← toScaledAddCircle_natCast, natCast_zmod_val]

variable (N) in
lemma toScaledAddCircle_injective [hp : Fact (0 < P)] :
    Function.Injective (toScaledAddCircle P : ZMod N → _) := by
  intro x y hxy
  have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos _)
  have mem_ico (z : ZMod N) : P * z.val / N ∈ Set.Ico 0 (0 + P) := by
    simp only [zero_add, Set.mem_Ico]
    field_simp
    simp only [zero_mul]
    constructor
    · exact mul_nonneg (le_of_lt hp.out) (Nat.cast_nonneg' z.val)
    · rw [mul_lt_mul_iff_right₀ hp.out, Nat.cast_lt]
      exact z.val_lt
  rwa [toScaledAddCircle_apply, toScaledAddCircle_apply,
    AddCircle.coe_eq_coe_iff_of_mem_Ico (mem_ico x) (mem_ico y), div_left_inj' this.ne',
    mul_left_cancel_iff_of_pos, Nat.cast_inj,
    (val_injective N).eq_iff] at hxy
  exact hp.out

@[simp] lemma toScaledAddCircle_inj [hp : Fact (0 < P)] {j k : ZMod N} :
    toScaledAddCircle P j = toScaledAddCircle P k ↔ j = k :=
  (toScaledAddCircle_injective P N).eq_iff

@[simp] lemma toScaledAddCircle_eq_zero [hp : Fact (0 < P)] {j : ZMod N} :
    toScaledAddCircle P j = 0 ↔ j = 0 :=
  map_eq_zero_iff _ (toScaledAddCircle_injective P N)

end ZMod

section

variable {G G' : Type*} [Monoid G] [Monoid G'] (f : G →* G') (H : Submonoid G)

@[to_additive]
def monoidHomToMap : H →* H.map f where
  toFun x := ⟨H.carrier.restrict f x, Submonoid.mem_map_of_mem f x.property⟩
  map_one' := by simp
  map_mul' := by simp

@[to_additive (attr := simp)]
lemma groupHomToMap_apply (x : H) :
    monoidHomToMap f H x = ⟨f x, Submonoid.mem_map_of_mem f x.property⟩ := rfl

@[to_additive]
lemma groupHomToMap_surjective : Function.Surjective (monoidHomToMap f H) := by
  intro y
  obtain ⟨x, hx⟩ := Submonoid.mem_map.mp y.property
  use ⟨x, hx.1⟩
  simp only [groupHomToMap_apply]
  grind

@[to_additive]
lemma groupHomToMap_bijective_of_injective (h : Function.Injective f) :
    Function.Bijective (monoidHomToMap f H) :=
  ⟨by intro a b; simp only [groupHomToMap_apply, Subtype.mk.injEq]; intro H; grind,
    groupHomToMap_surjective f H⟩

@[to_additive]
noncomputable def mulEquivToMap (h : Function.Injective f) : H ≃* H.map f :=
  MulEquiv.mk' (Equiv.ofBijective (monoidHomToMap f H) (groupHomToMap_bijective_of_injective f H h))
    (monoidHomToMap f H).map_mul'

variable {f} in
@[to_additive]
noncomputable def mulEquivToMapTop (h : Function.Injective f) : G ≃* (⊤ : Submonoid G).map f :=
  MulEquiv.trans Submonoid.topEquiv.symm (mulEquivToMap f (⊤ : Submonoid G) h)

variable {f} in
@[to_additive (attr := simp)]
lemma mulEquivToMapTop_apply (h : Function.Injective f) (g : G) :
    mulEquivToMapTop h g
    = ⟨f g, Submonoid.mem_map_of_mem f (Submonoid.topEquiv.symm g).property⟩ := by rfl

noncomputable section PeriodicLattice

open ZMod

variable (P : ℝ) [ltP : Fact (0 < P)] (N : ℕ) [NeZero N]

instance : NeZero P := ⟨ltP.out.ne'⟩

abbrev ScaledPeriodicLattice1d : AddSubgroup (AddCircle P) :=
  AddSubgroup.map (toScaledAddCircle P : ZMod N →+ AddCircle P) ⊤

lemma symm_equivIco_eq (x : Set.Ico 0 (0 + P)) : (AddCircle.equivIco P 0).symm x = x := by
  rw [Equiv.symm_apply_eq]
  exact (Equiv.symm_apply_eq (AddCircle.equivIco P 0)).mp rfl

omit ltP in
lemma mem_scaledPeriodicLattice1d_iff [Fact (0 < P)] (x : AddCircle P) :
    x ∈ ScaledPeriodicLattice1d P N ↔
    ∃ (m : ZMod N), toScaledAddCircle P m = x := by
  simp

def EquivToPeriodicLattice1d : ZMod N ≃+ ScaledPeriodicLattice1d P N :=
  addEquivToMapTop (toScaledAddCircle_injective P N)

@[simp]
lemma AddCircle.equivAddCircle_apply (p q : ℝ) [hp : Fact (0 < p)] [hq : Fact (0 < q)]
    (x : Set.Ico 0 (0 + p)) :
    (equivAddCircle p q (ne_of_gt hp.out) (ne_of_gt hq.out)) ((AddCircle.equivIco p 0).symm x)
    = x.val * (p⁻¹ * q) := by rw [equivIco]; simp

def AddCircle.equivScaledPeriodicLattice1d (p : ℝ) [hp : Fact (0 < p)] (N : ℕ) [NeZero N] (q : ℝ)
  [hq : Fact (0 < q)] (Q : ℕ) [NeZero Q] :
    ScaledPeriodicLattice1d p N ≃+ ScaledPeriodicLattice1d q Q where
  toFun x := sorry
  invFun x := sorry
  map_add' := sorry
  left_inv x := sorry
  right_inv x := sorry

end PeriodicLattice

section QuotientGroupPi

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {NG : (i : ι) → Subgroup (G i)}
  [nnormal : ∀ i, (NG i).Normal]

-- #synth (Subgroup.pi Set.univ NG).Normal -- fails

@[to_additive]
instance Subgroup_normal : (Subgroup.pi Set.univ NG).Normal :=
  { conj_mem := fun n hn g i hi => Subgroup.Normal.conj_mem (nnormal i) (n i) (hn i hi) (g i) }

#synth (Subgroup.pi Set.univ NG).Normal

-- missing Pi.mulEquiv? cf. Pi.monoidHom
-- missing the canonical iso between the groups below

#synth Group ((i : ι) → (G i) ⧸ (NG i))
#synth Group (((i : ι) → (G i)) ⧸ (Subgroup.pi Set.univ NG))


end QuotientGroupPi

section QuotientAddGroupPi

variable {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)] {NG : (i : ι) → AddSubgroup (G i)}

#synth (AddSubgroup.pi Set.univ NG).Normal

end QuotientAddGroupPi
