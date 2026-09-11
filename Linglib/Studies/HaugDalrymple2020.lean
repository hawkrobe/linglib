import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Dynamic.PPCDRT.Anaphora
import Linglib.Semantics.Supervaluation

/-!
# Haug and Dalrymple (2020): Reciprocity: Anaphora, scope, and quantification

This file formalizes the relational analysis of reciprocity of [haug-dalrymple-2020] in
Partial Plural Compositional DRT. The reciprocal contributes group identity with its
antecedent and pointwise distinctness ((41), `PPCDRT.reciprocityCond`); the scope
ambiguity of a reciprocal in a complement clause is the ambiguity of any plural anaphor
between group identity (`PPCDRT.groupIdentityCond`) and binding (`PPCDRT.bindingCond`)
with the matrix subject, read through the distribution of §2.3 under which the antecedent
escapes the distribution operator. The sample output states of the paper are transcribed
as plural information states (`ofRows`) and the conditions checked on them: the two
readings of the lawyers' secretary (24), (31), the narrow and wide readings of the girls'
belief (49), (51), (53), (55), the crossed reading (56), the modal (69), the mixed
construal of the Cheyenne affix (78), multiple reciprocals (85), (86), the forks (93), the
sailors (96), and the wide construal with three girls (136).
`no_low_reciprocal_under_binding` derives the empty cell of §3.3: a bound antecedent
leaves no plurality for a reciprocal inside the distribution.

Quantified antecedents (§5) get the two readings of (99), `RefSetReading` over a maximal
reciprocal subset and `MaxSetReading` over the participants, and the supervaluation truth
value of (109), `truthValue`, with `maxSetReading_of_refSetReading` for upward monotone
determiners and the street and club scenarios of §5.1–§5.2. Maximize Anaphora (128) is
`MaximizesAnaphora`; it selects the strong reading (126b) over the minimal state (126a) and
maximizes multiple reciprocals pairwise (§6.2).

## Implementation notes

* Distribution is represented by the set `Δ` of a `PPCDRT.PPDRSCond`; the operators `δ`,
  `T` and `think` of (14), (46) are not defined, and each sample state is checked under
  the `Δ` its DRS induces. The `max` operator of (97) is likewise replaced by the static
  readings it yields.
* Worlds are values of the same domain as individuals, at the discourse referent `w`.
* The antecedence condition for the second reciprocal of (85b) is read with `u₂`, as the
  indices of (85a) and the state (85c) give.

## TODO

* The dynamic DRS relations `I[u]O`, `δ_u` and `max^u` of (6), (14) and (97), so that the
  sample states are derived from the DRSs rather than transcribed.

## References

* [haug-dalrymple-2020]
* [dotlacil-2013]
* [murray-2008]
* [kriz-2015]
* [champollion-bumford-henderson-2019]
-/

namespace HaugDalrymple2020

open PPCDRT

/-! ### Sample states -/

/-- The individuals and worlds of the sample states. -/
inductive Ind where
  | girl1 | girl2
  | tracy | chris | matty
  | world1 | world2 | world3
  | lawyer1 | lawyer2 | lawyer3
  | secretary1 | secretary2 | secretary3
  | picture1 | picture2 | picture3
  | fork1 | fork2 | fork3
  | sailor1 | sailor2 | sailor3
  | ship1 | ship2 | ship3
  | child1 | child2 | child3
  | boy1 | boy2 | boy3
  deriving DecidableEq, Fintype, Repr

/-- The discourse referent `u₁`. -/
abbrev u₁ : ℕ := 1
/-- The discourse referent `u₂`. -/
abbrev u₂ : ℕ := 2
/-- The discourse referent `u₃`. -/
abbrev u₃ : ℕ := 3
/-- The discourse referent `u₄`. -/
abbrev u₄ : ℕ := 4
/-- The world discourse referent `w` of §3.1. -/
abbrev w : ℕ := 5

/-- A row of a sample state, from its defined discourse referents. -/
def row (l : List (ℕ × Ind)) : PartialAssign ℕ Ind :=
  λ u => (l.find? (·.1 == u)).map Prod.snd

/-- The plural information state with the given rows. -/
def ofRows (rows : List (PartialAssign ℕ Ind)) : PluralAssign ℕ Ind := {g | g ∈ rows}

section Rows

variable {rows : List (PartialAssign ℕ Ind)} {Δ : Set ℕ} {Δl : List ℕ} {u u' : ℕ}

theorem bindingCond_ofRows : bindingCond u u' (ofRows rows) Δ ↔ ∀ s ∈ rows, s u = s u' := by
  simp [bindingCond, ofRows]

theorem groupIdentityCond_ofRows (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) :
    groupIdentityCond u u' (ofRows rows) Δ ↔
      ∀ s ∈ rows, ∀ d, (∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = some d) ↔
        ∃ t ∈ rows, t u' = some d := by
  simp [groupIdentityCond, eqClass, ofRows, PluralAssign.sumDref, Set.ext_iff, hΔ, and_assoc]

theorem distinct_ofRows :
    (∀ s ∈ ofRows rows, ∀ a b, s u = some a → s u' = some b → a ≠ b) ↔
      ∀ s ∈ rows, ∀ a b, s u = some a → s u' = some b → a ≠ b := by
  simp [ofRows]

theorem reciprocityCond_ofRows (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) :
    reciprocityCond u u' (ofRows rows) Δ ↔
      (∀ s ∈ rows, ∀ d, (∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = some d) ↔
        ∃ t ∈ rows, t u' = some d) ∧
      ∀ s ∈ rows, ∀ a b, s u = some a → s u' = some b → a ≠ b :=
  and_congr (groupIdentityCond_ofRows hΔ) distinct_ofRows

theorem mem_R_u_ofRows {a b : Ind} :
    (a, b) ∈ R_u u u' (ofRows rows) ↔ ∃ s ∈ rows, s u = some a ∧ s u' = some b := by
  simp [R_u, ofRows]

theorem mem_R_u_eqClass_ofRows (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) {s : PartialAssign ℕ Ind}
    {a b : Ind} :
    (a, b) ∈ R_u u u' (eqClass (ofRows rows) Δ s) ↔
      ∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = some a ∧ t u' = some b := by
  simp [R_u, eqClass, ofRows, hΔ, and_assoc]

/-- The values of `u` summed over the `Δ`-class of `s`, as a finset. -/
def sumRows (rows : List (PartialAssign ℕ Ind)) (Δl : List ℕ) (s : PartialAssign ℕ Ind)
    (u : ℕ) : Finset Ind :=
  Finset.univ.filter λ d => ∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = some d

theorem coe_sumRows (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) (s : PartialAssign ℕ Ind) :
    (↑(sumRows rows Δl s u) : Set Ind) =
      PluralAssign.sumDref (eqClass (ofRows rows) Δ s) u := by
  ext d
  simp [sumRows, PluralAssign.sumDref, eqClass, ofRows, hΔ, and_assoc]

end Rows

/-- The collective condition `n-atoms(∪u)` of (9) under distribution: in every state, the
values of `u` summed over the state's class number `n` ((27), (28b)). -/
def atomsCond (n : ℕ) (u : ℕ) : PPDRSCond Ind := λ S Δ =>
  ∀ s ∈ S, (PluralAssign.sumDref (eqClass S Δ s) u).ncard = n

theorem atomsCond_ofRows {rows : List (PartialAssign ℕ Ind)} {Δ : Set ℕ} {Δl : List ℕ}
    {n u : ℕ} (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) :
    atomsCond n u (ofRows rows) Δ ↔ ∀ s ∈ rows, (sumRows rows Δl s u).card = n := by
  have key : ∀ s, (PluralAssign.sumDref (eqClass (ofRows rows) Δ s) u).ncard =
      (sumRows rows Δl s u).card :=
    λ s => by rw [← coe_sumRows hΔ, Set.ncard_coe_finset]
  simp only [atomsCond, key]
  exact Iff.rfl

/-- Group identity read inside the distribution operator of (14), summing both sides over
the class: the reading under which (23b) is not representable (§2.3). -/
def distributedGroupIdentityCond (uAnaph uAnt : ℕ) : PPDRSCond Ind := λ S Δ =>
  ∀ s ∈ S,
    PluralAssign.sumDref (eqClass S Δ s) uAnaph = PluralAssign.sumDref (eqClass S Δ s) uAnt

theorem distributedGroupIdentityCond_ofRows {rows : List (PartialAssign ℕ Ind)} {Δ : Set ℕ}
    {Δl : List ℕ} {u u' : ℕ} (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) :
    distributedGroupIdentityCond u u' (ofRows rows) Δ ↔
      ∀ s ∈ rows, ∀ d, (∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = some d) ↔
        ∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u' = some d := by
  simp [distributedGroupIdentityCond, eqClass, ofRows, PluralAssign.sumDref, Set.ext_iff, hΔ,
    and_assoc]

/-! ### Anaphora under distribution (§2.3) -/

/-- (24c): the lawyers hired secretaries they each liked, `u₃` bound to `u₁`. -/
def lawyersBound : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .lawyer1), (u₂, .secretary1), (u₃, .lawyer1)],
   row [(u₁, .lawyer2), (u₂, .secretary2), (u₃, .lawyer2)],
   row [(u₁, .lawyer3), (u₂, .secretary3), (u₃, .lawyer3)]]

/-- (31c): the lawyers hired secretaries all of them liked, `∪u₃ → ∪u₁` under
`δ_{u₁}`. -/
def lawyersGroup : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .lawyer1), (u₂, .secretary1), (u₃, .lawyer1)],
   row [(u₁, .lawyer1), (u₂, .secretary1), (u₃, .lawyer2)],
   row [(u₁, .lawyer1), (u₂, .secretary1), (u₃, .lawyer3)],
   row [(u₁, .lawyer2), (u₂, .secretary2), (u₃, .lawyer1)],
   row [(u₁, .lawyer2), (u₂, .secretary2), (u₃, .lawyer2)],
   row [(u₁, .lawyer2), (u₂, .secretary2), (u₃, .lawyer3)],
   row [(u₁, .lawyer3), (u₂, .secretary3), (u₃, .lawyer1)],
   row [(u₁, .lawyer3), (u₂, .secretary3), (u₃, .lawyer2)],
   row [(u₁, .lawyer3), (u₂, .secretary3), (u₃, .lawyer3)]]

private theorem mem_u₁ : ∀ v, v ∈ ({u₁} : Set ℕ) ↔ v ∈ [u₁] := by simp

private theorem mem_empty : ∀ v, v ∈ (∅ : Set ℕ) ↔ v ∈ ([] : List ℕ) := by simp

/-- (23a) as (24): `they` bound by `the lawyers`, one secretary per lawyer under
`δ_{u₁}`, and no group identity under the distribution. -/
theorem lawyers_bound :
    bindingCond u₃ u₁ (ofRows lawyersBound) {u₁} ∧
      atomsCond 1 u₂ (ofRows lawyersBound) {u₁} ∧
      ¬ groupIdentityCond u₃ u₁ (ofRows lawyersBound) {u₁} := by
  rw [bindingCond_ofRows, atomsCond_ofRows mem_u₁, groupIdentityCond_ofRows mem_u₁]
  decide

/-- (23b) as (31): `∪u₃ → ∪u₁` escapes `δ_{u₁}`, one secretary per lawyer, no binding;
the same state fails group identity read inside the distribution operator of (14), which
is why (23b) needs the distribution of §2.3. -/
theorem lawyers_group :
    groupIdentityCond u₃ u₁ (ofRows lawyersGroup) {u₁} ∧
      atomsCond 1 u₂ (ofRows lawyersGroup) {u₁} ∧
      ¬ bindingCond u₃ u₁ (ofRows lawyersGroup) {u₁} ∧
      ¬ atomsCond 1 u₂ (ofRows lawyersGroup) ∅ ∧
      ¬ distributedGroupIdentityCond u₃ u₁ (ofRows lawyersGroup) {u₁} := by
  rw [groupIdentityCond_ofRows mem_u₁, atomsCond_ofRows mem_u₁, bindingCond_ofRows,
    atomsCond_ofRows mem_empty, distributedGroupIdentityCond_ofRows mem_u₁]
  decide

/-! ### Reciprocal scope (§3) -/

private theorem mem_u₁w : ∀ v, v ∈ ({u₁, w} : Set ℕ) ↔ v ∈ [u₁, w] := by simp

private theorem mem_w : ∀ v, v ∈ ({w} : Set ℕ) ↔ v ∈ [w] := by simp

/-- (49): each girl thought "we will win", `∪u₂ → ∪u₁` under `δ_w`. -/
def girlsNarrow : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (w, .world1), (u₂, .girl1)],
   row [(u₁, .girl1), (w, .world1), (u₂, .girl2)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl1)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl2)]]

/-- (51): each girl thought "I will win", `u₂ → u₁`. -/
def girlsWide : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (w, .world1), (u₂, .girl1)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl2)]]

/-- §3.1: the two readings of (44) come apart under the distribution the attitude verb
induces: (49) is group identity without binding, (51) binding without group identity. -/
theorem win_readings :
    (groupIdentityCond u₂ u₁ (ofRows girlsNarrow) {u₁, w} ∧
        ¬ bindingCond u₂ u₁ (ofRows girlsNarrow) {u₁, w}) ∧
      bindingCond u₂ u₁ (ofRows girlsWide) {u₁, w} ∧
        ¬ groupIdentityCond u₂ u₁ (ofRows girlsWide) {u₁, w} := by
  rw [groupIdentityCond_ofRows mem_u₁w, bindingCond_ofRows, bindingCond_ofRows,
    groupIdentityCond_ofRows mem_u₁w]
  decide

/-- (53): each girl thought "we saw each other", the reciprocal inside the belief. -/
def sawNarrow : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (w, .world1), (u₂, .girl1), (u₃, .girl2)],
   row [(u₁, .girl1), (w, .world1), (u₂, .girl2), (u₃, .girl1)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl1), (u₃, .girl2)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl2), (u₃, .girl1)]]

/-- (55): each girl thought "I saw her", the reciprocal and its antecedent lifted to the
matrix DRS. -/
def sawWide : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (u₂, .girl1), (u₃, .girl2), (w, .world1)],
   row [(u₁, .girl2), (u₂, .girl2), (u₃, .girl1), (w, .world2)]]

/-- The crossed reading of (56): girl1 thought girl2 saw girl1 and girl2 thought girl1
saw girl2. -/
def sawCrossed : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (u₂, .girl2), (u₃, .girl1), (w, .world1)],
   row [(u₁, .girl2), (u₂, .girl1), (u₃, .girl2), (w, .world2)]]

/-- §3.2: (53) satisfies (52), group identity of the pronoun and reciprocity of the
reciprocal under the distribution. -/
theorem saw_narrow :
    groupIdentityCond u₂ u₁ (ofRows sawNarrow) {u₁, w} ∧
      reciprocityCond u₃ u₂ (ofRows sawNarrow) {u₁, w} := by
  rw [groupIdentityCond_ofRows mem_u₁w, reciprocityCond_ofRows mem_u₁w]
  decide

/-- §3.2: (55) satisfies (54), binding of the pronoun and reciprocity in the matrix. -/
theorem saw_wide :
    bindingCond u₂ u₁ (ofRows sawWide) ∅ ∧
      reciprocityCond u₃ u₂ (ofRows sawWide) ∅ := by
  rw [bindingCond_ofRows, reciprocityCond_ofRows mem_empty]
  decide

/-- §3.3: the crossed state satisfies (56), group identity of the pronoun with reciprocity
in the matrix, but not the binding of (54). -/
theorem saw_crossed :
    groupIdentityCond u₂ u₁ (ofRows sawCrossed) ∅ ∧
      reciprocityCond u₃ u₂ (ofRows sawCrossed) ∅ ∧
      ¬ bindingCond u₂ u₁ (ofRows sawCrossed) ∅ := by
  rw [groupIdentityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty, bindingCond_ofRows]
  decide

/-- §3.3: a bound antecedent cannot cooccur with a low reciprocal. If `u₂` is bound by
`u₁`, the distribution runs over `u₁`, and the reciprocal `u₃` is reciprocal to `u₂` under
that distribution, no state can assign `u₂` a value: the value must be covered by `u₃`
within the class, where distinctness excludes it. -/
theorem no_low_reciprocal_under_binding {E : Type*} {S : PluralAssign ℕ E} {Δ : Set ℕ}
    {v₁ v₂ v₃ : ℕ} (hΔ : v₁ ∈ Δ) (hb : bindingCond v₂ v₁ S Δ)
    (hr : reciprocityCond v₃ v₂ S Δ) {s : PartialAssign ℕ E} (hs : s ∈ S) {d : E}
    (hd : s v₂ = some d) : False := by
  have hmem : d ∈ PluralAssign.sumDref S v₂ := ⟨s, hs, hd⟩
  rw [← hr.1 s hs] at hmem
  obtain ⟨t, ⟨ht, hcls⟩, ht₃⟩ := hmem
  have ht₂ : t v₂ = some d := by rw [hb t ht, hcls v₁ hΔ, ← hb s hs, hd]
  exact hr.2 t ht d d ht₃ ht₂ rfl

/-- (69) distributed over two accessible worlds: the reciprocal lifted above `◇`. -/
def beatModal : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .tracy), (u₂, .chris), (w, .world1)],
   row [(u₁, .chris), (u₂, .tracy), (w, .world1)],
   row [(u₁, .tracy), (u₂, .chris), (w, .world2)],
   row [(u₁, .chris), (u₂, .tracy), (w, .world2)]]

/-- §3.4: with the reciprocal above the modal, every accessible world contains both
directions of `beat`, the contradiction that makes (64) strange. -/
theorem beat_modal :
    reciprocityCond u₂ u₁ (ofRows beatModal) ∅ ∧
      ∀ s ∈ beatModal,
        (Ind.tracy, Ind.chris) ∈ R_u u₁ u₂ (eqClass (ofRows beatModal) {w} s) ∧
          (Ind.chris, Ind.tracy) ∈ R_u u₁ u₂ (eqClass (ofRows beatModal) {w} s) := by
  rw [reciprocityCond_ofRows mem_empty]
  simp only [mem_R_u_eqClass_ofRows mem_w]
  decide

/-! ### Underspecification, multiple reciprocals, subgroups, collectives (§4) -/

/-- (78c): the mixed construal of the Cheyenne affix, one child scratching herself and two
scratching each other. -/
def scratchMixed : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .child1), (u₂, .child1)],
   row [(u₁, .child2), (u₂, .child3)],
   row [(u₁, .child3), (u₂, .child2)]]

/-- §4.2: the mixed construal satisfies the underspecified meaning (79b) but neither
reciprocity nor reflexive binding. -/
theorem scratch_mixed :
    underspecifiedCond u₂ u₁ (ofRows scratchMixed) ∅ ∧
      ¬ reciprocityCond u₂ u₁ (ofRows scratchMixed) ∅ ∧
      ¬ bindingCond u₂ u₁ (ofRows scratchMixed) ∅ := by
  rw [underspecifiedCond, groupIdentityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty,
    bindingCond_ofRows]
  decide

/-- (85c): each girl gave the other a picture of herself, the second reciprocal anteceded
by the first. -/
def picturesSecond : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (u₂, .girl2), (u₃, .picture1), (u₄, .girl1)],
   row [(u₁, .girl2), (u₂, .girl1), (u₃, .picture2), (u₄, .girl2)]]

/-- (86c): each girl gave the other a picture of the other, both reciprocals anteceded by
the subject. -/
def picturesSubject : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (u₂, .girl2), (u₃, .picture1), (u₄, .girl2)],
   row [(u₁, .girl2), (u₂, .girl1), (u₃, .picture2), (u₄, .girl1)]]

/-- §4.4: the two readings of (84) are the two antecedents of the second reciprocal; each
state satisfies its own DRS and fails the other's distinctness condition. -/
theorem pictures_readings :
    (reciprocityCond u₂ u₁ (ofRows picturesSecond) ∅ ∧
        reciprocityCond u₄ u₂ (ofRows picturesSecond) ∅ ∧
        ¬ reciprocityCond u₄ u₁ (ofRows picturesSecond) ∅) ∧
      reciprocityCond u₂ u₁ (ofRows picturesSubject) ∅ ∧
        reciprocityCond u₄ u₁ (ofRows picturesSubject) ∅ ∧
        ¬ reciprocityCond u₄ u₂ (ofRows picturesSubject) ∅ := by
  rw [reciprocityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty,
    reciprocityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty,
    reciprocityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty]
  exact ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide⟩

/-- (93): the forks propped against each other, each on one other. -/
def forks : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .fork1), (u₂, .fork2)],
   row [(u₁, .fork2), (u₂, .fork3)],
   row [(u₁, .fork3), (u₂, .fork1)]]

/-- §4.5: the chain of forks is reciprocal, though no fork is supported by all the
others: weak reciprocity is the basic reading. -/
theorem forks_weak :
    reciprocityCond u₂ u₁ (ofRows forks) ∅ ∧
      (Ind.fork3, Ind.fork1) ∉ R_u u₂ u₁ (ofRows forks) := by
  rw [reciprocityCond_ofRows mem_empty, mem_R_u_ofRows]
  decide

/-- (96c): the sailors worked together on each other's ships. -/
def sailors : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .sailor1), (u₂, .ship1), (u₃, .sailor2)],
   row [(u₁, .sailor2), (u₂, .ship2), (u₃, .sailor3)],
   row [(u₁, .sailor3), (u₂, .ship3), (u₃, .sailor1)]]

/-- §4.6: the collective antecedent `∪u₁` of `work.together` is the group of all three
sailors while the reciprocal holds pointwise; the distinctness does no work. -/
theorem sailors_collective :
    reciprocityCond u₃ u₁ (ofRows sailors) ∅ ∧ atomsCond 3 u₁ (ofRows sailors) ∅ := by
  rw [reciprocityCond_ofRows mem_empty, atomsCond_ofRows mem_empty]
  decide

/-! ### Quantified antecedents (§5) -/

section Quantified

variable {D : Type*} [DecidableEq D]

/-- Strong reciprocity of `R` over `Y` (fn. 24): each member bears `R` to every other. -/
def StrongRecip (R : D → D → Prop) (Y : Finset D) : Prop :=
  ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → R a b

/-- A reference set (101): a subset of the restrictor `A` over which `R` is strongly
reciprocal, of the largest cardinality any such subset has, as the operator of (97)
maximizes. Maxima need not be unique (fn. 18). -/
def IsRefSet (R : D → D → Prop) (A Y : Finset D) : Prop :=
  Y ∈ A.powerset ∧ StrongRecip R Y ∧
    ∀ Z ∈ A.powerset, StrongRecip R Z → Z.card ≤ Y.card

/-- The reference-set reading (101), (110a): the determiner holds of the restrictor and a
reference set. -/
def RefSetReading (Q : Finset D → Finset D → Prop) (R : D → D → Prop) (A : Finset D) :
    Prop :=
  ∃ Y ∈ A.powerset, IsRefSet R A Y ∧ Q A Y

/-- The participants (105): the members of `A` bearing `R` to some other member. -/
def participants (R : D → D → Prop) [DecidableRel R] (A : Finset D) : Finset D :=
  A.filter λ a => ∃ b ∈ A, b ≠ a ∧ R a b

/-- The maximal-set reading (104), (110b): the reciprocal ranges over the whole restrictor
and the determiner holds of the restrictor and the participants. -/
def MaxSetReading (Q : Finset D → Finset D → Prop) (R : D → D → Prop) [DecidableRel R]
    (A : Finset D) : Prop :=
  Q A (participants R A)

/-- The two ranges of the reciprocal in (99). -/
inductive Range where
  | referenceSet
  | maximalSet
  deriving DecidableEq, Fintype, Repr

/-- The reading of a quantified reciprocal sentence at a range. -/
def reading (Q : Finset D → Finset D → Prop) (R : D → D → Prop) [DecidableRel R]
    (A : Finset D) : Range → Prop
  | .referenceSet => RefSetReading Q R A
  | .maximalSet => MaxSetReading Q R A

variable (Q : Finset D → Finset D → Prop) (R : D → D → Prop) [DecidableRel R] (A : Finset D)

/-- Each member of a reference set with at least two members participates. -/
theorem refSet_subset_participants {Y : Finset D} (h : IsRefSet R A Y) (h2 : 2 ≤ Y.card) :
    Y ⊆ participants R A := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := Finset.exists_mem_ne h2 a
  exact Finset.mem_filter.2
    ⟨Finset.mem_powerset.1 h.1 ha, b, Finset.mem_powerset.1 h.1 hb, hab,
      h.2.1 a ha b hb hab.symm⟩

/-- §5.2: for a determiner upward monotone in its scope, the reciprocal relation holds over
the maximal set if it holds over a reference set of at least two members, so the
reference-set reading determines truth and the maximal-set reading falsity. -/
theorem maxSetReading_of_refSetReading (hQ : Monotone (Q A))
    (h2 : ∀ Y, IsRefSet R A Y → 2 ≤ Y.card) (h : RefSetReading Q R A) :
    MaxSetReading Q R A := by
  obtain ⟨Y, -, hY, hQY⟩ := h
  exact hQ (refSet_subset_participants R A hY (h2 Y hY)) hQY

variable [DecidableRel Q]

instance : DecidablePred (reading Q R A) := λ r => by
  cases r <;> unfold reading RefSetReading IsRefSet StrongRecip MaxSetReading <;> infer_instance

/-- (109): a quantified reciprocal sentence is true iff true at both ranges, false iff false
at both, and neither otherwise: the supervaluation over the two precisifications. -/
def truthValue : Trivalent :=
  Semantics.Supervaluation.superTrue (reading Q R A)
    ⟨{.referenceSet, .maximalSet}, ⟨.referenceSet, by simp⟩⟩

theorem truthValue_true_iff :
    truthValue Q R A = .true ↔ RefSetReading Q R A ∧ MaxSetReading Q R A := by
  unfold truthValue; rw [Semantics.Supervaluation.superTrue_true_iff]; simp [reading]

theorem truthValue_false_iff :
    truthValue Q R A = .false ↔ ¬ RefSetReading Q R A ∧ ¬ MaxSetReading Q R A := by
  unfold truthValue; rw [Semantics.Supervaluation.superTrue_false_iff]; simp [reading]

theorem truthValue_true_iff_of_monotone (hQ : Monotone (Q A))
    (h2 : ∀ Y, IsRefSet R A Y → 2 ≤ Y.card) :
    truthValue Q R A = .true ↔ RefSetReading Q R A :=
  (truthValue_true_iff Q R A).trans
    ⟨And.left, λ h => ⟨h, maxSetReading_of_refSetReading Q R A hQ h2 h⟩⟩

theorem truthValue_false_iff_of_monotone (hQ : Monotone (Q A))
    (h2 : ∀ Y, IsRefSet R A Y → 2 ≤ Y.card) :
    truthValue Q R A = .false ↔ ¬ MaxSetReading Q R A :=
  (truthValue_false_iff Q R A).trans
    ⟨And.right, λ h => ⟨λ hr => h (maxSetReading_of_refSetReading Q R A hQ h2 hr), h⟩⟩

end Quantified

/-- The five inhabitants of the street of (100) and (102). -/
abbrev Person := Fin 5

/-- Proportional `most`: the scope has more than half of the restrictor. -/
def most (A B : Finset Person) : Prop := A.card < 2 * B.card

/-- Proportional `few`: the scope has less than half of the restrictor. -/
def few (A B : Finset Person) : Prop := 2 * B.card < A.card

/-- (102): the first three inhabitants know each other and the other two know nobody. -/
def clique (a b : Person) : Prop := a ≠ b ∧ a.val < 3 ∧ b.val < 3

/-- The intermediate scenario of §5.2: two pairs know each other and one person knows
nobody. -/
def pairs (a b : Person) : Prop :=
  a ≠ b ∧ (a.val < 2 ∧ b.val < 2 ∨ 2 ≤ a.val ∧ a.val < 4 ∧ 2 ≤ b.val ∧ b.val < 4)

instance : DecidableRel clique := λ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance : DecidableRel pairs := λ _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel most := λ _ _ => inferInstanceAs (Decidable (_ < _))
instance : DecidableRel few := λ _ _ => inferInstanceAs (Decidable (_ < _))

/-- (110), (111): "most people know each other" is true and "few know each other" false in
the clique scenario of (102), and both are neither in the scenario of two pairs, which
Kamp and Reyle judged arguably true. -/
theorem street_scenarios :
    truthValue most clique Finset.univ = .true ∧ truthValue few clique Finset.univ = .false ∧
      truthValue most pairs Finset.univ = .indet ∧ truthValue few pairs Finset.univ = .indet := by
  decide

/-! ### Maximize Anaphora (§6) -/

/-- (128) Maximize Anaphora: among the states a DRS `K` admits, one whose set `R_u` of
anaphor–antecedent pairs is not properly included in another admitted state's. -/
def MaximizesAnaphora {E : Type*} (K : PluralAssign ℕ E → Prop) (uAnaph uAnt : ℕ)
    (S : PluralAssign ℕ E) : Prop :=
  K S ∧ ∀ S', K S' → ¬ R_u uAnaph uAnt S ⊂ R_u uAnaph uAnt S'

/-- The three boys of (125). -/
def boys : Finset Ind := {.boy1, .boy2, .boy3}

/-- (125b) for three boys: reciprocity of `u₂` to `u₁` over the boys, with nothing known
against any pair knowing each other. -/
def boysKnow (S : PluralAssign ℕ Ind) : Prop :=
  reciprocityCond u₂ u₁ S ∅ ∧ PluralAssign.sumDref S u₁ ⊆ ↑boys

/-- (126a): a minimal state for (125). -/
def boysMinimal : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .boy1), (u₂, .boy2)],
   row [(u₁, .boy2), (u₂, .boy3)],
   row [(u₁, .boy3), (u₂, .boy1)]]

/-- (126b): the strong reciprocal reading. -/
def boysStrong : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .boy1), (u₂, .boy2)],
   row [(u₁, .boy2), (u₂, .boy3)],
   row [(u₁, .boy3), (u₂, .boy1)],
   row [(u₁, .boy1), (u₂, .boy3)],
   row [(u₁, .boy2), (u₂, .boy1)],
   row [(u₁, .boy3), (u₂, .boy2)]]

private theorem boysStrong_sumDref : PluralAssign.sumDref (ofRows boysStrong) u₁ ⊆ ↑boys := by
  have h := coe_sumRows (rows := boysStrong) (u := u₁) mem_empty (row [])
  rw [eqClass_empty] at h
  rw [← h, Finset.coe_subset]
  decide

/-- §6: Maximize Anaphora selects the strong reading (126b) over the minimal state (126a):
every state (125) admits has its pairs among the strong state's. -/
theorem maximize_strong :
    MaximizesAnaphora boysKnow u₂ u₁ (ofRows boysStrong) ∧
      ¬ MaximizesAnaphora boysKnow u₂ u₁ (ofRows boysMinimal) := by
  have hK : boysKnow (ofRows boysStrong) :=
    ⟨by rw [reciprocityCond_ofRows mem_empty]; decide, boysStrong_sumDref⟩
  refine ⟨⟨hK, λ S' ⟨hr, hsub⟩ => not_ssubset_of_subset ?_⟩,
    λ h => h.2 _ hK (LE.le.ssubset_of_not_superset ?_ ?_)⟩
  · rintro ⟨a, b⟩ ⟨s, hs, ha, hb⟩
    have hb' : b ∈ boys := Finset.mem_coe.1 (hsub ⟨s, hs, hb⟩)
    have ha' : a ∈ boys := Finset.mem_coe.1 (hsub (by
      rw [← hr.1 s hs, eqClass_empty]
      exact ⟨s, hs, ha⟩))
    have hab := hr.2 s hs a b ha hb
    rw [mem_R_u_ofRows]
    clear ha hb
    revert a b
    decide
  · rintro ⟨a, b⟩ h
    rw [mem_R_u_ofRows] at h ⊢
    revert a b
    decide
  · intro h
    have := h (mem_R_u_ofRows.2
      (by decide : ∃ s ∈ boysStrong, s u₂ = some .boy3 ∧ s u₁ = some .boy1))
    rw [mem_R_u_ofRows] at this
    revert this
    decide

/-- §6.2: the classmates gave each other pictures of each other, each maximizing pairwise:
each gave a picture of herself to each of the others. -/
def classmates : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .tracy), (u₂, .chris), (u₃, .picture1), (u₄, .tracy)],
   row [(u₁, .tracy), (u₂, .matty), (u₃, .picture1), (u₄, .tracy)],
   row [(u₁, .chris), (u₂, .tracy), (u₃, .picture2), (u₄, .chris)],
   row [(u₁, .chris), (u₂, .matty), (u₃, .picture2), (u₄, .chris)],
   row [(u₁, .matty), (u₂, .tracy), (u₃, .picture3), (u₄, .matty)],
   row [(u₁, .matty), (u₂, .chris), (u₃, .picture3), (u₄, .matty)]]

/-- The three classmates. -/
def trio : Finset Ind := {.tracy, .chris, .matty}

/-- §6.2: both reciprocal relations of (134) are maximal, every ordered pair of distinct
classmates, without any all-triples row, in which a classmate gives a picture of a third
classmate. -/
theorem classmates_pairwise :
    (∀ a ∈ trio, ∀ b ∈ trio, a ≠ b → (a, b) ∈ R_u u₂ u₁ (ofRows classmates) ∧
      (a, b) ∈ R_u u₄ u₂ (ofRows classmates)) ∧
      ¬ ∃ s ∈ classmates,
        s u₁ = some .tracy ∧ s u₂ = some .chris ∧ s u₄ = some .matty := by
  simp only [mem_R_u_ofRows]
  decide

/-- (136): the wide construal of (135), each of Tracy, Matty and Chris believing that she
praised the two others. -/
def praisedWide : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .chris), (u₂, .chris), (u₃, .tracy), (w, .world1)],
   row [(u₁, .chris), (u₂, .chris), (u₃, .matty), (w, .world1)],
   row [(u₁, .tracy), (u₂, .tracy), (u₃, .chris), (w, .world2)],
   row [(u₁, .tracy), (u₂, .tracy), (u₃, .matty), (w, .world2)],
   row [(u₁, .matty), (u₂, .matty), (u₃, .chris), (w, .world3)],
   row [(u₁, .matty), (u₂, .matty), (u₃, .tracy), (w, .world3)]]

/-- §6.3: (136) is the wide reading, binding of the pronoun with reciprocity in the matrix,
and within each girl's world the reciprocal covers exactly the two others. -/
theorem praised_wide :
    bindingCond u₂ u₁ (ofRows praisedWide) ∅ ∧
      reciprocityCond u₃ u₂ (ofRows praisedWide) ∅ ∧
      ∀ s ∈ praisedWide, ∀ d,
        d ∈ sumRows praisedWide [w] s u₃ ↔ d ∈ trio ∧ some d ≠ s u₁ := by
  rw [bindingCond_ofRows, reciprocityCond_ofRows mem_empty]
  decide

end HaugDalrymple2020
