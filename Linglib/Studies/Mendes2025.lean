import Linglib.Semantics.Dynamic.CDRT
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Semantics.Mood.Situation
import Linglib.Semantics.Tense.Defs

/-!
# Mendes (2025): Indefiniteness in future reference

This file formalizes the analysis of the Subordinate Future, a subjunctive combined with a
forward-shifting temporal morpheme, in [mendes-2025]. The subjunctive is an indefinite over
situations, introducing a situation dref among the historical alternatives of its anchor, and
the indicative is the definite that retrieves it, so that a main clause is evaluated in the
future situation its subordinate clause introduced (modal donkey anaphora) and a strong
quantifier whose restrictor carries the form has its existence presupposition satisfied in a
historical alternative rather than at the anchor (modal displacement). The lexical entries are
the paper's, in the compositional discourse representation theory of [muskens-1996] at
`Semantics/Dynamic/CDRT` over situation drefs: `temporal` tests the running times of two
situations against a tense cell of `Semantics/Tense/Defs`, `subj` and `ind` are the moods, and
`sfForm_true_at` unpacks the paper's two derivations, the conditional *If Ivan leaves the room
smiling, the interview went well* and the relative clause *every candidate who delivers a good
job talk*, to their truth conditions, and `temporal_shift` reads the orderings of the paper's
table of main-clause tenses off the entries.

## Implementation notes

* The carrier registers situation drefs only: individual drefs are saturated in the radicals
  (*Ivan leaves the room* is a situation predicate), so the quantifying-in of the relative clause
  reduces to the implication of its restrictor and nuclear scope.
* A situation is a world–time `Index`, and *s₂ is part of the world of s₁* is world identity,
  `Mood.sameWorld`.

## References

* [mendes-2025]
* [muskens-1996]
-/

namespace Mendes2025

open Reference HistoricalAlternatives DynamicSemantics DynamicSemantics.Update
  DynamicSemantics.RegisterStructure
open CDRT (DProp dref)

variable {W T : Type*}

/-! ### Types -/

/-- A state assigns situations to drefs. -/
abbrev State (W T : Type*) := CDRT.State (Index W T)

/-- A situation dref, the type `s`. -/
abbrev Sit (W T : Type*) := Dref (State W T) (Index W T)

/-- A sentence radical, the type `st`: a situation dref to an update. -/
abbrev Radical (W T : Type*) := Sit W T → DProp (Index W T)

/-- A tensed radical, the type `(s, st)`, the argument of a mood morpheme. -/
abbrev Tensed (W T : Type*) := Sit W T → Sit W T → DProp (Index W T)

/-- The radical of a situation predicate, `λs.[ | P(s)]`. -/
def radical (P : Index W T → Prop) : Radical W T := fun s => test (atom1 P s)

/-! ### Lexical entries -/

/-- The indicative, `ind^{s₂,s₁} ⇝ λℙ.[ | s₂ ≤ w_{s₁}]; ℙ(s₂)(s₁)`: a definite over situations,
testing that `s₂` is part of the world of `s₁`. -/
def ind (s₂ s₁ : Sit W T) (ℙ : Tensed W T) : DProp (Index W T) :=
  seq (test fun i => Mood.sameWorld (s₂ i) (s₁ i)) (ℙ s₂ s₁)

variable {ℙ : Tensed W T} {s s' : Sit W T} {i o : State W T}

theorem ind_apply :
    ind s s' ℙ i o ↔ (s i).world = (s' i).world ∧ ℙ s s' i o := by
  simp [ind, seq, Relation.Comp, test]

private theorem randomAssign_apply {n : ℕ} :
    randomAssign (S := State W T) n i o ↔ ∃ e, o = Function.update i n e :=
  Iff.rfl

variable [LinearOrder T] (history : HistoricalAlternatives W T)

/-- A temporal morpheme, `λ𝒫.λs.λs'.[ | τ(s) ⋈ τ(s')]; 𝒫(s)`: it tests that the running times
of `s` and `s'` compare within the cell, then runs the radical at `s`. -/
def temporal (cell : Finset Ordering) (P : Radical W T) (s s' : Sit W T) :
    DProp (Index W T) :=
  seq (test fun i => compare (s i).time (s' i).time ∈ cell) (P s)

/-- `fut` places the event situation after the evaluation situation. -/
abbrev fut : Radical W T → Sit W T → Sit W T → DProp (Index W T) := temporal Tense.future

/-- `pres` places the event situation at the evaluation situation. -/
abbrev pres : Radical W T → Sit W T → Sit W T → DProp (Index W T) := temporal Tense.present

/-- `past` places the event situation before the evaluation situation. -/
abbrev past : Radical W T → Sit W T → Sit W T → DProp (Index W T) := temporal Tense.past

/-- The subjunctive, `subj^{s₁}_{s₀} ⇝ λℙ.[s₁ | s₁ ∈ hist s₀]; ℙ(s₁)(s₀)`: an indefinite over
situations, introducing `s₁` among the historical alternatives of the anchor `s₀`. -/
def subj (s₁ : ℕ) (s₀ : Sit W T) (ℙ : Tensed W T) : DProp (Index W T) :=
  seq (dexists s₁ (test fun i => dref s₁ i ∈ historicalBase history (s₀ i))) (ℙ (dref s₁) s₀)

/-! ### Unpacking the entries -/

variable {cell : Finset Ordering} {P : Index W T → Prop} {s₁ : ℕ}

theorem temporal_radical_apply :
    temporal cell (radical P) s s' i o ↔
      i = o ∧ compare (s o).time (s' o).time ∈ cell ∧ P (s o) := by
  rw [temporal, radical, test_seq_test]; exact Iff.rfl

/-- A temporal morpheme over a radical is a test: it neither introduces nor retrieves drefs. -/
theorem isTest_temporal_radical : IsTest (temporal cell (radical P) s s') :=
  (isTest_test _).seq (isTest_test _)

theorem subj_apply :
    subj history s₁ s ℙ i o ↔
      ∃ e, e ∈ historicalBase history (s (Function.update i s₁ e)) ∧
        ℙ (dref s₁) s (Function.update i s₁ e) o := by
  simp [subj, dexists, randomAssign_apply, seq, Relation.Comp, test, dref]

/-! ### The Subordinate Future

The forms `SF(A); tense(C)` of the paper's table of main-clause tenses: a conditional
antecedent or a relative clause carrying the Subordinate Future, `subj^{s₁}_{s₀}(fut(A))`, and
a main clause `ind^{s₂,s₁}(tense(C))` whose evaluation situation is the introduced `s₁`. The
anchor `s₀` is the dref `0`, the introduced situation the dref `1`, the main-clause situation
the dref `2`. -/

variable (A C : Index W T → Prop)

/-- A subordinate clause carrying the Subordinate Future and a main clause with the tense
`cell`, as a dynamic implication: the conditional and the relative-clause quantification of the
paper's derivations. -/
def sfForm (cell : Finset Ordering) : DProp (Index W T) :=
  DProp.impl (subj history 1 (dref 0) (fut (radical A)))
    (ind (dref 2) (dref 1) (temporal cell (radical C)))

/-- *If Ivan leaves the room smiling, the interview went well*: the Subordinate Future in the
antecedent, the past in the consequent. -/
abbrev conditional (leaves wentWell : Index W T → Prop) : DProp (Index W T) :=
  sfForm history leaves wentWell Tense.past

/-- *Every candidate who delivers a good job talk has an equal chance of being hired*: the
Subordinate Future in the restrictor, the present in the nuclear scope. -/
abbrev relativeClause (delivers chance : Index W T → Prop) : DProp (Index W T) :=
  sfForm history delivers chance Tense.present

/-- The truth conditions of the paper's derivations: the form is a test, true at a state iff
every historical alternative `e` of the anchor after it where `A` holds has the main-clause
situation in its world, timed by the cell relative to `e`, satisfying `C`. -/
theorem sfForm_true_at :
    DProp.true_at (sfForm history A C cell) i ↔
      ∀ e ∈ historicalBase history (i 0), (i 0).time < e.time → A e →
        (i 2).world = e.world ∧ compare (i 2).time e.time ∈ cell ∧ C (i 2) := by
  rw [sfForm, DProp.impl_true_at]
  simp only [DProp.true_at, closure, subj_apply, temporal_radical_apply, ind_apply, dref,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, exists_and_left, exists_eq_left']
  simp

/-- *If Ivan leaves the room smiling, the interview went well* is true iff in every later
historical alternative of the anchor where Ivan leaves, the interview situation lies in its world,
earlier, and went well. -/
theorem conditional_true_at (leaves wentWell : Index W T → Prop) :
    DProp.true_at (conditional history leaves wentWell) i ↔
      ∀ e ∈ historicalBase history (i 0), (i 0).time < e.time → leaves e →
        (i 2).world = e.world ∧ (i 2).time < e.time ∧ wentWell (i 2) := by
  simp only [conditional, sfForm_true_at, Tense.compare_mem_past]

/-- *Every candidate who delivers a good job talk has an equal chance of being hired* is true
iff in every later historical alternative of the anchor where the talk is delivered, the
hiring situation lies in its world, at its time, and gives an equal chance. -/
theorem relativeClause_true_at (delivers chance : Index W T → Prop) :
    DProp.true_at (relativeClause history delivers chance) i ↔
      ∀ e ∈ historicalBase history (i 0), (i 0).time < e.time → delivers e →
        (i 2).world = e.world ∧ (i 2).time = e.time ∧ chance (i 2) := by
  simp only [relativeClause, sfForm_true_at, Tense.compare_mem_present]

variable {k l : State W T}

/-- Temporal shift: the Subordinate Future places the situation it introduces after the anchor,
and the main clause is timed by its tense relative to that situation, not the anchor. The rows
of the paper's table of main-clause tenses are the cells `future`, `present` and `past`. -/
theorem temporal_shift (hk : subj history 1 (dref 0) (fut (radical A)) i k)
    (hl : ind (dref 2) (dref 1) (temporal cell (radical C)) k l) :
    (l 0).time < (l 1).time ∧ compare (l 2).time (l 1).time ∈ cell := by
  obtain ⟨e, -, hk⟩ := (subj_apply history).mp hk
  obtain ⟨rfl, ht, -⟩ := temporal_radical_apply.mp hk
  obtain ⟨-, hl⟩ := ind_apply.mp hl
  obtain ⟨rfl, hc, -⟩ := temporal_radical_apply.mp hl
  exact ⟨by simpa [dref] using ht, hc⟩

/-- Modal donkey anaphora: the indicative retrieves the situation the subjunctive introduced,
so the main clause is evaluated in a historical alternative of the anchor. -/
theorem modal_donkey_anaphora (hk : subj history 1 (dref 0) (fut (radical A)) i k)
    (hl : ind (dref 2) (dref 1) (temporal cell (radical C)) k l) :
    (l 2).world ∈ history (l 0) := by
  obtain ⟨e, he, hk⟩ := (subj_apply history).mp hk
  obtain ⟨rfl, -, -⟩ := temporal_radical_apply.mp hk
  obtain ⟨hw, hl⟩ := ind_apply.mp hl
  obtain ⟨rfl, -, -⟩ := temporal_radical_apply.mp hl
  have h₁ := he.1
  simp [dref] at hw h₁ ⊢
  rwa [hw]

/-! ### Modal displacement

A restrictor carrying the Subordinate Future is true at a state iff some historical alternative
of the anchor, after it, satisfies it: the existence presupposition of a strong quantifier is
satisfied in a historical alternative, not at the anchor, which is why the continuation *I doubt
anyone will come at all* is felicitous. Under the indicative it must be satisfied in the
anchor's world. -/

/-- The Subordinate Future restrictor is true iff the anchor has a later historical alternative
satisfying `A`. -/
theorem subj_fut_true_at :
    DProp.true_at (subj history 1 (dref 0) (fut (radical A))) i ↔
      ∃ e ∈ historicalBase history (i 0), (i 0).time < e.time ∧ A e := by
  simp [DProp.true_at, closure, subj_apply, temporal_radical_apply, dref]

/-- The indicative restrictor is true iff its situation lies in the anchor's world, after the
anchor, and satisfies `A`. -/
theorem ind_fut_true_at :
    DProp.true_at (ind (dref 2) (dref 0) (fut (radical A))) i ↔
      (i 2).world = (i 0).world ∧ (i 0).time < (i 2).time ∧ A (i 2) := by
  simp [DProp.true_at, closure, ind_apply, temporal_radical_apply, dref]

end Mendes2025
