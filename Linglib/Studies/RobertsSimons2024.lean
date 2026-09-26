module

public import Linglib.Core.Probability.UniformOn
public import Linglib.Fragments.English.Verbs
public import Linglib.Semantics.Aspect.Phasal
public import Linglib.Semantics.Presupposition.Context
public import Linglib.Semantics.Questions.Resolution

/-!
# Roberts and Simons (2024): Preconditions and projection

[roberts-simons-2024] explain the projective content of change-of-state predicates, factives and
selectional restrictions without a lexical constraint on the context. That content describes the
ontological preconditions of the event type the predicate denotes, the conditions any event of
the type depends on, so a sentence describing the event entails them (§2). Projection is the
listener's inference that the speaker presumes a context entailing them (§3), the model of
[qing-goodman-lassiter-2016] and [warstadt-2022]: a negated trigger is more informative relative
to a context restricted to the precondition, and a precondition, unlike a consequence of the
event, can hold where the event does not, so it is the safe thing to accommodate (§3.1).
Projection is suppressed where the presumption cannot be attributed to the speaker (§3.2.1), and
filtering is the case in which the speaker has asserted, supposed or entertained the
precondition, so that the trigger is evaluated in a context that includes it (§4).

## Main definitions

* `cosOccurs`, `cosPrecondition` — where a change of state occurs and where its precondition,
  the prior state of `Aspect.Phasal`, holds.
* `Cell` — the three cells of "Does Jane know that it's raining?" in §3.1.

## Main statements

* `cosOccurs_subset_cosPrecondition` — a change of state entails its precondition (§2.1).
* `mem_cosPrecondition_diff_cosOccurs`, `stop_mem_cosPrecondition_diff_cosOccurs`,
  `inter_compl_cosOccurs_eq_empty` — a precondition is consistent with the negated trigger, an
  entailment holding only where the change occurs is not (§3.1).
* `uniformOn_raining_compl_knows`, `uniformOn_knows_lt_one` — restricting the context to raining
  makes the negative answer less probable, so more informative, and the two answers
  equiprobable, while the affirmative is informative either way (§3.1).
* `not_presumes_of_doubt`, `resolves_of_presumes`, `not_subset_of_presumes_ignorance` — the
  suppression cases (23)–(25) and *discover* in (28c).
* `localContext_subset`, `disjunctive_antecedent_filters` — filtering in (41)–(44).

## Implementation notes

Indices are world–time pairs, and a change of state relates the prior state at an earlier index,
under a precedence relation `r`, to the result state at the index itself, so that its occurrence
entails its precondition as §2.1 requires. The paper's two diagnostics for preconditions, the
"part of what allowed for" frame and the counterfactual, sort entailments into preconditions,
consequences and concomitants ontologically rather than semantically, so they are not derived
here. The §3.1 cells are equiprobable, the paper's "roughly equal" probabilities.

## TODO

* (28) is [karttunen-1971b]'s *discover*/*regret* contrast (`Karttunen1971b.projection_rows`);
  only the conditional (28c) is derived here, not the question (28b) or *regret*'s projection.
* The reference-time account of the *know*/*discover* contrast in (32)–(34).

## References

* [C. Roberts, M. Simons, *Preconditions and Projection: Explaining Non-Anaphoric Presupposition*
  (2024)][roberts-simons-2024]
* [L. Karttunen, *Some observations on factivity* (1971)][karttunen-1971b]
* [L. Karttunen, *Presuppositions of Compound Sentences* (1973)][karttunen-1973]
* [R. C. Stalnaker, *Pragmatic Presuppositions* (1974)][stalnaker-1974]
* [L. Karttunen, *Presupposition and Linguistic Context* (1974)][karttunen-1974-presupposition]
* [I. Heim, *On the Projection Problem for Presuppositions* (1983)][heim-1983]
* [C. Qing, N. D. Goodman, D. Lassiter, *A Rational Speech-Act Model of Projective Content*
  (2016)][qing-goodman-lassiter-2016]
* [A. Warstadt, *Presupposition Triggering Reflects Pragmatic Reasoning about Utterance Utility*
  (2022)][warstadt-2022]
-/

@[expose] public section

namespace RobertsSimons2024

open Aspect Question MeasureTheory ProbabilityTheory

variable {ι : Type*}

/-! ### Ontological preconditions (§2) -/

section ChangeOfState

variable (t : Phasal) (r : ι → ι → Prop) (P : ι → Prop)

/-- A change of state occurs at an index when the prior state held at an earlier index and the
result state holds at the index. -/
def cosOccurs : Set ι := {i | ∃ i', r i' i ∧ t.Transition (P i') (P i)}

/-- The ontological precondition of a change of state is its prior state at an earlier index, as
being on the ladder is for falling off it (5). -/
def cosPrecondition : Set ι := {i | ∃ i', r i' i ∧ t.Prior (P i')}

variable {t r P}

/-- A sentence describing a change of state entails its precondition (§2.1). -/
theorem cosOccurs_subset_cosPrecondition : cosOccurs t r P ⊆ cosPrecondition t r P :=
  fun _ ⟨i', hr, hp, _⟩ ↦ ⟨i', hr, hp⟩

/-! ### Why preconditions project (§3.1) -/

/-- The precondition of a change of state can hold without the change, as when John smoked and
still smokes, so accommodating it is consistent with *John didn't stop smoking* (§3.1). -/
theorem mem_cosPrecondition_diff_cosOccurs {i i' : ι} (hr : r i' i) (hp : t.Prior (P i'))
    (hn : ¬ t.Result (P i)) : i ∈ cosPrecondition t r P \ cosOccurs t r P :=
  ⟨⟨i', hr, hp⟩, fun ⟨_, _, _, h⟩ ↦ hn h⟩

/-- An entailment that holds only where the change occurs, as a consequence or concomitant of it
does, is inconsistent with the negated trigger, which makes the precondition the safer thing to
accommodate (§3.1). -/
theorem inter_compl_cosOccurs_eq_empty {F : Set ι} (hF : F ⊆ cosOccurs t r P) :
    F ∩ (cosOccurs t r P)ᶜ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨h, hn⟩ ↦ hn (hF h)

/-- *John didn't stop smoking* (§3.1), with *stop* the English Fragment's entry: John having
smoked is consistent with the negated trigger, since he may still smoke. -/
theorem stop_mem_cosPrecondition_diff_cosOccurs {i i' : ι} (hr : r i' i) (h' : P i')
    (h : P i) : ∃ t, English.stop.phasal = some t ∧ i ∈ cosPrecondition t r P \ cosOccurs t r P :=
  ⟨.cessation, rfl, mem_cosPrecondition_diff_cosOccurs hr h' (not_not_intro h)⟩

end ChangeOfState

/-- The cells of the question "Does Jane know that it's raining?" in the §3.1 diagram: raining
and Jane knows it, raining and she doesn't, and not raining. -/
inductive Cell
  | rainKnown
  | rainUnknown
  | noRain
  deriving DecidableEq, Fintype

instance : MeasurableSpace Cell := ⊤
instance : DiscreteMeasurableSpace Cell := ⟨fun _ ↦ trivial⟩

/-- R, that it's raining. -/
def raining : Set Cell := {.rainKnown, .rainUnknown}

/-- K(j,r), that Jane knows that it's raining. -/
def knows : Set Cell := {.rainKnown}

private theorem ncard_raining : raining.ncard = 2 := Set.ncard_pair nofun

private theorem ncard_univ_cell : (Set.univ : Set Cell).ncard = 3 := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]; rfl

/-- Relative to a context restricted to raining, the negative answer *Jane doesn't know that
it's raining* is less probable than relative to one that leaves the rain open, so asserting it
is more informative, and the two answers become equiprobable (§3.1). -/
theorem uniformOn_raining_compl_knows :
    (uniformOn raining).real knowsᶜ < (uniformOn Set.univ).real knowsᶜ ∧
      (uniformOn raining).real knowsᶜ = (uniformOn raining).real knows := by
  have h₁ : raining ∩ knowsᶜ = {.rainUnknown} := by ext x; cases x <;> simp [raining, knows]
  have h₂ : raining ∩ knows = {.rainKnown} := by ext x; cases x <;> simp [raining, knows]
  have h₃ : Set.univ ∩ knowsᶜ = {.rainUnknown, .noRain} := by ext x; cases x <;> simp [knows]
  simp only [uniformOn_real_apply, h₁, h₂, h₃, ncard_raining, ncard_univ_cell,
    Set.ncard_singleton, Set.ncard_pair (show Cell.rainUnknown ≠ .noRain from nofun)]
  norm_num

/-- The affirmative *Jane knows that it's raining* is informative relative to either context
(§3.1). -/
theorem uniformOn_knows_lt_one :
    (uniformOn Set.univ).real knows < 1 ∧ (uniformOn raining).real knows < 1 := by
  have h₁ : Set.univ ∩ knows = {.rainKnown} := Set.univ_inter _
  have h₂ : raining ∩ knows = {.rainKnown} := by ext x; cases x <;> simp [raining, knows]
  simp only [uniformOn_real_apply, h₁, h₂, ncard_raining, ncard_univ_cell, Set.ncard_singleton]
  norm_num

/-! ### Suppression (§3.2)

On the projective reading the speaker presumes a context `C` entailing the precondition `pre` of
the event they raise, `C ⊆ pre` (§3.1); suppression is the case in which that presumption cannot
be attributed to them. -/

/-- Cases 1 and 2 of §3.2.1: projection is suppressed where someone who must accept the presumed
context does not take the precondition to hold, the hearer in (23), whom the speaker knows to
reject it, or the doubting speaker in (24). In (23) the context itself is agnostic, so the
suppression does not come from a contradiction in the context. -/
theorem not_presumes_of_doubt {C S pre : Set ι} (hS : S ⊆ C) (h : ¬ S ⊆ pre) : ¬ C ⊆ pre :=
  fun hp ↦ h (hS.trans hp)

/-- Case 3 of §3.2.1: projection is suppressed where the precondition is at issue, since
presuming a precondition that is an alternative of the question under discussion resolves it,
which the speaker in (25) signals she cannot do. -/
theorem resolves_of_presumes {C pre : Set ι} {Q : Question ι} (h : pre ∈ alt Q) (hp : C ⊆ pre) :
    C ∈ Q :=
  mem_of_exists_alt_subset ⟨_, h, hp⟩

/-- (28c), *If I discover later that I have not told the truth*: *discover* has the agent's
prior ignorance among its preconditions, and a speaker who presumes that she is ignorant whether
`P`, where `Dox` gives her beliefs, cannot also presume `P`, since she believes what she
presumes ([stalnaker-1974]'s explanation, sharpened by the ignorance precondition (29)). -/
theorem not_subset_of_presumes_ignorance {Dox : ι → Set ι} {C P : Set ι} {w : ι} (hw : w ∈ C)
    (hbel : Dox w ⊆ C) (hign : C ⊆ {v | ¬ Dox v ⊆ P}) : ¬ C ⊆ P :=
  fun hP ↦ hign hw (hbel.trans hP)

/-! ### Filtering (§4)

The filtering constructions (41), (42), (43) place the trigger in the second conjunct, in the
consequent, or in a disjunct. The paper shares with the satisfaction theory the assumption that
the trigger is evaluated in the context updated with the other clause, the local context of
[karttunen-1974-presupposition]'s table (`Presupposition.Connective.localContext`), but not the
requirement that the local context entail the precondition. -/

open Presupposition (Connective)

/-- Filtering arises where the first clause asserts or supposes the precondition, or the other
disjunct is its negation: the trigger is evaluated in a context entailing the precondition, so
no global presumption is attributable to the speaker; in disjunction the condition concerns the
other disjunct whichever comes first (§4). -/
theorem localContext_subset {C A pre : Set ι} :
    (A ⊆ pre → Connective.conj.localContext C A ⊆ pre ∧ Connective.cond.localContext C A ⊆ pre) ∧
      (Aᶜ ⊆ pre → Connective.disj.localContext C A ⊆ pre) :=
  ⟨fun h ↦ ⟨fun _ hw ↦ h hw.2, fun _ hw ↦ h hw.2⟩, fun h _ hw ↦ h hw.2⟩

/-- The contrast in (44) is that, in a context that leaves the precondition open, a disjunctive
antecedent whose other disjunct negates the precondition filters it, whereas a simple antecedent
leaves the precondition to be presumed globally, which the open context forbids. -/
theorem disjunctive_antecedent_filters {C pre : Set ι} (hopen : ¬ C ⊆ pre) :
    Connective.disj.localContext C preᶜ ⊆ pre ∧ ¬ Connective.cond.localContext C Set.univ ⊆ pre :=
  ⟨fun _ hw ↦ not_not.mp hw.2, fun h ↦ hopen fun _ hw ↦ h ⟨hw, trivial⟩⟩

end RobertsSimons2024
