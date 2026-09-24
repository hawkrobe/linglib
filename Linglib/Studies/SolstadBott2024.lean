module

public import Linglib.Semantics.Presupposition.Context
public import Linglib.Studies.SolstadBott2022
public import Linglib.Fragments.German.Verbs

/-!
# Solstad & Bott (2024): Cataphoric Resolution of Projective Content

This file formalizes the contextual constraint and the filtering behaviour of the occasion
verbs of [solstad-bott-2024]. An occasion verb (*gratulieren*, *kritisieren*, *bestrafen*) is
an agent-evocator verb of the implicit-causality literature whose use implies that an
eventuality prior to the agent's action gave the agent reason to act, the occasion. Three
rating experiments in the paradigm of [tonhauser-beaver-degen-2018] find the occasion
implication projective and not at issue like the content of established triggers, and find it,
uniquely among those triggers, resolvable on either side of the trigger: an utterance of an
occasion verb is degraded in a context that neither entails the occasion nor goes on to supply
it, and is restored as well by a following segment as by a preceding one. In conjoined
conditional antecedents the implication is filtered by a conjunct entailing it on either side,
where the factive and aspectual triggers of [mandelkern-etal-2020] filter only from the left.

`Given` and `Addressed` state two contextual constraints over a discourse: the strong
contextual felicity of [tonhauser-beaver-roberts-simons-2013], which demands a preceding
segment entailing the content, and the weaker constraint the paper introduces, which any
segment can meet. The paper refines the m-positive contexts of the former into m-anaphoric and
m-cataphoric ones, and `cataphoric_separates` shows that a cataphoric context meets the weak
constraint and not the strong one. `andSymmetric` is conjunction under the symmetric local
contexts of [schlenker-2009], `localAccommodation` the rival on which the trigger's content is
asserted in place, and `exp3_predictions` derives the three accounts' projection verdicts on
the three Experiment 3 antecedents: asymmetric filtering ([heim-1983]) levels the trigger-first
condition with the trigger alone, local accommodation levels all three, and only symmetric
filtering separates the trigger alone from both conjoined conditions, which is the pattern
occasion verbs show.

Occasion verbs are the agent-evocator class of [solstad-bott-2022]: their empty slot is the
occasion, presupposed rather than asserted, so the slot argument is the object and an
explanation continuation is a cataphoric resolution. The psych verbs of Experiment 2 share the
object bias and the explanation continuations but not the projectivity, so the two classes'
underspecification has different sources.

## Implementation notes

The experimental results are reported in prose; the library's format for experimental data
is pending, and the Block 2 means remain as rows in `Data/Examples/SolstadBott2024.json` for
the pooled projectivity data. Experiments 1 and 2 (Block 1) find occasion verbs, personal
pronouns, demonstratives and *auch* degraded in neutral contexts, and only occasion verbs
restored by a following segment; factives, *aufhören*, possessives and non-restrictive relatives
are unconstrained. Block 2 replicates the negative correlation between projectivity and
at-issueness across trigger types, with occasion verbs clustering with definites, clefts,
*auch* and pronouns and the psych verbs forming a cluster of their own in the middle of both
scales. Experiment 3 finds the trigger-first and trigger-last antecedents equally and clearly
less projective than the trigger alone for occasion verbs, and the trigger-first antecedent as
projective as the trigger alone for the factive and aspectual triggers.

The paper does not test obligatory local effect, and its finding that occasion verbs are
degraded in neutral contexts is a contextual felicity constraint, so occasion verbs are not
placed in the taxonomy of [tonhauser-beaver-roberts-simons-2013] here.

## References

* [solstad-bott-2024]
* [solstad-bott-2022]
* [tonhauser-beaver-roberts-simons-2013]
* [tonhauser-beaver-degen-2018]
* [mandelkern-etal-2020]
* [schlenker-2009]
* [heim-1983]
-/

@[expose] public section

namespace SolstadBott2024

open Presupposition Presupposition.Context Presupposition.PartialProp

variable {W : Type*}

/-! ### Anaphoric and cataphoric resolution -/

/-- A discourse, the sequence of its segments' contents. -/
abbrev Discourse (W : Type*) := List (Set W)

/-- Segment `j` of the discourse entails `m`. -/
def Entails (d : Discourse W) (j : ℕ) (m : Set W) : Prop := ∃ s ∈ d[j]?, s ⊆ m

/-- The content `m` of the trigger in segment `i` is given: a preceding segment entails it,
the m-positive context of [tonhauser-beaver-roberts-simons-2013], m-anaphoric here. -/
def Given (d : Discourse W) (i : ℕ) (m : Set W) : Prop := ∃ j < i, Entails d j m

/-- The content is resolved cataphorically: a following segment entails it. -/
def Cataphoric (d : Discourse W) (i : ℕ) (m : Set W) : Prop := ∃ j > i, Entails d j m

/-- The content is addressed: some other segment entails it, before or after the trigger. -/
def Addressed (d : Discourse W) (i : ℕ) (m : Set W) : Prop := ∃ j ≠ i, Entails d j m

theorem addressed_iff {d : Discourse W} {i : ℕ} {m : Set W} :
    Addressed d i m ↔ Given d i m ∨ Cataphoric d i m := by
  constructor
  · rintro ⟨j, hj, h⟩
    rcases Nat.lt_or_gt_of_ne hj with h' | h'
    exacts [.inl ⟨j, h', h⟩, .inr ⟨j, h', h⟩]
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩) <;> exact ⟨j, by omega, h⟩

theorem Given.addressed {d : Discourse W} {i : ℕ} {m : Set W} (h : Given d i m) :
    Addressed d i m :=
  addressed_iff.2 (.inl h)

theorem Cataphoric.addressed {d : Discourse W} {i : ℕ} {m : Set W} (h : Cataphoric d i m) :
    Addressed d i m :=
  addressed_iff.2 (.inr h)

/-- A trigger imposes on its content no contextual constraint, the strong contextual felicity of
[tonhauser-beaver-roberts-simons-2013], or the weaker constraint of occasion verbs, which is met on
either side of the trigger. -/
inductive Felicity where
  | free
  | strong
  | weak
  deriving DecidableEq, Repr

/-- The constraint holds of the content `m` of the trigger in segment `i`. -/
def Felicity.Satisfied : Felicity → Discourse W → ℕ → Set W → Prop
  | .free, _, _, _ => True
  | .strong, d, i, m => Given d i m
  | .weak, d, i, m => Addressed d i m

/-- The constraints are nested: whatever satisfies strong felicity satisfies weak felicity. -/
theorem Felicity.Satisfied.weak_of_strong {d : Discourse W} {i : ℕ} {m : Set W}
    (h : Felicity.strong.Satisfied d i m) : Felicity.weak.Satisfied d i m :=
  Given.addressed h

/-- In a neutral context, the trigger's segment alone, nothing is addressed. -/
theorem not_addressed_neutral (t m : Set W) : ¬ Addressed [t] 0 m := by
  rintro ⟨j, hj, s, hs, -⟩
  cases j with
  | zero => exact hj rfl
  | succ j => simp at hs

/-- In an anaphoric context a preceding segment entailing the content gives it. -/
theorem given_anaphoric {p m : Set W} (t : Set W) (h : p ⊆ m) : Given [p, t] 1 m :=
  ⟨0, Nat.zero_lt_one, p, rfl, h⟩

/-- In a cataphoric context the content is not given: nothing precedes the trigger. -/
theorem not_given_cataphoric (t p m : Set W) : ¬ Given [t, p] 0 m := by
  rintro ⟨j, hj, -⟩; omega

/-- In a cataphoric context a following segment entailing the content resolves it. -/
theorem cataphoric_cataphoric {p m : Set W} (t : Set W) (h : p ⊆ m) : Cataphoric [t, p] 0 m :=
  ⟨1, Nat.zero_lt_one, p, rfl, h⟩

/-- The paper refines m-positive contexts: a cataphoric context satisfies the weak constraint and
not the strong one, which is where occasion verbs part from pronouns. -/
theorem cataphoric_separates {p m : Set W} (t : Set W) (h : p ⊆ m) :
    Felicity.weak.Satisfied [t, p] 0 m ∧ ¬ Felicity.strong.Satisfied [t, p] 0 m :=
  ⟨(cataphoric_cataphoric t h).addressed, not_given_cataphoric t p m⟩

/-! ### Filtering in conditional antecedents -/

/-- Under the symmetric local contexts of [schlenker-2009] either conjunct's assertion may
satisfy the other's presupposition. -/
def andSymmetric (p q : PartialProp W) : PartialProp W where
  presup := λ w => (q.assertion w → p.presup w) ∧ (p.assertion w → q.presup w)
  assertion := λ w => p.assertion w ∧ q.assertion w

/-- Under local accommodation the trigger's presupposition is asserted in place of projecting. -/
def localAccommodation (p : PartialProp W) : PartialProp W where
  presup := λ _ => True
  assertion := λ w => p.presup w ∧ p.assertion w

/-- Under asymmetric filtering the trigger-first antecedent presupposes what the trigger
alone does: nothing is filtered from the right. -/
theorem andFilter_triggerFirst_presup (t : PartialProp W) (s : W → Prop) :
    (andFilter t (ofProp s)).presup = t.presup := by
  ext w; simp [andFilter, ofProp]

/-- Under asymmetric filtering the trigger-last antecedent is filtered whenever the first
conjunct entails the content. -/
theorem andFilter_triggerLast_satisfied (c : Set W) {t : PartialProp W} {s : W → Prop}
    (h : ∀ w, s w → t.presup w) : presupSatisfied c (andFilter (ofProp s) t) :=
  λ w _ => ⟨trivial, h w⟩

/-- Under symmetric filtering the trigger-first antecedent is filtered too. -/
theorem andSymmetric_triggerFirst_satisfied (c : Set W) {t : PartialProp W} {s : W → Prop}
    (h : ∀ w, s w → t.presup w) : presupSatisfied c (andSymmetric t (ofProp s)) :=
  λ w _ => ⟨h w, λ _ => trivial⟩

theorem andSymmetric_triggerLast_satisfied (c : Set W) {t : PartialProp W} {s : W → Prop}
    (h : ∀ w, s w → t.presup w) : presupSatisfied c (andSymmetric (ofProp s) t) :=
  λ w _ => ⟨λ _ => trivial, h w⟩

/-- Local accommodation never projects, whatever the antecedent. -/
theorem localAccommodation_not_projects (c : Set W) (p : PartialProp W) :
    ¬ presupProjects c (localAccommodation p) :=
  λ h => h λ _ _ => trivial

/-- The three accounts on the three Experiment 3 antecedents, in an ignorance context with
a world lacking the content and a conjunct entailing it. The trigger alone projects. Symmetric
filtering filters both conjoined orders; asymmetric filtering filters only the trigger-last
order, levelling trigger-first with the trigger alone; local accommodation levels all three.
Occasion verbs show the first pattern, the factive and aspectual triggers the second. -/
theorem exp3_predictions {c : Set W} {t : PartialProp W} {s : W → Prop}
    (hc : ∃ w ∈ c, ¬ t.presup w) (h : ∀ w, s w → t.presup w) :
    presupProjects c t ∧
    presupSatisfied c (andSymmetric t (ofProp s)) ∧
    presupSatisfied c (andSymmetric (ofProp s) t) ∧
    presupProjects c (andFilter t (ofProp s)) ∧
    presupSatisfied c (andFilter (ofProp s) t) ∧
    ¬ presupProjects c (localAccommodation t) := by
  obtain ⟨w, hw, hm⟩ := hc
  refine ⟨λ hs => hm (hs hw), andSymmetric_triggerFirst_satisfied c h,
    andSymmetric_triggerLast_satisfied c h, λ hs => hm ?_,
    andFilter_triggerLast_satisfied c h, localAccommodation_not_projects c t⟩
  have := hs hw
  rwa [andFilter_triggerFirst_presup] at this

/-! ### Occasion verbs as agent-evocator verbs -/

open German.Verbs in
/-- The paper's occasion verbs, the fragment entries carrying the occasion sense. -/
def occasionVerbs : List German.Verb := allVerbs.filter (·.senseTag = .occasion)

open SolstadBott2022 in
/-- Occasion verbs are the agent-evocator class: the slot argument is the object, whose
prior eventuality is the occasion. -/
theorem occasion_icausBias : VerbClass.agentEvocator.icausBias = some .np2 := by decide

open SolstadBott2022 in
/-- The object bias is shared with experiencer-stimulus verbs, whose slot content is not
projective: the coreference bias does not read off projectivity. -/
theorem icausBias_shared_with_expStim :
    VerbClass.agentEvocator.icausBias = VerbClass.expStim.icausBias := by decide

end SolstadBott2024
