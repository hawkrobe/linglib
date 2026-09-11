import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Tense.TemporalAdverbials
import Linglib.Studies.IatridouEtAl2001

/-!
# Iatridou and Zeijlstra (2021): The Complex Beauty of Boundary Adverbials

This file formalizes [iatridou-zeijlstra-2021]'s account of *in years* and *until* as
boundary adverbials that are domain wideners. A negated perfect asserts that no event lies in
the perfect time span (20), the perfective placing the event inside the span as
`Aspect.PRFV` does; *in years* introduces the subinterval alternatives of the span (49) and is
exhaustified, `Exh`, which contradicts the positive claim whenever the events are shorter than
the span and is vacuous under negation, the NPI-hood of Section 4. As a domain widener it
sets its boundary as far as is logically possible, `Widened`: the span is event-free and no
wider span with the same fixed boundary is, from which the actuality inference at the boundary
and the beyond expectation inference follow, Constant's observation. *Until* is the mirror
image with the left boundary fixed, and the unified analysis of Section 7 falls out of the
same operator: with an imperfective predicate, `Aspect.UNBOUNDED`, every alternative is
entailed and exhaustification vacuous, so *until* appears without negation and negation may
scope over or under it; with a perfective predicate only the construal exhaustifying the
negated claim survives.

## Implementation notes

* Exhaustification negates the proper subinterval alternatives that the claim does not entail
  as a schema, over every event predicate and world, the logical entailment of the paper's
  "stronger alternatives".
* The paper's contradiction for the not-throughout claim under exhaustification, (142), is
  not a matter of logic alone: `unbounded_of_forall_lt` needs the events to sum and the span
  to have an interior point.
* The paper's summary of the three scopal construals in Section 7.2 has the labels of the
  first two interchanged relative to (146) and (148); the theorems follow (146) and (148).
* Section 8's fact that *in*-adverbials lack the universal perfect, (153), is not derived.

## References

* [iatridou-zeijlstra-2021]
* [iatridou-anagnostopoulou-izvorski-2001]
* [chierchia-2013]
-/

namespace IatridouZeijlstra2021

open Aspect NonemptyInterval Tense.TemporalAdverbials

variable {W T : Type*} [LinearOrder T]

/-! ### Subdomain alternatives and exhaustification -/

/-- A span schema: a claim about a time span for any event predicate and world. -/
abbrev Schema (W T : Type*) [LinearOrder T] := (W → Event T → Prop) → IntervalPred W T

/-- The schema at `τ` entails its alternative at `τ'` when it holds at `τ'` in every model in
which it holds at `τ`. -/
def Entails (Φ : Schema W T) (τ τ' : NonemptyInterval T) : Prop := ∀ P w, Φ P w τ → Φ P w τ'

/-- Exhaustification over the subdomain alternatives of the span, (49b) and (127): the claim
together with the negation of every proper subinterval alternative it does not entail
([chierchia-2013]). -/
def Exh (Φ : Schema W T) (P : W → Event T → Prop) (w : W) (τ : NonemptyInterval T) : Prop :=
  Φ P w τ ∧ ∀ τ' < τ, ¬ Entails Φ τ τ' → ¬ Φ P w τ'

variable {Φ : Schema W T} {P : W → Event T → Prop} {w : W} {τ τ' : NonemptyInterval T}

/-- Exhaustification is vacuous for a schema that entails its subinterval alternatives. -/
theorem exh_of_antitone (h : ∀ P w τ τ', τ' ≤ τ → Φ P w τ → Φ P w τ') :
    Exh Φ P w τ ↔ Φ P w τ :=
  ⟨And.left, λ hφ => ⟨hφ, λ _ hτ' hne => absurd (λ P w => h P w _ _ hτ'.le) hne⟩⟩

/-! ### The perfect of the perfective and the NPI-hood of *in years*

The assertion of a perfect of the perfective, (14e) and (49a), is `Aspect.PRFV`: some event's
runtime is inside the span. Its subinterval alternatives are stronger and not entailed, so
exhaustification negates them all; the event would have to fill the span exactly, which a
culminated event shorter than weeks cannot, (44) and (49). Under negation, (50), every
alternative is weaker and exhaustification is vacuous. -/

/-- An event inside a subinterval is inside the span, (49). -/
theorem prfv_mono (h : τ' ≤ τ) : PRFV P w τ' → PRFV P w τ :=
  λ ⟨e, he, hP⟩ => ⟨e, he.trans h, hP⟩

/-- The event claim at a span does not entail it at a proper subinterval. -/
theorem not_entails_prfv [Nonempty W] (h : τ' < τ) : ¬ Entails (PRFV : Schema W T) τ τ' :=
  λ hent =>
  let ⟨_, he, heq⟩ :=
    hent (λ _ e => e.τ = τ) (Classical.arbitrary W) ⟨⟨τ, .action⟩, le_rfl, rfl⟩
  absurd (heq ▸ he : τ ≤ τ') (not_le_of_gt h)

/-- Exhaustifying the positive event claim negates every proper subinterval alternative: the
event must fill the span. -/
theorem exh_prfv_iff [Nonempty W] :
    Exh PRFV P w τ ↔ (∃ e, e.τ = τ ∧ P w e) ∧ ∀ τ' < τ, ¬ PRFV P w τ' := by
  constructor
  · rintro ⟨⟨e, he, hP⟩, hex⟩
    have hex' : ∀ τ' < τ, ¬ PRFV P w τ' := λ τ' hτ' => hex τ' hτ' (not_entails_prfv hτ')
    exact ⟨⟨e, eq_of_le_of_not_lt he (λ hlt => hex' _ hlt ⟨e, le_rfl, hP⟩), hP⟩, hex'⟩
  · rintro ⟨⟨e, rfl, hP⟩, hex⟩
    exact ⟨⟨e, le_rfl, hP⟩, λ τ' hτ' _ => hex τ' hτ'⟩

/-- (44), (49): where every relevant event is shorter than the span, the exhaustified positive
claim is contradictory, so *in years* is an NPI; (152b) and the presupposition of (180) are
instances. -/
theorem not_exh_prfv [Nonempty W] (hshort : ∀ e, P w e → e.τ ≠ τ) : ¬ Exh PRFV P w τ :=
  λ h => let ⟨⟨e, he, hP⟩, _⟩ := exh_prfv_iff.1 h; hshort e hP he

/-- (50): under negation exhaustification is vacuous. -/
theorem exh_not_prfv_iff : Exh (λ P w τ => ¬ PRFV P w τ) P w τ ↔ ¬ PRFV P w τ :=
  exh_of_antitone λ _ _ _ _ h hn hp => hn (prfv_mono h hp)

/-! ### Domain widening: the actuality and beyond expectation inferences

A boundary adverbial sets one boundary of its span, Tense or the argument of *until* fixing
the other (`fixed`). A domain widener stretches its boundary as far as is logically possible:
the span is event-free and every wider span with the same fixed boundary contains an event
(`Widened`, Section 4). The event that bounds the widening is the actuality inference, at the
boundary and not cancelable, Constant's observation; the span's containing every event-free
alternative is the beyond expectation inference. *In years* widens leftward from the right
boundary, *until* rightward from the left boundary (Section 6). -/

/-- The boundary that is fixed for the adverbial: the right boundary of a perfect time span,
set by Tense, (14b), or the left boundary of an until time span, set contextually. -/
def fixed : IatridouEtAl2001.BoundaryKind → T → PTSConstraint T
  | .right, t => (RB · t)
  | .left, t => LB t

/-- Spans sharing a fixed boundary are comparable. -/
theorem fixed_le_or_le {b : IatridouEtAl2001.BoundaryKind} {t : T} {τ₁ τ₂ : NonemptyInterval T}
    (h₁ : fixed b t τ₁) (h₂ : fixed b t τ₂) : τ₁ ≤ τ₂ ∨ τ₂ ≤ τ₁ := by
  cases b
  · rcases le_total τ₁.snd τ₂.snd with h | h
    · exact Or.inl (le_def.2 ⟨(h₂.trans h₁.symm).le, h⟩)
    · exact Or.inr (le_def.2 ⟨(h₁.trans h₂.symm).le, h⟩)
  · rcases le_total τ₂.fst τ₁.fst with h | h
    · exact Or.inl (le_def.2 ⟨h, (h₁.trans h₂.symm).le⟩)
    · exact Or.inr (le_def.2 ⟨h, (h₂.trans h₁.symm).le⟩)

/-- A domain-widening boundary adverbial's span: event-free, with the other boundary fixed at
`t`, and every wider such span contains an event. -/
def Widened (b : IatridouEtAl2001.BoundaryKind) (t : T) (P : W → Event T → Prop) (w : W)
    (τ : NonemptyInterval T) : Prop :=
  fixed b t τ ∧ ¬ PRFV P w τ ∧ ∀ τ', fixed b t τ' → τ < τ' → PRFV P w τ'

variable {b : IatridouEtAl2001.BoundaryKind} {t : T}

/-- The actuality inference at the boundary: every wider span with the same fixed boundary
contains an event that the widened span does not. -/
theorem event_of_widened (h : Widened b t P w τ) (hτ' : fixed b t τ') (hlt : τ < τ') :
    ∃ e, P w e ∧ e.τ ≤ τ' ∧ ¬ e.τ ≤ τ :=
  let ⟨e, he, hP⟩ := h.2.2 τ' hτ' hlt
  ⟨e, hP, he, λ hle => h.2.1 ⟨e, hle, hP⟩⟩

/-- Constant's observation: the actuality inference of a domain widener is not cancelable, a
relevant event existing whenever the span could be widened at all, (22) and (26). -/
theorem exists_event_of_widened (h : Widened b t P w τ) (hw : ∃ τ', fixed b t τ' ∧ τ < τ') :
    ∃ e, P w e :=
  let ⟨_, hτ', hlt⟩ := hw
  let ⟨e, hP, _⟩ := event_of_widened h hτ' hlt
  ⟨e, hP⟩

/-- The beyond expectation inference: the widened span contains every event-free span with
the same fixed boundary, so the boundary lies beyond any contextual alternative, (31)–(33)
and (119)–(122). -/
theorem le_of_widened (h : Widened b t P w τ) {τc : NonemptyInterval T} (hc : fixed b t τc)
    (hfree : ¬ PRFV P w τc) : τc ≤ τ := by
  rcases fixed_le_or_le hc h.1 with hle | hle
  · exact hle
  · rcases hle.lt_or_eq with hlt | heq
    · exact absurd (h.2.2 τc hc hlt) hfree
    · exact heq.symm.le

/-- *In years*: the last event lies at the left boundary of the widened perfect time span,
(51): however close to the boundary one looks, an event starts there, (23)–(24). -/
theorem event_near_lb (h : Widened .right t P w τ) {s : T} (hs : s < τ.fst) :
    ∃ e, P w e ∧ s ≤ e.τ.fst ∧ e.τ.fst < τ.fst := by
  have hτ' : fixed .right t ⟨(s, τ.snd), hs.le.trans τ.fst_le_snd⟩ := h.1
  obtain ⟨e, hP, he, hne⟩ := event_of_widened h hτ'
    (lt_of_le_of_ne (le_def.2 ⟨hs.le, le_rfl⟩) λ heq => hs.ne' (congrArg (·.fst) heq))
  exact ⟨e, hP, (le_def.1 he).1, lt_of_not_ge λ hge => hne (le_def.2 ⟨hge, (le_def.1 he).2⟩)⟩

/-- *Until*: the event lies at the right boundary of the widened until time span, (123). -/
theorem event_near_rb (h : Widened .left t P w τ) {s : T} (hs : τ.snd < s) :
    ∃ e, P w e ∧ e.τ.snd ≤ s ∧ τ.snd < e.τ.snd := by
  have hτ' : fixed .left t ⟨(τ.fst, s), τ.fst_le_snd.trans hs.le⟩ := h.1
  obtain ⟨e, hP, he, hne⟩ := event_of_widened h hτ'
    (lt_of_le_of_ne (le_def.2 ⟨le_rfl, hs.le⟩) λ heq => hs.ne (congrArg (·.snd) heq))
  exact ⟨e, hP, (le_def.1 he).2, lt_of_not_ge λ hge => hne (le_def.2 ⟨(le_def.1 he).1, hge⟩)⟩

/-- A boundary adverbial that fixes its own boundary, *in (the last) 5 years* or *since 2015*
setting the left boundary at `s` (`forDurationFrom`, `everSince`), leaves the actuality
inference cancelable: the negated perfect holds in a model with no relevant event at all,
(11)–(12) and (23). -/
theorem cancelable_of_forDurationFrom (s : T) (hs : s ≤ t) :
    ∃ P : W → Event T → Prop, ∃ τ, forDurationFrom s τ ∧ RB τ t ∧ ¬ PRFV P w τ ∧ ∀ e, ¬ P w e :=
  ⟨λ _ _ => False, ⟨(s, t), hs⟩, rfl, rfl, λ ⟨_, _, h⟩ => h, λ _ => id⟩

/-! ### *Until* with an imperfective predicate

The predicate holds throughout the until time span, (137): `Aspect.UNBOUNDED`, the span inside
the event's runtime. Every subinterval alternative is then entailed and exhaustification is
vacuous, for the affirmative (148a) as for the throughout-not reading with the negated event
(148c1) and the not-throughout reading with negation above the exhaustifier (148c2). The
remaining construal, exhaustifying the not-throughout claim (148b), makes every proper
subinterval a throughout, (142), which is contradictory once overlapping events sum. -/

/-- The predicate holding throughout a span holds throughout its subintervals. -/
theorem unbounded_anti (h : τ' ≤ τ) : UNBOUNDED P w τ → UNBOUNDED P w τ' :=
  λ ⟨e, he, hP⟩ => ⟨e, h.trans he, hP⟩

/-- (137), (139) and (141): exhaustifying the throughout claim is vacuous. -/
theorem exh_unbounded_iff : Exh UNBOUNDED P w τ ↔ UNBOUNDED P w τ :=
  exh_of_antitone λ _ _ _ _ h => unbounded_anti h

/-- (142): the proper subinterval alternatives of the not-throughout claim are stronger and
not entailed. -/
theorem not_entails_not_unbounded [Nonempty W] (h : τ' < τ) :
    ¬ Entails (λ P w τ => ¬ UNBOUNDED P w τ : Schema W T) τ τ' := λ hent =>
  hent (λ _ e => e.τ = τ') (Classical.arbitrary W)
    (λ ⟨_, he, heq⟩ => absurd (heq ▸ he : τ ≤ τ') (not_le_of_gt h)) ⟨⟨τ', .action⟩, le_rfl, rfl⟩

/-- Exhaustifying the not-throughout claim makes the predicate hold throughout every proper
subinterval. -/
theorem exh_not_unbounded_iff [Nonempty W] :
    Exh (λ P w τ => ¬ UNBOUNDED P w τ) P w τ ↔ ¬ UNBOUNDED P w τ ∧ ∀ τ' < τ, UNBOUNDED P w τ' :=
  ⟨λ ⟨h, hex⟩ => ⟨h, λ τ' hτ' => not_not.1 (hex τ' hτ' (not_entails_not_unbounded hτ'))⟩,
    λ ⟨h, hall⟩ => ⟨h, λ τ' hτ' _ => not_not.2 (hall τ' hτ')⟩⟩

/-- Where overlapping events sum to an event and the span has an interior point, a predicate
holding throughout every proper subinterval holds throughout the span. -/
theorem unbounded_of_forall_lt [DenselyOrdered T]
    (hsum : ∀ e₁ e₂, P w e₁ → P w e₂ → e₁.τ.overlaps e₂.τ →
      ∃ e, P w e ∧ e₁.τ ≤ e.τ ∧ e₂.τ ≤ e.τ)
    (hτ : τ.fst < τ.snd) (h : ∀ τ' < τ, UNBOUNDED P w τ') : UNBOUNDED P w τ := by
  obtain ⟨m, hm₁, hm₂⟩ := exists_between hτ
  obtain ⟨e₁, he₁, hP₁⟩ := h ⟨(τ.fst, m), hm₁.le⟩
    (lt_of_le_of_ne (le_def.2 ⟨le_rfl, hm₂.le⟩) λ heq => hm₂.ne (congrArg (·.snd) heq))
  obtain ⟨e₂, he₂, hP₂⟩ := h ⟨(m, τ.snd), hm₂.le⟩
    (lt_of_le_of_ne (le_def.2 ⟨hm₁.le, le_rfl⟩) λ heq => hm₁.ne' (congrArg (·.fst) heq))
  obtain ⟨he₁f, he₁s⟩ := le_def.1 he₁
  obtain ⟨he₂f, he₂s⟩ := le_def.1 he₂
  obtain ⟨e, hP, h₁, h₂⟩ := hsum e₁ e₂ hP₁ hP₂
    ⟨(he₁f.trans hm₁.le).trans (hm₂.le.trans he₂s), he₂f.trans he₁s⟩
  exact ⟨e, le_def.2 ⟨(le_def.1 h₁).1.trans he₁f, he₂s.trans (le_def.1 h₂).2⟩, hP⟩

/-- (148b) with an imperfective predicate is ruled out: exhaustifying the not-throughout claim
is contradictory. -/
theorem not_exh_not_unbounded [Nonempty W] [DenselyOrdered T]
    (hsum : ∀ e₁ e₂, P w e₁ → P w e₂ → e₁.τ.overlaps e₂.τ →
      ∃ e, P w e ∧ e₁.τ ≤ e.τ ∧ e₂.τ ≤ e.τ)
    (hτ : τ.fst < τ.snd) : ¬ Exh (λ P w τ => ¬ UNBOUNDED P w τ) P w τ := λ h =>
  let ⟨hn, hall⟩ := exh_not_unbounded_iff.1 h
  hn (unbounded_of_forall_lt hsum hτ hall)

/-! ### *Until* with a perfective predicate

With a perfective predicate, (126)–(132), the positive claim exhaustified is contradictory
(`not_exh_prfv`), which excludes the affirmative (128) and the construals exhaustifying below
negation, (146b), or exhaustifying the negated event inside the span, (146a) with the negated
predicate in `not_exh_prfv`; exhaustifying the negated claim, (148b), is vacuous
(`exh_not_prfv_iff`), the construal the literature calls *until-p*, with the noncancelable
actuality inference and beyond expectation inference of its widened span (`event_near_rb`,
`le_of_widened`). -/

/-- (148b): the negated perfective claim survives exhaustification, and its widened until time
span has an event at its right boundary. -/
theorem untilP (h : Widened .left t P w τ) :
    Exh (λ P w τ => ¬ PRFV P w τ) P w τ ∧ ∀ s, τ.snd < s → ∃ e, P w e ∧ τ.snd < e.τ.snd :=
  ⟨exh_not_prfv_iff.2 h.2.1, λ _ hs => let ⟨e, hP, _, h⟩ := event_near_rb h hs; ⟨e, hP, h⟩⟩

end IatridouZeijlstra2021
