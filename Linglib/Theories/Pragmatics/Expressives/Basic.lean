/-
# Two-Dimensional Semantics for Conventional Implicatures
@cite{potts-2005} @cite{wang-2025}

Formalization of @cite{potts-2005} "The Logic of Conventional Implicatures" (LCI).

## Insight

Natural language meanings have TWO dimensions:
1. **At-issue content**: Truth-conditional, composes normally
2. **CI content**: Use-conditional, "floats up" to root

These dimensions are INDEPENDENT:
- CIs don't affect truth conditions
- CIs project through truth-functional operators (negation, conditionals, etc.)
- Exception: quotation blocks CI projection (@cite{kirk-giannini-2024} §3;
  @cite{potts-2005} also acknowledges this). See `pureQuote`.

## The LCI Type System

Potts uses superscripts to track dimensions:
- τᵃ: at-issue type
- τᶜ: CI type
- ⟨σᵃ, τᶜ⟩: CI-functor (takes at-issue, returns CI)

Key CI expressions:
- Expressives: ⟦bastard⟧ : ⟨eᵃ, tᶜ⟩
- Appositives: via comma feature
- Supplementary adverbs: ⟦luckily⟧ : ⟨tᵃ, tᶜ⟩

-/

import Linglib.Core.Semantics.Proposition
import Linglib.Core.Semantics.Presupposition

namespace Pragmatics.Expressives

open Core.Proposition


/--
A two-dimensional meaning following @cite{potts-2005}.

The key insight: linguistic expressions contribute to TWO independent
dimensions of meaning that compose by different rules.

- `atIssue`: Truth-conditional content (what is said)
- `ci`: Conventional implicature (use-conditional content)

Example: "That bastard John is late"
- atIssue: John is late
- ci: Speaker has negative attitude toward John
-/
structure TwoDimProp (W : Type*) where
  /-- At-issue (truth-conditional) content -/
  atIssue : W → Bool
  /-- Conventional implicature (use-conditional) content -/
  ci : W → Bool

namespace TwoDimProp

variable {W : Type*}


/--
Create a proposition with no CI content.

Most ordinary expressions have trivial CI content (always satisfied).
-/
def ofAtIssue (p : (W → Bool)) : TwoDimProp W :=
  { atIssue := p, ci := λ _ => true }

/--
Create a pure CI (no at-issue contribution).

Some expressions ONLY contribute CI content.
Example: "damn" in "the damn dog" doesn't change truth conditions.
-/
def pureCI (c : (W → Bool)) : TwoDimProp W :=
  { atIssue := λ _ => true, ci := c }

/--
Combine at-issue content with CI content.
-/
def withCI (p : (W → Bool)) (c : (W → Bool)) : TwoDimProp W :=
  { atIssue := p, ci := c }

/--
Pure quotation: strips CI content, preserving only at-issue content.

When an expression is purely quoted, its CI content (expressives, slurs,
NRRCs) does not project. The quoted material is "frozen" — its peripheral
content is blocked from passing up the tree.

This operation is the semantic reflex of pure quotation blocking peripheral
content passage (@cite{kirk-giannini-2024}, Appendix Remark 6).

Example: In "He said 'that bastard Jones left'", the expressive
'bastard' is inside pure quotation and does not project to the speaker.
-/
def pureQuote (p : TwoDimProp W) : TwoDimProp W :=
  { atIssue := p.atIssue, ci := λ _ => true }

/-- Pure quotation neutralizes CI content. -/
theorem pureQuote_strips_ci (p : TwoDimProp W) (w : W) :
    (pureQuote p).ci w = true := rfl

/-- Pure quotation preserves at-issue content. -/
theorem pureQuote_preserves_atIssue (p : TwoDimProp W) :
    (pureQuote p).atIssue = p.atIssue := rfl


/--
Negation: negates at-issue content; CI projects unchanged.

"John didn't see that bastard Pete"
- atIssue: ¬(John saw Pete)
- ci: Speaker thinks Pete is a bastard (unchanged)

This distinguishes CIs from presuppositions.
-/
def neg (p : TwoDimProp W) : TwoDimProp W :=
  { atIssue := λ w => !p.atIssue w
  , ci := p.ci }  -- CI projects through negation

/--
Conjunction: at-issue content conjoins; both CIs project.

"That bastard John met that jerk Pete"
- atIssue: John met Pete
- ci: Speaker thinks John is bastard and Pete is jerk
-/
def and (p q : TwoDimProp W) : TwoDimProp W :=
  { atIssue := λ w => p.atIssue w && q.atIssue w
  , ci := λ w => p.ci w && q.ci w }  -- Both CIs project

/--
Disjunction: at-issue content disjoins; both CIs project.

CIs project through disjunction rather than being disjoined.
-/
def or (p q : TwoDimProp W) : TwoDimProp W :=
  { atIssue := λ w => p.atIssue w || q.atIssue w
  , ci := λ w => p.ci w && q.ci w }  -- Both CIs project (conjunction, not disjunction)

/--
Implication: at-issue content forms conditional; both CIs project.

"If that bastard John calls, I'll leave"
- atIssue: John calls → I leave
- ci: Speaker thinks John is bastard (projects from antecedent)
-/
def imp (p q : TwoDimProp W) : TwoDimProp W :=
  { atIssue := λ w => !p.atIssue w || q.atIssue w
  , ci := λ w => p.ci w && q.ci w }  -- Both CIs project


/--
CI projects through negation.

Presuppositions can be filtered by antecedents; CIs cannot.
-/
theorem ci_projects_through_neg (p : TwoDimProp W) :
    (neg p).ci = p.ci := rfl

/--
CI projects through conditional antecedent.

Unlike presuppositions, CIs in the antecedent of a conditional
are not filtered; they project to the root.

"If the king of France is bald,..." - presupposes king exists (filtered)
"If that bastard calls,..." - CI projects (speaker thinks he's bastard)
-/
theorem ci_projects_from_antecedent (p q : TwoDimProp W) (w : W) :
    (imp p q).ci w = (p.ci w && q.ci w) := rfl

/--
Double negation preserves CI.

CIs are unaffected by truth-functional operators.
-/
theorem ci_double_neg (p : TwoDimProp W) :
    (neg (neg p)).ci = p.ci := rfl

/--
At-issue independence: CI content is independent of at-issue truth value.

The at-issue content can be true, false, or unknown; CI still holds.
-/
theorem ci_independent_of_atIssue (p : TwoDimProp W) (w : W)
    (h_ci : p.ci w = true) :
    -- CI holds regardless of at-issue value
    (p.atIssue w = true → p.ci w = true) ∧
    (p.atIssue w = false → p.ci w = true) := by
  exact ⟨λ _ => h_ci, λ _ => h_ci⟩

end TwoDimProp


/--
Properties of secondary (non-at-issue) meaning expressions.

Extends @cite{potts-2007}'s six expressive diagnostics with two additional
properties needed to distinguish outlook markers (@cite{kubota-2026}) from
pure expressives and pure presuppositions.
-/
structure SecondaryMeaningProperties where
  /-- CI contributes to a dimension separate from at-issue content -/
  independent : Bool
  /-- Predicates something of the utterance situation (not the described situation) -/
  nondisplaceable : Bool
  /-- Evaluated from a particular perspective (usually the speaker's) -/
  perspectiveDependent : Bool
  /-- Cannot be fully paraphrased by descriptive, non-expressive terms -/
  descriptivelyIneffable : Bool
  /-- Achieves its effect simply by being uttered (like a performative) -/
  immediate : Bool
  /-- Repetition strengthens rather than creating redundancy -/
  repeatable : Bool
  /-- Allows perspective shift to a non-speaker attitude holder under embedding -/
  allowsPerspectiveShift : Bool
  /-- Requires a salient issue/counterstance in prior discourse -/
  requiresDiscourseAntecedent : Bool
  deriving Repr

/--
Expressives satisfy all six @cite{potts-2007} properties and do NOT typically
allow perspective shift or require discourse antecedents.
-/
def expressiveProperties : SecondaryMeaningProperties :=
  { independent := true
  , nondisplaceable := true
  , perspectiveDependent := true
  , descriptivelyIneffable := true
  , immediate := true
  , repeatable := true       -- "damn damn damn" strengthens
  , allowsPerspectiveShift := false
  , requiresDiscourseAntecedent := false }

/--
Appositives share most expressive properties but are not repeatable
and ARE descriptively paraphrasable ("Laura, a doctor" → "Laura is a doctor").
-/
def appositiveProperties : SecondaryMeaningProperties :=
  { independent := true
  , nondisplaceable := true
  , perspectiveDependent := true
  , descriptivelyIneffable := false  -- "Laura, a doctor" ↔ "Laura is a doctor"
  , immediate := true
  , repeatable := false              -- "John, a doctor, a doctor" is odd
  , allowsPerspectiveShift := false
  , requiresDiscourseAntecedent := false }


/--
The comma feature type-shifts at-issue content to CI content.

This is Potts' mechanism for appositives:
- "Laura, a doctor, recommended aspirin"
- "a doctor" is at-issue predicate
- comma shifts it to CI: "Laura is a doctor" becomes CI content

Formally: comma : ⟨⟨eᵃ,tᵃ⟩, ⟨eᵃ,tᶜ⟩⟩
-/
def comma {W : Type*} (pred : W → Bool) (entity : W → Bool) : TwoDimProp W :=
  { atIssue := entity  -- Entity denotation passes through
  , ci := pred }       -- Predicate becomes CI content

/--
Supplementary adverb application.

"Luckily, John won" = John won + CI(speaker considers it lucky)

Formally: comma₂ : ⟨⟨tᵃ,tᵃ⟩, ⟨tᵃ,tᶜ⟩⟩
-/
def supplementaryAdverb {W : Type*}
    (adverbMeaning : (W → Bool) → (W → Bool))  -- The adverb's at-issue meaning
    (prop : (W → Bool)) : TwoDimProp W :=
  { atIssue := prop              -- Base proposition unchanged
  , ci := adverbMeaning prop }   -- Adverb meaning becomes CI


/--
CI informativeness ordering.

φ has stronger CI than ψ iff the contexts where φ is felicitous
are a proper subset of contexts where ψ is felicitous.

⟦φ⟧ᵘ ⊂ ⟦ψ⟧ᵘ

Example:
- "That bastard John" is CI-stronger than "John"
- "That fucking bastard John" is CI-stronger than "That bastard John"
-/
def ciStrongerThan {W : Type*} (φ ψ : TwoDimProp W) : Prop :=
  -- φ's CI entails ψ's CI (more restrictive)
  (∀ w, φ.ci w = true → ψ.ci w = true) ∧
  -- But not vice versa (strictly stronger)
  (∃ w, ψ.ci w = true ∧ φ.ci w = false)

/--
CI equivalence: same CI content.
-/
def ciEquiv {W : Type*} (φ ψ : TwoDimProp W) : Prop :=
  ∀ w, φ.ci w = ψ.ci w

/-- CI-stronger-than is irreflexive: no proposition is strictly CI-stronger than itself. -/
theorem ciStrongerThan_irrefl {W : Type*} (φ : TwoDimProp W) :
    ¬ ciStrongerThan φ φ :=
  fun ⟨_, _, hw, hw'⟩ => by simp [hw] at hw'

/-- CI-stronger-than is transitive. -/
theorem ciStrongerThan_trans {W : Type*} (φ ψ χ : TwoDimProp W)
    (h1 : ciStrongerThan φ ψ) (h2 : ciStrongerThan ψ χ) :
    ciStrongerThan φ χ := by
  obtain ⟨h2e, w, hwc, hwp⟩ := h2
  constructor
  · exact fun w h => h2e w (h1.1 w h)
  · refine ⟨w, hwc, ?_⟩
    cases hb : φ.ci w with
    | false => rfl
    | true => simp [h1.1 w hb] at hwp

/-- CI-stronger-than is asymmetric: if φ is CI-stronger than ψ, ψ is not CI-stronger than φ. -/
theorem ciStrongerThan_asymm {W : Type*} (φ ψ : TwoDimProp W)
    (h : ciStrongerThan φ ψ) : ¬ ciStrongerThan ψ φ := by
  obtain ⟨_, w, hwp, hwf⟩ := h
  intro ⟨he, _⟩
  simp [he w hwp] at hwf


-- ============================================================================
-- CI Bifurcation for De Re Presupposition (@cite{wang-2025})
-- ============================================================================

/-!
## CI Lift: Presupposition → Two-Dimensional Meaning

@cite{wang-2025} analyze de re presupposition by bifurcating a @cite{gutzmann-2015}
presuppositional meaning into two dimensions using @cite{potts-2005}'s CI type system:

- **At-issue**: the assertion component (identity function on the propositional content)
- **CI**: the presupposition (projects to root, evaluated against CG)

This derives de re readings: when a presuppositional expression appears under
an attitude verb, the presupposition can be evaluated against the common ground
(CG) rather than the attitude holder's beliefs, because it projects as CI content.

### Bridge: PrProp ↔ TwoDimProp

This provides a new cross-module connection between:
- `Core.Presupposition.PrProp` (presupposition + assertion)
- `Pragmatics.Expressives.TwoDimProp` (at-issue + CI)

-/

/--
CI lift: type-shift a Bool-valued presupposition/assertion pair into a
two-dimensional meaning.

The presupposition becomes CI content (projects universally), while the
assertion becomes at-issue content (composes truth-functionally).

This is the ⟦CI⟧ operator from @cite{wang-2025}.

Takes Bool functions directly because `TwoDimProp` is Bool-valued.
To lift a `PrProp` constructed via `PrProp.ofBool`, pass the original
Bool functions rather than the Prop-wrapped fields.
-/
def ciLift {W : Type*} (presupBool assertionBool : (W → Bool)) : TwoDimProp W :=
  { atIssue := assertionBool
  , ci := presupBool }

/--
CI lift preserves the assertion as at-issue content.
-/
theorem ciLift_atIssue {W : Type*} (presupBool assertionBool : (W → Bool)) :
    (ciLift presupBool assertionBool).atIssue = assertionBool := rfl

/--
CI lift maps presupposition to CI dimension.
-/
theorem ciLift_ci {W : Type*} (presupBool assertionBool : (W → Bool)) :
    (ciLift presupBool assertionBool).ci = presupBool := rfl

/--
De re reading: when CG entails the presupposition, the CI dimension is satisfied
at all CG worlds. This means the presupposition is resolved against the CG
regardless of what is embedded under an attitude verb.
-/
theorem deRe_from_ciLift {W : Type*} (presupBool : (W → Bool))
    (assertionBool : (W → Bool))
    (cg : (W → Bool))
    (h : ∀ w, cg w = true → presupBool w = true) :
    ∀ w, cg w = true → (ciLift presupBool assertionBool).ci w = true :=
  h

/--
CI lift composes with negation: negating a CI-lifted meaning negates the
at-issue content but preserves the presupposition (as CI).

This matches both Potts' CI projection and standard presupposition projection
through negation.
-/
theorem ciLift_neg_preserves_presup {W : Type*} (presupBool assertionBool : (W → Bool)) :
    (TwoDimProp.neg (ciLift presupBool assertionBool)).ci = presupBool := rfl

/--
Round-trip: CI lift then extract components recovers the original Bool functions.
-/
theorem ciLift_roundtrip {W : Type*} (presupBool assertionBool : (W → Bool)) :
    (ciLift presupBool assertionBool).ci = presupBool ∧
    (ciLift presupBool assertionBool).atIssue = assertionBool :=
  ⟨rfl, rfl⟩

end Pragmatics.Expressives
