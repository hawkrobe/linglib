import Linglib.Semantics.Presupposition.Basic

/-!
# Two-dimensional semantics for conventional implicatures
[potts-2005] [wang-2025]

Following [potts-2005], a `TwoDimProp` splits a meaning into two independent predicates over
worlds: **at-issue** content (truth-conditional, composes normally) and **conventional
implicature** content (use-conditional, projecting to the root). CIs project through the
truth-functional connectives and are blocked only by direct quotation ([potts-2007]; see
`pureQuote`, and `Semantics.Quotation.Mixed` for [kirk-giannini-2024]'s mixed quotation).

The at-issue tier carries the Heyting algebra of `W → Prop` (`ᶜ`/`⊓`/`⊔`/`⇨`); the CI tier
always takes the meet `⊓`. `TwoDimProp.ofPartialProp` bridges
`Semantics.Presupposition.PartialProp` into this type.

## Main definitions

* `TwoDimProp` — a two-dimensional meaning (at-issue and CI predicates over worlds).
* `neg`, `and`, `or`, `imp` — the connectives (at-issue Heyting op, CI meet).
* `SecondaryMeaningProperties` — the six [potts-2007] expressive diagnostics.

## References

[potts-2005] [potts-2007] [wang-2025] [kirk-giannini-2024]
-/

namespace Pragmatics.Expressives

/-- A two-dimensional meaning ([potts-2005]): two predicates over worlds, the at-issue
(truth-conditional) content `atIssue` and the conventional-implicature (use-conditional)
content `ci`. E.g. "that bastard John is late" has `atIssue` "John is late" and `ci` "the
speaker disdains John". -/
@[ext]
structure TwoDimProp (W : Type*) where
  /-- At-issue (truth-conditional) content. -/
  atIssue : W → Prop
  /-- Conventional-implicature (use-conditional) content. -/
  ci : W → Prop

namespace TwoDimProp

variable {W : Type*}

/-- Combine at-issue content with CI content. -/
@[simps] def withCI (p c : W → Prop) : TwoDimProp W := ⟨p, c⟩

/-- Pure quotation strips CI content to `⊤`, preserving only at-issue content: expressives
are nondisplaceable *outside of direct quotation* ([potts-2007]), so in "He said 'that
bastard Jones left'" the expressive is frozen inside the quotation and not attributed to
the speaker. [kirk-giannini-2024]'s *mixed* quotation (used and mentioned at once) is the
refinement in `Semantics.Quotation.Mixed`. -/
@[simps] def pureQuote (p : TwoDimProp W) : TwoDimProp W := ⟨p.atIssue, ⊤⟩

/-- Pure quotation is information-losing: two meanings with identical at-issue content but
different CI collapse to the same `pureQuote`, so the original CI is unrecoverable. -/
theorem pureQuote_loses_ci_info :
    ∃ (p₁ p₂ : TwoDimProp Unit), p₁.ci ≠ p₂.ci ∧ pureQuote p₁ = pureQuote p₂ := by
  refine ⟨⟨λ _ => True, λ _ => True⟩, ⟨λ _ => True, λ _ => False⟩, ?_, rfl⟩
  intro h; simpa using congrFun h ()

/-! ### Connectives

Both dimensions are `W → Prop`, so each connective is built from that type's order
structure: the **at-issue** tier carries the full Heyting algebra (`ᶜ`, `⊓`, `⊔`, `⇨`), while
the **CI** tier always takes the meet `⊓`. In [potts-2005]'s logic CIs do not compose via
connectives at all — they are split off and collected at the root, interpreted conjunctively;
the per-connective meet flattens that root collection into a compositional rule (the
projection predictions coincide). -/

/--
Negation: negates at-issue content; CI projects unchanged.

"John didn't see that bastard Pete"
- atIssue: ¬(John saw Pete)
- ci: Speaker thinks Pete is a bastard (unchanged)

This distinguishes CIs from presuppositions.
-/
def neg (p : TwoDimProp W) : TwoDimProp W :=
  { p with atIssue := p.atIssueᶜ }

/-- Negation flips the at-issue dimension. -/
@[simp] theorem neg_atIssue (p : TwoDimProp W) (w : W) :
    (neg p).atIssue w ↔ ¬ p.atIssue w := Iff.rfl

/--
Conjunction: at-issue content conjoins; both CIs project.

"That bastard John met that jerk Pete"
- atIssue: John met Pete
- ci: Speaker thinks John is bastard and Pete is jerk
-/
def and (p q : TwoDimProp W) : TwoDimProp W :=
  { atIssue := p.atIssue ⊓ q.atIssue, ci := p.ci ⊓ q.ci }

/-- Conjunction's at-issue dimension. -/
@[simp] theorem and_atIssue (p q : TwoDimProp W) (w : W) :
    (and p q).atIssue w ↔ p.atIssue w ∧ q.atIssue w := Iff.rfl

/-- Conjunction propagates both CIs. -/
@[simp] theorem and_ci (p q : TwoDimProp W) (w : W) :
    (and p q).ci w ↔ p.ci w ∧ q.ci w := Iff.rfl

/--
Disjunction: at-issue content disjoins; both CIs project.

CIs project through disjunction rather than being disjoined.
-/
def or (p q : TwoDimProp W) : TwoDimProp W :=
  { atIssue := p.atIssue ⊔ q.atIssue, ci := p.ci ⊓ q.ci }  -- at-issue joins; CIs still meet

/-- Disjunction's at-issue dimension. -/
@[simp] theorem or_atIssue (p q : TwoDimProp W) (w : W) :
    (or p q).atIssue w ↔ p.atIssue w ∨ q.atIssue w := Iff.rfl

/-- Disjunction propagates both CIs. -/
@[simp] theorem or_ci (p q : TwoDimProp W) (w : W) :
    (or p q).ci w ↔ p.ci w ∧ q.ci w := Iff.rfl

/--
Implication: at-issue content forms conditional; both CIs project.

"If that bastard John calls, I'll leave"
- atIssue: John calls → I leave
- ci: Speaker thinks John is bastard (projects from antecedent)
-/
def imp (p q : TwoDimProp W) : TwoDimProp W :=
  { atIssue := p.atIssue ⇨ q.atIssue, ci := p.ci ⊓ q.ci }

/-- Implication's at-issue dimension. -/
@[simp] theorem imp_atIssue (p q : TwoDimProp W) (w : W) :
    (imp p q).atIssue w ↔ (p.atIssue w → q.atIssue w) := Iff.rfl

/--
CI projects through negation.

Presuppositions can be filtered by antecedents; CIs cannot.
-/
@[simp] theorem ci_projects_through_neg (p : TwoDimProp W) :
    (neg p).ci = p.ci := rfl

/--
CI projects through conditional antecedent.

Unlike presuppositions, CIs in the antecedent of a conditional
are not filtered; they project to the root.

"If the king of France is bald,..." - presupposes king exists (filtered)
"If that bastard calls,..." - CI projects (speaker thinks he's bastard)
-/
@[simp] theorem ci_projects_from_antecedent (p q : TwoDimProp W) (w : W) :
    (imp p q).ci w ↔ (p.ci w ∧ q.ci w) := Iff.rfl

end TwoDimProp

variable {W : Type*}

/-- The six expressive diagnostics of [potts-2007]: a yes/no fingerprint a class of
secondary-meaning items either matches or fails. -/
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
  deriving Repr, DecidableEq

/-- Expressives satisfy all six [potts-2007] diagnostics ("damn damn damn" strengthens).
Speaker orientation is the default, not an absolute: [potts-2007] adopts a shiftable
contextual judge, and [harris-potts-2009] document non-speaker-oriented readings even
unembedded. -/
def expressiveProperties : SecondaryMeaningProperties :=
  { independent := true
  , nondisplaceable := true
  , perspectiveDependent := true
  , descriptivelyIneffable := true
  , immediate := true
  , repeatable := true }

/-- Appositives (supplements) share independence and perspective dependence with expressives
but fail the expressive-specific diagnostics ([potts-2007]): their content is ordinary
propositional material — displaceable ("Ed, then a first-year resident, ..."), paraphrasable
("Laura, a doctor" ↔ "Laura is a doctor"), not performative-like, not repeatable. -/
def appositiveProperties : SecondaryMeaningProperties :=
  { independent := true
  , nondisplaceable := false
  , perspectiveDependent := true
  , descriptivelyIneffable := false
  , immediate := false
  , repeatable := false }

/-- A presupposition/assertion pair as a two-dimensional meaning: the presupposition becomes
(universally projecting) CI content, the assertion at-issue content — [wang-2025]'s de re
analysis. Deliberately discards presupposition *filtering*: a CI-tier presupposition projects
through `and`/`imp` where a real presupposition would be filtered by its local context, which
is the point — the de re presupposition is evaluated against the common ground instead. -/
@[simps] def TwoDimProp.ofPartialProp (p : Semantics.Presupposition.PartialProp W) :
    TwoDimProp W := ⟨p.assertion, p.presup⟩

end Pragmatics.Expressives
