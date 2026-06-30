import Linglib.Semantics.Presupposition.Basic

/-!
# Two-dimensional semantics for conventional implicatures
[potts-2005] [wang-2025]

Following [potts-2005], a `TwoDimProp` splits a meaning into two independent predicates over
worlds: **at-issue** content (truth-conditional, composes normally) and **conventional
implicature** content (use-conditional, projecting to the root). CIs project through the
truth-functional connectives and are blocked only by pure quotation ([kirk-giannini-2024];
see `pureQuote`).

The at-issue tier carries the Heyting algebra of `W → Prop` (`ᶜ`/`⊓`/`⊔`/`⇨`); the CI tier
always takes the meet `⊓` — CIs conjoin through every connective rather than tracking the
at-issue operation — and `ciStrongerThan` is the strict order `<` on that tier. `ciLift`
([wang-2025]) bridges `Semantics.Presupposition.PartialProp` into this type.

## Main definitions

* `TwoDimProp` — a two-dimensional meaning (at-issue and CI predicates over worlds).
* `neg`, `and`, `or`, `imp` — the connectives (at-issue Heyting op, CI meet).
* `SecondaryMeaningProperties` — the [potts-2007] expressive diagnostics, plus two fields
  distinguishing outlook markers ([kubota-2026]).

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


/--
Create a proposition with no CI content.

Most ordinary expressions have trivial CI content (always satisfied).
-/
def ofAtIssue (p : W → Prop) : TwoDimProp W :=
  { atIssue := p, ci := λ _ => True }

/--
Create a pure CI (no at-issue contribution).

Some expressions ONLY contribute CI content.
Example: "damn" in "the damn dog" doesn't change truth conditions.
-/
def pureCI (c : W → Prop) : TwoDimProp W :=
  { atIssue := λ _ => True, ci := c }

/--
Combine at-issue content with CI content.
-/
def withCI (p : W → Prop) (c : W → Prop) : TwoDimProp W :=
  { atIssue := p, ci := c }

/-- `withCI` projects to its at-issue argument. -/
@[simp] theorem withCI_atIssue (p c : W → Prop) :
    (withCI p c).atIssue = p := rfl

/-- `withCI` projects to its CI argument. -/
@[simp] theorem withCI_ci (p c : W → Prop) :
    (withCI p c).ci = c := rfl

/--
Pure quotation: strips CI content, preserving only at-issue content.

When an expression is purely quoted, its CI content (expressives, slurs,
NRRCs) does not project. The quoted material is "frozen" — its peripheral
content is blocked from passing up the tree.

This operation is the semantic reflex of pure quotation blocking peripheral
content passage ([kirk-giannini-2024], Appendix Remark 6).

Example: In "He said 'that bastard Jones left'", the expressive
'bastard' is inside pure quotation and does not project to the speaker.
-/
def pureQuote (p : TwoDimProp W) : TwoDimProp W :=
  { atIssue := p.atIssue, ci := λ _ => True }

/-- Pure quotation neutralizes CI content. -/
@[simp] theorem pureQuote_strips_ci (p : TwoDimProp W) (w : W) :
    (pureQuote p).ci w := trivial

/-- Pure quotation preserves at-issue content. -/
@[simp] theorem pureQuote_preserves_atIssue (p : TwoDimProp W) :
    (pureQuote p).atIssue = p.atIssue := rfl

/--
Pure quotation with strip witness.

`pureQuote` is information-losing — once the CI is flattened to `λ _ => True`,
the original CI cannot be recovered from the result alone. `PureQuoted` records
both the stripped result AND the original, so downstream operators (in
particular `MQContext.applyMQ` for the strip-then-mix pattern of
[kirk-giannini-2024] §3) can refer to what was discarded.

This is the substrate K-G's CI-projection-failure theorems need: rather than
proving `(pureQuote p).ci w := trivial` (which is vacuously true regardless
of input), they can compare the stripped output against the recorded original.
-/
structure PureQuoted (W : Type*) where
  /-- The stripped output: at-issue preserved, CI flattened. -/
  result : TwoDimProp W
  /-- The original input, retained for downstream comparison. -/
  original : TwoDimProp W
  /-- The result is the original with CI stripped via `pureQuote`. -/
  is_strip : result = pureQuote original

/--
Build a `PureQuoted` witness from an input proposition.

Bundles the existing `pureQuote p` with a record of the original `p` and a
trivial proof of the strip relation.
-/
def pureQuoteRich (p : TwoDimProp W) : PureQuoted W :=
  { result := pureQuote p, original := p, is_strip := rfl }

@[simp] theorem pureQuoteRich_result (p : TwoDimProp W) :
    (pureQuoteRich p).result = pureQuote p := rfl

@[simp] theorem pureQuoteRich_original (p : TwoDimProp W) :
    (pureQuoteRich p).original = p := rfl

/-- The rich operator preserves at-issue between original and result. -/
theorem pureQuoteRich_atIssue_preserved (p : TwoDimProp W) :
    (pureQuoteRich p).result.atIssue = (pureQuoteRich p).original.atIssue := by
  simp

/-- The rich operator strips the original CI: result.ci is constantly True. -/
theorem pureQuoteRich_ci_stripped (p : TwoDimProp W) (w : W) :
    (pureQuoteRich p).result.ci w := by simp

/--
**Pure quotation is information-losing.**

Two propositions with identical at-issue content but different CI dimensions
produce identical results under `pureQuote`. This is the substantive
non-trivial fact about the operator: the original CI is unrecoverable from the
result. Constructive witness: `λ _ => True` and `λ _ => False` for the CI
dimension, with at-issue trivial — `pureQuote` collapses both to the same
`{ atIssue := True, ci := True }`.

This theorem is what `quotation_blocks_ci_projection` should be, instead of
the vacuous `:= trivial`. After `pureQuote`, no CI information remains; any
downstream peripheral content must be re-introduced (by `applyMQ`'s `R`).
-/
theorem pureQuote_loses_ci_info :
    ∃ (p₁ p₂ : TwoDimProp Unit), p₁.ci ≠ p₂.ci ∧ pureQuote p₁ = pureQuote p₂ := by
  refine ⟨⟨λ _ => True, λ _ => True⟩, ⟨λ _ => True, λ _ => False⟩, ?_, rfl⟩
  intro h; simpa using congrFun h ()


/-! ### Connectives

Both dimensions are `W → Prop`, so each connective is built from that type's order
structure: the **at-issue** tier carries the full Heyting algebra (`ᶜ`, `⊓`, `⊔`, `⇨`), while
the **CI** tier always takes the meet `⊓` — CIs project by conjunction through every
connective rather than tracking the at-issue operation. -/

/--
Negation: negates at-issue content; CI projects unchanged.

"John didn't see that bastard Pete"
- atIssue: ¬(John saw Pete)
- ci: Speaker thinks Pete is a bastard (unchanged)

This distinguishes CIs from presuppositions.
-/
def neg (p : TwoDimProp W) : TwoDimProp W :=
  { p with atIssue := p.atIssueᶜ }  -- at-issue complemented; CI projects unchanged

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

/--
Properties of secondary (non-at-issue) meaning expressions.

Extends [potts-2007]'s six expressive diagnostics with two additional
properties needed to distinguish outlook markers ([kubota-2026]) from
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
  deriving Repr, DecidableEq

/--
Expressives satisfy all six [potts-2007] properties and do NOT typically
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
def comma (pred : W → Prop) (entity : W → Prop) : TwoDimProp W :=
  { atIssue := entity  -- Entity denotation passes through
  , ci := pred }       -- Predicate becomes CI content

/--
Supplementary adverb application.

"Luckily, John won" = John won + CI(speaker considers it lucky)

Formally: comma₂ : ⟨⟨tᵃ,tᵃ⟩, ⟨tᵃ,tᶜ⟩⟩
-/
def supplementaryAdverb
    (adverbMeaning : (W → Prop) → (W → Prop))  -- The adverb's at-issue meaning
    (prop : W → Prop) : TwoDimProp W :=
  { atIssue := prop              -- Base proposition unchanged
  , ci := adverbMeaning prop }   -- Adverb meaning becomes CI


/--
CI informativeness ordering: `φ` has a stronger CI than `ψ` when `φ`'s CI strictly entails
`ψ`'s — i.e. `φ.ci < ψ.ci` in the pointwise entailment order that `W → Prop` inherits from
`Prop`. Concretely, `φ.ci` implies `ψ.ci` at every world, but some world satisfies `ψ.ci`
and not `φ.ci`.

Example:
- "That bastard John" is CI-stronger than "John"
- "That fucking bastard John" is CI-stronger than "That bastard John"
-/
def ciStrongerThan (φ ψ : TwoDimProp W) : Prop := φ.ci < ψ.ci

/-- CI equivalence: same CI content. -/
def ciEquiv (φ ψ : TwoDimProp W) : Prop := φ.ci = ψ.ci

/-- CI-stronger-than is irreflexive (the strict entailment order on `W → Prop`). -/
theorem ciStrongerThan_irrefl (φ : TwoDimProp W) : ¬ ciStrongerThan φ φ := lt_irrefl _

/-- CI-stronger-than is transitive. -/
theorem ciStrongerThan_trans {φ ψ χ : TwoDimProp W}
    (h1 : ciStrongerThan φ ψ) (h2 : ciStrongerThan ψ χ) : ciStrongerThan φ χ := lt_trans h1 h2

/-- CI-stronger-than is asymmetric. -/
theorem ciStrongerThan_asymm {φ ψ : TwoDimProp W}
    (h : ciStrongerThan φ ψ) : ¬ ciStrongerThan ψ φ := lt_asymm h


/-!
## CI Lift: Presupposition → Two-Dimensional Meaning ([wang-2025])

[wang-2025] analyze de re presupposition by bifurcating a [gutzmann-2015]
presuppositional meaning into two dimensions using [potts-2005]'s CI type system:

- **At-issue**: the assertion component (identity function on the propositional content)
- **CI**: the presupposition (projects to root, evaluated against CommonGround)

This derives de re readings: when a presuppositional expression appears under
an attitude verb, the presupposition can be evaluated against the common ground
(CommonGround) rather than the attitude holder's beliefs, because it projects as CI content.

### Bridge: PartialProp ↔ TwoDimProp

This provides a new cross-module connection between:
- `Semantics.Presupposition.PartialProp` (presupposition + assertion)
- `Pragmatics.Expressives.TwoDimProp` (at-issue + CI)

-/

/--
CI lift: type-shift a presupposition/assertion pair into a
two-dimensional meaning.

The presupposition becomes CI content (projects universally), while the
assertion becomes at-issue content (composes truth-functionally).

This is the ⟦CI⟧ operator from [wang-2025].
-/
def ciLift (presup assertion : W → Prop) : TwoDimProp W :=
  { atIssue := assertion
  , ci := presup }

/--
CI lift preserves the assertion as at-issue content.
-/
theorem ciLift_atIssue (presup assertion : W → Prop) :
    (ciLift presup assertion).atIssue = assertion := rfl

/--
CI lift maps presupposition to CI dimension.
-/
theorem ciLift_ci (presup assertion : W → Prop) :
    (ciLift presup assertion).ci = presup := rfl

/--
De re reading: when CommonGround entails the presupposition, the CI dimension is satisfied
at all CommonGround worlds. This means the presupposition is resolved against the CommonGround
regardless of what is embedded under an attitude verb.
-/
theorem deRe_from_ciLift (presup : W → Prop)
    (assertion : W → Prop)
    (cg : W → Prop)
    (h : ∀ w, cg w → presup w) :
    ∀ w, cg w → (ciLift presup assertion).ci w :=
  h

/--
CI lift composes with negation: negating a CI-lifted meaning negates the
at-issue content but preserves the presupposition (as CI).

This matches both Potts' CI projection and standard presupposition projection
through negation.
-/
theorem ciLift_neg_preserves_presup (presup assertion : W → Prop) :
    (TwoDimProp.neg (ciLift presup assertion)).ci = presup := rfl

/--
Round-trip: CI lift then extract components recovers the original predicates.
-/
theorem ciLift_roundtrip (presup assertion : W → Prop) :
    (ciLift presup assertion).ci = presup ∧
    (ciLift presup assertion).atIssue = assertion :=
  ⟨rfl, rfl⟩

end Pragmatics.Expressives
