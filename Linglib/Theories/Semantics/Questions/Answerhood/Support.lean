import Linglib.Theories.Semantics.Questions.Answerhood.ProbabilisticAnswerhood

/-!
# Evidential Support
@cite{ippolito-kiss-williams-2025} @cite{thomas-2026}

Named abstraction over probabilistic answerhood primitives, factored out for
reuse across discourse particles that share the notion of "supporting an
answer to a QUD" — additive particles and discourse *only*.

## Two layers of SUPPORT

@cite{ippolito-kiss-williams-2025} Definition 13 decomposes SUPPORT into two
independent conditions:

1. **Doxastic**: the speaker believes some alternative q of the sentence's
   denotation (DOX_sp ⊆ q for some q ∈ ⟦S⟧)
2. **Probabilistic**: q provides evidence for answer r (P(r|q) > P(r))

The doxastic condition is what blocks canonical info-seeking questions as the
left argument of discourse *only*: the speaker doesn't believe any answer, so
DOX_sp ⊄ q for all q ∈ ⟦S⟧. Biased/rhetorical questions CAN satisfy the
doxastic condition because the speaker does believe an answer.

## Definitions (Set/Prop, mathlib-aligned)

- `probSupportsS` — probabilistic support: P(α|E) > P(α) (wraps `isPositiveEvidenceS`)
- `fullSupportS` — IKW Def. 13: doxastic + probabilistic
  (∃ q ∈ alt(sentDen), DOX_sp ⊆ q ∧ P(r|q) > P(r))
-/

namespace Semantics.Questions.Support

open Semantics.Questions.ProbabilisticAnswerhood

/-! ### Set/Prop API (mathlib-pure)

Wrappers over the Set/Prop primitives in `ProbabilisticAnswerhood`
(`isPositiveEvidenceS`, etc.) using `Core.Issue` for inquisitive denotations
and `Set W` (with `[DecidablePred (· ∈ s)]`) for evidence/answer arguments.
DOX-subset check uses native `Set.Subset`. -/

/-- Probabilistic support: `evidence` raises `P(answer)`. -/
def probSupportsS {W : Type*} [Fintype W]
    (prior : Prior W) (evidence answer : Set W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ answer)] : Prop :=
  isPositiveEvidenceS evidence answer prior

instance {W : Type*} [Fintype W] (prior : Prior W) (evidence answer : Set W)
    [DecidablePred (· ∈ evidence)] [DecidablePred (· ∈ answer)] :
    Decidable (probSupportsS prior evidence answer) :=
  inferInstanceAs (Decidable (isPositiveEvidenceS evidence answer prior))

open Classical in
/-- Full SUPPORT from @cite{ippolito-kiss-williams-2025} Def. 13.

`fullSupportS dox sentDen prior answer` holds iff some alternative `q` of
`sentDen` is doxastically endorsed (`dox ⊆ q`) AND probabilistically
supports `answer` (`P(answer | q) > P(answer)`).

Spec uses `Classical.dec` so we don't need `[∀ q, DecidablePred (· ∈ q)]`. -/
noncomputable def fullSupportS {W : Type*} [Fintype W]
    (dox : Set W) (sentDen : Core.Issue W) (prior : Prior W)
    (answer : Set W) : Prop :=
  ∃ q ∈ Core.Issue.alt sentDen, dox ⊆ q ∧ isPositiveEvidenceS q answer prior

/-- Full support fails when no alternative is doxastically endorsed.

For canonical info-seeking questions, `dox ⊄ q` for all `q ∈ alt sentDen`,
which blocks SUPPORT entirely regardless of the probabilistic component.
This is IKW's explanation of the interrogative left-argument restriction
on discourse *only*. -/
theorem fullSupport_fails_unbelievedS {W : Type*} [Fintype W]
    (dox : Set W) (sentDen : Core.Issue W) (prior : Prior W) (answer : Set W)
    (hNoBelief : ∀ q ∈ Core.Issue.alt sentDen, ¬ (dox ⊆ q)) :
    ¬ fullSupportS dox sentDen prior answer := by
  rintro ⟨q, hq, hSub, _⟩
  exact hNoBelief q hq hSub

end Semantics.Questions.Support
