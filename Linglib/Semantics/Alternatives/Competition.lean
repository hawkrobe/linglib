import Linglib.Semantics.Alternatives.Source

/-!
# Pragmatic competition operators

Source-agnostic competition principles: do not use `φ` if there is a
competitor `φ'` drawn from an `Alternatives.Source` that is stronger
along the relevant content dimension. The competitor set is supplied as
a `Source S` parameter, so the same operators work for Katzir
alternatives (`Structural.katzirSource lex`), indirect alternatives
(`indirectFrom (katzirSource lex) …`,
[jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]), Horn scales,
or any other source — over any carrier `S`, not just parse trees.

## Main definitions

* `violatesMaximize` — the generic "maximize content" principle along a
  `Prop`-valued content dimension ([katzir-2007]).
* `violatesConversationalPrinciple` — at-issue content instantiation
  (scalar implicature, [katzir-2007]).
* `violatesMP` — Maximize Presupposition ([heim-1991], [schlenker-2012]):
  same assertive content, stronger presupposition.
* `violatesMCIs` — Maximize Conventional Implicatures ([lo-guercio-2025]):
  CI-content instantiation.

## Main results

* `violatesMaximize_of_violatesMP` / `violatesMP_of_violatesMaximize_sameAssertion`
  — relate `violatesMP` to `violatesMaximize` on the presuppositional axis.
-/

namespace Alternatives

variable {S World : Type*}

/-- Generic "maximize content" principle parameterized over content dimension.

Scalar inferences arise from comparing a sentence `φ` with formal
alternatives `φ'` that are more informative along some content dimension.
The same reasoning applies to three dimensions:

- **At-issue content** → Scalar Implicatures (Conversational Principle, [katzir-2007])
- **Presuppositional content** → Antipresuppositions (Maximize Presupposition, [schlenker-2012])
- **CI content** → Anti-Conventional Implicatures (MCIs!, [lo-guercio-2025])

`contentFn` maps each expression to its content along the relevant
dimension, a `Prop`-valued predicate (felicity, entailment, or CI
satisfaction). -/
def violatesMaximize
    (src : Source S) (contentFn : S → World → Prop)
    (φ : S) (weaklyAssertable : S → Prop) : Prop :=
  ∃ φ' ∈ src φ,
    (∀ w, contentFn φ' w → contentFn φ w) ∧
    (∃ w, contentFn φ w ∧ ¬ contentFn φ' w) ∧
    weaklyAssertable φ'

/-- The neo-Gricean conversational principle: `violatesMaximize` applied
to at-issue (truth-conditional) content ([katzir-2007]). -/
abbrev violatesConversationalPrinciple
    (src : Source S) (meaning : S → World → Prop)
    (φ : S) (weaklyAssertable : S → Prop) : Prop :=
  violatesMaximize src meaning φ weaklyAssertable

/-- Maximize Presupposition (the principle: [heim-1991]; reconstructed
from Gricean reasoning by [schlenker-2012]): `violatesMaximize` applied
to presuppositional content. Do not use `φ` if there is a competitor `φ'`
(from `src`) with the same assertive content but stronger presupposition.

Modeling note on the same-assertion clause. `assertionFn φ' w ↔
assertionFn φ w` is required at *every* world. This is the right notion
when `assertionFn` is the total at-issue content with presupposition
factored out. If instead `assertionFn` were partial (undefined where φ'`s
stronger presupposition fails), the standard antipresupposition condition
asks for assertion-agreement only *where φ' is defined*, i.e.
`∀ w, presupFn φ' w → (assertionFn φ' w ↔ assertionFn φ w)`. The
unconditional form here is retained because the consumer
`Studies/JereticEtAl2025.lean` (`tous_violatesMP_via_indirect`) supplies
total `Prop`-valued content; switch to the guarded form if a partial
`assertionFn` is ever used. -/
def violatesMP
    (src : Source S) (presupFn : S → World → Prop)
    (assertionFn : S → World → Prop)
    (φ : S) (weaklyAssertable : S → Prop) : Prop :=
  ∃ φ' ∈ src φ,
    (∀ w, assertionFn φ' w ↔ assertionFn φ w) ∧
    (∀ w, presupFn φ' w → presupFn φ w) ∧
    (∃ w, presupFn φ w ∧ ¬ presupFn φ' w) ∧
    weaklyAssertable φ'

/-- Maximize Conventional Implicatures ([lo-guercio-2025]):
`violatesMaximize` applied to CI content. Unlike MP!, does NOT require
the same assertive content — CI content is independent of truth conditions.
UNVERIFIED: the specific numbered definition in [lo-guercio-2025] (was
cited as "def 15" from memory) is not checked against the PDF. -/
abbrev violatesMCIs
    (src : Source S) (ciContentFn : S → World → Prop)
    (φ : S) (weaklyAssertable : S → Prop) : Prop :=
  violatesMaximize src ciContentFn φ weaklyAssertable

/-! ### Structural relationships between MP and Maximize

`violatesMP` differs from `violatesMaximize` on the same `presupFn` only
by the additional same-assertion clause. The two theorems below make the
relationship Lean-checkable, discharging the diagnostic prose in
[lo-guercio-2025] §4 that "ACIs do not require same assertive content,
unlike antipresuppositions." -/

variable {src : Source S} {presupFn assertionFn : S → World → Prop}
  {φ : S} {weaklyAssertable : S → Prop}

/-- Every `violatesMP` violation is also a `violatesMaximize` violation
on the presuppositional axis (drops the same-assertion clause). -/
theorem violatesMaximize_of_violatesMP
    (h : violatesMP src presupFn assertionFn φ weaklyAssertable) :
    violatesMaximize src presupFn φ weaklyAssertable := by
  obtain ⟨φ', hφ', _hassert, himp, hstrict, hwa⟩ := h
  exact ⟨φ', hφ', himp, hstrict, hwa⟩

/-- Conversely, a `violatesMaximize` violation on `presupFn` combined with
same-assertion at every alternative gives a `violatesMP` violation. -/
theorem violatesMP_of_violatesMaximize_sameAssertion
    (h_max : violatesMaximize src presupFn φ weaklyAssertable)
    (h_assert : ∀ φ' ∈ src φ, ∀ w, assertionFn φ' w ↔ assertionFn φ w) :
    violatesMP src presupFn assertionFn φ weaklyAssertable := by
  rcases h_max with ⟨φ', hφ', himp, hstrict, hwa⟩
  exact ⟨φ', hφ', h_assert φ' hφ', himp, hstrict, hwa⟩

end Alternatives
