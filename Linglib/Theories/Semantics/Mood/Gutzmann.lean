import Linglib.Theories.Semantics.UseConditional.LTU

/-!
# Sentence Mood as Use-Conditional Meaning
@cite{gutzmann-2015}

Sentence mood operators (deontic, epistemic, hearer knowledge) analyzed
as use-conditional items within the L_TU framework.

## Key Thesis

@cite{gutzmann-2015} argues that Truckenbrodt (2006b)'s sentence mood
operators — epistemic and deontic — should NOT be treated as
presuppositions integrated into truth conditions. Instead, they are
*use-conditional*: they constrain the context of utterance without
affecting truth conditions.

Evidence:
- Epistemic interpretation does not pass standard presupposition tests
  (negation test, disjunction test)
- Integrative treatment yields wrong truth conditions: "Snow is white"
  would be true iff the speaker wants the hearer to believe snow is white
- Integrative treatment breaks valid inferences (e.g., "Peter wrote
  three books" ⊨ "Peter wrote at least one book" fails under embedding)

## Three Sentence Mood Operators

1. **DEONT**: deontic attitude (root rule — present in every matrix clause)
   Type: functional expletive UCI `⟨⟨s,t⟩, u⟩`
2. **EPIS**: epistemic attitude (triggered by [±wh] visible at LF)
   Reformulated as a uc-modifier E on DEONT
3. **HKNOW**: hearer knowledge (triggered by [−wh] in C⁰ for V2-interrogatives)
   Type: functional expletive UCI `⟨⟨s,t⟩, u⟩`

## Scope

This file provides the *language-agnostic* operators. Per-language
clause-type taxonomies and their mood compositions live in
`Fragments/<Language>/ClauseTypes.lean` (e.g.,
`Fragments.German.ClauseTypes` for the German V2/VL/dass-VL/imperative
inventory analyzed in @cite{gutzmann-2015}, Ch 5).
-/

namespace Semantics.Mood.Gutzmann


-- ════════════════════════════════════════════════════════════════
-- § 1. Mood Context
-- ════════════════════════════════════════════════════════════════

/-- A context of utterance for sentence mood evaluation.

Captures the context parameters that sentence mood operators quantify
over: `c_S` (speaker), `c_A` (addressee), `c_W` (world of the context).

**Simplification**: @cite{gutzmann-2015} defines DEONT via existential
quantification over a set D of contextually suitable deontic predicates
(wants, wishes, orders, ...). The full definition is:
`⟦DEONT⟧ = λp.{c : ∃ d ∈ D, d suitable for p in c ∧ d(c_S, p, c_W)}`.
We simplify this to a fixed `speakerWants` function, which suffices for
the core derivation theorems but does not capture the context-dependent
selection among different deontic attitudes. -/
structure MoodContext (W : Type*) where
  /-- The world of the utterance context -/
  world : W
  /-- Whether the speaker wants p to hold (given p's truth value at world) -/
  speakerWants : Bool → Bool
  /-- Whether the addressee knows whether p (given p's truth value at world) -/
  addresseeKnows : Bool → Bool


-- ════════════════════════════════════════════════════════════════
-- § 2. Sentence Mood Operators
-- ════════════════════════════════════════════════════════════════

/-- Deontic sentence mood operator (@cite{gutzmann-2015}, (5.85)).

⟦DEONT⟧ = λp. {c : there is a d ∈ D such that d is suitable for p
in c and d holds for p in c_W}

Simplified: the speaker wants `p` to hold in the utterance world.

Introduced by the root rule (5.43): every matrix clause gets a deontic
interpretation, expressing a volition on the part of the speaker. -/
def deont {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  c.speakerWants (p c.world)

/-- Epistemic sentence mood operator (@cite{gutzmann-2015}, (5.90)).

⟦EPIS⟧ = λp. {w : EPIS(p)(w) in w} = λp. {w : there is an e ∈ E
suitable for p in w and e holds for p in w}

Simplified: at the world level, epistemic embedding preserves truth.
The epistemic contribution is in the *use-conditional* dimension,
mediated by the E modifier. -/
def epis {W : Type*} (p : W → Bool) : W → Bool := p

/-- The E operator: epistemic modifier on UCIs (@cite{gutzmann-2015}, (5.91)).

E = λDλp. D(EPIS(p))

This is a use-conditional modifier of type
`⟨⟨⟨s,t⟩,u⟩, ⟨⟨s,t⟩,u⟩⟩`. It takes a UCI (like DEONT) that maps
propositions to use-conditional propositions, and pre-composes it
with EPIS. The result is that DEONT applies to the epistemically
embedded proposition rather than the raw propositional content. -/
def episModifier {W : Type*}
    (d : (W → Bool) → MoodContext W → Bool) :
    (W → Bool) → MoodContext W → Bool :=
  λ p c => d (epis p) c

/-- Hearer knowledge operator (@cite{gutzmann-2015}, (5.99)).

⟦HKNOW⟧ = λp. {c : c_A knows whether p in c_W}

A functional expletive UCI that adds a "free-floating" use condition:
the addressee knows the answer to the question. Present only in
V2-interrogatives (triggered by [−wh] in C⁰), absent from
VL-interrogatives — accounting for the Cuban cigar scenario. -/
def hknow {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  c.addresseeKnows (p c.world)


-- ════════════════════════════════════════════════════════════════
-- § 3. Mood Operator Inventory
-- ════════════════════════════════════════════════════════════════

/-- Which sentence mood operators are present in a clause type
(@cite{gutzmann-2015}, Table 5.1).

Language-agnostic predicate over a (possibly language-specific) clause
type, recording which of DEONT, EPIS, and HKNOW the clause composes.
Used by per-language clause-type fragments to declare their mood
inventories (e.g., `Fragments.German.ClauseTypes.GermanClauseType.moodStructure`). -/
structure MoodStructure where
  hasDeontic : Bool
  hasEpistemic : Bool
  hasHearerKnowledge : Bool
  deriving DecidableEq, Repr


-- ════════════════════════════════════════════════════════════════
-- § 4. Operator-level theorems
-- ════════════════════════════════════════════════════════════════

/-- Epistemic embedding preserves truth at the world level. The
epistemic contribution is purely use-conditional, not truth-conditional. -/
theorem epis_preserves_truth {W : Type*} (p : W → Bool) (w : W) :
    epis p w = p w := rfl

end Semantics.Mood.Gutzmann
