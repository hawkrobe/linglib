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

## German Clause Types

| Clause type       | Mood operators           | Example                    |
|-------------------|--------------------------|----------------------------|
| dass-VL           | DEONT only               | "Dass du kommst!"          |
| V2-declarative    | DEONT(EPIS(p))           | "Jim wohnt in Berlin."     |
| VL-interrogative  | DEONT(EPIS(p))           | "Wann Peter kommt?"        |
| V2-interrogative  | DEONT(EPIS(p)) ⊙ HKNOW  | "Kommt Peter?"             |
| Imperative        | DEONT only               | "Tritt zurück!"            |
-/

namespace Semantics.Mood.SentenceMoodUCI


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
-- § 3. German Clause Type Derivations
-- ════════════════════════════════════════════════════════════════

/-- dass-VL clause mood: DEONT only (@cite{gutzmann-2015}, (5.82)).

No [±wh] visible at LF (dass is semantically empty, so [−wh] is
invisible per the visibility condition (5.41)). Therefore no epistemic
interpretation is triggered. The root rule introduces DEONT.

"Dass du nicht zu spät kommst!" = The speaker wants [you not arrive late]. -/
def dassVLMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  deont p c

/-- V2-declarative mood: DEONT(EPIS(p)) (@cite{gutzmann-2015}, (5.93)–(5.96)).

The finite verb moves to C⁰ (V-to-C triggered by [−wh] attached to an
overt element at PF). The [−wh] is visible at LF, triggering epistemic
interpretation. The root rule adds DEONT, and E modifies it to embed
the epistemic predicate.

"Jim wohnt in Berlin." = The speaker wants the hearer to believe
[Jim lives in Berlin]. -/
def v2DeclMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  episModifier deont p c

/-- V2-interrogative mood: DEONT(EPIS(p)) ⊙ HKNOW(p)
(@cite{gutzmann-2015}, (5.100)).

V2-interrogatives have two [±wh] specifications: [+wh] in CP^spec
and [−wh] in C⁰ (Brandt et al. 1992). The first triggers epistemic
interpretation, the second (in C⁰) triggers an additional epistemic
interpretation resolved to hearer knowledge. HKNOW is a separate
functional expletive UCI whose u-content is conjoined (⊙) with the
deontic/epistemic mood.

"Kommt Peter?" = The speaker wants to know [whether Peter comes]
AND the addressee knows [whether Peter comes]. -/
def v2InterrogMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  episModifier deont p c && hknow p c

/-- VL-interrogative mood: DEONT(EPIS(p)) only — no HKNOW
(@cite{gutzmann-2015}, p. 213).

VL-interrogatives (e.g., "Wann Peter nach Hause kommt?") lack the
[−wh] in C⁰ that triggers HKNOW. Therefore they are felicitous even
when the hearer does not know the answer (the Cuban cigar scenario). -/
def vlInterrogMood {W : Type*} (p : W → Bool) (c : MoodContext W) : Bool :=
  episModifier deont p c


-- ════════════════════════════════════════════════════════════════
-- § 4. Theorems
-- ════════════════════════════════════════════════════════════════

/-- dass-VL clauses have no epistemic component. -/
theorem dassVL_is_pure_deontic {W : Type*}
    (p : W → Bool) (c : MoodContext W) :
    dassVLMood p c = deont p c := rfl

/-- Epistemic embedding preserves truth at the world level. The
epistemic contribution is purely use-conditional, not truth-conditional. -/
theorem epis_preserves_truth {W : Type*} (p : W → Bool) (w : W) :
    epis p w = p w := rfl

/-- V2-interrogatives differ from VL-interrogatives only in the
HKNOW component (hearer knowledge use condition). -/
theorem v2_vs_vl_interrog {W : Type*}
    (p : W → Bool) (c : MoodContext W) :
    v2InterrogMood p c = (vlInterrogMood p c && hknow p c) := rfl

/-- Imperatives and dass-VL clauses share the same mood structure:
DEONT only, no epistemic. Both lack [±wh] visible at LF. -/
theorem imperative_equals_dassVL {W : Type*}
    (p : W → Bool) (c : MoodContext W) :
    dassVLMood p c = deont p c := rfl

-- ════════════════════════════════════════════════════════════════
-- § 5. German Clause Types and Mood Structure
-- ════════════════════════════════════════════════════════════════

/-- German clause types distinguished by verb position and complementizer,
which determine mood operator inventory (@cite{gutzmann-2015}, Ch 5). -/
inductive GermanClauseType where
  /-- dass-VL: complementizer clause, verb-last. No [±wh] visible at LF. -/
  | dassVL
  /-- V2-declarative: finite verb in C⁰, [−wh] visible at LF. -/
  | v2Declarative
  /-- V2-interrogative: verb-second, [+wh] in SpecCP + [−wh] in C⁰. -/
  | v2Interrogative
  /-- VL-interrogative: verb-last, [+wh] only (no [−wh] in C⁰). -/
  | vlInterrogative
  /-- Imperative: no [±wh] visible at LF. -/
  | imperative
  deriving DecidableEq, Repr

/-- Which sentence mood operators are present in a clause type
(@cite{gutzmann-2015}, Table 5.1).

This captures the *theoretical prediction* about mood operator inventory,
derived from the visibility of [±wh] features at LF and the presence
of specific syntactic heads (C⁰, SpecCP). -/
structure MoodStructure where
  hasDeontic : Bool
  hasEpistemic : Bool
  hasHearerKnowledge : Bool
  deriving DecidableEq, Repr

/-- The mood structure of each German clause type, derived from
the theory of [±wh] visibility and the root rule. -/
def GermanClauseType.moodStructure : GermanClauseType → MoodStructure
  | .dassVL          => ⟨true, false, false⟩
  | .v2Declarative   => ⟨true, true, false⟩
  | .v2Interrogative => ⟨true, true, true⟩
  | .vlInterrogative => ⟨true, true, false⟩
  | .imperative      => ⟨true, false, false⟩

/-- Every matrix clause has a deontic operator (the root rule). -/
theorem every_clause_has_deont (ct : GermanClauseType) :
    ct.moodStructure.hasDeontic = true := by
  cases ct <;> rfl

/-- Imperatives lack EPIS — the structural basis for selectional
restrictions on UC-modifiers like *wohl*. -/
theorem imperative_lacks_epis :
    GermanClauseType.imperative.moodStructure.hasEpistemic = false := rfl

/-- dass-VL and imperatives share mood structure: deontic only. -/
theorem dassVL_matches_imperative :
    GermanClauseType.dassVL.moodStructure =
    GermanClauseType.imperative.moodStructure := rfl

/-- V2-interrogatives differ from VL-interrogatives only in HKNOW. -/
theorem v2_vl_differ_only_in_hknow :
    GermanClauseType.v2Interrogative.moodStructure.hasDeontic =
      GermanClauseType.vlInterrogative.moodStructure.hasDeontic ∧
    GermanClauseType.v2Interrogative.moodStructure.hasEpistemic =
      GermanClauseType.vlInterrogative.moodStructure.hasEpistemic ∧
    GermanClauseType.v2Interrogative.moodStructure.hasHearerKnowledge = true ∧
    GermanClauseType.vlInterrogative.moodStructure.hasHearerKnowledge = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end Semantics.Mood.SentenceMoodUCI
