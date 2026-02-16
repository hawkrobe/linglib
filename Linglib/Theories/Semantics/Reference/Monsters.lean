/-
# Kaplan's Anti-Monster Thesis

Kaplan (1989) "Demonstratives" §VIII: the claim that natural language
operators are *content operators* (shifting circumstances of evaluation)
rather than *context operators* (shifting contexts of utterance).

Context operators — "monsters" — would shift the context, changing what
"I", "here", and "now" refer to. Kaplan argues English has none.
Cross-linguistic work (Schlenker 2003, Anand & Nevins 2004) challenges
this with indexical shift under attitude verbs in Amharic and Zazaki.

## Key Definitions

- `ContentOperator`: shifts circumstances (modal, tense — standard)
- `ContextOperator`: shifts context (the monster)
- `IsMonster`: an operator whose output depends on input at OTHER contexts
- `KaplansThesis`: all NL operators are content operators
- `SchlenkerCounterexample`: cross-linguistic monster evidence

## References

- Kaplan, D. (1989). Demonstratives, §VIII.
- Schlenker, P. (2003). A Plea for Monsters. Linguistics & Philosophy.
- Anand, P. & Nevins, A. (2004). Shifty Operators in Changing Contexts.
  SALT XIV.
-/

import Linglib.Core.Context
import Linglib.Core.Intension

namespace Semantics.Reference.Monsters

open Core.Intension (Intension IsRigid)

/-! ## Operator Types -/

/-- A content operator: maps intensions to intensions by operating on the
circumstance of evaluation. Standard operators (modals, tense) are content
operators.

Given an intension (W → τ), a content operator produces a new intension
that may quantify over worlds/times but does NOT shift the context. -/
abbrev ContentOperator (W : Type*) (τ : Type*) := Intension W τ → Intension W τ

/-- A context operator: maps characters to characters by operating on the
context of utterance. Kaplan calls these "monsters."

Given a character (C → W → τ), a context operator produces a new character
that may shift which context the embedded expression is evaluated at. -/
abbrev ContextOperator (C : Type*) (W : Type*) (τ : Type*) :=
  (C → Intension W τ) → (C → Intension W τ)

/-- An operator is a monster if its output at context c can depend on the
input's value at contexts OTHER than c.

Formally: there exist two characters that agree at c but produce different
outputs, meaning the operator "looked at" other contexts. -/
def IsMonster {C W τ : Type*} (op : ContextOperator C W τ) : Prop :=
  ∃ (char₁ char₂ : C → Intension W τ) (c : C),
    char₁ c = char₂ c ∧ op char₁ c ≠ op char₂ c

/-! ## Schlenker's Fixity Thesis (Schlenker 2003, (1)) -/

/-- The Fixity Thesis: the semantic value of an indexical is fixed solely by
the context of the actual speech act, and cannot be affected by any logical
operators.

Schlenker (2003, p. 30): "The semantic value of an indexical is fixed solely
by the context of the actual speech act, and cannot be affected by any
logical operators."

This is the formal content of Kaplan's ban on monsters, stated as a property
of indexicals rather than of operators. An indexical satisfies fixity iff
its content at context c does not depend on what operators embed it. -/
def FixityThesis {C W E : Type*} (indexicalChar : C → Intension W E) : Prop :=
  ∀ (op : ContextOperator C W E) (c : C), op indexicalChar c = indexicalChar c

/-! ## Schlenker's Say_m Operator (Schlenker 2003, (6)) -/

/-- Schlenker's monstrous `Say_m`: attitude verbs as quantifiers over contexts.

Standard analysis: "John says that φ" quantifies over worlds compatible
with John's assertion. Schlenker's monster analysis: "John says that φ"
quantifies over *contexts* compatible with John's assertion, where the
shifted context has John as agent.

`sayM attHolder assert φ c w` is true iff for every context c' compatible
with what `attHolder` asserts at time/world, φ is true at c'. The
`assert` function returns the set of compatible contexts. -/
def sayM {C W E : Type*}
    (assert : E → W → C → Prop)
    (attHolder : E)
    (φ : C → W → Prop)
    (_c : C) (w : W) : Prop :=
  ∀ c', assert attHolder w c' → φ c' w

/-- `sayM` depends on φ's value at contexts other than c: if a compatible
context c' exists where φ differs, then `sayM ... φ c w` requires φ c' w. -/
theorem sayM_accesses_shifted_context {C W E : Type*}
    (assert : E → W → C → Prop)
    (attHolder : E) (w : W) (c' : C)
    (hCompat : assert attHolder w c')
    (φ : C → W → Prop) :
    ∀ c, sayM assert attHolder φ c w → φ c' w :=
  λ _c h => h c' hCompat

/-! ## Kaplan's Thesis -/

/-- Kaplan's thesis (1989 §VIII): natural language has no monsters.

All natural language operators are content operators — they shift
circumstances of evaluation, never contexts of utterance.

Quotation is explicitly excluded: Kaplan acknowledges that quotation
shifts context but treats it as a metalinguistic device, not an operator
within the object language.

In English, this thesis appears to hold: "I", "here", "now" always refer
to the actual speaker, place, and time, even under attitude verbs.
"John said that I am happy" ⟹ the speaker (not John) is happy. -/
structure KaplansThesis where
  /-- The thesis applies to this language -/
  language : String
  /-- All operators in the language are content operators -/
  noMonsters : Bool
  /-- Quotation is excluded from the thesis -/
  quotationExcluded : Bool := true

/-- English obeys Kaplan's thesis. -/
def englishThesis : KaplansThesis :=
  { language := "English"
  , noMonsters := true }

/-! ## Cross-Linguistic Counterexamples -/

/-- A Schlenker-style counterexample: a language where an indexical shifts
under an embedding verb, violating Kaplan's thesis.

Records the language, the shifted indexical, the embedding verb, and
the citation. -/
structure SchlenkerCounterexample where
  /-- Language exhibiting the shift -/
  language : String
  /-- The indexical that shifts (e.g., "I", "here") -/
  shiftedIndexical : String
  /-- The embedding verb triggering the shift -/
  embeddingVerb : String
  /-- Citation for the empirical claim -/
  citation : String
  /-- Description of the shift -/
  description : String

/-- Amharic indexical shift (Schlenker 2003).

In Amharic, the first person pronoun can shift under 'say' to refer to
the subject of the attitude verb rather than the actual speaker.

"John yä-nä Ïnä dässïtäñ alä" ≈ "John said that {I/he} am happy"
where "I" refers to John, not the speaker. -/
def amharicShift : SchlenkerCounterexample :=
  { language := "Amharic"
  , shiftedIndexical := "first person pronoun"
  , embeddingVerb := "say (alä)"
  , citation := "Schlenker (2003)"
  , description := "'I' shifts to refer to the attitude holder under 'say'" }

/-- Zazaki indexical shift (Anand & Nevins 2004).

In Zazaki, both first and second person indexicals can shift under
attitude verbs, with all shifted indexicals referring to the same
shifted context. -/
def zazakiShift : SchlenkerCounterexample :=
  { language := "Zazaki"
  , shiftedIndexical := "first and second person pronouns"
  , embeddingVerb := "say (vatene)"
  , citation := "Anand & Nevins (2004)"
  , description := "Both 'I' and 'you' shift uniformly under attitude verbs" }

/-! ## Debate Status -/

/-- The current status of the monster debate.

Kaplan's thesis holds for English (and most European languages). It is
challenged by Amharic, Zazaki, Slave, Navajo, and other languages with
indexical shift under attitude verbs.

The leading analysis (Anand & Nevins 2004) treats attitude verbs in these
languages as context-shifting operators: the embedded clause is evaluated
relative to a *shifted context* whose agent is the attitude holder.

This connects to `Attitude/Doxastic.lean`: the doxastic accessibility
relation determines the shifted context's world, while the shifted
agent comes from the embedding predicate's subject. -/
structure MonsterDebate where
  /-- Languages supporting the thesis -/
  supporting : List String
  /-- Languages challenging the thesis -/
  challenging : List String
  /-- Current consensus -/
  consensus : String

def monsterDebate : MonsterDebate :=
  { supporting := ["English", "German", "French", "Japanese"]
  , challenging := ["Amharic", "Zazaki", "Slave", "Navajo", "Uyghur"]
  , consensus := "Thesis holds for English person indexicals; " ++
      "challenged cross-linguistically and by English temporal adverbials" }

/-- Schlenker (2003) also argues that English temporal adverbials show
monster-like behavior: "yesterday" can shift under attitude verbs to
refer to the day before the reported speech act, not the actual one.

"On Tuesday, John said that yesterday it was raining"
→ "yesterday" = Monday (day before John's speech), not the day before
the actual utterance. This is an English quasi-monster in the temporal
domain. -/
def englishTemporalShift : SchlenkerCounterexample :=
  { language := "English"
  , shiftedIndexical := "yesterday (temporal adverbial)"
  , embeddingVerb := "say"
  , citation := "Schlenker (2003)"
  , description := "'yesterday' can shift to the day before the reported " ++
      "speech act under attitude verbs" }

end Semantics.Reference.Monsters
