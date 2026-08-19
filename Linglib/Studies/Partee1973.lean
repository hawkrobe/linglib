import Linglib.Semantics.Tense.Compositional

/-!
# Tenses and Pronouns: Partee's Structural Analogy
[partee-1973] [prior-1967]

Formalizes [partee-1973]: tenses in English exhibit the same three-way
interpretive ambiguity as pronouns — indexical, anaphoric, and
bound-variable — and share the same formal mechanisms (assignment
functions, variable lookup, lambda abstraction). The substrate carrier is
`TensePronoun` (`Semantics/Tense/Pronoun.lean`).

| Mode      | Pronouns                     | Tenses                              |
|-----------|------------------------------|-------------------------------------|
| Indexical | "I" → agent of context       | present → speech time               |
| Anaphoric | "he" → salient individual    | past → salient narrative time       |
| Bound     | "his" in ∀x...his...         | tense in "whenever...is..."         |

Partee's main argument against [prior-1967]'s tense-as-operator view: "I
didn't turn off the stove" with past tense does not mean "at SOME past
time I didn't turn off the stove" (trivially true) but "at THAT specific
time I didn't turn off the stove" — tenses refer, they don't quantify
(`stove_refutes_prior`).

The definitions here are the temporal counterparts of the entity variable
infrastructure in `Semantics.Montague.Variables`; both instantiate the
generic `Assignment` infrastructure, which is Partee's point: the same
referential mechanism operates over different domains.

Later engagements with the analogy live in their own studies:
`Ogihara1989` (operator–referential reconciliation), `Kratzer1998` (zero
tense, SOT deletion), `Elbourne2013` (situation-variable coarsening).
-/

open Tense

namespace Partee1973

open Tense (interpTense PAST)
open Intensional (Index)

/-- Partee's stove example: "I didn't turn off the stove."

    Past tense introduces a temporal variable resolved to a specific
    contextually salient time. The negation scopes over the temporal
    reference, giving ¬P(t_i) rather than Prior's ∃t < now. ¬P(t). -/
def parteeStoveExample {Time : Type*} (turnedOff : Time → Bool)
    (g : TemporalAssignment Time) (n : ℕ) : Bool :=
  !turnedOff (interpTense n g)

/-- [partee-1973]'s argument against [prior-1967], as a countermodel: in a
    context where the stove WAS turned off at the salient time (−1), the
    referential reading is false — the utterance is correctly predicted
    false — while the Priorean existential reading stays true (witnessed
    by any other past time), so the operator analysis trivializes the
    sentence. -/
theorem stove_refutes_prior :
    parteeStoveExample (· == (-1 : ℤ)) (λ _ => (-1 : ℤ)) 0 = false ∧
    ∃ s : Index Unit ℤ,
      PAST (λ s => (s.time == (-1 : ℤ)) = false) s ⟨(), 0⟩ :=
  ⟨by decide, ⟨(), -2⟩, by decide, by decide⟩

/-- Partee's narrative example: "He turned the corner. He saw a house."

    Both past tenses refer to the same narrative time — temporal
    anaphora. Under the referential analysis both clauses evaluate at
    g(n) for the same discourse-salient temporal variable n, just as
    anaphoric pronouns corefer with an established individual. -/
def narrativeAnaphora {Time : Type*} (P Q : Time → Bool)
    (g : TemporalAssignment Time) (n : ℕ) : Bool :=
  P (interpTense n g) && Q (interpTense n g)

end Partee1973
