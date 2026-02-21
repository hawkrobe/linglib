import Linglib.Core.Intension
import Linglib.Theories.Semantics.Reference.Kaplan

/-!
# Kaplan's Anti-Monster Thesis (Tower Formulation)

Kaplan (1989) "Demonstratives" VIII: the claim that natural language
operators are *content operators* (shifting circumstances of evaluation)
rather than *context operators* (shifting contexts of utterance).

Under the tower analysis, a monster is a non-identity context shift:
an embedding operator that pushes a shift where .apply c != c for some c.
Kaplan's thesis for English says attitude verbs push identity shifts —
they embed without changing the context of utterance.

Cross-linguistic counterexamples (Schlenker 2003, Anand & Nevins 2004)
are languages where attitude verbs push non-identity shifts (e.g.,
`attitudeShift` changes the agent to the attitude holder).

## Key Definitions

- `IsTowerMonster`: a shift where apply c != c for some c
- `kaplansThesisAsTower`: English embedding verbs push identity shifts
- `sayM`: Schlenker's monster operator, rewritten via tower push + fold
- Bridge: old `IsMonster` concept <-> `IsTowerMonster`

## References

- Kaplan, D. (1989). Demonstratives, VIII.
- Schlenker, P. (2003). A Plea for Monsters. Linguistics & Philosophy.
- Anand, P. & Nevins, A. (2004). Shifty Operators in Changing Contexts.
  SALT XIV.
-/

namespace Semantics.Reference.Monsters

open Core.Context
open Core.Intension (Intension IsRigid)

-- ════════════════════════════════════════════════════════════════
-- § Tower Monster
-- ════════════════════════════════════════════════════════════════

/-- A context shift is a tower monster iff it is non-identity: there exists
    some context c where applying the shift produces a different context.

    Under the tower analysis, monsters are exactly the non-identity shifts.
    English attitude verbs push identity shifts (not monsters); Amharic
    attitude verbs push attitude shifts (monsters). -/
def IsTowerMonster {C : Type*} (σ : ContextShift C) : Prop :=
  ∃ (c : C), σ.apply c ≠ c

/-- The identity shift is not a monster. -/
theorem identityShift_not_monster {W : Type*} {E : Type*} {P : Type*} {T : Type*} :
    ¬ IsTowerMonster (identityShift (W := W) (E := E) (P := P) (T := T)) := by
  intro ⟨c, h⟩
  exact h (identityShift_apply c)

/-- An attitude shift is a monster when the holder differs from some
    context's agent. -/
theorem attitudeShift_is_monster {W : Type*} {E : Type*} {P : Type*} {T : Type*}
    (holder : E) (attWorld : W) (c : KContext W E P T)
    (hAgent : c.agent ≠ holder) :
    IsTowerMonster (attitudeShift (P := P) (T := T) holder attWorld) := by
  refine ⟨c, λ h => ?_⟩
  have : (attitudeShift (P := P) (T := T) holder attWorld).apply c = c := h
  have hagent : ((attitudeShift (P := P) (T := T) holder attWorld).apply c).agent = c.agent :=
    congrArg KContext.agent this
  simp only [attitudeShift] at hagent
  exact hAgent hagent.symm

-- ════════════════════════════════════════════════════════════════
-- § Kaplan's Thesis (Tower Formulation)
-- ════════════════════════════════════════════════════════════════

/-- Kaplan's thesis as a tower property: embedding verbs in a language push
    shifts that are not monsters (i.e., identity shifts).

    For English, this means all attitude verbs push `identityShift`:
    "John said that I am happy" evaluates "I" at the original context,
    because the embedding verb didn't shift anything.

    The `embeddingShifts` parameter lists the shifts that the language's
    embedding verbs produce. The thesis holds iff none of them is a monster. -/
def KaplansThesisHolds {C : Type*} (embeddingShifts : List (ContextShift C)) : Prop :=
  ∀ σ ∈ embeddingShifts, ¬ IsTowerMonster σ

/-- English embedding verbs push identity shifts. Kaplan's thesis holds. -/
theorem kaplansThesisAsTower {W : Type*} {E : Type*} {P : Type*} {T : Type*} :
    KaplansThesisHolds
      [identityShift (W := W) (E := E) (P := P) (T := T)] := by
  intro σ hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rw [hMem]
  exact identityShift_not_monster

-- ════════════════════════════════════════════════════════════════
-- § Schlenker's Say_m (Tower Formulation)
-- ════════════════════════════════════════════════════════════════

/-- Schlenker's monstrous `Say_m`, rewritten via tower push.

    Standard analysis: "John says that phi" quantifies over worlds compatible
    with John's assertion. Schlenker's monster analysis: "John says that phi"
    pushes an attitude shift onto the tower, making the embedded clause
    see John as the agent.

    `sayMTower assert attHolder phi t w` pushes `attitudeShift attHolder w'`
    for each compatible world w', evaluating phi against the shifted tower. -/
def sayMTower {W E P T : Type*}
    (assert : E → W → W → Prop)
    (attHolder : E)
    (φ : ContextTower (KContext W E P T) → W → Prop)
    (t : ContextTower (KContext W E P T)) (w : W) : Prop :=
  ∀ w', assert attHolder w w' →
    φ (t.push (attitudeShift attHolder w')) w'

/-- `sayMTower` accesses shifted contexts: the embedded clause is evaluated
    with the attitude holder as agent at the compatible world. -/
theorem sayMTower_shifts_agent {W E P T : Type*}
    (assert : E → W → W → Prop)
    (attHolder : E) (w w' : W)
    (hCompat : assert attHolder w w')
    (φ : ContextTower (KContext W E P T) → W → Prop)
    (t : ContextTower (KContext W E P T))
    (h : sayMTower assert attHolder φ t w) :
    φ (t.push (attitudeShift attHolder w')) w' :=
  h w' hCompat

-- ════════════════════════════════════════════════════════════════
-- § Legacy Operator Types (for backward reference)
-- ════════════════════════════════════════════════════════════════

/-- A content operator: maps intensions to intensions by operating on the
    circumstance of evaluation. Standard operators (modals, tense) are content
    operators. -/
abbrev ContentOperator (W : Type*) (τ : Type*) := Intension W τ → Intension W τ

/-- A context operator: maps characters to characters by operating on the
    context of utterance. Kaplan calls these "monsters." -/
abbrev ContextOperator (C : Type*) (W : Type*) (τ : Type*) :=
  (C → Intension W τ) → (C → Intension W τ)

/-- An operator is a monster if its output at context c can depend on the
    input's value at contexts OTHER than c. -/
def IsMonster {C W τ : Type*} (op : ContextOperator C W τ) : Prop :=
  ∃ (char₁ char₂ : C → Intension W τ) (c : C),
    char₁ c = char₂ c ∧ op char₁ c ≠ op char₂ c

-- ════════════════════════════════════════════════════════════════
-- § Bridge: IsTowerMonster <-> IsMonster
-- ════════════════════════════════════════════════════════════════

/-- The Fixity Thesis: the semantic value of an indexical is fixed solely by
    the context of the actual speech act, and cannot be affected by any logical
    operators.

    Schlenker (2003, p. 30). Under the tower analysis, fixity is equivalent
    to reading from `.origin` — an `AccessPattern` with depth `.origin` is
    invariant under any push (by `origin_stable`). -/
def FixityThesis {C W E : Type*} (indexicalChar : C → Intension W E) : Prop :=
  ∀ (op : ContextOperator C W E) (c : C), op indexicalChar c = indexicalChar c

-- ════════════════════════════════════════════════════════════════
-- § Cross-Linguistic Counterexamples
-- ════════════════════════════════════════════════════════════════

/-- A Schlenker-style counterexample: a language where an indexical shifts
    under an embedding verb, violating Kaplan's thesis.

    In tower terms: the embedding verb pushes a non-identity shift, and
    the indexical reads from `.local` rather than `.origin`. -/
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

"John ya-na Ina dassitany ala" = "John said that {I/he} am happy"
where "I" refers to John, not the speaker. -/
def amharicShift : SchlenkerCounterexample :=
  { language := "Amharic"
  , shiftedIndexical := "first person pronoun"
  , embeddingVerb := "say (ala)"
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

/-- The current status of the monster debate.

Kaplan's thesis holds for English (and most European languages). It is
challenged by Amharic, Zazaki, Slave, Navajo, and other languages with
indexical shift under attitude verbs.

The leading analysis (Anand & Nevins 2004) treats attitude verbs in these
languages as context-shifting operators: the embedded clause is evaluated
relative to a *shifted context* whose agent is the attitude holder.

Under the tower analysis, the debate reduces to: what shift does an
attitude verb push? Identity (Kaplan) or non-identity (Schlenker)? -/
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
-> "yesterday" = Monday (day before John's speech), not the day before
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
