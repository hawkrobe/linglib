import Linglib.Theories.Semantics.Mood.SentenceMoodUCI
import Linglib.Fragments.German.ModalParticles

/-!
# Gutzmann (2015): Sentence Mood as Use-Conditional Meaning
@cite{gutzmann-2015}

Use-Conditional Meaning: Studies in Multidimensional Semantics.
Oxford University Press.

## Key Claims

1. Sentence mood operators (deontic, epistemic) are UCIs, not presuppositions
2. The epistemic interpretation of [±wh] does NOT pass standard
   presupposition tests (negation, disjunction)
3. V2-interrogatives carry a HKNOW condition absent from VL-interrogatives
4. Modal particles are functional expletive UCIs whose mood restrictions
   derive from interaction with sentence mood operators
5. *wohl* is a UC-modifier (not a UCI), with selectional restriction

## Clause Type Predictions

| Clause type       | t-content | u-content                    |
|-------------------|-----------|------------------------------|
| dass-VL           | p         | DEONT(p)                     |
| V2-declarative    | p         | DEONT(EPIS(p))               |
| VL-interrogative  | p         | DEONT(EPIS(p))               |
| V2-interrogative  | p         | DEONT(EPIS(p)) ⊙ HKNOW(p)   |
| Imperative        | p         | DEONT(p)                     |
-/

namespace Gutzmann2015

open Semantics.Mood.SentenceMoodUCI
open Fragments.German.ModalParticles


-- ════════════════════════════════════════════════════════════════
-- § 1. Mood Structure Predictions
-- ════════════════════════════════════════════════════════════════

/-- The Cuban cigar argument: V2- and VL-interrogatives differ ONLY in
the hearer knowledge condition. This explains why VL-interrogatives
are felicitous even when the hearer clearly does not know the answer
(the Cuban cigar scenario), while V2-interrogatives are not. -/
theorem cuban_cigar :
    GermanClauseType.v2Interrogative.moodStructure.hasHearerKnowledge = true ∧
    GermanClauseType.vlInterrogative.moodStructure.hasHearerKnowledge = false :=
  ⟨rfl, rfl⟩

/-- Imperatives share dass-VL mood structure (deontic only):
both lack [±wh] at LF, so neither triggers epistemic interpretation. -/
theorem imperative_matches_dassVL :
    GermanClauseType.imperative.moodStructure =
    GermanClauseType.dassVL.moodStructure := rfl

/-- Every matrix clause has a deontic operator (the root rule). -/
theorem root_rule :
    ∀ ct : GermanClauseType, ct.moodStructure.hasDeontic = true :=
  every_clause_has_deont


-- ════════════════════════════════════════════════════════════════
-- § 2. Mood Operator Theorems
-- ════════════════════════════════════════════════════════════════

/-- dass-VL clauses have no epistemic component. -/
theorem dassVL_no_epis :
    GermanClauseType.dassVL.moodStructure.hasEpistemic = false := rfl

/-- V2-declaratives have epistemic but not hearer knowledge. -/
theorem v2Decl_epis_no_hknow :
    GermanClauseType.v2Declarative.moodStructure.hasEpistemic = true ∧
    GermanClauseType.v2Declarative.moodStructure.hasHearerKnowledge = false :=
  ⟨rfl, rfl⟩

/-- Epistemic embedding preserves truth at the world level. The
epistemic contribution is purely use-conditional, not truth-conditional. -/
theorem epis_preserves_truth {W : Type*} (p : W → Bool) (w : W) :
    epis p w = p w := rfl

/-- V2-interrogatives differ from VL-interrogatives only in HKNOW.
Derived from the theory of [±wh] feature visibility. -/
theorem v2_vs_vl_interrog {W : Type*}
    (p : W → Bool) (c : MoodContext W) :
    v2InterrogMood p c = (vlInterrogMood p c && hknow p c) := rfl


-- ════════════════════════════════════════════════════════════════
-- § 3. Modal Particle–Mood Interaction
-- ════════════════════════════════════════════════════════════════

/-- *wohl*'s distribution is fully derived from EPIS presence: wohl is
licensed in a clause type iff that clause type has an epistemic mood
operator. This is the formal content of the selectional restriction
analysis — wohl has type `⟨⟨⟨s,t⟩,u⟩, ⟨⟨s,t⟩,u⟩⟩` and modifies EPIS,
so clause types lacking EPIS produce a type mismatch. -/
theorem wohl_derived_from_epis :
    ∀ ct : GermanClauseType,
      wohl.licensedInClause ct = ct.moodStructure.hasEpistemic :=
  wohl_iff_epis

/-- *ja* is restricted to declaratives, matching the clause type with
deontic + epistemic mood but without the hearer knowledge condition. -/
theorem ja_declarative_restriction :
    ja.declOk = true ∧ ja.interrogOk = false := ⟨rfl, rfl⟩

/-- *denn* is the interrogative counterpart of *ja*. -/
theorem denn_interrogative_restriction :
    denn.declOk = false ∧ denn.interrogOk = true := ⟨rfl, rfl⟩

/-- *ja* and *denn* partition clause types: they are never both
licensed in the same clause type. -/
theorem ja_denn_partition :
    ∀ ct : GermanClauseType,
      ¬(ja.licensedInClause ct = true ∧ denn.licensedInClause ct = true) :=
  ja_denn_complementary

/-- The restriction kind for all particles reflects the UCI/UC-modifier
distinction: UCIs have conflict restrictions, UC-modifiers have
selectional restrictions. -/
theorem restriction_reflects_kind :
    ∀ mp ∈ allModalParticles,
      (mp.exprKind = .uci → mp.restrictionKind = .ucConflict) ∧
      (mp.exprKind = .ucModifier → mp.restrictionKind = .selectional) :=
  restriction_tracks_kind

end Gutzmann2015
