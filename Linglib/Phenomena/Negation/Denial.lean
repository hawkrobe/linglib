import Linglib.Core.Semantics.ContentLayer
import Linglib.Core.Empirical

/-!
# Denial in Discourse
@cite{van-der-sandt-maier-2003}

Theory-neutral empirical data on denial: how correction sequences
selectively retract different content layers of the denied sentence.

## Central Claim: Denial ≠ Negation

@cite{van-der-sandt-maier-2003} argue that denial and negation are
**orthogonal** concepts:

- **Negation** is a semantic operator (a logical connective on propositions)
- **Denial** is a discourse operation (non-monotonic correction of
  contextual information)

A denial can use a POSITIVE sentence: "Mary IS happy" denies "Mary is
unhappy" (§2.1, ex. 6). And a negative sentence can be a plain assertion,
not a denial: "Mary is unhappy" uttered in isolation (§2.1, ex. 2).
What makes something a denial is its discourse function (correcting prior
information), not its syntactic form.

## Three Denial Types

When denial DOES use negation, the correction determines which content
layer is retracted:

| Denial type | Layer targeted | Paper example |
|-------------|----------------|---------------|
| Propositional | `fr` (at-issue) | "Mary is NOT happy" (5) |
| Presuppositional | `pr` | "...NOT bald — there is no king" (30b) |
| Implicature | `imp` | "Not POSSIBLE — NECESSARY" (29b) |

The paper also identifies a fourth empirical category — register/
connotation denials like "not a steed — a horse" (14) and "didn't kick the
bucket — passed away" (15) — which maps to the `imp` layer alongside
scalar implicature.

## Scope

This module captures theory-neutral denial data and the `DenialType →
ContentLayer` mapping. The directed reverse anaphora (RA*) mechanism
is formalized in `Theories.Semantics.Dynamic.DRT.Basic` (`LDRS.directedRA`),
with worked examples and Off→DenialDatum agreement proofs in
`VanDerSandtMaier2003`.
-/

namespace Phenomena.Negation.Denial

open Core.Semantics.ContentLayer

-- ════════════════════════════════════════════════════
-- § Denial Type
-- ════════════════════════════════════════════════════

/-- The type of denial, determined by which content layer is targeted.

    Each type corresponds to a `ContentLayer` via `targetLayer`. This
    is the central claim of: the different
    denial types are not different operations, but one mechanism
    (non-monotonic discourse correction) targeting different layers. -/
inductive DenialType where
  /-- Propositional denial: targets at-issue content.
      The presupposition survives; the assertion is retracted.
      (5): "Mary is not happy." (8): "The king of France is not bald —
      he has a full head of hair." -/
  | propositional
  /-- Presuppositional denial: targets presupposed content.
      The presupposition is retracted; the assertion falls with it.
      (30b): "The king of France is not bald — France does not have a king."
      (10): "John did not stop smoking — he never smoked." -/
  | presuppositional
  /-- Implicature denial: targets enrichment beyond truth conditions.
      Literal meaning survives; the implicature or connotation is retracted.
      (29b): "It's not POSSIBLE — it's NECESSARY."
      (14): "That is not a steed — it's a horse." -/
  | implicature
  deriving DecidableEq, Repr

/-- Map denial type to the content layer it targets. -/
def DenialType.targetLayer : DenialType → ContentLayer
  | .propositional => .atIssue
  | .presuppositional => .presupposition
  | .implicature => .implicature

/-- Each denial type targets a distinct layer. -/
theorem denial_types_target_distinct_layers :
    DenialType.propositional.targetLayer ≠ DenialType.presuppositional.targetLayer ∧
    DenialType.propositional.targetLayer ≠ DenialType.implicature.targetLayer ∧
    DenialType.presuppositional.targetLayer ≠ DenialType.implicature.targetLayer :=
  ⟨by decide, by decide, by decide⟩

/-- The mapping from denial types to content layers is injective:
    no two denial types target the same layer. -/
theorem targetLayer_injective (d₁ d₂ : DenialType)
    (h : d₁.targetLayer = d₂.targetLayer) : d₁ = d₂ := by
  cases d₁ <;> cases d₂ <;> simp_all [DenialType.targetLayer]

-- ════════════════════════════════════════════════════
-- § Denial Data
-- ════════════════════════════════════════════════════

/-- A denial datum: an assertion-denial-correction triple.

    Records the empirical pattern where a speaker asserts S, a hearer
    denies with a correction C, and the denial selectively retracts one
    content layer while preserving others.

    Note: `denial` and `correction` may be the same sentence in positive
    denials (where the correcting utterance is itself affirmative). -/
structure DenialDatum where
  /-- The original assertion being denied -/
  assertion : String
  /-- The denial utterance (may be negative or positive) -/
  denial : String
  /-- The correction that follows or constitutes the denial -/
  correction : String
  /-- Which content layer the correction targets -/
  denialType : DenialType
  /-- What content is retracted by the denial -/
  retractedContent : String
  /-- What content survives the denial -/
  survivingContent : String := ""
  /-- Paper example number, if from -/
  exampleNum : String := ""
  notes : String := ""
  deriving Repr

-- ════════════════════════════════════════════════════
-- § Positive Denial (§2.1)
-- ════════════════════════════════════════════════════

/-- Positive denial: denial does not require negation.

    §2.1, ex. 6: "Mary IS happy" can deny
    "Mary is unhappy." The correcting utterance is syntactically positive.
    This demonstrates the paper's central architectural claim: denial is a
    discourse operation (non-monotonic correction), not a syntactic one
    (negation). -/
def maryHappy_positive : DenialDatum :=
  { assertion := "Mary is unhappy"
  , denial := "Mary is happy"
  , correction := "Mary is happy"
  , denialType := .propositional
  , retractedContent := "Mary is unhappy"
  , exampleNum := "6"
  , notes := "Positive denial: no negation; the denial IS the correction" }

-- ════════════════════════════════════════════════════
-- § Propositional Denial (§2.2B)
-- ════════════════════════════════════════════════════

/-- Propositional denial: negation targets the assertion (at-issue content).
    §2.2, ex. 5. -/
def maryNotHappy : DenialDatum :=
  { assertion := "Mary is happy"
  , denial := "Mary is not happy"
  , correction := ""
  , denialType := .propositional
  , retractedContent := "Mary is happy"
  , exampleNum := "5"
  , notes := "Standard propositional denial" }

-- ════════════════════════════════════════════════════
-- § Presuppositional Denial (§2.2C)
-- ════════════════════════════════════════════════════

/-- Presuppositional denial of the king of France.
    §2.4, ex. 30b. -/
def kingBald_presuppositional : DenialDatum :=
  { assertion := "The king of France is bald"
  , denial := "The king of France is NOT bald"
  , correction := "France does not have a king"
  , denialType := .presuppositional
  , retractedContent := "France has a king (existence presupposition of the definite)"
  , exampleNum := "30b"
  , notes := "The correction targets the existence presupposition, not the predication" }

/-- Presuppositional denial of "stop" (prior-state presupposition).
    §2.2, ex. 10. -/
def stop_presuppositional : DenialDatum :=
  { assertion := "John stopped smoking"
  , denial := "John did not stop smoking"
  , correction := "He never smoked"
  , denialType := .presuppositional
  , retractedContent := "John used to smoke (prior-state presupposition of 'stop')"
  , exampleNum := "10" }

/-- Presuppositional denial of "know" (factive presupposition).
    §2.2, ex. 9. -/
def know_presuppositional : DenialDatum :=
  { assertion := "Virginia knows that the earth is flat"
  , denial := "Virginia cannot know that the earth is flat"
  , correction := ""
  , denialType := .presuppositional
  , retractedContent := "The earth is flat (factive presupposition of 'know')"
  , exampleNum := "9"
  , notes := "The modal 'cannot' makes denial indirect; targets the factive presupposition" }

-- ════════════════════════════════════════════════════
-- § Implicature Denial (§2.2D)
-- ════════════════════════════════════════════════════

/-- Scalar implicature denial: "possible" implicates "not necessary."
    §2.2, ex. 11 / §2.4, ex. 29b.

    "Possible" literally means ◇p; the scalar implicature is ¬□p (not
    necessary). The correction "it is necessary" retracts the implicature
    while preserving the literal meaning (□p entails ◇p). -/
def possible_necessary : DenialDatum :=
  { assertion := "It is possible that the pope is right"
  , denial := "It is not POSSIBLE"
  , correction := "It is NECESSARY that the pope is right"
  , denialType := .implicature
  , retractedContent := "Not necessary (scalar implicature of 'possible')"
  , survivingContent := "It is possible (= at least possible; necessity entails possibility)"
  , exampleNum := "29b" }

/-- Scalar implicature denial with "several."
    §2.3, ex. 21.

    "Several" implicates "not all." The correction "all" retracts the
    upper-bound implicature. -/
def several_all : DenialDatum :=
  { assertion := "Johnny ate several cookies"
  , denial := "Johnny did not eat SEVERAL cookies"
  , correction := "He ate them all"
  , denialType := .implicature
  , retractedContent := "Not all (scalar implicature of 'several')"
  , survivingContent := "Johnny ate cookies (at least several)"
  , exampleNum := "21" }

/-- Gradable adjective implicature denial: "good" implicates "not excellent."
    §2.2, ex. 12. -/
def good_excellent : DenialDatum :=
  { assertion := "That haggis is good"
  , denial := "That haggis is not good"
  , correction := "It is excellent"
  , denialType := .implicature
  , retractedContent := "Not excellent (scalar implicature of 'good')"
  , survivingContent := "The haggis is at least good"
  , exampleNum := "12" }

-- ════════════════════════════════════════════════════
-- § Connotation / Register Denial (§2.2E → imp layer)
-- ════════════════════════════════════════════════════

/-- Connotation denial: "lady" connotes a social role beyond "woman/wife."
    §2.2, ex. 13. -/
def lady_wife : DenialDatum :=
  { assertion := "That was a lady I kissed last night"
  , denial := "That wasn't a lady I kissed last night"
  , correction := "It was my wife"
  , denialType := .implicature
  , retractedContent := "Social role / formality connotation of 'lady'"
  , survivingContent := "The speaker kissed a woman last night"
  , exampleNum := "13"
  , notes := "Category E: connotation/register denial, mapped to imp layer" }

/-- Register denial: "steed" connotes formality/literary register.
    §2.2, ex. 14. -/
def steed_horse : DenialDatum :=
  { assertion := "That is a steed"
  , denial := "That is not a steed"
  , correction := "It's a horse"
  , denialType := .implicature
  , retractedContent := "Literary/formal register (connotation of 'steed')"
  , survivingContent := "That is an equine animal"
  , exampleNum := "14"
  , notes := "Category E: register denial, mapped to imp layer" }

-- ════════════════════════════════════════════════════
-- § Denial Ambiguity
-- ════════════════════════════════════════════════════

/-! The same surface negation can correspond to different denial types,
    disambiguated by the correction. The paper's §2.3 example (19)/(20)
    demonstrates this with "still":

- (19) "John does NOT still live in Paris — he did live there but has moved"
  = propositional denial (targets `fr`: "John lives in Paris now")
- (20) "John does NOT still live in Paris — he has never set foot in France"
  = presuppositional denial (targets `pr`: "John lived in Paris before") -/

/-- Propositional reading of "still" denial.
    §2.3, ex. 19. -/
def still_propositional : DenialDatum :=
  { assertion := "John still lives in Paris"
  , denial := "John does NOT still live in Paris"
  , correction := "He did live there but has moved"
  , denialType := .propositional
  , retractedContent := "John lives in Paris now (at-issue)"
  , survivingContent := "John lived in Paris before (presupposition of 'still')"
  , exampleNum := "19" }

/-- Presuppositional reading of "still" denial.
    §2.3, ex. 20. -/
def still_presuppositional : DenialDatum :=
  { assertion := "John still lives in Paris"
  , denial := "John does NOT still live in Paris"
  , correction := "He has never set foot in France"
  , denialType := .presuppositional
  , retractedContent := "John lived in Paris before (presupposition of 'still')"
  , exampleNum := "20" }

/-- Same surface negation, different denial types. -/
theorem still_denial_same_surface :
    still_propositional.denial = still_presuppositional.denial := rfl

/-- But they target different layers. -/
theorem still_denial_different_layers :
    still_propositional.denialType ≠ still_presuppositional.denialType := by
  decide

-- ════════════════════════════════════════════════════
-- § Data Collection
-- ════════════════════════════════════════════════════

def propositionalDenials : List DenialDatum :=
  [maryHappy_positive, maryNotHappy, still_propositional]

def presuppositionalDenials : List DenialDatum :=
  [kingBald_presuppositional, stop_presuppositional, know_presuppositional,
   still_presuppositional]

def implicatureDenials : List DenialDatum :=
  [possible_necessary, several_all, good_excellent, lady_wife, steed_horse]

def allDenialData : List DenialDatum :=
  propositionalDenials ++ presuppositionalDenials ++ implicatureDenials

end Phenomena.Negation.Denial
