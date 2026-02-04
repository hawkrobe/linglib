/-
# Bridging Anaphora: Empirical Data

Theory-neutral data on bridging anaphora (associative anaphora, indirect anaphora).

## The Phenomenon

Bridging occurs when a definite description refers to an entity that is
inferentially related to a previously mentioned antecedent, rather than
being coreferent with it.

"I saw a bicycle yesterday. The seat was broken."
- "the seat" is NOT coreferent with "a bicycle"
- But "the seat" is inferentially accessible via part-whole relation

## Two Types of Bridging (Clark 1975, Asher & Lascarides 1998)

1. **Part-whole bridging**: The bridged entity is a part of the antecedent
   - "a bicycle" → "the seat" (seat is part of bicycle)
   - Mediated by uniqueness (there's typically one seat per bicycle)

2. **Relational bridging**: The bridged entity is relationally connected
   - "a book" → "the author" (author is the one who wrote it)
   - Mediated by familiarity (the author must be contextually salient)

## Cross-Linguistic Variation (Ahn & Zhu 2025)

Mandarin vs English contrast in bridging:
- **Mandarin bare nouns**: Accept both bridging types freely
- **Mandarin *na*+CL**: Accept both bridging types (relationalizing operator)
- **English demonstratives**: Degraded in bridging contexts

## References

- Clark, H. (1975). Bridging. Theoretical Issues in Natural Language Processing.
- Asher, N. & Lascarides, A. (1998). Bridging. Journal of Semantics.
- Ahn, D. & Zhu, Y. (2025). A bridge to definiteness. Forthcoming.
- Prince, E. (1981). Toward a taxonomy of given-new information.
-/

namespace Phenomena.Anaphora.Bridging

-- Data Structure

/-- Felicity judgment for bridging examples -/
inductive Felicity where
  | ok       -- Fully acceptable
  | marginal -- Somewhat degraded
  | odd      -- Clearly infelicitous
  deriving DecidableEq, Repr, BEq

/-- Type of bridging relation -/
inductive BridgingType where
  /-- Part-whole: bridged entity is part of antecedent -/
  | partWhole
  /-- Relational: bridged entity is relationally connected (author, mother, etc.) -/
  | relational
  deriving DecidableEq, Repr, BEq

/-- Definite form used in the bridging context -/
inductive DefiniteForm where
  /-- English definite article "the" -/
  | theArticle
  /-- English demonstrative "that" -/
  | thatDem
  /-- Mandarin bare noun -/
  | mandarinBare
  /-- Mandarin demonstrative na + classifier -/
  | mandarinNaCl
  deriving DecidableEq, Repr, BEq

/-- A bridging anaphora datum -/
structure BridgingDatum where
  /-- The full sentence/discourse -/
  sentence : String
  /-- The antecedent NP -/
  antecedent : String
  /-- The bridged definite NP -/
  bridged : String
  /-- The bridging relation -/
  bridgingType : BridgingType
  /-- Form of the definite (the, that, bare, na+CL) -/
  definiteForm : DefiniteForm
  /-- Language -/
  language : String
  /-- Felicity judgment -/
  felicity : Felicity := .ok
  /-- Notes -/
  notes : String := ""
  /-- Source -/
  source : String := ""

-- English Part-Whole Bridging

/-- English "the" in part-whole bridging: Good -/
def englishPartWholeThe : BridgingDatum :=
  { sentence := "I saw a bicycle yesterday. The seat was broken."
  , antecedent := "a bicycle"
  , bridged := "the seat"
  , bridgingType := .partWhole
  , definiteForm := .theArticle
  , language := "English"
  , felicity := .ok
  , notes := "Standard bridging with 'the' - fully acceptable"
  , source := "Clark 1975" }

/-- English "that" in part-whole bridging: Degraded -/
def englishPartWholeThat : BridgingDatum :=
  { sentence := "?I saw a bicycle yesterday. That seat was broken."
  , antecedent := "a bicycle"
  , bridged := "that seat"
  , bridgingType := .partWhole
  , definiteForm := .thatDem
  , language := "English"
  , felicity := .odd
  , notes := "Demonstrative 'that' degraded in bridging - requires familiarity"
  , source := "Ahn & Zhu 2025" }

-- English Relational Bridging

/-- English "the" in relational bridging: Good -/
def englishRelationalThe : BridgingDatum :=
  { sentence := "I read a book yesterday. The author was brilliant."
  , antecedent := "a book"
  , bridged := "the author"
  , bridgingType := .relational
  , definiteForm := .theArticle
  , language := "English"
  , felicity := .ok
  , notes := "Relational bridging with 'the'"
  , source := "Asher & Lascarides 1998" }

/-- English "that" in relational bridging: Degraded -/
def englishRelationalThat : BridgingDatum :=
  { sentence := "?I read a book yesterday. That author was brilliant."
  , antecedent := "a book"
  , bridged := "that author"
  , bridgingType := .relational
  , definiteForm := .thatDem
  , language := "English"
  , felicity := .odd
  , notes := "Demonstrative 'that' degraded in bridging"
  , source := "Ahn & Zhu 2025" }

-- Mandarin Part-Whole Bridging

/-- Mandarin bare noun in part-whole bridging: Good -/
def mandarinPartWholeBare : BridgingDatum :=
  { sentence := "我昨天看见了一辆车。座椅坏了。"
  , antecedent := "一辆车 (a car)"
  , bridged := "座椅 (seat)"
  , bridgingType := .partWhole
  , definiteForm := .mandarinBare
  , language := "Mandarin"
  , felicity := .ok
  , notes := "Bare noun freely bridges in Mandarin"
  , source := "Ahn & Zhu 2025" }

/-- Mandarin na+CL in part-whole bridging: Good -/
def mandarinPartWholeNa : BridgingDatum :=
  { sentence := "我昨天看见了一辆车。那个座椅坏了。"
  , antecedent := "一辆车 (a car)"
  , bridged := "那个座椅 (na-CL seat)"
  , bridgingType := .partWhole
  , definiteForm := .mandarinNaCl
  , language := "Mandarin"
  , felicity := .ok
  , notes := "na+CL also good in part-whole bridging"
  , source := "Ahn & Zhu 2025" }

-- Mandarin Relational Bridging

/-- Mandarin bare noun in relational bridging: Good -/
def mandarinRelationalBare : BridgingDatum :=
  { sentence := "我昨天读了一本书。作者很有名。"
  , antecedent := "一本书 (a book)"
  , bridged := "作者 (author)"
  , bridgingType := .relational
  , definiteForm := .mandarinBare
  , language := "Mandarin"
  , felicity := .ok
  , notes := "Bare noun bridges relationally"
  , source := "Ahn & Zhu 2025" }

/-- Mandarin na+CL in relational bridging: Good -/
def mandarinRelationalNa : BridgingDatum :=
  { sentence := "我昨天读了一本书。那个作者很有名。"
  , antecedent := "一本书 (a book)"
  , bridged := "那个作者 (na-CL author)"
  , bridgingType := .relational
  , definiteForm := .mandarinNaCl
  , language := "Mandarin"
  , felicity := .ok
  , notes := "na+CL as relationalizing operator (Ahn & Zhu analysis)"
  , source := "Ahn & Zhu 2025" }

-- Ahn & Zhu (2025) Experimental Items

/-- Ahn & Zhu Experiment 1: Part-whole condition -/
def ahnZhuExp1PartWhole : BridgingDatum :=
  { sentence := "Mary bought a car. The steering wheel was too small."
  , antecedent := "a car"
  , bridged := "the steering wheel"
  , bridgingType := .partWhole
  , definiteForm := .theArticle
  , language := "English"
  , felicity := .ok
  , notes := "Experiment 1: Part-whole bridging baseline"
  , source := "Ahn & Zhu 2025, Experiment 1" }

/-- Ahn & Zhu Experiment 1: Relational condition -/
def ahnZhuExp1Relational : BridgingDatum :=
  { sentence := "Mary bought a book. The author was very famous."
  , antecedent := "a book"
  , bridged := "the author"
  , bridgingType := .relational
  , definiteForm := .theArticle
  , language := "English"
  , felicity := .ok
  , notes := "Experiment 1: Relational bridging baseline"
  , source := "Ahn & Zhu 2025, Experiment 1" }

-- Uniqueness vs Familiarity Presupposition Types

/-- Presupposition type for definites (Ahn & Zhu's key distinction) -/
inductive PresupType where
  /-- Uniqueness: there is a unique entity satisfying the description -/
  | uniqueness
  /-- Familiarity: the entity is already salient/familiar in discourse -/
  | familiarity
  deriving DecidableEq, Repr, BEq

/-- Part-whole bridging is mediated by uniqueness -/
def partWholePresupType : PresupType := .uniqueness

/-- Relational bridging is mediated by familiarity -/
def relationalPresupType : PresupType := .familiarity

-- Collected Data

/-- English bridging examples -/
def englishBridgingData : List BridgingDatum :=
  [ englishPartWholeThe
  , englishPartWholeThat
  , englishRelationalThe
  , englishRelationalThat
  , ahnZhuExp1PartWhole
  , ahnZhuExp1Relational ]

/-- Mandarin bridging examples -/
def mandarinBridgingData : List BridgingDatum :=
  [ mandarinPartWholeBare
  , mandarinPartWholeNa
  , mandarinRelationalBare
  , mandarinRelationalNa ]

/-- All bridging data -/
def allBridgingData : List BridgingDatum :=
  englishBridgingData ++ mandarinBridgingData

-- Summary

/-!
## What This Module Provides

### Data Types
- `BridgingType`: Part-whole vs relational bridging
- `DefiniteForm`: English the/that vs Mandarin bare/na+CL
- `PresupType`: Uniqueness vs familiarity presupposition
- `BridgingDatum`: Full bridging example record

### Key Empirical Generalizations (Ahn & Zhu 2025)

1. **English "the"** works for both bridging types
2. **English "that"** is degraded in bridging (requires prior familiarity)
3. **Mandarin bare nouns** work for both bridging types
4. **Mandarin na+CL** works for both bridging types

### Theoretical Insight

Ahn & Zhu propose that:
- Part-whole bridging is mediated by **uniqueness** (the unique seat of the bike)
- Relational bridging is mediated by **familiarity** (the author must be salient)
- Mandarin *na* is a **relationalizing operator** that introduces an external relatum
- English "that" encodes strong familiarity, blocking bridging

### Connection to Other Modules

- `Core.Presupposition`: Presupposition machinery (uniqueness as presup)
- `DynamicSemantics/Core/Basic`: `definedAt` = familiarity condition
- `Fragments/Mandarin/Nouns`: Mandarin NP structure with demonstratives
-/

end Phenomena.Anaphora.Bridging
