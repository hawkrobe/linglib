import Linglib.Core.Basic

/-!
# Copredication Data

Empirical judgments for copredication — the phenomenon where predicates
selecting different semantic aspects apply to the same polysemous noun phrase.

## Phenomena

1. **Book copredication**: "The book is heavy and interesting"
   — heavy selects physical object, interesting selects informational content.

2. **Counting under copredication**: "Three books were mastered and burned"
   — ambiguous between counting physical volumes vs. informational contents.

3. **Lunch copredication**: "The lunch was delicious but took forever"
   — delicious selects food, took forever selects event.

## References

- Pustejovsky, J. (1995). The Generative Lexicon. MIT Press.
- Asher, N. (2011). Lexical Meaning in Context. CUP.
- Chatzikyriakidis et al. (2025). Types and the Structure of Meaning. §3.
- Gotham, M. (2017). Composing Criteria of Individuation in Copredication.
  Journal of Semantics 34(2): 331–371.
-/

namespace Phenomena.Polysemy

/-- Acceptability judgment for copredication examples. -/
inductive Acceptability where
  | acceptable
  | marginal
  | unacceptable
  deriving Repr, DecidableEq

/-- A copredication datum: a sentence with two predicates on different aspects. -/
structure CopredDatum where
  /-- The sentence -/
  sentence : String
  /-- The polysemous noun -/
  noun : String
  /-- The aspect selected by the first predicate -/
  aspect₁ : String
  /-- The aspect selected by the second predicate -/
  aspect₂ : String
  /-- Acceptability judgment -/
  judgment : Acceptability
  deriving Repr

/-- The canonical book copredication example. -/
def bookHeavyInteresting : CopredDatum :=
  { sentence := "The book is heavy and interesting"
    noun := "book"
    aspect₁ := "physical"
    aspect₂ := "informational"
    judgment := .acceptable }

/-- Lunch copredication: food + event aspects. -/
def lunchDeliciousLong : CopredDatum :=
  { sentence := "The lunch was delicious but took forever"
    noun := "lunch"
    aspect₁ := "food"
    aspect₂ := "event"
    judgment := .acceptable }

/-- Newspaper copredication: organization + physical aspects. -/
def newspaperFiredTore : CopredDatum :=
  { sentence := "The newspaper fired the editor and was thrown in the bin"
    noun := "newspaper"
    aspect₁ := "organization"
    aspect₂ := "physical"
    judgment := .acceptable }

/-- A counting-under-copredication datum. -/
structure CountingDatum where
  /-- The sentence -/
  sentence : String
  /-- The polysemous noun -/
  noun : String
  /-- Count under physical individuation -/
  physicalCount : Nat
  /-- Count under informational individuation -/
  informationalCount : Nat
  /-- Whether the two counts diverge -/
  countsDiverge : Bool
  deriving Repr

/-- "Three books were mastered and burned" with two copies of the same novel.
Gotham (2017): physical count = 3, informational count = 2 (if one novel
has two copies). -/
def masteredAndBurned : CountingDatum :=
  { sentence := "Three books were mastered and burned"
    noun := "book"
    physicalCount := 3
    informationalCount := 2
    countsDiverge := true }

/-- All copredication data points. -/
def copredData : List CopredDatum :=
  [bookHeavyInteresting, lunchDeliciousLong, newspaperFiredTore]

/-- All copredication data points are acceptable. -/
theorem all_copred_acceptable :
    ∀ d ∈ copredData, d.judgment = .acceptable := by
  intro d hd
  simp [copredData] at hd
  rcases hd with rfl | rfl | rfl <;> rfl

end Phenomena.Polysemy
