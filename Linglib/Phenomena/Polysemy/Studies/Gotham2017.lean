import Linglib.Core.Lexical.Word
import Linglib.Theories.Semantics.TypeTheoretic.Copredication

/-!
# Copredication: @cite{gotham-2017}'s account + bridge data
@cite{asher-2011} @cite{gotham-2017} @cite{pustejovsky-1995}
@cite{chatzikyriakidis-etal-2025}

Copredication is the phenomenon where predicates selecting different
semantic aspects apply to the same polysemous noun phrase ("the book
is heavy and interesting"). This study file owns the canonical
empirical data (formerly `Polysemy/Data.lean`, dissolved per the
provenance-tracking policy) and proves bridge theorems connecting
the data to the TTR dot-type infrastructure
(@cite{chatzikyriakidis-etal-2025}).

## Empirical phenomena

1. **Book copredication**: "The book is heavy and interesting" —
   *heavy* selects physical object, *interesting* selects
   informational content.
2. **Counting under copredication**: "Three books were mastered and
   burned" — ambiguous between counting physical volumes vs.
   informational contents.
3. **Lunch copredication**: "The lunch was delicious but took
   forever" — *delicious* selects food, *took forever* selects event.

## Bridge theorems

1. Copredication is well-typed via meet-type projection
2. Different individuation criteria yield different counts
3. The counting puzzle from @cite{gotham-2017} is reproduced

-/

namespace Phenomena.Polysemy

-- ============================================================
-- Empirical data (was `Polysemy/Data.lean`, inlined 0.230.270)
-- ============================================================

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
@cite{gotham-2017}: physical count = 3, informational count = 2 (if one novel
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


namespace Bridge

open Semantics.TypeTheoretic

/-! ## Book as a dot type -/

/-- Physical-object aspect of a book. -/
structure PhysObj where
  weight : Nat  -- grams
  deriving Repr, DecidableEq

/-- Informational-content aspect of a book. -/
structure Info where
  title : String
  deriving Repr, DecidableEq

/-- "book" as a dot type: physical × informational, individuated physically.
@cite{gotham-2017}: the default criterion for "book" counts physical volumes. -/
def bookDot : DotType PhysObj Info := DotType.byAspect₁

/-- "heavy": a predicate on the physical aspect. -/
def heavy (threshold : Nat) (p : PhysObj) : Prop := p.weight > threshold

/-- "interesting": a predicate on the informational aspect. -/
def interesting (_i : Info) : Prop := True  -- stipulated for the example

/-- "The book is heavy and interesting" is well-typed copredication.
This is the formal content of bookHeavyInteresting from Data.lean. -/
theorem book_heavy_and_interesting (b : PhysObj × Info) (h : b.1.weight > 500) :
    copredicate (heavy 500) interesting b :=
  ⟨h, trivial⟩

/-! ## Counting under copredication

Model the scenario from @cite{gotham-2017} / @cite{chatzikyriakidis-etal-2025} §3:
Two physical copies of one novel, plus one copy of a different novel.
Physical count = 3, informational count = 2. -/

/-- Three books: two copies of "Hamlet" and one of "Ulysses". -/
def hamlet1 : PhysObj × Info := ⟨⟨200⟩, ⟨"Hamlet"⟩⟩
def hamlet2 : PhysObj × Info := ⟨⟨210⟩, ⟨"Hamlet"⟩⟩  -- different physical copy
def ulysses : PhysObj × Info := ⟨⟨400⟩, ⟨"Ulysses"⟩⟩

def threeBooks : List (PhysObj × Info) := [hamlet1, hamlet2, ulysses]

/-- Physical individuation: count by PhysObj (weight distinguishes copies). -/
instance : ∀ x y, Decidable (bookDot.individuation.r x y) :=
  λ x y => inferInstanceAs (Decidable (x.1 = y.1))

/-- Informational individuation: count by Info (title). -/
def infoDot : DotType PhysObj Info := DotType.byAspect₂

instance : ∀ x y, Decidable (infoDot.individuation.r x y) :=
  λ x y => inferInstanceAs (Decidable (x.2 = y.2))

/-- Under physical individuation: 3 distinct objects. -/
theorem physical_count : countDistinct bookDot.individuation threeBooks = 3 := by
  native_decide

/-- Under informational individuation: 2 distinct contents. -/
theorem informational_count : countDistinct infoDot.individuation threeBooks = 2 := by
  native_decide

/-- The counting datum from Data.lean is reproduced.
This bridges the empirical datum to the TTR formalization. -/
theorem counting_matches_datum :
    countDistinct bookDot.individuation threeBooks = masteredAndBurned.physicalCount ∧
    countDistinct infoDot.individuation threeBooks = masteredAndBurned.informationalCount := by
  exact ⟨physical_count, informational_count⟩

/-- Counts diverge, as predicted by the datum. -/
theorem counts_diverge :
    countDistinct bookDot.individuation threeBooks ≠
    countDistinct infoDot.individuation threeBooks := by
  native_decide

end Bridge

end Phenomena.Polysemy
