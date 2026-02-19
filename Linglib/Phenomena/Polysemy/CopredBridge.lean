import Linglib.Phenomena.Polysemy.Data
import Linglib.Theories.Semantics.TypeTheoretic.Copredication

/-!
# Copredication Bridge @cite{chatzikyriakidis-etal-2025}

Bridge theorems connecting copredication data to the TTR dot-type
infrastructure. We model the "book" examples from §3 of
Chatzikyriakidis et al. (2025) and prove that:

1. Copredication is well-typed via meet-type projection
2. Different individuation criteria yield different counts
3. The counting puzzle from Gotham (2017) is reproduced

## References

- Chatzikyriakidis et al. (2025). Types and the Structure of Meaning. §3.
- Gotham, M. (2017). Composing Criteria of Individuation in Copredication.
-/

namespace Phenomena.Polysemy.Bridge

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
Gotham (2017): the default criterion for "book" counts physical volumes. -/
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

Model the scenario from Gotham (2017) / Chatzikyriakidis et al. (2025) §3:
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

end Phenomena.Polysemy.Bridge
