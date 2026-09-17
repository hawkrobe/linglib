import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Positions of the Agreement Hierarchy

This file defines the four positions of Corbett's Agreement Hierarchy, the attributive
modifier, the predicate, the relative pronoun and the personal pronoun, as a chain with the
attributive on top.

Every agreement target agrees at one of the four positions, a finite verb at the predicate,
and the hierarchy predicts that semantic agreement is increasingly likely from the attributive
to the personal pronoun; `Syntax/Agreement/Hierarchy.lean` states that prediction over the
chain. Comrie's Predicate Hierarchy, which grades the verb, participle, adjective and noun
within the predicate, is `Corbett2000.PredicateTarget`.

## References

* [corbett-1979] — the Agreement Hierarchy
* [corbett-1991] — the hierarchy applied to gender, chapter 8
* [corbett-2006] — the standard monograph on agreement
-/

namespace Agreement

/-- A position of the Agreement Hierarchy ([corbett-1979]). -/
inductive Position where
  /-- The attributive modifier (French *un bon livre*). -/
  | attributive
  /-- The predicate, a finite verb or a predicate adjective (Russian *kniga interesna*). -/
  | predicate
  /-- The relative pronoun (German *der ~ die ~ das*). -/
  | relativePronoun
  /-- The personal pronoun (English *he ~ she ~ it*). -/
  | personalPronoun
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Position

/-- The place of a position in the chain, the attributive highest. -/
def rank : Position → ℕ
  | .attributive => 3
  | .predicate => 2
  | .relativePronoun => 1
  | .personalPronoun => 0

theorem rank_injective : Function.Injective rank := by decide

/-- The Agreement Hierarchy as a chain:
`personalPronoun < relativePronoun < predicate < attributive`. -/
instance : LinearOrder Position := LinearOrder.lift' rank rank_injective

end Position

end Agreement
