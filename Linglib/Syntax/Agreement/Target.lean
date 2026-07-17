import Mathlib.Data.Sum.Order
import Mathlib.Tactic.DeriveFintype

/-!
# Agreement targets

This file defines the morphosyntactic positions where agreement surfaces,
ordered by Corbett's Agreement Hierarchy: attributive > predicate >
relative pronoun > personal pronoun, with semantic (rather than syntactic)
agreement increasingly likely from left to right.

## Main declarations

* `Agreement.Target`: the four hierarchy positions, plus `verb` for
  languages with verbal gender/number agreement.
* `Agreement.Target.hierarchyRank`: position on the hierarchy (higher =
  more syntactic); `none` for `verb`.
* The `PartialOrder` instance: the four positions form a chain; `verb` is
  comparable only to itself.

## Implementation notes

`verb` is not a position of Corbett's hierarchy, and no ranking of it is
encoded. [wechsler-zlatic-2000] classify verbs with the pronouns as
INDEX-readers without ranking the INDEX-readers among themselves
(`WechslerZlatic2000.indexReaders_lowerSet`), and [comrie-1975]'s Predicate
Hierarchy grades semantic-agreement likelihood among predicate
sub-positions (`Corbett2000.PredicateTarget`); the two classifications are
orthogonal. Hence the order is partial rather than linear.

## References

* [corbett-1979] — the Agreement Hierarchy
* [corbett-1991], ch. 8 — the hierarchy applied to gender
* [corbett-2006] — the standard monograph on agreement
-/

namespace Agreement

/-- A morphosyntactic target where agreement can surface: the four positions
    of the Agreement Hierarchy ([corbett-1979]), plus `verb` for verbal
    gender/number agreement (off the hierarchy — see the module docstring). -/
inductive Target where
  /-- Attributive adjective (e.g. French *un bon livre*). -/
  | attributive
  /-- Predicate adjective/verb (e.g. Russian *kniga interesna*). -/
  | predicate
  /-- Relative pronoun (e.g. German *der/die/das*). -/
  | relativePronoun
  /-- Personal pronoun (e.g. English *he/she/it*). -/
  | personalPronoun
  /-- Verb (e.g. Hindi *laRkaa aayaa* vs *laRkii aayii*). A label only,
      not a fifth hierarchy position: `hierarchyRank` is `none`. -/
  | verb
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Target

/-- Position on the four-point Agreement Hierarchy, higher = more syntactic
    (more likely to show syntactic agreement); `none` for `verb`, which is
    off the hierarchy. -/
def hierarchyRank : Target → Option ℕ
  | .attributive     => some 3
  | .predicate       => some 2
  | .relativePronoun => some 1
  | .personalPronoun => some 0
  | .verb            => none

/-- Coordinate of a target in the disjoint sum `ℕ ⊕ Unit`: chain positions
    to `Sum.inl` via `hierarchyRank`, `verb` to the isolated point. -/
private def hierarchyCoord (t : Target) : ℕ ⊕ Unit :=
  t.hierarchyRank.elim (.inr ()) .inl

-- [UPSTREAM] Mathlib has the disjoint-sum order (`Sum.instLESum`) but no
-- decidability instance for it.
instance {α β : Type*} [LE α] [LE β] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    [DecidableRel ((· ≤ ·) : β → β → Prop)] :
    DecidableRel ((· ≤ ·) : α ⊕ β → α ⊕ β → Prop)
  | .inl a, .inl b => decidable_of_iff (a ≤ b) Sum.inl_le_inl_iff.symm
  | .inl _, .inr _ => .isFalse Sum.not_inl_le_inr
  | .inr _, .inl _ => .isFalse Sum.not_inr_le_inl
  | .inr a, .inr b => decidable_of_iff (a ≤ b) Sum.inr_le_inr_iff.symm

/-- The Agreement Hierarchy as a partial order, lifted along
    `hierarchyCoord`: the four canonical positions form a chain (so
    `personalPronoun ≤ attributive`); `verb`, off the hierarchy, is
    comparable only to itself. -/
instance : PartialOrder Target :=
  .lift hierarchyCoord (by decide)

instance : DecidableRel ((· ≤ ·) : Target → Target → Prop) :=
  fun t u => inferInstanceAs (Decidable (hierarchyCoord t ≤ hierarchyCoord u))

end Target

end Agreement
