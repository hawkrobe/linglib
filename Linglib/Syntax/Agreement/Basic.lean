import Mathlib.Order.Nat
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

private def HierarchyLE (t u : Target) : Prop :=
  match t.hierarchyRank, u.hierarchyRank with
  | some rt, some ru => rt ≤ ru
  | none, none => True
  | _, _ => False

private instance : DecidableRel HierarchyLE := fun t u => by
  cases t <;> cases u <;> simp only [HierarchyLE, hierarchyRank] <;> infer_instance

/-- The Agreement Hierarchy as a partial order: `t ≤ u` iff both occupy
    hierarchy positions and `t`'s is at most as syntactic as `u`'s (so
    `personalPronoun ≤ attributive`); `verb`, off the hierarchy, is
    comparable only to itself. -/
instance : PartialOrder Target where
  le := HierarchyLE
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel ((· ≤ ·) : Target → Target → Prop) :=
  fun t u => inferInstanceAs (Decidable (HierarchyLE t u))

end Target

end Agreement
