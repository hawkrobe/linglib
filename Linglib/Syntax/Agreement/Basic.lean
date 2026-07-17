import Mathlib.Order.Nat
import Mathlib.Tactic.DeriveFintype

/-!
# Agreement targets [corbett-1979]

`Agreement.Target` enumerates the morphosyntactic positions where agreement
surfaces: the four positions of the Agreement Hierarchy ([corbett-1979];
[corbett-1991] ch. 8; [corbett-2006]) — attributive > predicate > relative
pronoun > personal pronoun, along which the likelihood of *semantic* (rather
than syntactic) agreement increases monotonically from left to right — plus
`verb` for languages with verbal gender/number agreement.

`verb` is a label only: it is not a fifth position of Corbett's hierarchy,
and the literature licenses no ranking for it. [wechsler-zlatic-2000]
classify verbs with the pronouns as INDEX-readers but do not rank the
INDEX-readers among themselves (`WechslerZlatic2000.indexReaders_lowerSet`
needs no such ranking), while [comrie-1975]'s Predicate Hierarchy grades
semantic-agreement *likelihood* within the predicate position (finite verb
least likely; `Corbett2000.PredicateTarget`). Reading INDEX and showing
semantic agreement are orthogonal axes — INDEX features can be lexically
fixed — so the two classifications are not rival rankings of `verb`, and
neither is encoded here. Accordingly the order on `Target` is partial:
`hierarchyRank` places the four canonical positions on a chain (higher =
more syntactic) and leaves `verb` comparable only to itself.

This type is shared by gender typology (`Studies/Corbett1991.lean`) and
number agreement (`Studies/Corbett2000.lean`).
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
