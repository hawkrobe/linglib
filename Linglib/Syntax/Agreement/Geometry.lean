import Linglib.Core.Data.Fintype.Order
import Mathlib.Data.Fintype.Card
import Mathlib.Order.SuccPred.Basic
import Linglib.Core.Order.UpperLower.Finset
import Linglib.Syntax.Person.Basic
import Linglib.Syntax.Number.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# The φ-feature geometry

The morphosyntactic feature geometry of pronouns: monovalent person, number,
and class features organized as a dependency tree under a root Referring
Expression node, with Participant (Speaker, Addressee) and Individuation
(Group, Minimal with its dependent Augmented, and Class) as the organizing
nodes, with the collective first-person node Multispeaker below Speaker. A
feature appears only together with the nodes it depends on, so the
feature content of a pronoun is a lower set of the dominance order; markedness
is node count; and an organizing node with no dependent receives its default
daughter — Speaker, Minimal, Inanimate — by rule. Person and number cells are
assigned their geometries, the contrastive Minimal node being present only in
inventories that activate it. The tree is a feature geometry in the sense of
[clements-1985] and [sagey-1986] whose nodes are the features themselves, a
rooted tree in mathlib's terms: dominance the partial order, the root `⊥` and
the parent `Order.pred`.

## Main definitions

* `Node`, `Node.ancestors` and `Node.pred`, and dominance `≤`, the tree of the parent map
  with the root as `⊥`; `Node.below` is the content a node brings with it.
* `Node.defaultDependent?`, `fillDefaults`: the default daughters and their fill-in.
* `personNodes`, `numberNodes`, `cell`: the geometries of person, of number, and of
  a person–number cell, relative to an active inventory.
* `Licenses`: an inventory licenses a cell when the cell's geometry lies within it.

## Main results

* `cell_isLowerSet`: every assigned geometry is a lower set.
* `fillDefaults_isLowerSet`: default fill-in preserves lower sets.

## References

* [H. Harley and E. Ritter, *Person and number in pronouns: A feature-geometric
  analysis*][harley-ritter-2002]
* [H. Harley, *Hug a tree*][harley-1994]
* [M. McGinnis, *Agree and Fission in Georgian plurals*][mcginnis-2013]
* [G. N. Clements, *The geometry of phonological features*][clements-1985]
* [E. Sagey, *The representation of features and relations in non-linear
  phonology*][sagey-1986]
-/

namespace Phi.Geometry

/-- The nodes of the geometry: the root, the three organizing nodes, and
their dependents. -/
inductive Node where
  /-- The root: every pronoun; bare, the third person. -/
  | referringExpression
  /-- Discourse participant: first and second person. -/
  | participant
  /-- Includes the speaker; Participant's default dependent. -/
  | speaker
  /-- Includes the speaker and others: a collective first person, expressing
  first-person plurality through person where number does not. -/
  | multispeaker
  /-- Includes the addressee. -/
  | addressee
  /-- Number and class. -/
  | individuation
  /-- More than one: plural. -/
  | group
  /-- A minimal set; Individuation's default dependent, singular alone and dual
  together with Group. -/
  | minimal
  /-- A minimal group and more: paucal or trial. -/
  | augmented
  /-- Gender and class. -/
  | nounClass
  /-- Animate. -/
  | animate
  /-- Inanimate or neuter; Class's default dependent. -/
  | inanimate
  /-- Feminine. -/
  | feminine
  /-- Masculine. -/
  | masculine
  deriving DecidableEq, Repr, Fintype

namespace Node

/-- The nodes a node depends on, nearest first: the tree as the path from each node to
the root. -/
def ancestors : Node → List Node
  | .referringExpression => []
  | .participant | .individuation => [.referringExpression]
  | .speaker | .addressee => [.participant, .referringExpression]
  | .multispeaker => [.speaker, .participant, .referringExpression]
  | .group | .minimal | .nounClass => [.individuation, .referringExpression]
  | .augmented => [.minimal, .individuation, .referringExpression]
  | .animate | .inanimate => [.nounClass, .individuation, .referringExpression]
  | .feminine | .masculine => [.animate, .nounClass, .individuation, .referringExpression]

/-- The node a node depends on directly, the root fixed. -/
def pred (n : Node) : Node := n.ancestors.head?.getD n

/-- A node with its ancestors: the iterates of `pred`. -/
def up (n : Node) : Finset Node := (Finset.range (Fintype.card Node)).image (pred^[·] n)

/-- Dominance: `a ≤ b` when `b` depends on `a`. -/
instance : PartialOrder Node := PartialOrder.lift up (by decide)

instance : DecidableLE Node := fun a b ↦ inferInstanceAs (Decidable (up a ⊆ up b))

instance : DecidableLT Node := decidableLTOfDecidableLE

/-- The root dominates every node. -/
instance : OrderBot Node where
  bot := .referringExpression
  bot_le := by decide

/-- The parent as the predecessor. -/
instance : PredOrder Node where
  pred := pred
  pred_le := by decide
  min_of_le_pred := by decide
  le_pred_of_lt := by decide

instance : LocallyFiniteOrder Node := Fintype.toLocallyFiniteOrder

/-- Dominance is dependence: `a ≤ b` when `a` is `b` or a node `b` depends on. -/
theorem le_iff : ∀ a b : Node, a ≤ b ↔ a = b ∨ a ∈ b.ancestors := by decide

/-- The nodes a node depends on, itself included and the root excluded, from the root down:
the content a privative feature brings with it. -/
def below (n : Node) : List Node := ((n :: n.ancestors).filter (· ≠ ⊥)).reverse

theorem mem_below : ∀ {a n : Node}, a ∈ below n ↔ ⊥ < a ∧ a ≤ n := by decide

theorem toFinset_below : ∀ n : Node, (below n).toFinset = Finset.Ioc ⊥ n := by decide

/-- A dependent brings more than what it depends on. -/
theorem below_subset_below : ∀ {a b : Node}, a ≤ b → below a ⊆ below b := by decide

/-- The default daughter of an organizing node: Speaker, Minimal, Inanimate. -/
def defaultDependent? : Node → Option Node
  | .participant => some .speaker
  | .individuation => some .minimal
  | .nounClass => some .inanimate
  | _ => none

end Node

/-! ### Default fill-in -/

/-- Fill in defaults: an organizing node present without any dependent
receives its default daughter. The node count of a geometry is taken before
fill-in. -/
def fillDefaults (s : Finset Node) : Finset Node :=
  s ∪ Finset.univ.filter fun d => ∃ o ∈ s, o.defaultDependent? = some d ∧ ∀ c ∈ s, ¬ o < c

theorem subset_fillDefaults (s : Finset Node) : s ⊆ fillDefaults s := Finset.subset_union_left

theorem fillDefaults_isLowerSet {s : Finset Node} (hs : IsLowerSet (↑s : Set Node)) :
    IsLowerSet (↑(fillDefaults s) : Set Node) := by
  intro b a hab hb
  simp only [fillDefaults, Finset.mem_coe, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and] at hb ⊢
  rcases hb with hb | ⟨o, ho, hod, hno⟩
  · exact .inl (hs hab hb)
  · have key : ∀ o d x : Node, o.defaultDependent? = some d → x ≤ d → x = d ∨ x ≤ o := by decide
    rcases key o b a hod hab with rfl | hao
    · exact .inr ⟨o, ho, hod, hno⟩
    · exact .inl (hs hao ho)

/-! ### Person and number cells -/

/-- The person geometries: first person is the bare Participant node (Speaker
by default), exclusive Participant with Speaker, inclusive Participant with
Speaker and Addressee, second Participant with Addressee, third nothing; the
impersonal has no geometry. -/
def personNodes : Person → Option (Finset Node)
  | .first => some {.participant}
  | .firstExclusive => some {.participant, .speaker}
  | .firstInclusive => some {.participant, .speaker, .addressee}
  | .second => some {.participant, .addressee}
  | .third => some ∅
  | .zero => none

/-- The number geometries, relative to an active inventory: singular is the bare
Individuation node, with Minimal where the inventory activates it
contrastively; plural adds Group; dual Minimal with Group; paucal and trial add
Augmented; the number-neutral value is nothing. Greater numbers and the
minimal–augmented values have no geometry. -/
def numberNodes (active : Finset Node) : Number → Option (Finset Node)
  | .singular =>
    some (if Node.minimal ∈ active then {.individuation, .minimal} else {.individuation})
  | .plural => some {.individuation, .group}
  | .dual => some {.individuation, .minimal, .group}
  | .trial | .paucal => some {.individuation, .minimal, .group, .augmented}
  | .general => some ∅
  | _ => none

/-- The geometry of a person–number cell: the root with the person and number
nodes, the latter only in an inventory that activates Individuation. -/
def cell (active : Finset Node) (p : Person) (n : Number) : Option (Finset Node) := do
  let ps ← personNodes p
  let ns ← if Node.individuation ∈ active then numberNodes active n else pure ∅
  pure (insert .referringExpression (ps ∪ ns))

/-- An inventory licenses a cell when the cell's geometry lies within it. -/
def Licenses (active : Finset Node) (p : Person) (n : Number) : Prop :=
  ∃ g ∈ cell active p n, g ⊆ active

instance (active : Finset Node) (p : Person) (n : Number) : Decidable (Licenses active p n) :=
  inferInstanceAs (Decidable (∃ g ∈ cell active p n, g ⊆ active))

theorem personNodes_isLowerSet {p : Person} {ps : Finset Node} (h : personNodes p = some ps) :
    IsLowerSet (↑(insert ⊥ ps) : Set Node) := by
  cases p <;> simp [personNodes] at h <;> subst h <;> decide

theorem numberNodes_isLowerSet {active : Finset Node} {n : Number} {ns : Finset Node}
    (h : numberNodes active n = some ns) : IsLowerSet (↑(insert ⊥ ns) : Set Node) := by
  cases n <;> simp [numberNodes] at h <;> (try split_ifs at h) <;> subst h <;> decide

/-- Every assigned geometry is a lower set. -/
theorem cell_isLowerSet {active : Finset Node} {p : Person} {n : Number} {g : Finset Node}
    (h : cell active p n = some g) : IsLowerSet (↑g : Set Node) := by
  simp only [cell, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨ps, hps, h⟩ := h
  have key : ∀ ns : Finset Node, IsLowerSet (↑(insert ⊥ ns) : Set Node) →
      IsLowerSet (↑(insert Node.referringExpression (ps ∪ ns)) : Set Node) := fun ns hns => by
    rw [show insert Node.referringExpression (ps ∪ ns) = insert ⊥ ps ∪ insert ⊥ ns by
      rw [Finset.insert_union, Finset.union_insert, Finset.insert_idem]; rfl, Finset.coe_union]
    exact (personNodes_isLowerSet hps).union hns
  split_ifs at h <;> obtain ⟨ns, hns, hg⟩ := Option.bind_eq_some_iff.1 h <;> cases hg
  · exact key ns (numberNodes_isLowerSet hns)
  · cases hns; exact key ∅ (by decide)

end Phi.Geometry
