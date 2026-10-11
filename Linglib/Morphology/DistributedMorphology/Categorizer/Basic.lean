module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Data.UnorderedTree.Leaves
public import Linglib.Morphology.DistributedMorphology.Root

/-!
# Categorization

This file defines the categorizing heads n, v and a of Distributed Morphology and the
word-internal structures they build. A categorizer merges with an acategorial root, and a
further categorizer merges with the result, so *to shelve* is [v [n √SHELF]] beside
[n √SHELF] for *shelf*. A word structure is a nonplanar tree whose leaves are roots and
heads.

## Main definitions

* `Categorizer`: the categorizers n, v and a.
* `WordStructure`: word-internal structure over a type of head labels.
* `categorize`, `roots`, `heads`: merger of a head, and the root and head leaves.

## Main results

* `roots_categorize`: categorization leaves the root leaves unchanged.

## References

* [halle-marantz-1993]
* [marantz-1997]
* [harley-2014]
* [embick-marantz-2008]
-/

@[expose] public section

namespace DistributedMorphology

/-! ### The categorizer inventory -/

/-- The categorizing heads, which merge with an acategorial root. -/
inductive Categorizer where
  | n
  | v
  | a
  deriving DecidableEq, Repr, Fintype

/-- There are exactly three categorizers, unlike the infinitely many roots. -/
theorem card_categorizer : Fintype.card Categorizer = 3 := rfl

/-! ### Word-internal structure -/

/-- Word-internal structure over head labels `H`. Its leaves are roots or heads and its internal
vertices are bare. -/
abbrev WordStructure (H : Type*) :=
  UnorderedTree ((Root ⊕ H) ⊕ Unit)

variable {H : Type*}

/-- The structure consisting of a bare root. -/
def ofRoot (r : Root) : WordStructure H :=
  UnorderedTree.leaf (.inl (.inl r))

/-- The structure consisting of a bare head. -/
def ofHead (h : H) : WordStructure H := UnorderedTree.leaf (.inl (.inr h))

/-- The merger of a head `h` with a structure `T`, the configuration [h T]. -/
noncomputable def categorize (h : H) (T : WordStructure H) : WordStructure H :=
  UnorderedTree.node (.inr ()) (ofHead h ::ₘ {T})

/-- The root leaves of a word structure. -/
def roots (T : WordStructure H) : Multiset Root :=
  T.leaves.filterMap fun x => x.getLeft?.bind Sum.getLeft?

/-- The head leaves of a word structure. -/
def heads (T : WordStructure H) : Multiset H :=
  T.leaves.filterMap fun x => x.getLeft?.bind Sum.getRight?

@[simp] theorem roots_ofRoot (r : Root) :
    roots (ofRoot r : WordStructure H) = {r} := rfl

@[simp] theorem roots_ofHead (h : H) :
    roots (ofHead h : WordStructure H) = 0 := rfl

@[simp] theorem heads_ofHead (h : H) :
    heads (ofHead h : WordStructure H) = {h} := rfl

@[simp] theorem heads_ofRoot (r : Root) :
    heads (ofRoot r : WordStructure H) = 0 := rfl

/-- Categorization leaves the root leaves unchanged, so a root keeps its index across
categorization and recategorization, as √HAMMER does in *hammer* and *to hammer*. -/
theorem roots_categorize (h : H) (T : WordStructure H) :
    roots (categorize h T) = roots T := by
  rw [categorize, roots, UnorderedTree.leaves_node_cons, Multiset.filterMap_add,
    show Multiset.filterMap (fun x => x.getLeft?.bind Sum.getLeft?)
      (ofHead h : WordStructure H).leaves
      = (0 : Multiset Root) from rfl]
  simp [roots]

/-- Each categorization adds its head. -/
theorem heads_categorize (h : H) (T : WordStructure H) :
    heads (categorize h T) = h ::ₘ heads T := by
  rw [categorize, heads, UnorderedTree.leaves_node_cons, Multiset.filterMap_add]
  rw [show Multiset.filterMap (fun x => x.getLeft?.bind Sum.getRight?)
      (ofHead h : WordStructure H).leaves = {h} from rfl]
  simp [heads, Multiset.singleton_add]

end DistributedMorphology
