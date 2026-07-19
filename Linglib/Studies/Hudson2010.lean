import Mathlib.Logic.Relation
import Linglib.Syntax.WordGrammar.Inheritance.Basic
import Linglib.Syntax.WordGrammar.Inheritance.Order
import Linglib.Syntax.WordGrammar.Network

open Morphology (Word)

/-!
# Hudson 2010: kinship as an inheritance network [hudson-2010]

The "one network" thesis: Word Grammar models all conceptual knowledge —
linguistic and non-linguistic alike — as a single inheritance network of
isA links and labelled property relations. The kinship system is Hudson's
running non-linguistic example (§3.2 with Fig 3.7, cross-referenced from
§7.2.6 "Syntactic triangles" on p. 160) and serves as the foil for the
syntactic triangle of Figure 7.6 (p. 161, "A triangle in syntax and in
kinship").

This study file is the demonstration that the *same*
`WordGrammar.Inheritance.Network` infrastructure used by `WordGrammar.englishAuxNet`
also supports a kinship hierarchy. Two demos:

1. A small kinship taxonomy as a `Network`, with isA links
   (`mother isA parent`, `parent isA ancestor`), described by the same
   propositional `IsA` relation and the same `parents`/`ancestors`
   computational helpers used by `WordGrammar.englishAuxNet`.
2. The Fig 7.6 triangle pattern: `grandparentOf` is the relational
   composition `parentOf ∘r parentOf` (mathlib's `Relation.Comp`) — the
   same shape Hudson uses for syntactic raising (HAVE's subject is also
   the subject of HAVE's valent).

The point is structural: a single `Network α R` type carries both the
syntactic word-class hierarchy of `WordGrammar.englishAuxNet` (over
nodes typed by linguistic categories) and the kinship taxonomy below
(over nodes typed by `KinRole`). No Bridge theorem is needed — the
identity is by construction at the level of the type `Network`.
-/

set_option autoImplicit false

namespace Hudson2010


open WordGrammar.Inheritance

-- ============================================================================
-- Kinship roles and a small inheritance taxonomy
-- ============================================================================

/-- Atomic kinship roles. The taxonomy: `grandmother` and `grandfather`
are `grandparent`s; `mother` and `father` are `parent`s; `parent`s and
`grandparent`s are `ancestor`s. -/
inductive KinRole where
  | mother | father
  | parent
  | grandmother | grandfather
  | grandparent
  | ancestor
  deriving Repr, DecidableEq

/-- A small kinship inheritance network. All links are isA edges; the
taxonomy is `mother / father → parent`, `grandmother / grandfather →
grandparent`, and `parent / grandparent → ancestor`. The relation-label
type is `Empty`: there are no `prop` links here, only the `isA` backbone,
so no labels are reachable. The Fig 7.6 triangle below uses an abstract
`ParentRel α` rather than a network `prop` link, so no kinship-specific
label type is needed. -/
def kinshipNet : Network KinRole Empty where
  links :=
    [ ⟨.isA, .mother,      .parent,      none⟩
    , ⟨.isA, .father,      .parent,      none⟩
    , ⟨.isA, .grandmother, .grandparent, none⟩
    , ⟨.isA, .grandfather, .grandparent, none⟩
    , ⟨.isA, .parent,      .ancestor,    none⟩
    , ⟨.isA, .grandparent, .ancestor,    none⟩
    ]

-- ============================================================================
-- Demo 1: the network's isA traversal works the same way it does for syntax
-- ============================================================================

/-- A `mother` is a `parent` (one step). -/
theorem mother_IsA_parent : IsA kinshipNet .mother .parent := by decide

/-- A `mother` is an `ancestor` (two steps via `parent`). -/
theorem mother_IsA_ancestor : IsA kinshipNet .mother .ancestor := by decide

/-- A `grandmother` is an `ancestor` (two steps via `grandparent`). -/
theorem grandmother_IsA_ancestor : IsA kinshipNet .grandmother .ancestor := by decide

/-- A `mother` is **not** a `grandmother` — the taxonomy doesn't conflate the
two, even though both are `ancestor`s. Now stated as the full propositional
`¬ IsA kinshipNet .mother .grandmother`, decidable thanks to path compression
landed in `WordGrammar.Inheritance.Basic`. -/
theorem mother_not_IsA_grandmother :
    ¬ IsA kinshipNet .mother .grandmother := by decide

/-- Sanity: reflexive case. `IsA.refl` gives this directly, but exercising the
`Decidable` instance on it confirms the reflexive disjunct fires. -/
example : IsA kinshipNet .mother .mother := by decide

/-- Sanity: `ancestor` has no proper ancestors, so `¬ IsA ancestor mother`
follows. Exercises the BFS-side of the decision procedure (no chain exists). -/
example : ¬ IsA kinshipNet .ancestor .mother := by decide

/-- The `ancestor` node sits at the top: nothing is its ancestor. -/
theorem ancestor_has_no_proper_ancestors :
    ancestors kinshipNet .ancestor = [] := by decide

-- ----------------------------------------------------------------------------
-- The mathlib `≤` view: with `IsAOrder net`'s `Preorder` instance in place,
-- every preorder lemma applies to the kinship taxonomy (e.g. `le_trans`,
-- `LowerSet`/`UpperSet`).
-- ----------------------------------------------------------------------------

/-- The same fact as `mother_IsA_ancestor` via mathlib's `≤`. The `IsAOrder.mk`
wrapper tags the nodes as inhabiting the preorder view of `kinshipNet`, so
instance search picks up the `Preorder (IsAOrder kinshipNet)` instance instead
of unfolding to `KinRole` and looking for the (nonexistent) `LE KinRole`. -/
theorem mother_le_ancestor :
    IsAOrder.mk kinshipNet .mother ≤ IsAOrder.mk kinshipNet .ancestor :=
  mother_IsA_ancestor

-- ============================================================================
-- Demo 2: the Fig 7.6 triangle — grandparent as parent ∘ parent
-- ============================================================================

/-- The "parent of" relation between people. Modelled abstractly as a
binary relation over an arbitrary type of individuals. -/
abbrev ParentRel (α : Type) : Type := α → α → Prop

/-- `grandparentOf` is the relational composition of `parentOf` with itself —
the kinship side of [hudson-2010]'s Figure 7.6 (p. 161): "my grandmother
is someone who is the mother of one of my parents". This is mathlib's
`Relation.Comp`, not a fresh definition. -/
abbrev grandparentOf {α : Type} (parentOf : ParentRel α) : α → α → Prop :=
  Relation.Comp parentOf parentOf

/-! Hudson's kinship instance of Fig 7.6: the triangle commutes by definition,
since `grandparentOf` *is* `parentOf ∘r parentOf`. -/
section KinshipTriangle

variable {α : Type} (parentOf : ParentRel α)

/-- The triangle for kinship commutes by definition. This is the formal
counterpart of Hudson's prose on p. 160 (§7.2.6): "my grandmother is
someone who is the mother of one of my parents". -/
theorem kinship_triangle_commutes :
    ∀ a c, grandparentOf parentOf a c ↔ ∃ b, parentOf a b ∧ parentOf b c :=
  fun _ _ => Iff.rfl

/-- Given an apex grandparent `a`, an intermediate parent `b`, and a base
person `c`, the composition witness exists. -/
theorem kinship_triangle_witness (a b c : α)
    (h1 : parentOf a b) (h2 : parentOf b c) : grandparentOf parentOf a c :=
  ⟨b, h1, h2⟩

end KinshipTriangle

-- ============================================================================
-- The "one network" thesis: same `Network` type, two domains
-- ============================================================================

/-- Witness that `WordGrammar.Inheritance.Network` accommodates both the syntactic
word-class hierarchy (`WordGrammar.englishAuxNet`) and the kinship taxonomy
(`kinshipNet`) by inhabiting the *same* parameterized type. The structural
identity is at the type level — no Bridge theorem needed.

This is the formal counterpart of Hudson's §7.7 ("Syntax without modules",
p. 189): linguistic and non-linguistic conceptual knowledge live in one
network. -/
example : Network WordGrammar.WGNode WordGrammar.WGRel × Network KinRole Empty :=
  (WordGrammar.englishAuxNet, kinshipNet)

end Hudson2010
