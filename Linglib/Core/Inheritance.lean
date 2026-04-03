/-!
# Inheritance Networks

Hudson's Word Grammar organizes all linguistic knowledge as networks of nodes
connected by labeled directed links. @cite{hudson-2010}

Properties in WG are not key-value pairs attached to nodes — they ARE links
between nodes. "Bird has wing" is a link labeled `front-limb` from `bird` to
`wing`. IsA links form a taxonomy; properties flow down the taxonomy by default
inheritance. The **Best Fit Principle** (§3.5) resolves conflicts: the most
specific value (nearest ancestor in the isA chain) wins.

## Hudson's five primitive relations (§3.2.5)

- **isA** — taxonomic classification (bird isA animal)
- **or** — mutual exclusivity / choice sets (male or female)
- **prop** — named property/relation links (bird --front-limb--> wing)

(Hudson also lists `argument` and `value` as primitives for defining relational
concepts; these are modeled here as `prop` links with appropriate labels.)

## Key definitions

- `LinkKind` — isA, or, prop (the three distinguished link types)
- `Link` — a labeled directed edge in the network
- `Network` — a set of labeled directed links between nodes
- `parents`, `ancestors`, `isA` — taxonomy traversal
- `choiceSet` — OR alternatives (mutually exclusive values)
- `localProps`, `inherited` — property lookup with Best Fit default inheritance
- `Prototype` — graded category membership (typicality rankings)
-/

set_option autoImplicit false

namespace Core.Inheritance

-- ============================================================================
-- Links
-- ============================================================================

/-- Distinguished link types in a WG network. @cite{hudson-2010} §3.2.
IsA and or are separated from general property links because the inheritance
algorithm must traverse isA links and choice-set resolution uses or links. -/
inductive LinkKind where
  | isA   -- taxonomic inheritance
  | or    -- mutual exclusivity (choice set)
  | prop  -- named property / relation
  deriving Repr, DecidableEq

/-- A labeled directed edge: `source --[kind, label]--> target`.
In WG, all knowledge is encoded as links between nodes: "cat isA mammal",
"bird --front-limb--> wing", "male or female". -/
structure Link (α R : Type) where
  kind : LinkKind
  source : α
  target : α
  label : Option R := none
  deriving Repr, DecidableEq

-- ============================================================================
-- Network
-- ============================================================================

/-- A WG inheritance network: nodes connected by labeled directed links.
Parameterized over node type `α` and relation-label type `R`. -/
structure Network (α R : Type) [DecidableEq α] [DecidableEq R] where
  links : List (Link α R)

-- ============================================================================
-- Taxonomy (isA)
-- ============================================================================

section NetworkOps

variable {α R : Type} [DecidableEq α] [DecidableEq R]

/-- Direct isA parents of a node. -/
def parents (net : Network α R) (node : α) : List α :=
  (net.links.filter (λ l => l.kind == .isA && l.source == node)).map Link.target

/-- Ancestors: transitive closure of `parents`, with fuel for termination. -/
def ancestors (net : Network α R) (node : α) (fuel : Nat := 100) : List α :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    let ps := parents net node
    ps ++ (ps.map (λ p => ancestors net p fuel')).flatten

/-- Reflexive-transitive isA: does `a` inherit from `b`? -/
def isA (net : Network α R) (a b : α) (fuel : Nat := 100) : Bool :=
  a == b || (ancestors net a fuel).elem b

-- ============================================================================
-- Choice Sets (OR)
-- ============================================================================

/-- OR-alternatives of a node (§3.3): mutually exclusive choices.
E.g., `choiceSet net gender` returns `[male, female]` if the network contains
`male --or--> gender` and `female --or--> gender`. -/
def choiceSet (net : Network α R) (node : α) : List α :=
  (net.links.filter (λ l => l.kind == .or && l.target == node)).map Link.source

-- ============================================================================
-- Properties (Named Relation Links)
-- ============================================================================

/-- Local property values: targets of `.prop` links from `node` with label `r`.
A node may have multiple values for the same relation (e.g., a bird has two wings). -/
def localProps (net : Network α R) (node : α) (r : R) : List α :=
  (net.links.filter (λ l =>
    l.kind == .prop && l.source == node && l.label == some r)).map Link.target

/-- Inherited property values for relation `r`, resolved by the Best Fit Principle
(§3.5): the most specific (nearest ancestor in the isA chain) wins. Breadth-first
walk up the taxonomy; returns the first non-empty result found. -/
def inherited (net : Network α R) (node : α) (r : R)
    (fuel : Nat := 100) : List α :=
  match localProps net node r with
  | [] =>
    match fuel with
    | 0 => []
    | fuel' + 1 =>
      let ps := parents net node
      -- breadth-first: check all direct parents before going deeper
      match ps.findSome? (λ p =>
        match localProps net p r with
        | [] => none
        | vs => some vs) with
      | some vs => vs
      | none =>
        ps.findSome? (λ p =>
          match inherited net p r fuel' with
          | [] => none
          | vs => some vs) |>.getD []
  | vs => vs

-- ============================================================================
-- Theorems
-- ============================================================================

/-- Every node isA itself. -/
theorem isA_refl (net : Network α R) (a : α) : isA net a a = true := by
  simp [isA]

/-- If a node has local properties for `r`, `inherited` returns them directly
(the Best Fit Principle: local overrides inherited). -/
theorem bestFit_local (net : Network α R) (node : α) (r : R)
    (h : localProps net node r ≠ []) :
    inherited net node r = localProps net node r := by
  unfold inherited
  split <;> simp_all

end NetworkOps

-- ============================================================================
-- Prototype Effects
-- ============================================================================

/-- A prototype: a category with graded typicality over instances.
Higher values = more prototypical. @cite{hudson-2010} Ch 2: categories have
graded membership; the prototype is the best exemplar. -/
structure Prototype (α : Type) where
  category : α
  typicality : α → Nat

/-- Whether `a` is at least as typical as `b` in a prototype. -/
def Prototype.atLeastAsTypical {α : Type} (proto : Prototype α) (a b : α) : Bool :=
  proto.typicality a ≥ proto.typicality b

/-- Whether `a` is strictly more typical than `b` in a prototype. -/
def Prototype.moreTypical {α : Type} (proto : Prototype α) (a b : α) : Bool :=
  proto.typicality a > proto.typicality b

/-- `atLeastAsTypical` is reflexive. -/
theorem Prototype.atLeastAsTypical_refl {α : Type} (proto : Prototype α) (a : α) :
    proto.atLeastAsTypical a a = true := by
  simp [atLeastAsTypical]

/-- `atLeastAsTypical` is transitive. -/
theorem Prototype.atLeastAsTypical_trans {α : Type} (proto : Prototype α) (a b c : α)
    (hab : proto.atLeastAsTypical a b = true)
    (hbc : proto.atLeastAsTypical b c = true) :
    proto.atLeastAsTypical a c = true := by
  simp [atLeastAsTypical] at *
  omega

end Core.Inheritance
