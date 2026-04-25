import Mathlib.Tactic.TypeStar

/-!
# DRS Syntax: Discourse Representation Structures
@cite{kamp-reyle-1993} @cite{muskens-1996}

Pure syntactic representation of DRS expressions with structural
operations — no semantic imports, no interpretation.

## Definitions

- `DRSExpr`: recursive syntax for DRS boxes, conditions, and connectives
- `adr K`: active discourse referents (drefs introduced by `K`)
- `occurs u K`: whether dref `u` occurs in `K`
- `acc u K`: drefs accessible from `u`'s occurrence in `K`
- `isFree u K`: `u` occurs in `K` but is not accessible
- `isProper K`: no free referents (@cite{muskens-1996}, p. 171)

## Design

This module is the pure-syntax layer of the four-layer dynamic
semantics architecture:

```
DynProp.lean       ← semantic algebra (DRS S, dseq, test, ...)
DynamicTy2.lean    ← compositional layer (Dref, AssignmentStructure)
DRSExpr.lean       ← DRS syntax (this file)
Accessibility.lean ← interpretation bridge (DRSExpr → DRS)
```

`DRSExpr` has no dependency on the semantic algebra (`DRS S`) or
compositional types (`Dref`, `Assign`). Interpretation is defined
in `Accessibility.lean` via `interp : DRSExpr → DRS (Assign E)`.
-/

namespace Semantics.Dynamic.Core.DRSExpr

-- ════════════════════════════════════════════════════════════════
-- § 1. DRS Syntax
-- ════════════════════════════════════════════════════════════════

/-- Syntactic representation of DRS expressions.

Dref indices are natural numbers. Relation symbols are identified
by natural number indices; their arity is implicit in the dref list. -/
inductive DRSExpr where
  /-- Atomic condition: relation R applied to drefs -/
  | atom (rel : Nat) (drefs : List Nat) : DRSExpr
  /-- Identity condition: u₁ is u₂ -/
  | is (u v : Nat) : DRSExpr
  /-- Negation: not K -/
  | neg (K : DRSExpr) : DRSExpr
  /-- Disjunction: K₁ or K₂ -/
  | disj (K₁ K₂ : DRSExpr) : DRSExpr
  /-- Implication: K₁ ⇒ K₂ -/
  | impl (K₁ K₂ : DRSExpr) : DRSExpr
  /-- Box: [u₁,...,uₙ | γ₁,...,γₘ] -/
  | box (newDrefs : List Nat) (conds : List DRSExpr) : DRSExpr
  /-- Sequencing: K₁ ; K₂ -/
  | seq (K₁ K₂ : DRSExpr) : DRSExpr
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 2. Active Discourse Referents
-- ════════════════════════════════════════════════════════════════

/-- Active discourse referents: the drefs *introduced* by `K`.

`adr([u₁,...,uₙ | γ₁,...,γₘ]) = {u₁,...,uₙ}`
`adr(K₁ ; K₂) = adr(K₁) ∪ adr(K₂)`

Conditions (atoms, negation, disjunction, implication) introduce no drefs. -/
def adr : DRSExpr → List Nat
  | .atom _ _ => []
  | .is _ _ => []
  | .neg _ => []
  | .disj _ _ => []
  | .impl _ _ => []
  | .box newDrefs _ => newDrefs
  | .seq K₁ K₂ => adr K₁ ++ adr K₂

-- ════════════════════════════════════════════════════════════════
-- § 3. Occurrence and Accessibility
-- ════════════════════════════════════════════════════════════════

/-- Whether dref `u` occurs anywhere in expression `K`. -/
def occurs (u : Nat) : DRSExpr → Bool
  | .atom _ drefs => drefs.contains u
  | .is v w => u == v || u == w
  | .neg K => occurs u K
  | .disj K₁ K₂ => occurs u K₁ || occurs u K₂
  | .impl K₁ K₂ => occurs u K₁ || occurs u K₂
  | .box newDrefs conds => newDrefs.contains u || occursAny u conds
  | .seq K₁ K₂ => occurs u K₁ || occurs u K₂
where
  occursAny (u : Nat) : List DRSExpr → Bool
    | [] => false
    | c :: cs => occurs u c || occursAny u cs

/-- Accessible drefs from an occurrence of `u` in `K`.

Defined by structural recursion following @cite{muskens-1996} pp. 170–171:
- Atomic: no drefs are accessible
- Negation: accessibility passes through
- Disjunction/implication: accessibility from the branch containing `u`,
  with antecedent drefs accessible in the consequent
- Box: new drefs are accessible, plus accessibility from the condition containing `u`
- Sequencing: drefs from `K₁` are accessible in `K₂` -/
def acc (u : Nat) : DRSExpr → List Nat
  | .atom _ _ => []
  | .is _ _ => []
  | .neg K => acc u K
  | .disj K₁ K₂ =>
    if occurs u K₁ then acc u K₁ else acc u K₂
  | .impl K₁ K₂ =>
    if occurs u K₁ then acc u K₁
    else acc u K₂ ++ adr K₁
  | .box newDrefs conds =>
    match accFind u conds with
    | some r => r ++ newDrefs
    | none => newDrefs
  | .seq K₁ K₂ =>
    if occurs u K₁ then acc u K₁
    else acc u K₂ ++ adr K₁
where
  /-- Find the first condition containing `u` and return its accessible drefs. -/
  accFind (u : Nat) : List DRSExpr → Option (List Nat)
    | [] => none
    | c :: cs => if occurs u c then some (acc u c) else accFind u cs

/-- Collect all dref indices mentioned anywhere in `K`. -/
def allOccurring : DRSExpr → List Nat
  | .atom _ drefs => drefs
  | .is v w => [v, w]
  | .neg K => allOccurring K
  | .disj K₁ K₂ => allOccurring K₁ ++ allOccurring K₂
  | .impl K₁ K₂ => allOccurring K₁ ++ allOccurring K₂
  | .box newDrefs conds => newDrefs ++ allOccurringList conds
  | .seq K₁ K₂ => allOccurring K₁ ++ allOccurring K₂
where
  allOccurringList : List DRSExpr → List Nat
    | [] => []
    | c :: cs => allOccurring c ++ allOccurringList cs

/-- A dref `u` is *free* in `K` if it occurs in `K` but is not
among the drefs accessible from its position. -/
def isFree (u : Nat) (K : DRSExpr) : Bool :=
  occurs u K && !(acc u K).contains u

/-- A DRS is *proper* if it contains no free referents
(@cite{muskens-1996}, p. 171). -/
def isProper (K : DRSExpr) : Bool :=
  (allOccurring K).all (λ u => !(isFree u K))

-- ════════════════════════════════════════════════════════════════
-- § 4. Verification Examples
-- ════════════════════════════════════════════════════════════════

/-- "A man adores a woman" as a syntactic DRS.

`[u₁ u₂ | man u₁, woman u₂, u₁ adores u₂]`

Using relation indices: 0 = man, 1 = woman, 2 = adores. -/
def exManAdoresWoman : DRSExpr :=
  .box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]]

/-- The example DRS is proper: all drefs (1, 2) are introduced by the box. -/
example : isProper exManAdoresWoman = true := by decide

/-- "If a farmer owns a donkey, he beats it" as a syntactic DRS.

`[u₁ u₂ | farmer u₁, donkey u₂, u₁ owns u₂] ⇒ [| u₁ beats u₂]`

Using relation indices: 0 = farmer, 1 = donkey, 2 = owns, 3 = beats. -/
def exDonkey : DRSExpr :=
  .impl
    (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
    (.box [] [.atom 3 [1, 2]])

/-- The donkey sentence is proper: drefs 1, 2 are introduced in the
antecedent and accessible in the consequent. -/
example : isProper exDonkey = true := by decide

/-- "He₁ stinks" (with no antecedent) is NOT proper: dref 1 is free. -/
def exFree : DRSExpr := .box [] [.atom 0 [1]]

example : isProper exFree = false := by decide

end Semantics.Dynamic.Core.DRSExpr
