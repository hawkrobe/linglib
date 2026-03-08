import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Theories.Semantics.Dynamic.Core.WeakestPrecondition

/-!
# DRS Syntax and Accessibility
@cite{muskens-1996}

§III.5 (pp. 170–171): Accessibility determines which discourse referents
can be anaphorically resolved. A dref `u` occurring in condition `γ`
within DRS `K` is *accessible* from `u`'s position if an earlier part
of `K` introduced `u`. A DRS with no *free* (inaccessible) referents
is called *proper*.

## Definitions

- `adr K`: active discourse referents (drefs introduced by `K`)
- `occurs u K`: whether dref `u` occurs in `K`
- `acc u K`: drefs accessible from `u`'s occurrence in `K`
- `isFree u K`: `u` occurs in `K` but is not accessible
- `isProper K`: no free referents

## Key Result

Proposition 1 (@cite{muskens-1996}, p. 174): A DRS `K` is proper
iff `wp(K, ⊤)` is a closed formula.
-/

namespace Semantics.Dynamic.Core.Accessibility

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
-- § 4. Semantic Interpretation
-- ════════════════════════════════════════════════════════════════

open DynamicTy2

/-- Assignment type: dref indices map to entities. -/
abbrev Assign (E : Type*) := Nat → E

/-- Update an assignment at index `n`. -/
def Assign.update {E : Type*} (g : Assign E) (n : Nat) (e : E) : Assign E :=
  λ m => if m = n then e else g m

/-- Interpretation of relation symbols. -/
abbrev RelInterp (E : Type*) := Nat → List E → Prop

/-- Semantic interpretation: maps DRS syntax to DRS semantics.

Each syntactic DRS expression denotes a binary relation on assignments
(type `DRS (Assign E)`), following the abbreviation clauses
ABB1–ABB4 (@cite{muskens-1996}, p. 157). -/
def interp {E : Type*} (rels : RelInterp E) : DRSExpr → DRS (Assign E)
  | .atom rel drefs =>
    test (λ g => rels rel (drefs.map (λ i => g i)))
  | .is u v =>
    test (λ g => g u = g v)
  | .neg K =>
    test (dneg (interp rels K))
  | .disj K₁ K₂ =>
    test (ddisj (interp rels K₁) (interp rels K₂))
  | .impl K₁ K₂ =>
    test (dimpl (interp rels K₁) (interp rels K₂))
  | .box newDrefs conds =>
    let introduce := newDrefs.foldl
      (λ D n => dseq D (λ i j => ∃ e : E, j = i.update n e)) (λ i j => i = j)
    dseq introduce (interpConds rels conds)
  | .seq K₁ K₂ =>
    dseq (interp rels K₁) (interp rels K₂)
where
  interpConds (rels : RelInterp E) : List DRSExpr → DRS (Assign E)
    | [] => λ i j => i = j
    | c :: cs => dseq (interp rels c) (interpConds rels cs)

-- ════════════════════════════════════════════════════════════════
-- § 5. Verification Examples
-- ════════════════════════════════════════════════════════════════

/-- "A man adores a woman" as a syntactic DRS.

`[u₁ u₂ | man u₁, woman u₂, u₁ adores u₂]`

Using relation indices: 0 = man, 1 = woman, 2 = adores. -/
def exManAdoresWoman : DRSExpr :=
  .box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]]

/-- The example DRS is proper: all drefs (1, 2) are introduced by the box. -/
example : isProper exManAdoresWoman = true := by native_decide

/-- "If a farmer owns a donkey, he beats it" as a syntactic DRS.

`[u₁ u₂ | farmer u₁, donkey u₂, u₁ owns u₂] ⇒ [| u₁ beats u₂]`

Using relation indices: 0 = farmer, 1 = donkey, 2 = owns, 3 = beats. -/
def exDonkey : DRSExpr :=
  .impl
    (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
    (.box [] [.atom 3 [1, 2]])

/-- The donkey sentence is proper: drefs 1, 2 are introduced in the
antecedent and accessible in the consequent. -/
example : isProper exDonkey = true := by native_decide

/-- "He₁ stinks" (with no antecedent) is NOT proper: dref 1 is free. -/
def exFree : DRSExpr := .box [] [.atom 0 [1]]

example : isProper exFree = false := by native_decide

-- ════════════════════════════════════════════════════════════════
-- § 6. Projection Drefs and Assignment Properties
-- ════════════════════════════════════════════════════════════════

/-- Projection dref: the n-th register value.

In @cite{muskens-1996}'s terminology, `projDref n` is the *variable register*
`uₙ` — the function that reads the n-th slot of an assignment. -/
def projDref {E : Type*} (n : Nat) : Dref (Assign E) E := λ g => g n

/-- Updating at index n assigns the new value to the n-th projection dref.

This is the concrete version of `AssignmentStructure.extend_at` for
`Assign E`: `uₙ(g[n ↦ e]) = e`. -/
theorem update_projDref_eq {E : Type*} (g : Assign E) (n : Nat) (e : E) :
    projDref n (g.update n e) = e := by
  simp [projDref, Assign.update]

/-- Updating at index n preserves other projection drefs.

Concrete version of `AssignmentStructure.extend_other`:
`uₘ(g[n ↦ e]) = uₘ(g)` when `n ≠ m`. -/
theorem update_projDref_ne {E : Type*} (g : Assign E) (n m : Nat) (e : E) (h : n ≠ m) :
    projDref m (g.update n e) = projDref m g := by
  simp [projDref, Assign.update, h.symm]

-- ════════════════════════════════════════════════════════════════
-- § 7. Merging Lemma
-- ════════════════════════════════════════════════════════════════

/-- Merging Lemma (@cite{muskens-1996}, p. 150).

If drefs `x'₁,...,x'ₖ` do not occur in any condition `γ₁,...,γₘ`, then
sequencing two boxes equals a single merged box:

  `⟦[x₁...xₙ|γ₁,...,γₘ]; [x'₁...x'ₖ|δ₁,...,δq]⟧`
  `= ⟦[x₁...xₙx'₁...x'ₖ|γ₁,...,γₘ,δ₁,...,δq]⟧`

This is used throughout §III.4 to simplify compositional derivations
(e.g., merging (10) and (11) into (12), reducing (21) to (22)).

-- TODO: The proof requires showing that random assignments for fresh
-- drefs commute with tests that don't mention those drefs. -/
theorem mergingLemma {E : Type*} (rels : RelInterp E)
    (drefs1 drefs2 : List Nat) (conds1 conds2 : List DRSExpr)
    (hfresh : ∀ n ∈ drefs2, ∀ c ∈ conds1, occurs n c = false) :
    interp rels (.seq (.box drefs1 conds1) (.box drefs2 conds2)) =
    interp rels (.box (drefs1 ++ drefs2) (conds1 ++ conds2)) := by
  sorry

-- ════════════════════════════════════════════════════════════════
-- § 8. Proposition 1 and Truth-Condition Extraction
-- ════════════════════════════════════════════════════════════════

/-- Proposition 1 (@cite{muskens-1996}, p. 174).

A syntactically proper DRS (no free discourse referents) has
state-independent truth conditions: `wp(⟦K⟧, ⊤)` doesn't depend
on the input assignment.

This bridges syntactic properness (`Accessibility.isProper`) with
semantic properness (`WeakestPrecondition.isProper`).

-- TODO: The proof requires induction on DRSExpr, showing that `interp`
-- only reads registers through drefs that are introduced by boxes
-- or tested in conditions (never "leaked" as free). -/
theorem proposition_1 {E : Type*} [Nonempty E] (rels : RelInterp E) (K : DRSExpr)
    (hproper : isProper K = true) :
    WeakestPrecondition.isProper (interp rels K) := by
  sorry

/-- Truth conditions of "A man adores a woman" extracted via `wp`.

`wp(⟦[u₁ u₂ | man u₁, woman u₂, u₁ adores u₂]⟧, ⊤)(g)`
`= ∃ e₁ e₂, man(e₁) ∧ woman(e₂) ∧ adores(e₁, e₂)`

for any input assignment `g`. This demonstrates the full pipeline:
syntactic DRS → semantic interpretation → wp truth-condition extraction,
yielding the expected first-order formula (24) from @cite{muskens-1996} p. 159.

-- TODO: Proof by unfolding `interp`, `dseq`, `test`, `Assign.update`, `wp`. -/
theorem exManAdoresWoman_truthConditions {E : Type*} (rels : RelInterp E)
    (g : Assign E) :
    WeakestPrecondition.wp (interp rels exManAdoresWoman) (λ _ => True) g ↔
    ∃ e₁ e₂ : E, rels 0 [e₁] ∧ rels 1 [e₂] ∧ rels 2 [e₁, e₂] := by
  sorry

end Semantics.Dynamic.Core.Accessibility
