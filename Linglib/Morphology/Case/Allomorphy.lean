import Mathlib.Order.Fin.Basic
import Linglib.Features.Case.Basic
import Linglib.Morphology.Paradigm.Contiguity

/-!
# Case Allomorphy and Syncretism — Substrate
[blake-1994] [caha-2009] [bobaljik-2012]

Framework-neutral substrate for talking about allomorphy and
syncretism patterns over morphological case. Provides:

- `AllomorphyPattern`: a 4-tuple of form-class indices over the four
  core cases (NOM, ACC, GEN, DAT); decidable `ViolatesABA` /
  `IsContiguous` predicates derived from `Morphology.Containment`.
- `HierarchyAdjacent` / `InventoryAdjacent`: adjacency relations on
  cases, the latter relativized to a particular language's inventory.
- `Syncretism`: a record-pair of cases that share an exponent.
- A handful of well-known syncretism patterns (NOM/ACC, COM/INST) and
  decidability theorems for adjacency on small inventories.

What *explains* the *ABA gap is contested between DM (post-syntactic
VI + Elsewhere ordering — `[bobaljik-2012]`) and Nanosyntax
(phrasal spellout + Superset Principle — `[caha-2009]`). This
file commits to neither; per-paper analyses live in
`Studies/`.
-/

namespace Morphology.Case.Allomorphy

open Features

-- ============================================================================
-- § 1: AllomorphyPattern + *ABA
-- ============================================================================

/-- An allomorphy pattern over the four core cases (NOM, ACC, GEN, DAT),
    represented as a form-class index for each case. -/
structure AllomorphyPattern where
  nom : Nat
  acc : Nat
  gen : Nat
  dat : Nat
  deriving DecidableEq, Repr

/-- The general-substrate form of an allomorphy pattern: the n = 4
    instance of `Morphology.Paradigm`. -/
def AllomorphyPattern.toParadigm (p : AllomorphyPattern) :
    Morphology.Paradigm 4 ℕ :=
  ![p.nom, p.acc, p.gen, p.dat]

/-- Is a pattern contiguous? Each form class occupies a contiguous span
    on the hierarchy — the generic
    `Morphology.IsContiguous`, by construction. -/
def AllomorphyPattern.IsContiguous (p : AllomorphyPattern) : Prop :=
  Morphology.IsContiguous p.toParadigm

instance (p : AllomorphyPattern) : Decidable p.IsContiguous :=
  inferInstanceAs (Decidable (Morphology.IsContiguous _))

/-- A pattern violates *ABA: some form class recurs across a distinct
    intervening one. Equivalent to ¬IsContiguous. -/
def AllomorphyPattern.ViolatesABA (p : AllomorphyPattern) : Prop :=
  ¬ p.IsContiguous

instance (p : AllomorphyPattern) : Decidable p.ViolatesABA :=
  inferInstanceAs (Decidable (¬ _))

-- ============================================================================
-- § 2: *ABA Verification on Concrete Patterns
-- ============================================================================

def abbPattern : AllomorphyPattern := ⟨0, 1, 1, 1⟩
def aabPattern : AllomorphyPattern := ⟨0, 0, 0, 1⟩
def aabbPattern : AllomorphyPattern := ⟨0, 0, 1, 1⟩
def ababPattern : AllomorphyPattern := ⟨0, 1, 0, 1⟩
def abaPattern : AllomorphyPattern := ⟨0, 1, 0, 0⟩
def babPattern : AllomorphyPattern := ⟨1, 0, 1, 0⟩
def uniformPattern : AllomorphyPattern := ⟨0, 0, 0, 0⟩

/-! Smoke tests for the named patterns: each evaluates as the
    AllomorphyPattern shape its name implies. Demoted from `theorem`
    to `example` because nothing in the codebase consumes them by
    name. -/

example : abbPattern.IsContiguous := by decide
example : ¬ abbPattern.ViolatesABA := by decide
example : aabPattern.IsContiguous := by decide
example : aabbPattern.IsContiguous := by decide
example : ababPattern.ViolatesABA := by decide
example : ¬ ababPattern.IsContiguous := by decide
example : abaPattern.ViolatesABA := by decide
example : babPattern.ViolatesABA := by decide
example : uniformPattern.IsContiguous := by decide

-- ============================================================================
-- § 3: Containment Rank vs. Blake Hierarchy Rank
-- ============================================================================

/-- Containment rank preserves Blake's typological ordering on the core
    cases (NOM, ACC, GEN, DAT): the orderings are *inverses*. Blake ranks
    by "how likely a language is to have it" (NOM most common → highest),
    while the containment view ranks by "how much structure it contains"
    (NOM least complex → lowest). This is a theorem about the Blake
    hierarchy, framework-neutral. -/
theorem containment_refines_blake :
    Case.hierarchyRank .nom ≥ Case.hierarchyRank .acc ∧
    Case.hierarchyRank .acc ≥ Case.hierarchyRank .gen ∧
    Case.hierarchyRank .gen ≥ Case.hierarchyRank .dat := by decide

-- ============================================================================
-- § 4: Syncretism
-- ============================================================================

/-- A syncretism pattern: two cases share a morphological exponent. -/
structure Syncretism where
  case1 : Case
  case2 : Case
  neq : case1 ≠ case2
  deriving Repr

/-- Are two cases adjacent on the hierarchy (same rank or ranks differ by 1)? -/
def _root_.Case.HierarchyAdjacent (c1 c2 : Case) : Prop :=
  c1.hierarchyRank = c2.hierarchyRank ∨
  c1.hierarchyRank + 1 = c2.hierarchyRank ∨
  c2.hierarchyRank + 1 = c1.hierarchyRank

instance : DecidableRel Case.HierarchyAdjacent := λ _ _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Relaxed adjacency: no case in the inventory falls strictly between
    the two syncretic cases on the hierarchy. -/
def _root_.Case.InventoryAdjacent (inv : Finset Case) (c1 c2 : Case) : Prop :=
  let lo := min c1.hierarchyRank c2.hierarchyRank
  let hi := max c1.hierarchyRank c2.hierarchyRank
  ∀ c ∈ inv, c = c1 ∨ c = c2 ∨ c.hierarchyRank ≤ lo ∨ c.hierarchyRank ≥ hi

instance (inv : Finset Case) (c1 c2 : Case) : Decidable (Case.InventoryAdjacent inv c1 c2) := by
  unfold Case.InventoryAdjacent; infer_instance

-- ============================================================================
-- § 5: Well-Known Syncretism Patterns
-- ============================================================================

def nomAccSyncretism : Syncretism :=
  ⟨.nom, .acc, by decide⟩

def comInstSyncretism : Syncretism :=
  ⟨.com, .inst, by decide⟩

-- ============================================================================
-- § 6: Adjacency Theorems
-- ============================================================================

/-! Adjacency-on-canonical-hierarchy smoke tests. The named theorems
    below have no codebase consumers (Tamil/Case.lean defines its own
    locally-named `com_inst_adjacent`, not a use of this one); all are
    `example`s. The one consumed lemma is `same_tier_adjacent`, kept
    as `theorem` because it is parametric over the hierarchy ranks
    (not a fixed pair). -/

example : Case.HierarchyAdjacent .nom .acc := by decide
example : Case.HierarchyAdjacent .com .inst := by decide
example : Case.HierarchyAdjacent .dat .loc := by decide
example : Case.HierarchyAdjacent .gen .dat := by decide

/-- ERG/INST hierarchy non-adjacency (ranks 6, 2): Blake's known
    exception, explained by historical derivation. -/
example : ¬ Case.HierarchyAdjacent .erg .inst := by decide

/-- ERG/INST IS inventory-adjacent in a system with only
    {ERG, ABS, INST}. -/
example : Case.InventoryAdjacent ({.erg, .abs, .inst} : Finset Case) .erg .inst := by
  decide

/-- Same-tier cases are always strictly adjacent. (Parametric over
    the rank — kept as named `theorem` for downstream re-use.) -/
theorem _root_.Case.same_tier_adjacent (c1 c2 : Case)
    (h : c1.hierarchyRank = c2.hierarchyRank) :
    Case.HierarchyAdjacent c1 c2 := Or.inl h

-- ============================================================================
-- § 7: *ABA and Syncretism Examples
-- ============================================================================

/-! Five fixed `AllomorphyPattern` shapes that show up in the
    syncretism literature. Demoted to `example` for the same reason as
    the smoke tests above: no by-name consumers. -/

example : (AllomorphyPattern.mk 0 0 1 1).IsContiguous := by decide
example : (AllomorphyPattern.mk 0 1 0 1).ViolatesABA := by decide
example : (AllomorphyPattern.mk 0 1 1 2).IsContiguous := by decide
example : (AllomorphyPattern.mk 0 1 2 2).IsContiguous := by decide
example : (AllomorphyPattern.mk 0 1 1 0).ViolatesABA := by decide

end Morphology.Case.Allomorphy
