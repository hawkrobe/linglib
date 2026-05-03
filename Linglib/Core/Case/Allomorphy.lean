import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
import Linglib.Core.Morphology.Containment

/-!
# Case Allomorphy and Syncretism — Substrate
@cite{blake-1994} @cite{caha-2009} @cite{bobaljik-2012}

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
VI + Elsewhere ordering — `@cite{bobaljik-2012}`) and Nanosyntax
(phrasal spellout + Superset Principle — `@cite{caha-2009}`). This
file commits to neither; per-paper analyses live in
`Phenomena/Case/Studies/`.
-/

namespace Core.Case.Allomorphy

open Core

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

/-- A pattern violates *ABA when its 4-position projection violates the
    generic contiguity predicate. By construction this reduces by `rfl`
    to the generic substrate's `ViolatesABA` on the list. -/
def AllomorphyPattern.ViolatesABA (p : AllomorphyPattern) : Prop :=
  Morphology.Containment.ViolatesABA [p.nom, p.acc, p.gen, p.dat]

instance (p : AllomorphyPattern) : Decidable p.ViolatesABA :=
  inferInstanceAs (Decidable (Morphology.Containment.ViolatesABA _))

/-- Is a pattern contiguous? Each form class occupies a contiguous span
    on the hierarchy. Equivalent to ¬ViolatesABA. -/
def AllomorphyPattern.IsContiguous (p : AllomorphyPattern) : Prop :=
  ¬ p.ViolatesABA

instance (p : AllomorphyPattern) : Decidable p.IsContiguous :=
  inferInstanceAs (Decidable (¬ _))

/-- Bridge: case-specific `ViolatesABA` is the generic predicate
    applied to the 4-position projection. Holds by definition. -/
theorem case_violatesABA_iff_generic (p : AllomorphyPattern) :
    p.ViolatesABA ↔
      Morphology.Containment.violatesABA [p.nom, p.acc, p.gen, p.dat] = true :=
  Iff.rfl

-- ============================================================================
-- § 2: *ABA Verification on Concrete Patterns
-- ============================================================================

def abbPattern : AllomorphyPattern := ⟨0, 1, 1, 1⟩
theorem abb_contiguous : abbPattern.IsContiguous := by decide
theorem abb_no_aba : ¬ abbPattern.ViolatesABA := by decide

def aabPattern : AllomorphyPattern := ⟨0, 0, 0, 1⟩
theorem aab_contiguous : aabPattern.IsContiguous := by decide

def aabbPattern : AllomorphyPattern := ⟨0, 0, 1, 1⟩
theorem aabb_contiguous : aabbPattern.IsContiguous := by decide

def ababPattern : AllomorphyPattern := ⟨0, 1, 0, 1⟩
theorem abab_violates_aba : ababPattern.ViolatesABA := by decide
theorem abab_not_contiguous : ¬ ababPattern.IsContiguous := by decide

def abaPattern : AllomorphyPattern := ⟨0, 1, 0, 0⟩
theorem aba_violates : abaPattern.ViolatesABA := by decide

def babPattern : AllomorphyPattern := ⟨1, 0, 1, 0⟩
theorem bab_violates : babPattern.ViolatesABA := by decide

def uniformPattern : AllomorphyPattern := ⟨0, 0, 0, 0⟩
theorem uniform_contiguous : uniformPattern.IsContiguous := by decide

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
def HierarchyAdjacent (c1 c2 : Case) : Prop :=
  c1.hierarchyRank = c2.hierarchyRank ∨
  c1.hierarchyRank + 1 = c2.hierarchyRank ∨
  c2.hierarchyRank + 1 = c1.hierarchyRank

instance : DecidableRel HierarchyAdjacent := λ _ _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Relaxed adjacency: no case in the inventory falls strictly between
    the two syncretic cases on the hierarchy. -/
def InventoryAdjacent (inv : Finset Case) (c1 c2 : Case) : Prop :=
  let lo := min c1.hierarchyRank c2.hierarchyRank
  let hi := max c1.hierarchyRank c2.hierarchyRank
  ∀ c ∈ inv, c = c1 ∨ c = c2 ∨ c.hierarchyRank ≤ lo ∨ c.hierarchyRank ≥ hi

instance (inv : Finset Case) (c1 c2 : Case) : Decidable (InventoryAdjacent inv c1 c2) := by
  unfold InventoryAdjacent; infer_instance

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

theorem nom_acc_adjacent : HierarchyAdjacent .nom .acc := by decide
theorem com_inst_adjacent : HierarchyAdjacent .com .inst := by decide
theorem dat_loc_adjacent : HierarchyAdjacent .dat .loc := by decide
theorem gen_dat_adjacent : HierarchyAdjacent .gen .dat := by decide

/-- ERG/INST hierarchy non-adjacency (ranks 6, 2). Blake's known
    exception, explained by historical derivation. -/
theorem erg_inst_not_strictly_adjacent :
    ¬ HierarchyAdjacent .erg .inst := by decide

/-- ERG/INST IS inventory-adjacent in a system with only {ERG, ABS, INST}. -/
theorem erg_inst_inv_adjacent :
    InventoryAdjacent ({.erg, .abs, .inst} : Finset Case) .erg .inst := by
  decide

/-- Same-tier cases are always strictly adjacent. -/
theorem same_tier_adjacent (c1 c2 : Case)
    (h : c1.hierarchyRank = c2.hierarchyRank) :
    HierarchyAdjacent c1 c2 := Or.inl h

-- ============================================================================
-- § 7: *ABA and Syncretism Examples
-- ============================================================================

theorem neuter_syncretism_contiguous :
    (AllomorphyPattern.mk 0 0 1 1).IsContiguous := by decide

theorem nom_gen_without_acc_violates_aba :
    (AllomorphyPattern.mk 0 1 0 1).ViolatesABA := by decide

theorem acc_gen_syncretism_contiguous :
    (AllomorphyPattern.mk 0 1 1 2).IsContiguous := by decide

theorem gen_dat_syncretism_contiguous :
    (AllomorphyPattern.mk 0 1 2 2).IsContiguous := by decide

theorem nom_dat_syncretism_violates_aba :
    (AllomorphyPattern.mk 0 1 1 0).ViolatesABA := by decide

end Core.Case.Allomorphy
