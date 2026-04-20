import Linglib.Core.Case.Basic
import Linglib.Core.Case.FeatureBundle
import Linglib.Core.Case.Hierarchy
import Linglib.Core.Case.Order
import Linglib.Theories.Morphology.Containment
import Mathlib.Order.BoundedOrder.Basic

/-!
# Case Containment and Syncretism
@cite{caha-2009} @cite{mcfadden-2018} @cite{bobaljik-2012} @cite{blake-1994}


## Containment

@cite{caha-2009} proposes that the morphosyntactic representation of each
case on the hierarchy literally *contains* the representations of all
cases below it:

    [[[[[ NOM ] ACC ] GEN ] DAT ] P ]

This means ACC's representation includes NOM's; GEN's includes both
ACC's and NOM's; etc. A Vocabulary Insertion rule conditioned on feature
F therefore matches every case whose representation contains F. A rule
conditioned on ACC matches ACC, GEN, DAT, and P — the set of all
nonnominative cases — explaining the widespread NOM vs. oblique split in
stem allomorphy (@cite{mcfadden-2018}).

## The *ABA Constraint

@cite{bobaljik-2012} and @cite{caha-2009} observe that case-conditioned
suppletion obeys a *contiguity* restriction: if two cases X and Z
(with X ⊂ Y ⊂ Z on the hierarchy) share a suppletive form A, then
the case Y between them must also have form A. The pattern A–B–A
(with B ≠ A) is systematically unattested. This is the **\*ABA
constraint**.

The constraint falls out from containment: if a VI rule inserts form B
in the context of feature F, and Y's representation contains F, then
so does Z's (since Z ⊃ Y ⊃ X). There is no way for Z to "skip" B and
revert to A.

## Syncretism

Syncretism is the systematic neutralization of case distinctions: two or more
cases share a single morphological exponent in some paradigm cells.
@cite{blake-1994} documents syncretism patterns in Latin, Greek, and
other IE languages. He observes that syncretisms cluster into groups
(NOM+ACC vs. DAT+ABL) that are "significant on other grounds" (p. 22).

The **adjacency constraint** — that syncretic cases must be adjacent on the
case hierarchy — is a generalization from the Nanosyntax tradition, not an
explicit claim by Blake. Blake's data is consistent with it.

## Connection to Blake

`Core.Case.Hierarchy` formalizes Blake's *typological* hierarchy — an
implicational tendency about which cases languages tend to have.
Caha's containment hierarchy is a different object: a *syntactic*
claim about the internal structure of case representations. The two
are complementary, not competing.
-/

namespace Interfaces.Morphosyntax.CaseContainment

open Core
open Core.Case (containmentRank)

-- The Caha containment rank, the `≤`-based containment relation, the
-- `IsNonnominative` natural class, and the `PartialOrder Case` instance
-- all live in `Core.Case.Order` (they are foundational and theory-neutral).
-- This file builds on top of them with allomorphy / syncretism / inventory
-- predicates that are specific to morphology–syntax interface theorizing.

-- ============================================================================
-- § 1: The *ABA Constraint
-- ============================================================================

/-- An allomorphy pattern over the four core cases (NOM, ACC, GEN, DAT),
    represented as a form-class index for each case. -/
structure AllomorphyPattern where
  nom : Nat
  acc : Nat
  gen : Nat
  dat : Nat
  deriving DecidableEq, Repr

/-- Does a pattern contain an ABA subsequence? An ABA violation occurs
    when two non-adjacent cases on the containment hierarchy share a form
    that the intervening case does not. -/
def AllomorphyPattern.ViolatesABA (p : AllomorphyPattern) : Prop :=
  (p.nom = p.gen ∧ p.nom ≠ p.acc) ∨
  (p.nom = p.dat ∧ p.nom ≠ p.acc) ∨
  (p.nom = p.dat ∧ p.nom ≠ p.gen) ∨
  (p.acc = p.dat ∧ p.acc ≠ p.gen)

instance (p : AllomorphyPattern) : Decidable p.ViolatesABA := by
  unfold AllomorphyPattern.ViolatesABA; infer_instance

/-- Is a pattern contiguous? Each form class occupies a contiguous
    span on the containment hierarchy. Equivalent to ¬ViolatesABA. -/
def AllomorphyPattern.IsContiguous (p : AllomorphyPattern) : Prop :=
  ¬ p.ViolatesABA

instance (p : AllomorphyPattern) : Decidable p.IsContiguous :=
  inferInstanceAs (Decidable (¬ _))

-- ============================================================================
-- § 2: *ABA Verification
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
-- § 3: Containment vs. Typological Hierarchy
-- ============================================================================

/-- Containment rank preserves Blake's typological ordering on the core
    cases (NOM, ACC, GEN, DAT): the orderings are *inverses*. Blake ranks
    by "how likely a language is to have it" (NOM most common → highest),
    while containment ranks by "how much structure it contains"
    (NOM least complex → lowest). -/
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

instance : DecidableRel HierarchyAdjacent := fun _ _ =>
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

/-- ERG/INST syncretism does NOT satisfy strict adjacency (ranks 6, 2) —
    this is Blake's known exception, explained by historical derivation. -/
theorem erg_inst_not_strictly_adjacent :
    ¬ HierarchyAdjacent .erg .inst := by decide

/-- But ERG/INST IS inventory-adjacent in a system with only {ERG, ABS, INST}. -/
theorem erg_inst_inv_adjacent :
    InventoryAdjacent ({.erg, .abs, .inst} : Finset Case) .erg .inst := by
  decide

/-- Same-tier cases are always strictly adjacent. -/
theorem same_tier_adjacent (c1 c2 : Case)
    (h : c1.hierarchyRank = c2.hierarchyRank) :
    HierarchyAdjacent c1 c2 := Or.inl h

-- ============================================================================
-- § 7: *ABA and Syncretism
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

-- ============================================================================
-- § 8: Anderson's Features Explain Syncretism
-- ============================================================================

/-- ERG/INST syncretism: both share the {src} feature despite hierarchy
    non-adjacency. -/
theorem erg_inst_share_src :
    (Case.toCaseRelation .erg).any (CaseFeature.src ∈ ·) ∧
    (Case.toCaseRelation .inst).any (CaseFeature.src ∈ ·) ∧
    ¬ HierarchyAdjacent .erg .inst :=
  ⟨by decide, by decide, by decide⟩

/-- NOM/ACC syncretism (neuter nouns): both contain the abs feature. -/
theorem nom_acc_share_abs :
    (Case.toCaseRelation .nom).any (CaseFeature.abs ∈ ·) ∧
    (Case.toCaseRelation .acc).any (CaseFeature.abs ∈ ·) :=
  ⟨by decide, by decide⟩

/-- ABL/LOC syncretism: both map to {loc}. -/
theorem abl_loc_same_case_relation :
    Case.toCaseRelation .abl = Case.toCaseRelation .loc := rfl

-- ============================================================================
-- § 9: Bridge to Generic Containment
-- ============================================================================

/-- Case-specific `ViolatesABA` is the generic contiguity checker
    applied to the 4-position list [nom, acc, gen, dat].

    This makes the isomorphism with degree containment structural:
    both `AllomorphyPattern.ViolatesABA` and `DegreePattern.violatesABA`
    (in `DegreeContainment.lean`) reduce to the same generic predicate
    from `Containment.lean`. -/
theorem case_violatesABA_iff_generic (p : AllomorphyPattern) :
    p.ViolatesABA ↔
      Morphology.Containment.violatesABA [p.nom, p.acc, p.gen, p.dat] = true := by
  rw [Morphology.Containment.violatesABA_four]
  simp only [AllomorphyPattern.ViolatesABA, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]
  tauto

-- ============================================================================
-- § 10: Inventory Contiguity Predicate
-- ============================================================================

/-- Does an inventory respect Caha's containment hierarchy? True iff `inv`
    is downward-closed under the canonical `PartialOrder Case` (Caha
    containment): whenever `c ∈ inv` and `d ≤ c`, then `d ∈ inv`.

    Off-hierarchy cases (ERG, ABS, INST, COM, …) impose no constraint —
    in the Caha order, off-hierarchy `c` only has `c ≤ c`, so the
    downward-closure condition is vacuous. On-hierarchy `c` of rank `r`
    forces every lower on-hierarchy case (ranks `0, …, r-1`) into `inv`,
    which is exactly the prefix-contiguity Caha demands.

    This is the standard "lower set" predicate from order theory, applied
    to the Caha order extracted in `Core/Case/Order.lean`. Per-Fragment
    instantiation lives in `Phenomena/Case/Studies/Caha2009.lean`. -/
def RespectsCahaContainment (inv : Finset Case) : Prop :=
  ∀ c ∈ inv, ∀ d, d ≤ c → d ∈ inv

instance (inv : Finset Case) : Decidable (RespectsCahaContainment inv) := by
  unfold RespectsCahaContainment; infer_instance

end Interfaces.Morphosyntax.CaseContainment
