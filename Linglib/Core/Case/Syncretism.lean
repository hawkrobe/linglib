import Linglib.Core.Case.Hierarchy
import Linglib.Core.Case.Containment

/-!
# Case Syncretism @cite{blake-1994}
@cite{baerman-2005} @cite{caha-2009}

Syncretism is the systematic neutralization of case distinctions: two or more
cases share a single morphological exponent in some paradigm cells. @cite{blake-1994} documents syncretism patterns in Latin, Greek, and
other IE languages. He observes that syncretisms cluster into groups
(NOM+ACC vs. DAT+ABL) that are "significant on other grounds" (p. 22).

The **adjacency constraint** — that syncretic cases must be adjacent on the
case hierarchy — is a generalization from the Nanosyntax tradition, not an explicit claim by Blake. Blake's data is consistent with
it, and his ERG/INST syncretism (Australian languages) is the canonical
exception, which he explains via historical derivation of ERG from INST
(pp. 174–175).

## Examples

- NOM/ACC syncretism in neuter nouns (Latin, Greek, Russian): same tier (rank 6)
- COM/INST syncretism (WALS Ch. 52): adjacent (ranks 1, 2)

## Formalization

We define syncretism as a relation between two cases within a given inventory.
`hierarchyAdjacent` checks strict adjacency (ranks differ by ≤ 1).
`inventoryAdjacent` checks relaxed adjacency (no intervening case in the
actual inventory).

-/

namespace Core

-- ============================================================================
-- § 1: Syncretism as a Relation
-- ============================================================================

/-- A syncretism pattern: two cases share a morphological exponent. -/
structure Syncretism where
  /-- The two syncretic cases -/
  case1 : Case
  case2 : Case
  /-- The cases must be distinct -/
  neq : case1 ≠ case2
  deriving Repr

/-- Are two cases adjacent on the hierarchy (same rank or ranks differ by 1)?

    This is the strict form of the adjacency constraint. In
    practice, some syncretisms span larger distances (e.g., ERG/INST in
    Australian languages), but the generalization is that adjacency is the
    norm. -/
def hierarchyAdjacent (c1 c2 : Case) : Bool :=
  let r1 := c1.hierarchyRank
  let r2 := c2.hierarchyRank
  r1 == r2 || r1 + 1 == r2 || r2 + 1 == r1

/-- Relaxed adjacency: no case in the inventory falls strictly between
    the two syncretic cases on the hierarchy.

    This captures the idea that syncretism is "locally adjacent" within the
    language's actual inventory, even if non-adjacent on the full hierarchy.
    E.g., DAT/ACC might be adjacent in a system that lacks GEN. -/
def inventoryAdjacent (inv : List Case) (c1 c2 : Case) : Bool :=
  let lo := min c1.hierarchyRank c2.hierarchyRank
  let hi := max c1.hierarchyRank c2.hierarchyRank
  !inv.any fun c =>
    c != c1 && c != c2 && c.hierarchyRank > lo && c.hierarchyRank < hi

-- ============================================================================
-- § 2: Well-Known Syncretism Patterns
-- ============================================================================

/-- NOM/ACC syncretism (neuter nouns in Latin, Greek, Russian, etc.).
    Same rank — trivially adjacent. -/
def nomAccSyncretism : Syncretism :=
  ⟨.nom, .acc, by decide⟩

/-- COM/INST syncretism (WALS Ch. 52: many languages use one marker). -/
def comInstSyncretism : Syncretism :=
  ⟨.com, .inst, by decide⟩

-- ============================================================================
-- § 3: Adjacency Theorems
-- ============================================================================

/-- NOM/ACC syncretism satisfies strict adjacency (same tier). -/
theorem nom_acc_adjacent : hierarchyAdjacent .nom .acc = true := by native_decide

/-- COM/INST syncretism satisfies strict adjacency (ranks 1, 2). -/
theorem com_inst_adjacent : hierarchyAdjacent .com .inst = true := by native_decide

/-- DAT/LOC syncretism satisfies strict adjacency (ranks 4, 3). -/
theorem dat_loc_adjacent : hierarchyAdjacent .dat .loc = true := by native_decide

/-- GEN/DAT syncretism satisfies strict adjacency (ranks 5, 4). -/
theorem gen_dat_adjacent : hierarchyAdjacent .gen .dat = true := by native_decide

/-- ERG/INST syncretism does NOT satisfy strict adjacency (ranks 6, 2) —
    this is Blake's known exception, explained by historical derivation. -/
theorem erg_inst_not_strictly_adjacent :
    hierarchyAdjacent .erg .inst = false := by native_decide

/-- But ERG/INST IS inventory-adjacent in a system with only {ERG, ABS, INST}
    (no GEN, DAT, LOC between them). -/
theorem erg_inst_inv_adjacent :
    inventoryAdjacent [.erg, .abs, .inst] .erg .inst = true := by native_decide

-- ============================================================================
-- § 4: Syncretism Respects Hierarchy Direction
-- ============================================================================

/-- Same-tier cases (NOM/ACC, ERG/ABS, ABL/INST) are always strictly adjacent.
    These are the most common syncretism targets cross-linguistically. -/
theorem same_tier_adjacent (c1 c2 : Case)
    (h : c1.hierarchyRank = c2.hierarchyRank) :
    hierarchyAdjacent c1 c2 = true := by
  simp [hierarchyAdjacent, h]

-- ============================================================================
-- § 5: *ABA and Syncretism (@cite{caha-2009})
-- ============================================================================

-- The *ABA constraint (@cite{caha-2009}) applies to syncretism just as
-- it does to suppletive allomorphy: if NOM and GEN are syncretic
-- (same form), ACC must also share that form.

/-- NOM/ACC syncretism (neuter paradigms): NOM=ACC share form 0,
    GEN and DAT have form 1. AABB pattern — contiguous. -/
theorem neuter_syncretism_contiguous :
    (AllomorphyPattern.mk 0 0 1 1).isContiguous = true := by native_decide

/-- NOM/GEN syncretism without ACC syncretism would be an ABA pattern
    — predicted NOT to occur by @cite{caha-2009}. -/
theorem nom_gen_without_acc_violates_aba :
    (AllomorphyPattern.mk 0 1 0 1).violatesABA = true := by native_decide

/-- ACC/GEN syncretism with distinct NOM and DAT: ABBC — contiguous. -/
theorem acc_gen_syncretism_contiguous :
    (AllomorphyPattern.mk 0 1 1 2).isContiguous = true := by native_decide

/-- GEN/DAT syncretism: NOM and ACC distinct from GEN=DAT.
    AABC — contiguous. -/
theorem gen_dat_syncretism_contiguous :
    (AllomorphyPattern.mk 0 1 2 2).isContiguous = true := by native_decide

/-- NOM/DAT syncretism (skipping ACC and GEN): ABBA — violates *ABA.
    The containment hierarchy predicts this cannot occur: DAT contains
    ACC, so any form shared by NOM and DAT must also be shared by ACC. -/
theorem nom_dat_syncretism_violates_aba :
    (AllomorphyPattern.mk 0 1 1 0).violatesABA = true := by native_decide

end Core
