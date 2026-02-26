import Linglib.Core.Case.Hierarchy

/-!
# Case Syncretism @cite{blake-2001}

Syncretism is the systematic neutralization of case distinctions: two or more
cases share a single morphological exponent in some paradigm cells. Blake
(2001, Ch. 2) documents that syncretism patterns are constrained by the case
hierarchy — syncretic cases must be **adjacent** on the hierarchy.

## Examples

- NOM/ACC syncretism in neuter nouns (Latin, Greek, Russian): adjacent (rank 6)
- DAT/ACC syncretism in German, many IE languages: adjacent (ranks 6, 4 —
  but GEN intervenes, so this requires a refined notion of adjacency within the
  inventory, not the full hierarchy)
- ERG/INST syncretism in Australian languages: adjacent (ranks 6, 2 — but
  this is a known counterexample to strict adjacency; Blake argues it reflects
  historical derivation of ERG from INST)

## Formalization

We define syncretism as a relation between two cases within a given inventory.
The **adjacency constraint** says that for two cases to be syncretic, no case
between them on the hierarchy can be distinctly marked in the same inventory.

## References

- Blake, B. J. (2001). *Case* (2nd ed.). Cambridge University Press. Ch. 2.
- Baerman, M. et al. (2005). *The Syntax-Morphology Interface*. CUP.
- Caha, P. (2009). *The Nanosyntax of Case*. Ph.D. thesis, Tromsø.
-/

namespace Core.Case

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

    This is the strict form of Blake's adjacency constraint. In practice,
    some syncretisms span larger distances (e.g., ERG/INST in Australian
    languages), but the generalization is that adjacency is the norm. -/
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

/-- ERG/INST syncretism (many Australian languages).
    Blake (2001) argues ERG historically derives from INST. -/
def ergInstSyncretism : Syncretism :=
  ⟨.erg, .inst, by decide⟩

/-- DAT/ALL syncretism (Latin ad, many languages merge goal/recipient). -/
def datAllSyncretism : Syncretism :=
  ⟨.dat, .all, by decide⟩

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

end Core.Case
