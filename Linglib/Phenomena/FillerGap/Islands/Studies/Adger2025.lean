import Linglib.Theories.Syntax.SynGraph
import Linglib.Phenomena.FillerGap.Islands.Data

set_option autoImplicit false

/-!
# Mereological Syntax Account of Islands
@cite{adger-2025}

@cite{adger-2025} derives island constraints from Angular Locality (AL)
and Dimensionality, without stipulating phases, barriers, or subjacency.
The key insight: transitivity of parthood does NOT cross dimensions.
When an element's path to the target traverses both 1-part and 2-part
edges, AL blocks movement.

## Island derivations

- **Subject islands**: The subject is a 2-part of T. Elements inside the
  subject reach it via 1-part edges, but the subject-to-T edge is a
  2-part edge — cross-dimensional. So elements inside the subject cannot
  be within-dimension transitive parts of any node in C's 1-part chain.
  But the subject DP *itself* can extract (it is T's direct 2-part).

- **Adjunct islands**: Same mechanism. The adjunct is a 2-part of v.
  Elements inside the adjunct traverse 1-part edges to reach the adjunct,
  then a 2-part edge to v — cross-dimensional.

- **Definite nominal islands**: When D has a filled 2-part (Det/Dem),
  elements inside the DP cannot subjoin to D (Dimensionality blocks it)
  AND cannot reach above D (the path crosses dimensions). Indefinite DPs
  (D with a free 2-part) are transparent.

- **Successive cyclicity**: Cross-clausal movement requires intermediate
  stops. An embedded wh must first stop at embedded C (within its EP),
  then reach matrix C (now in the right dimension chain).

## Connection to island typology

This file cross-references the `SynGraph` derivations with the island
constraint categories from `Data.lean`. The key prediction: subject,
adjunct, and CNPC islands all follow from the SAME mechanism (cross-
dimensional transitivity), not from separate constraints.

-/

namespace Phenomena.FillerGap.Islands.Studies.Adger2025

-- ════════════════════════════════════════════════════
-- § 1. Re-export key SynGraph theorems
-- ════════════════════════════════════════════════════

/-! The core AL derivations are verified in `SynGraph.lean` (§ 10):

- `al_blocks_superlocal`: antilocality (35a)
- `al_blocks_sideward`: no sideward movement (35c)
- `al_blocks_lowering`: no lowering (35b)
- `al_blocks_parallel`: no parallel merge (35d)
- `al_blocks_cross_dim` / `al_allows_within_dim`: cross-dimensional
  transitivity restriction (35e)
- `al_allows_rollup_2part` / `al_allows_rollup_1part`: roll-up movement
- `succ_cyc_blocked_cross_clause` / `succ_cyc_wh_reaches_C1_after_stop`:
  successive cyclicity
- `subject_island_blocks` / `subject_itself_can_extract`: subject islands
- `adjunct_island_blocks` / `adjunct_itself_can_extract`: adjunct islands
- `nominal_island_definite_blocks` / `nominal_island_indefinite_allows`:
  definite nominal islands / Specificity Condition
- `antilocality_sub1` / `antilocality_sub12`: general antilocality -/

-- ════════════════════════════════════════════════════
-- § 2. Unifying mechanism
-- ════════════════════════════════════════════════════

/-- All three strong island types (subject, adjunct, CNPC) are derived
    from the same mechanism: cross-dimensional transitivity failure.
    This contrasts with accounts that stipulate separate constraints
    for each island type.

    We verify that AL blocks extraction from within each type using
    the same `satisfiesAL` predicate. -/
theorem uniform_island_mechanism :
    -- Subject island: blocked
    (SynGraph.satisfiesAL
      (mkGraph 9
        [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
         (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨4, by omega⟩, ⟨5, by omega⟩),
         (⟨5, by omega⟩, ⟨6, by omega⟩), (⟨7, by omega⟩, ⟨8, by omega⟩)]
        [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨5, by omega⟩, ⟨7, by omega⟩)])
      ⟨8, by decide⟩ ⟨0, by decide⟩ = false) ∧
    -- Adjunct island: blocked
    (SynGraph.satisfiesAL
      (mkGraph 8
        [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
         (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
         (⟨6, by omega⟩, ⟨7, by omega⟩)]
        [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩)])
      ⟨7, by decide⟩ ⟨0, by decide⟩ = false) ∧
    -- Definite nominal island: blocked
    (SynGraph.satisfiesAL
      (mkGraph 10
        [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
         (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
         (⟨6, by omega⟩, ⟨7, by omega⟩)]
        [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
         (⟨5, by omega⟩, ⟨8, by omega⟩), (⟨6, by omega⟩, ⟨9, by omega⟩)])
      ⟨9, by decide⟩ ⟨0, by decide⟩ = false) :=
  ⟨by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 3. Island source classification
-- ════════════════════════════════════════════════════

/-- All island types that @cite{adger-2025} derives are classified as
    syntactic in `Data.lean`'s `constraintSource`. This is consistent:
    AL is a structural constraint. -/
theorem adger_derives_syntactic_islands :
    constraintSource .subject = .syntactic ∧
    constraintSource .adjunct = .syntactic ∧
    constraintSource .complexNP = .syntactic := ⟨rfl, rfl, rfl⟩

/-- @cite{adger-2025}'s account predicts that subject islands are weak
    (ameliorable): the subject *itself* can always extract; only
    sub-extraction is blocked. The data classification agrees. -/
theorem subject_island_weak :
    constraintStrength .subject = .weak := rfl

/-- Adjunct islands are strong in the data and strongly blocked by AL
    (the adjunct is a 2-part; cross-dimensional transitivity always
    fails for elements deeper than the adjunct itself). -/
theorem adjunct_island_strong :
    constraintStrength .adjunct = .strong := rfl

end Phenomena.FillerGap.Islands.Studies.Adger2025
