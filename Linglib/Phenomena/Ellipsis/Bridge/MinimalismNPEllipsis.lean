import Linglib.Phenomena.Ellipsis.NPEllipsis
import Linglib.Theories.Syntax.Minimalism.Formal.Sluicing.FormalMatching
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Properties

/-!
# Bridge: Minimalist Nominal Spine → NP-Ellipsis @cite{saab-2026}

Connects the Minimalist nominal extended projection (N → n → Q → Num → D)
to the NP-ellipsis data in Spanish binominals.

## Key Results

1. The nominal argument domain (nP = {N, n}) parallels the verbal
   argument domain (vP = {V, v}) at the same F-level cutoff.
2. NP-ellipsis targets exactly the nominal argument domain: everything
   at or below n (F1) is deleted when Num carries [E].
3. Pseudo-partitive and quantificational binominals have Num[E];
   qualitative binominals lack it due to their EquP structure.

## References

- Saab, A. (2026). NP-Ellipsis Patterns in Spanish Binominals.
- Ritter, E. (1991). Two Functional Categories in Noun Phrases.
- Lobeck, A. (1995). Ellipsis: Functional Heads, Licensing, and
  Identification.
-/

namespace Phenomena.Ellipsis.Bridge.MinimalismNPEllipsis

open Minimalism
open Minimalism.Sluicing
open Phenomena.Ellipsis.NPEllipsis

-- ═══════════════════════════════════════════════════════════════
-- § 1: Nominal Extended Projection Well-Formedness
-- ═══════════════════════════════════════════════════════════════

/-- The full nominal EP [N, n, Q, Num, D] is well-formed:
    category-consistent and F-monotone. -/
theorem nominal_ep_wellformed :
    allCategoryConsistent fullNominalEP = true ∧
    allFMonotone fullNominalEP = true := by decide

/-- The nominal spine is structurally parallel to the verbal spine
    at all F-levels: lexical (F0) → categorizer (F1) → specification
    (F2) → inner edge (F3) → discourse (F4+).

    At F2–F3, the parallel is structural (same EP zone) rather than
    functional: T specifies temporally while Q specifies via
    individuation; Fin types the clause while Num types the nominal. -/
theorem nominal_verbal_spine_parallel :
    fValue .N = fValue .V ∧
    fValue .n = fValue .v ∧
    fValue .Q = fValue .T ∧
    fValue .Num = fValue .Fin := by decide

-- ═══════════════════════════════════════════════════════════════
-- § 2: Argument Domain Symmetry
-- ═══════════════════════════════════════════════════════════════

/-- The verbal and nominal argument domains use the same F-level
    boundary (F1): v for clauses, n for noun phrases. -/
theorem argdomain_boundary_parallel :
    fValue (argumentDomainCat .C) = fValue (argumentDomainCat .D) := by decide

/-- The verbal argument domain is {V, v} (F0–F1).
    The nominal argument domain is {N, n} (F0–F1).
    Both exclude inflectional heads (T/Num at F2). -/
theorem verbal_nominal_argdomain_symmetric :
    -- Verbal: V and v are in, T is out
    isInArgumentDomain .V .C = true ∧
    isInArgumentDomain .v .C = true ∧
    isInArgumentDomain .T .C = false ∧
    -- Nominal: N and n are in, Q (first head above n) is out
    isInArgumentDomain .N .D = true ∧
    isInArgumentDomain .n .D = true ∧
    isInArgumentDomain .Q .D = false := by decide

-- ═══════════════════════════════════════════════════════════════
-- § 3: NP-Ellipsis Licensing via Num[E]
-- ═══════════════════════════════════════════════════════════════

/-- Build a NominalEllipsisLicense from a BinominalType. -/
def mkNominalLicense (b : BinominalType) : NominalEllipsisLicense :=
  { numHasE := b.hasNumE }

/-- Pseudo-partitive Num[E] licenses NP-ellipsis. -/
theorem pseudopartitive_license :
    (mkNominalLicense .pseudoPartitive).isLicensed = true := by decide

/-- Quantificational Num[E] licenses NP-ellipsis. -/
theorem quantificational_license :
    (mkNominalLicense .quantificational).isLicensed = true := by decide

/-- Qualitative lacks Num[E], blocking NP-ellipsis. -/
theorem qualitative_no_license :
    (mkNominalLicense .qualitative).isLicensed = false := by decide

/-- The licensing prediction matches the empirical data for every
    binominal type. -/
theorem licensing_matches_data (b : BinominalType) :
    (mkNominalLicense b).isLicensed = b.licensesNPE := by
  cases b <;> decide

-- ═══════════════════════════════════════════════════════════════
-- § 4: EP-Internal Relations in the Nominal Spine
-- ═══════════════════════════════════════════════════════════════

/-- Each nominal functional head is EP-internal to the next higher
    head — complement selection proceeds up the nominal spine:
    N(F0) → n(F1) → Q(F2) → Num(F3) → D(F4). -/
theorem nominal_spine_ep_internal :
    isEPInternal .N .n = true ∧
    isEPInternal .n .Q = true ∧
    isEPInternal .Q .Num = true ∧
    isEPInternal .Num .D = true := by decide

/-- Nominal heads are EP-external to verbal projections:
    a DP in Spec,vP is always EP-external (nominal ≠ verbal). -/
theorem nominal_external_to_verbal :
    isEPExternal .D .v = true ∧
    isEPExternal .Q .T = true ∧
    isEPExternal .n .v = true := by decide

end Phenomena.Ellipsis.Bridge.MinimalismNPEllipsis
