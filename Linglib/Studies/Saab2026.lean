import Linglib.Syntax.Minimalist.Ellipsis.Nominal
import Linglib.Syntax.Minimalist.ExtendedProjection.Properties
import Linglib.Semantics.Quantification.BinominalDefs
import Linglib.Features.Number.Basic
import Linglib.Data.Examples.Saab2026

/-!
# Minimalist Nominal Spine → NP-Ellipsis [saab-2026]
[lobeck-1995] [ritter-1991]

Connects the Minimalist nominal extended projection (N → n → Q → Num → D)
to the NP-ellipsis data in Spanish binominals.

## Key Results

1. The nominal argument domain (nP = {N, n}) parallels the verbal
   argument domain (vP = {V, v}) at the same F-level cutoff.
2. NP-ellipsis targets exactly the nominal argument domain: everything
   at or below n (F1) is deleted when Num carries [E].
3. Pseudo-partitive and quantificational binominals have Num[E];
   qualitative binominals lack it due to their EquP structure.
4. The genitive source ([pesetsky-2013] primeval vs. equative) and the
   verbal-agreement number track the same split, and the typed example
   rows (`Data.Examples.Saab2026`) conform to all predictions.

-/

namespace Saab2026

open Minimalist
open Minimalist.Ellipsis.Nominal
open Quantification.Binominal

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
-- § 4: Genitive Source and Verbal Agreement
-- ═══════════════════════════════════════════════════════════════

/-- The structural source of the genitive *de* in a binominal. -/
inductive GenitiveSource where
  /-- [pesetsky-2013]'s primeval genitive: default case assigned when
      D blocks structural case. -/
  | primeval
  /-- [dendikken-2006]-style EquP predication, not a true genitive. -/
  | equative
  deriving DecidableEq, Repr

/-- Map a binominal type to its genitive source. Pseudo-partitive and
    quantificational binominals have the primeval genitive; qualitative
    binominals have the equative structure, whose indexical empty noun
    (contextually referential, like a pronoun) is unrecoverable at the
    ellipsis site. -/
def genitiveSource : BinominalType → GenitiveSource
  | .pseudoPartitive  => .primeval
  | .quantificational => .primeval
  | .qualitative      => .equative

/-- Primeval genitive ↔ NP-ellipsis licensed: the genitive source and
    Num[E]-driven licensing are coextensive across binominal types. -/
theorem primeval_iff_npe (b : BinominalType) :
    (genitiveSource b == .primeval) = b.licensesNPE := by
  cases b <;> rfl

/-- The number on the verb for each binominal type: Num inherits plural
    from the complement NP in pseudo-partitives and quantificationals,
    but gets singular from the expressive noun in qualitatives. -/
def verbAgreement : BinominalType → Number
  | .pseudoPartitive  => .plural
  | .quantificational => .plural
  | .qualitative      => .singular

-- ═══════════════════════════════════════════════════════════════
-- § 5: Conformance with the Example Data
-- ═══════════════════════════════════════════════════════════════

/-- Parse a `binominal_type` paper-feature value. -/
def binominalOfFeature : String → Option BinominalType
  | "pseudo_partitive" => some .pseudoPartitive
  | "quantificational" => some .quantificational
  | "qualitative"      => some .qualitative
  | _                  => none

/-- Parse a `verb_agreement` paper-feature value. -/
def numberOfFeature : String → Option Number
  | "singular" => some .singular
  | "plural"   => some .plural
  | _          => none

/-- Every example row's `npe_grammatical` and `verb_agreement` features
    match the predictions (`licensesNPE`, `verbAgreement`) for its
    `binominal_type`. -/
theorem examples_conform :
    Examples.all.all (λ e =>
      match (e.paperFeatures.lookup "binominal_type").bind binominalOfFeature with
      | some b =>
          e.paperFeatures.lookup "npe_grammatical"
            == some (if b.licensesNPE then "true" else "false") &&
          (e.paperFeatures.lookup "verb_agreement").bind numberOfFeature
            == some (verbAgreement b)
      | none => false) := by decide

-- ═══════════════════════════════════════════════════════════════
-- § 6: EP-Internal Relations in the Nominal Spine
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

end Saab2026
