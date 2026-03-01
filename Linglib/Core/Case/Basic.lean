/-!
# Case: Theory-Neutral Inventory @cite{blake-1994}
@cite{comrie-1978}

A framework-agnostic case inventory drawn from Blake's (1994) cross-linguistic
survey. These 19 values cover the cases attested across Blake's typological
sample (Chs. 2, 5). Every syntactic framework (Minimalism, HPSG, DG, CCG)
can import this type without committing to a particular theory of case assignment.

The inventory is ordered by Blake's case hierarchy (§5.8): if a language has a
case lower on the hierarchy, it usually has all cases above it. The formal
hierarchy itself lives in `Core.Case.Hierarchy`.

## Core vs. Peripheral

Blake's most basic distinction (p. 32): **core** cases (NOM/ACC in accusative
systems, ERG/ABS in ergative systems) mark grammatical relations determined by
argument structure. **Peripheral** cases mark semantic roles (source, goal,
instrument, etc.).

-/

namespace Core

-- ============================================================================
-- § 1: Alignment Family
-- ============================================================================

/-- The two major morphosyntactic alignment families (Blake 1994, Ch. 2).

    Used by `SplitErgativity` to parameterize which alignment a split-ergative
    system selects. The full five-way typology (neutral, accusative, ergative,
    tripartite, active) lives in `Phenomena.Alignment.Typology.AlignmentType`;
    this Core type restricts to the two families relevant to case splits. -/
inductive AlignmentFamily where
  /-- Accusative alignment: S = A (NOM) vs P (ACC) -/
  | accusative
  /-- Ergative alignment: S = P (ABS) vs A (ERG) -/
  | ergative
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Case Inventory
-- ============================================================================

/-- Cross-linguistic case inventory (Blake 1994, Chs. 2, 5).

    The 19 values cover the morphological cases attested across Blake's
    typological sample. Ordered roughly by the Blake hierarchy (formalized
    in `Hierarchy.lean`), from core grammatical cases to peripheral
    semantic cases. -/
inductive Case where
  -- Core grammatical cases (Ch. 2, 5)
  /-- Nominative: unmarked subject in accusative systems -/
  | nom
  /-- Accusative: transitive patient in accusative systems -/
  | acc
  /-- Ergative: transitive agent in ergative systems -/
  | erg
  /-- Absolutive: unmarked S/P in ergative systems -/
  | abs
  -- Major peripheral cases (Ch. 2, 5)
  /-- Genitive: possessor, partitive source -/
  | gen
  /-- Dative: recipient, goal, experiencer -/
  | dat
  /-- Locative: spatial location -/
  | loc
  /-- Ablative: spatial source, origin -/
  | abl
  /-- Allative: spatial goal, direction toward -/
  | all
  /-- Instrumental: means, instrument -/
  | inst
  /-- Comitative: accompaniment ('with X') -/
  | com
  -- Minor/rare cases (Ch. 5)
  /-- Vocative: direct address -/
  | voc
  /-- Partitive: partial affectedness, existential -/
  | part
  /-- Perlative: path, motion through -/
  | perl
  /-- Benefactive: beneficiary -/
  | ben
  /-- Causal: reason, cause -/
  | caus
  -- Finnish/Uralic-specific (Karlsson 2018, Blake 1994 "others")
  /-- Essive: state or role ('as X') — Finnish -nA -/
  | ess
  /-- Translative: change of state ('becoming X') — Finnish -ksi -/
  | transl
  /-- Abessive: privative ('without X') — Finnish -ttA -/
  | abess
  deriving DecidableEq, BEq, Repr, Inhabited

-- ============================================================================
-- § 3: Exhaustive Enumeration
-- ============================================================================

/-- All 19 case values (for finite verification). -/
def Case.allCases : List Case :=
  [.nom, .acc, .erg, .abs, .gen, .dat, .loc, .abl,
   .all, .inst, .com, .voc, .part, .perl, .ben, .caus,
   .ess, .transl, .abess]

theorem Case.allCases_length : Case.allCases.length = 19 := by native_decide

/-- Check that a case is in the exhaustive list (Bool version for native_decide). -/
def Case.inAllCases (c : Case) : Bool :=
  Case.allCases.any (· == c)

/-- Every case is in the exhaustive list. -/
theorem Case.allCases_complete (c : Case) : c.inAllCases = true := by
  cases c <;> native_decide

end Core
