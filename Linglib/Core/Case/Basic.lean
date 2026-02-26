/-!
# Case: Theory-Neutral Inventory @cite{blake-1994}

A framework-agnostic case inventory drawn from Blake's (1994) cross-linguistic
survey. These 16 values cover the cases attested across Blake's typological
sample (Chs. 2, 5). Every syntactic framework (Minimalism, HPSG, DG, CCG)
can import this type without committing to a particular theory of case assignment.

The inventory is ordered by Blake's case hierarchy (§5.8): if a language has a
case lower on the hierarchy, it usually has all cases above it. The formal
hierarchy itself lives in `Core.Case.Hierarchy`.

## Core vs. Peripheral

Blake's most basic distinction (p. 32): **core** cases (NOM/ACC in accusative
systems, ERG/ABS in ergative systems) mark grammatical relations determined by
argument structure. **Peripheral** cases mark semantic roles (source, goal,
instrument, etc.). The `isCore` predicate encodes this partition, parameterized
by alignment type.

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press.
- Comrie, B. (1978). Ergativity. In Lehmann, W. P. (ed.), *Syntactic Typology*.
-/

namespace Core

-- ============================================================================
-- § 1: Alignment Family
-- ============================================================================

/-- Alignment family for determining which cases are core.

    Duplicated from `Phenomena.Alignment.Typology.AlignmentType` at the level
    of the two major families relevant to core-case identification. Core
    infrastructure cannot import Phenomena. -/
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

    The 16 values cover the morphological cases attested across Blake's
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
-- § 3: Core vs. Peripheral
-- ============================================================================

/-- Is this case a core grammatical case under the given alignment?

    Core cases mark the primary grammatical relations (subject, object) and
    are determined by argument structure rather than semantic role. In
    accusative systems, NOM and ACC are core. In ergative systems, ERG and
    ABS are core. All other cases are peripheral (Blake 1994, p. 32). -/
def Case.isCore (alignment : AlignmentFamily) : Case → Bool
  | .nom => alignment == .accusative
  | .acc => alignment == .accusative
  | .erg => alignment == .ergative
  | .abs => alignment == .ergative
  | _    => false

/-- Is this case peripheral (not core)? -/
def Case.isPeripheral (alignment : AlignmentFamily) (c : Case) : Bool :=
  !c.isCore alignment

-- ============================================================================
-- § 4: Core/Peripheral Theorems
-- ============================================================================

/-- In accusative systems, exactly NOM and ACC are core. -/
theorem acc_core_nom : Case.isCore .accusative .nom = true := rfl
theorem acc_core_acc : Case.isCore .accusative .acc = true := rfl
theorem acc_periph_erg : Case.isCore .accusative .erg = false := rfl
theorem acc_periph_dat : Case.isCore .accusative .dat = false := rfl

/-- In ergative systems, exactly ERG and ABS are core. -/
theorem erg_core_erg : Case.isCore .ergative .erg = true := rfl
theorem erg_core_abs : Case.isCore .ergative .abs = true := rfl
theorem erg_periph_nom : Case.isCore .ergative .nom = false := rfl
theorem erg_periph_acc : Case.isCore .ergative .acc = false := rfl

/-- DAT is always peripheral regardless of alignment. -/
theorem dat_always_peripheral (a : AlignmentFamily) :
    Case.isPeripheral a .dat = true := by
  cases a <;> rfl

/-- LOC is always peripheral regardless of alignment. -/
theorem loc_always_peripheral (a : AlignmentFamily) :
    Case.isPeripheral a .loc = true := by
  cases a <;> rfl

-- ============================================================================
-- § 5: Exhaustive Enumeration
-- ============================================================================

/-- All 16 case values (for finite verification). -/
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
