import Linglib.Theories.Phonology.Prosodic.Syllable.Defs

/-!
# Metrical Foot Structure
@cite{hayes-1995} @cite{kager-2007}

Foot types, metrical parsing, and OT constraints on metrical structure.

A metrical foot is a prosodic constituent grouping syllables into a
rhythmic unit. @cite{hayes-1995} identifies three canonical foot types:

| Type              | Well-formed shapes | Stress system   |
|-------------------|--------------------|-----------------|
| Moraic trochee    | (H), (LL)         | Weight-sensitive |
| Syllabic trochee  | (σσ)               | Weight-insensitive |
| Iamb              | (LH), (LL), (H)   | Right-prominent  |

The foot's *head* (prominent syllable) determines stress: initial in
trochees, final in iambs.

## Definitions

- `SyllWeight.morae`: mora count from weight class
- `FootType`: the three canonical foot types
- `ParseElement`: element in a metrical parse (footed or unfooted)
- `MetricalParse`: a complete metrical parse of a prosodic domain
- OT constraints: `ftBinViolations`, `parseSylViolations`, `allFtLeftViolations`
-/

namespace Phonology.Syllable

-- `SyllWeight.morae` is now a field accessor — no separate function needed.

-- ============================================================================
-- § 1: Foot Type
-- ============================================================================

/-- The three canonical foot types (@cite{hayes-1995}, Ch. 3). -/
inductive FootType where
  /-- Moraic trochee: bimoraic with initial prominence.
      Well-formed shapes: (H) = 2μ, (LL) = 2μ.
      Used in weight-sensitive stress (Turkish, Latin, Telugu). -/
  | moraicTrochee
  /-- Syllabic trochee: bisyllabic with initial prominence.
      Well-formed shape: (σσ) regardless of weight.
      Used in weight-insensitive stress (Czech, Pintupi). -/
  | syllabicTrochee
  /-- Iamb: prominence on the heavier/final syllable.
      Well-formed shapes: (LH), (LL), (H).
      Used in right-prominent stress (Creek, Yupik). -/
  | iamb
  deriving DecidableEq, Repr

-- ============================================================================
-- § 3: Metrical Parse
-- ============================================================================

/-- An element in a metrical parse: either a foot grouping syllables
    or an unparsed (stray) syllable. The list preserves left-to-right
    linear order within the prosodic domain. -/
inductive ParseElement where
  /-- A foot containing one or more syllables (represented by weight). -/
  | foot : List SyllWeight → ParseElement
  /-- An unparsed syllable not dominated by any foot. -/
  | unfooted : SyllWeight → ParseElement
  deriving DecidableEq, Repr

/-- A metrical parse: a prosodic domain represented as a linear sequence
    of footed and unfooted syllables. -/
abbrev MetricalParse := List ParseElement

-- ============================================================================
-- § 4: Parse Properties
-- ============================================================================

/-- Extract all feet from a parse. -/
def MetricalParse.feet (p : MetricalParse) : List (List SyllWeight) :=
  p.filterMap λ | .foot ws => some ws | .unfooted _ => none

/-- Mora count of a single foot. -/
def footMorae (ws : List SyllWeight) : Nat :=
  ws.foldl (· + ·.morae) 0

/-- Total syllable count in a parse. -/
def MetricalParse.syllableCount (p : MetricalParse) : Nat :=
  p.foldl (λ acc e => acc + match e with
    | .foot ws => ws.length
    | .unfooted _ => 1) 0

/-- Number of unparsed syllables in a parse. -/
def MetricalParse.unparsedCount (p : MetricalParse) : Nat :=
  p.filter (λ | .unfooted _ => true | _ => false) |>.length

/-- Is a foot degenerate (subminimal)? A monomoraic foot (L) is
    degenerate — it fails to meet the bimoraic minimum. -/
def isDegenerate (ws : List SyllWeight) : Prop :=
  footMorae ws < 2

instance (ws : List SyllWeight) : Decidable (isDegenerate ws) := by
  unfold isDegenerate; infer_instance

/-- Is a foot well-formed for the given foot type? -/
def isWellFormedFoot (ft : FootType) (ws : List SyllWeight) : Prop :=
  match ft with
  | .moraicTrochee => footMorae ws = 2
  | .syllabicTrochee => ws.length = 2
  | .iamb => footMorae ws ≥ 1 ∧ footMorae ws ≤ 3 ∧ ws.length ≤ 2

instance (ft : FootType) (ws : List SyllWeight) :
    Decidable (isWellFormedFoot ft ws) := by
  unfold isWellFormedFoot; cases ft <;> infer_instance

-- ============================================================================
-- § 5: OT Metrical Constraints
-- ============================================================================

/-- FT-BIN(μ): assign one violation for each foot that does not consist
    of exactly two morae (@cite{kager-2007}).

    Well-formed moraic trochees: (H) = 2μ, (LL) = 2μ.
    Violations: degenerate (L) = 1μ, superheavy (SH) = 3μ. -/
def ftBinViolations (p : MetricalParse) : Nat :=
  p.feet.filter (λ ws => footMorae ws != 2) |>.length

/-- PARSE-SYL: assign one violation for each syllable not parsed into
    a foot (@cite{kager-2007}). Drives exhaustive parsing. -/
def parseSylViolations (p : MetricalParse) : Nat :=
  p.unparsedCount

/-- ALL-FT-LEFT: for each foot, count the number of syllables
    intervening between the left edge of the prosodic domain and the
    left edge of the foot (@cite{kager-2007}). Sum over all feet.

    A foot at syllable position k (0-indexed) incurs k violations.
    Drives left-to-right iterative footing. -/
def allFtLeftViolations (p : MetricalParse) : Nat :=
  let rec go : List ParseElement → Nat → Nat
    | [], _ => 0
    | .foot ws :: rest, pos => pos + go rest (pos + ws.length)
    | .unfooted _ :: rest, pos => go rest (pos + 1)
  go p 0

/-- ALL-FT-RIGHT: for each foot, count the number of syllables
    intervening between the right edge of the foot and the right edge
    of the prosodic domain. Sum over all feet.

    Drives right-to-left iterative footing. -/
def allFtRightViolations (p : MetricalParse) : Nat :=
  let total := p.syllableCount
  let rec go : List ParseElement → Nat → Nat
    | [], _ => 0
    | .foot ws :: rest, pos =>
      let rightEdge := pos + ws.length
      (total - rightEdge) + go rest rightEdge
    | .unfooted _ :: rest, pos => go rest (pos + 1)
  go p 0

-- ============================================================================
-- § 6: Verification Theorems
-- ============================================================================

-- Mora counts

theorem heavy_foot_bimoraic : footMorae [.heavy] = 2 := rfl
theorem ll_foot_bimoraic : footMorae [.light, .light] = 2 := rfl
theorem light_foot_monomoraic : footMorae [.light] = 1 := rfl
theorem superheavy_foot_trimoraic : footMorae [.superheavy] = 3 := rfl

-- Well-formedness

theorem heavy_wellformed_mt :
    isWellFormedFoot .moraicTrochee [.heavy] := by decide

theorem ll_wellformed_mt :
    isWellFormedFoot .moraicTrochee [.light, .light] := by decide

theorem l_not_wellformed_mt :
    ¬ isWellFormedFoot .moraicTrochee [.light] := by decide

-- Degeneracy

theorem light_degenerate : isDegenerate [.light] := by decide
theorem heavy_not_degenerate : ¬ isDegenerate [.heavy] := by decide
theorem ll_not_degenerate : ¬ isDegenerate [.light, .light] := by decide

-- Example parses

/-- (ˈCV.CV).CV: one bimoraic foot (LL) + one unparsed light syllable.
    Models odd-numbered light-syllable strings with left-to-right
    moraic trochees: the final syllable is stranded. -/
private abbrev parse_llU : MetricalParse :=
  [.foot [.light, .light], .unfooted .light]

theorem llU_ftbin : ftBinViolations parse_llU = 0 := rfl
theorem llU_parsesyl : parseSylViolations parse_llU = 1 := rfl
theorem llU_allftleft : allFtLeftViolations parse_llU = 0 := rfl

/-- (ˈLL)(ˌH): two bimoraic feet. Models the Telugu stem-level parse
    of *samudr-am* 'ocean-n': (ˈsa.mu).(ˌdram). -/
private abbrev parse_llH : MetricalParse :=
  [.foot [.light, .light], .foot [.heavy]]

theorem llH_ftbin : ftBinViolations parse_llH = 0 := rfl
theorem llH_parsesyl : parseSylViolations parse_llH = 0 := rfl
theorem llH_allftleft : allFtLeftViolations parse_llH = 2 := rfl

/-- Competing parse: (ˈsa.mu).dram with final syllable unfooted.
    Worse on PARSE-SYL than (ˈsa.mu).(ˌdram). -/
private abbrev parse_llU_heavy : MetricalParse :=
  [.foot [.light, .light], .unfooted .heavy]

theorem llU_heavy_parsesyl : parseSylViolations parse_llU_heavy = 1 := rfl

/-- Competing parse: two monomoraic feet (ˈsa).(ˌmu).(ˌdram).
    Violates FT-BIN twice. -/
private abbrev parse_lllH : MetricalParse :=
  [.foot [.light], .foot [.light], .foot [.heavy]]

theorem lllH_ftbin : ftBinViolations parse_lllH = 2 := rfl

end Phonology.Syllable
