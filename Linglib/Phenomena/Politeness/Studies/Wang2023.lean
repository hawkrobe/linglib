import Linglib.Features.PrivativePair
import Linglib.Core.Constraint.OT.Basic
import Linglib.Theories.Semantics.Presupposition.PhiFeatures
import Linglib.Theories.Semantics.Presupposition.MaximizePresupposition
import Linglib.Theories.Syntax.Minimalism.Features
import Linglib.Phenomena.Politeness.Honorifics

/-!
# Wang (Ruoan) 2023: Honorifics without [HON]
@cite{wang-r-2023}

Wang, R. (2023). Honorifics without [HON].
*Natural Language & Linguistic Theory*, 41(4), 1287--1347.

## Core Insight

The cross-linguistic pattern of honorific pronoun recruitment — only
PL, 3rd, INDEF are recruited; never SG, 1st/2nd, DEF — falls out from
the interaction of phi-feature presuppositions (@cite{sauerland-2003},
@cite{harbour-2016}) with a pragmatic maxim called the **Taboo of
Directness** (ToD).

## Key Result

ToD reverses Maximize Presupposition (@cite{heim-1991}): where MP!
prefers the strongest available presupposition (= most marked form),
ToD prefers the weakest (= least marked = semantically unmarked). The
semantically unmarked values — plural, 3rd person, indefinite — are
precisely those at `PrivativePair.minimal` (specLevel 0), with vacuous
presuppositions.

No dedicated [HON] feature is needed. The attested patterns are derived
from the same `PrivativePair` structure that governs ordinary phi-feature
semantics, plus a single pragmatic constraint (ToD).

## Architecture

This file connects three layers:
- `Features.PrivativePair`: the algebraic structure (specLevel ordering)
- `Theories.Semantics.Presupposition.PhiFeatures`: presuppositional
  denotations, semantic markedness, and presuppositional strength ordering
- `Core.Constraint.OT`: constraint evaluation and factorial typology

## Sections

1. Typological data: the three attested honorific strategies
2. ToD and MP! as OT constraints (derived from `presupStrength`)
3. Binary case: ToD >> MP! derives unmarked recruitment
4. Ternary case: Strong/Weak ToD for articulated number systems
5. [iHON] eliminability — bridge to @cite{alok-bhalla-2026}
6. Bridges to `Honorifics.lean` and phi-feature denotations
7. General structural theorem: ToD >> MP! selects unmarked for ANY candidate set
8. HonLevel ↔ PrivativePair bridge — `PhiFeatures HonLevel` instance
-/

set_option autoImplicit false

namespace Wang2023

open Features (PrivativePair PhiFeatures)
open Core.Constraint.OT (NamedConstraint ConstraintFamily mkTableau
              mkFactorialOptima mkFactorialTypologySize)
open Semantics.Presupposition.PhiFeatures (isSemanticUnmarked presupStrength
  presupWeakerThan wellFormed_specLevel_le_two sgSem plSem)
open Phenomena.Politeness.Honorifics (AllocDatum allAllocData)

-- ============================================================================
-- §1  Typological Data
-- ============================================================================

/-!
## §1: Typological Data

Three honorific strategies are attested cross-linguistically — each
recruits the **semantically unmarked** value of a phi-feature domain:

| Domain       | Strategy         | Unmarked value    | Examples                |
|-------------|------------------|-------------------|-------------------------|
| Number      | Plural pronoun   | PL (specLevel 0)  | French, Slovenian       |
| Person      | 3rd person       | 3rd (specLevel 0) | Ainu, Malay             |
| Definiteness| Indefinite       | INDEF (specLevel 0)| Ainu (DP strategy)     |

No language recruits a semantically **marked** value (SG, 1st/2nd, DEF)
for honorification. @cite{wang-r-2023} derives this from the ToD.
-/

/-- The three attested honorific recruitment strategies. Each targets
    a different phi-feature domain but always recruits the **minimal**
    cell (specLevel 0) within that domain. -/
inductive HonStrategy where
  | plural       -- Use plural for singular referent (French vous)
  | thirdPerson  -- Use 3rd person for 2nd person referent (Ainu)
  | indefinite   -- Use indefinite for definite referent (Ainu DP)
  deriving DecidableEq, Repr

/-- Map each strategy to the PrivativePair cell that is recruited.
    The key empirical generalization: all three strategies map to the
    same cell — `.minimal` (specLevel 0). -/
def honStrategyCell : HonStrategy → PrivativePair
  | .plural      => .minimal  -- PL = specLevel 0
  | .thirdPerson => .minimal  -- 3rd = specLevel 0
  | .indefinite  => .minimal  -- INDEF = specLevel 0

/-- All attested strategies recruit the minimal (unmarked) cell.
    This is the empirical generalization that the ToD analysis derives. -/
theorem all_strategies_use_minimal :
    ∀ s : HonStrategy, honStrategyCell s = .minimal :=
  fun s => by cases s <;> rfl

/-- Corollary: all attested strategies recruit a semantically unmarked
    value. Follows from `all_strategies_use_minimal` + `minimal_is_unmarked`. -/
theorem all_strategies_use_unmarked :
    ∀ s : HonStrategy, isSemanticUnmarked (honStrategyCell s) = true :=
  fun s => (all_strategies_use_minimal s) ▸ rfl

/-- A language's honorific profile: which strategies it uses. -/
structure HonProfile where
  language : String
  strategies : List HonStrategy
  deriving Repr

-- Representative languages from Wang 2023
def french    : HonProfile := ⟨"French",    [.plural]⟩
def italian   : HonProfile := ⟨"Italian",   [.plural, .thirdPerson]⟩
def german    : HonProfile := ⟨"German",    [.plural, .thirdPerson]⟩  -- Sie is 3p.pl
def ainu      : HonProfile := ⟨"Ainu",      [.thirdPerson, .indefinite]⟩
def slovenian : HonProfile := ⟨"Slovenian", [.plural]⟩

def table1 : List HonProfile := [french, italian, german, ainu, slovenian]

/-- Every language in the typological data uses only unmarked strategies. -/
theorem table1_all_unmarked :
    table1.all (fun hp => hp.strategies.all
      (fun s => isSemanticUnmarked (honStrategyCell s))) = true := by
  native_decide

-- ============================================================================
-- §2  ToD and MP! as OT Constraints
-- ============================================================================

/-!
## §2: Taboo of Directness (ToD) and Maximize Presupposition (MP!)

**ToD**: In respect contexts, avoid the form with the strongest
presupposition. Violation count = `presupStrength` (= specLevel).

**MP!**: Use the form with the strongest satisfied presupposition.
Violation count = max presupStrength − `presupStrength`.

ToD and MP! are **antagonistic**: for any two distinct well-formed
cells, they prefer opposite directions. This is the structural heart
of @cite{wang-r-2023}'s analysis.

The constraints are defined in terms of `presupStrength` from
`Theories.Semantics.Presupposition.PhiFeatures`, not reimplemented —
ToD IS the presuppositional strength ordering.
-/

/-- ToD constraint: penalizes presuppositional strength.
    Defined as `presupStrength` — ToD literally IS the strength
    ordering from `PhiFeatures`, applied as an OT penalty. -/
def todConstraint : NamedConstraint PrivativePair :=
  { name := "ToD"
  , family := .markedness
  , eval := presupStrength }

/-- MP! constraint: penalizes failure to maximize presupposition.
    Violation count = maxSpecLevel − presupStrength.
    `PrivativePair.spec_maximal` proves maxSpecLevel = 2. -/
def mpConstraint : NamedConstraint PrivativePair :=
  { name := "MP!"
  , family := .faithfulness
  , eval := fun c => PrivativePair.maximal.specLevel - presupStrength c }

/-- ToD's evaluation IS `presupStrength` — not a reimplementation. -/
theorem tod_eval_eq_presupStrength (c : PrivativePair) :
    todConstraint.eval c = presupStrength c := rfl

/-- ToD prefers exactly the presuppositionally weaker cell.
    This is the bridge between OT evaluation and the `presupWeakerThan`
    ordering from `PhiFeatures`: fewer ToD violations ↔ weaker presupposition. -/
theorem tod_prefers_weaker (c₁ c₂ : PrivativePair) :
    todConstraint.eval c₁ < todConstraint.eval c₂ ↔
    presupWeakerThan c₁ c₂ = true := by
  simp [todConstraint, presupStrength, presupWeakerThan]

/-- ToD and MP! impose opposite orderings on well-formed cells:
    ToD prefers c₁ iff MP! prefers c₂. -/
theorem tod_reverses_mp (c₁ c₂ : PrivativePair)
    (hw₁ : c₁.wellFormed = true) (hw₂ : c₂.wellFormed = true) :
    todConstraint.eval c₁ < todConstraint.eval c₂ ↔
    mpConstraint.eval c₁ > mpConstraint.eval c₂ := by
  have h₁ := wellFormed_specLevel_le_two c₁ hw₁
  have h₂ := wellFormed_specLevel_le_two c₂ hw₂
  show presupStrength c₁ < presupStrength c₂ ↔
       PrivativePair.maximal.specLevel - presupStrength c₁ >
       PrivativePair.maximal.specLevel - presupStrength c₂
  simp only [presupStrength, PrivativePair.spec_maximal]; omega

/-- ToD prefers the minimal (unmarked) cell: it has 0 violations. -/
theorem tod_minimal_zero : todConstraint.eval .minimal = 0 := rfl

/-- MP! prefers the maximal (most marked) cell: it has 0 violations. -/
theorem mp_maximal_zero : mpConstraint.eval .maximal = 0 := rfl

/-- `mpConstraint` is an instance of the general `phiMP` from
    `MaximizePresupposition`: same eval function, same name, same family.
    This connects Wang2023's domain-specific MP! to the general theory. -/
theorem mpConstraint_eq_phiMP :
    mpConstraint = Semantics.Presupposition.MaximizePresupposition.phiMP := rfl

/-- `todConstraint.eval` equals `markednessPenalty presupStrength`.eval.
    ToD is an instance of the general markedness penalty from
    `MaximizePresupposition`. -/
theorem todConstraint_eval_eq_markednessPenalty (c : PrivativePair) :
    todConstraint.eval c =
    (Semantics.Presupposition.MaximizePresupposition.markednessPenalty presupStrength).eval c := rfl

/-- `tod_reverses_mp` is a corollary of the general
    `mp_reverses_markedness` theorem from `MaximizePresupposition`. -/
theorem tod_reverses_mp_from_general (c₁ c₂ : PrivativePair)
    (hw₁ : c₁.wellFormed = true) (hw₂ : c₂.wellFormed = true) :
    todConstraint.eval c₁ < todConstraint.eval c₂ ↔
    mpConstraint.eval c₁ > mpConstraint.eval c₂ :=
  Semantics.Presupposition.MaximizePresupposition.phi_mp_reverses_markedness c₁ c₂ hw₁ hw₂

-- ============================================================================
-- §3  Binary Case: ToD >> MP! Derives Unmarked Recruitment
-- ============================================================================

/-!
## §3: Binary Phi-Feature Domains

For binary phi-feature contrasts (SG/PL, 1st/3rd, DEF/INDEF), the
candidate set is {maximal, minimal}. Under ToD >> MP!, the optimal
candidate is the minimal (unmarked) cell — deriving the universal
recruitment of unmarked values for honorification.
-/

/-- Binary candidate set: {maximal, minimal}. -/
def binaryCandidates : List PrivativePair := [.maximal, .minimal]

private theorem binaryCandidates_ne : binaryCandidates ≠ [] := by
  simp [binaryCandidates]

/-- **Core prediction**: ToD >> MP! selects the minimal (unmarked) cell.
    Respect contexts recruit the semantically unmarked value.

    This is the central theorem: the recruitment generalization
    (`all_strategies_use_minimal`) is DERIVED, not stipulated.
    It follows from the interaction of two independently motivated
    constraints (ToD from politeness, MP! from presupposition theory)
    evaluated over the `PrivativePair` structure from @cite{harbour-2016}. -/
theorem tod_mp_selects_minimal :
    (mkTableau binaryCandidates [todConstraint, mpConstraint]
      binaryCandidates_ne).optimal = {PrivativePair.minimal} := by
  native_decide

/-- Converse: MP! >> ToD selects the maximal (marked) cell.
    Non-respect speech uses the strongest presupposition.
    This is the standard Maximize Presupposition from @cite{heim-1991}. -/
theorem mp_tod_selects_maximal :
    (mkTableau binaryCandidates [mpConstraint, todConstraint]
      binaryCandidates_ne).optimal = {PrivativePair.maximal} := by
  native_decide

/-- The optimal candidate under ToD >> MP! is semantically unmarked. -/
theorem tod_mp_optimal_is_unmarked :
    ∀ c ∈ (mkTableau binaryCandidates [todConstraint, mpConstraint]
      binaryCandidates_ne).optimal,
      isSemanticUnmarked c = true := by
  decide

/-- Factorial typology: the binary ToD/MP! system predicts exactly
    2 language types — honorific (unmarked) vs normal (marked). -/
theorem binary_factorial_typology :
    mkFactorialTypologySize binaryCandidates [todConstraint, mpConstraint]
      binaryCandidates_ne = 2 := by
  native_decide

-- ============================================================================
-- §4  Ternary Case: Articulated Number Systems
-- ============================================================================

/-!
## §4: Articulated Number (SG/DU/PL)

Languages with a three-way number distinction (singular/dual/plural)
require two ToD strengths:

- **SToD** (Strong ToD): penalizes ALL marked candidates (specLevel > 0).
  Identical to `todConstraint` — same `presupStrength` penalty.
- **WToD** (Weak ToD): penalizes only the MOST marked candidate (specLevel = 2).
  Tolerates intermediate marking.

The factorial typology over {SToD, WToD, MP!} with candidates
{maximal, intermediate, minimal} derives exactly **3 patterns**:

| Ranking               | Optimal       | Interpretation          |
|-----------------------|---------------|-------------------------|
| MP! dominant          | maximal (SG)  | Normal speech           |
| WToD >> MP! >> SToD   | intermediate (DU) | Moderate respect    |
| SToD dominant         | minimal (PL)  | Maximal respect (French) |
-/

/-- Ternary candidate set: {maximal, intermediate, minimal}. -/
def ternaryCandidates : List PrivativePair :=
  [.maximal, .intermediate, .minimal]

private theorem ternaryCandidates_ne : ternaryCandidates ≠ [] := by
  simp [ternaryCandidates]

/-- Weak ToD: penalizes only the most marked form (specLevel = max).
    Tolerates intermediate marking, unlike `todConstraint` which
    penalizes all marked forms proportionally. -/
def wtodConstraint : NamedConstraint PrivativePair :=
  { name := "WToD"
  , family := .markedness
  , eval := fun c =>
      if presupStrength c == PrivativePair.maximal.specLevel then 1 else 0 }

/-- SToD has the same eval function as todConstraint: both penalize
    by `presupStrength`. The ternary case uses `todConstraint` directly
    rather than defining a separate `stodConstraint`. -/
theorem stod_eval_eq_tod (c : PrivativePair) :
    todConstraint.eval c = presupStrength c := rfl

/-- WToD >> MP! >> SToD selects the intermediate (dual) cell.
    Moderate respect in articulated number systems. -/
theorem wtod_mp_stod_selects_dual :
    (mkTableau ternaryCandidates
      [wtodConstraint, mpConstraint, todConstraint]
      ternaryCandidates_ne).optimal = {PrivativePair.intermediate} := by
  native_decide

/-- SToD >> MP! >> WToD selects the minimal (plural) cell.
    Maximal respect (French/Slovenian-type pattern). -/
theorem stod_mp_wtod_selects_plural :
    (mkTableau ternaryCandidates
      [todConstraint, mpConstraint, wtodConstraint]
      ternaryCandidates_ne).optimal = {PrivativePair.minimal} := by
  native_decide

/-- MP! >> SToD >> WToD selects the maximal (singular) cell.
    Normal non-honorific speech. -/
theorem mp_stod_wtod_selects_singular :
    (mkTableau ternaryCandidates
      [mpConstraint, todConstraint, wtodConstraint]
      ternaryCandidates_ne).optimal = {PrivativePair.maximal} := by
  native_decide

/-- Factorial typology: {SToD (= todConstraint), WToD, MP!} with 3
    candidates predicts exactly 3 language types. -/
theorem ternary_factorial_typology :
    mkFactorialTypologySize ternaryCandidates
      [todConstraint, wtodConstraint, mpConstraint]
      ternaryCandidates_ne = 3 := by
  native_decide

/-- No unattested ternary pattern: every constraint permutation selects
    one of the three canonical cells. -/
theorem no_unattested_ternary_pattern :
    (mkFactorialOptima ternaryCandidates
      [todConstraint, wtodConstraint, mpConstraint]
      ternaryCandidates_ne).all
    (fun opt => opt == {PrivativePair.maximal} ||
                opt == {PrivativePair.intermediate} ||
                opt == {PrivativePair.minimal}) = true := by
  native_decide

-- ============================================================================
-- §5  iHON Eliminability
-- ============================================================================

/-!
## §5: [iHON] is Redundant

@cite{alok-bhalla-2026} posits a dedicated [iHON] feature in the syntax
(formalized in `Minimalism.Features.HonLevel`). @cite{wang-r-2023}
argues this is unnecessary: the honorific recruitment pattern falls out
from `phiPresup` + ToD, without any feature beyond standard phi-features.

The key argument: [iHON] + impoverishment rules must *stipulate* which
phi-values are recruited (always the unmarked one). ToD + phi-feature
presuppositions *derive* this — the unmarked value wins because it has
the weakest presupposition, and ToD selects the weakest.

Note: @cite{alok-bhalla-2026}'s analysis of allocutive Agree (probe
locus, embeddability) is orthogonal — [iHON] may play a role in the
*agreement mechanism* even if it is unnecessary for *recruitment*.
-/

/-- The phi-feature presuppositional framework + ToD derives all
    attested recruitment patterns without [iHON]:
    1. ToD >> MP! selects the minimal cell
    2. The minimal cell is semantically unmarked
    3. All attested strategies target the minimal cell -/
theorem ihon_redundant_for_recruitment :
    (mkTableau binaryCandidates [todConstraint, mpConstraint]
      binaryCandidates_ne).optimal = {PrivativePair.minimal} ∧
    isSemanticUnmarked .minimal = true ∧
    (∀ s : HonStrategy, honStrategyCell s = .minimal) :=
  ⟨by native_decide, rfl, fun s => by cases s <;> rfl⟩

-- ============================================================================
-- §6  Bridges to PhiFeatures and Allocutive Data
-- ============================================================================

/-!
## §6: Bridges

### Per-domain bridges

Each recruitment strategy targets a specific phi-feature domain.
The recruited cell (`.minimal`) corresponds to a specific `PrProp`
denotation from `PhiFeatures`: `plSem` (number), `thirdSem` (person),
or `indefSem` (definiteness). All three are `phiPresup` at the minimal
cell, which has a vacuous presupposition — this is WHY ToD selects them.

### Allocutive data bridges

The allocutive data in `Honorifics.lean` tracks `hasTV` (T/V pronoun
distinction = plural recruitment) and `has3PHon` (3rd-person honorifics
= person recruitment). Both correspond to the `.minimal` cell in their
respective phi-feature domains.
-/

section DomainBridges

/-- The plural recruitment strategy targets the minimal NUMBER cell,
    which is `plSem` — the PrProp with vacuous presupposition.
    `pl_is_minimal_cell` (PhiFeatures) proves `pluralF` maps to `.minimal`. -/
theorem plural_strategy_is_plSem :
    honStrategyCell .plural = PhiFeatures.toPair Features.Number.pluralF :=
  rfl

/-- The 3rd-person strategy targets the minimal PERSON cell,
    which is `thirdSem` — the PrProp with vacuous presupposition. -/
theorem thirdPerson_strategy_is_third :
    honStrategyCell .thirdPerson = PhiFeatures.toPair Features.Person.third :=
  rfl

/-- Both strategies target cells whose presuppositional denotations
    are vacuously defined — this is the semantic reason ToD selects them.
    Proved via `unmarked_vacuous_presup` from PhiFeatures. -/
theorem recruited_cells_have_vacuous_presup {E : Type*} (innerP outerP : E → Prop) :
    ∀ s : HonStrategy,
      ∀ x : E, (Semantics.Presupposition.PhiFeatures.phiPresup innerP outerP
        (honStrategyCell s)).defined x := by
  intro s x; cases s <;> trivial

end DomainBridges

section AllocutiveBridges

/-- The `hasTV` field in `AllocDatum` tracks whether a language uses
    the plural (= minimal number cell) recruitment strategy.
    All 9 allocutive languages have T/V. Cross-reference: `Honorifics.all_have_tv`. -/
theorem allocData_tv_uses_minimal :
    allAllocData.all (fun d => d.hasTV) = true ∧
    honStrategyCell .plural = .minimal :=
  ⟨by native_decide, rfl⟩

/-- Languages with `has3PHon = true` use the minimal PERSON cell.
    The languages are: Magahi, Korean, Japanese, Tamil, Hindi, Maithili, Punjabi. -/
theorem allocData_3phon_uses_minimal :
    (allAllocData.filter (fun d => d.has3PHon)).length = 7 ∧
    honStrategyCell .thirdPerson = .minimal :=
  ⟨by native_decide, rfl⟩

/-- Dual-domain languages (hasTV ∧ has3PHon) recruit the minimal cell
    independently in both the number and person domains. -/
theorem dual_domain_both_minimal :
    ∀ d ∈ allAllocData, d.hasTV && d.has3PHon = true →
      honStrategyCell .plural = .minimal ∧
      honStrategyCell .thirdPerson = .minimal :=
  fun _ _ _ => ⟨rfl, rfl⟩

end AllocutiveBridges

-- ============================================================================
-- §7  General Structural Theorem: ToD >> MP! Selects Unmarked
-- ============================================================================

/-!
## §7: General Structural Theorem

The binary-case theorem (`tod_mp_selects_minimal`) uses `native_decide` over
a fixed 2-element candidate set. Here we prove the **general** result: for
ANY non-empty set of well-formed `PrivativePair` candidates that includes
`.minimal`, ToD >> MP! selects `.minimal` as the unique winner.

This is the structural backbone of @cite{wang-r-2023}'s analysis: the
recruitment of unmarked values is not an accident of the binary case —
it holds for arbitrary candidate sets. The proof is purely algebraic:

1. `optimal_zero_first`: if any candidate has 0 violations on the top
   constraint, all optimal candidates must too
2. The only well-formed cell with `presupStrength = 0` is `.minimal`
3. `.minimal`'s profile `[0, maxSpec]` lexicographically dominates
   all other profiles
-/

section GeneralTheorem

open Core.Constraint.OT (mkTableau_optimal_zero_first mkTableau_optimal_mem)
open Core.Constraint.Evaluation (Tableau buildViolationProfile)

/-- Every optimal candidate under ToD >> MP! is `.minimal`. The proof:
    `optimal_zero_first` gives `todConstraint.eval c = 0`, i.e.
    `presupStrength c = 0`. A case split on `PrivativePair`'s fields
    shows `.minimal` is the only well-formed cell with specLevel 0. -/
theorem tod_mp_only_minimal (candidates : List PrivativePair)
    (hWF : ∀ c ∈ candidates, c.wellFormed = true)
    (hMin : PrivativePair.minimal ∈ candidates)
    (hNE : candidates ≠ []) :
    ∀ c ∈ (mkTableau candidates [todConstraint, mpConstraint] hNE).optimal,
      c = .minimal := by
  intro c hc
  have hZero := mkTableau_optimal_zero_first candidates todConstraint [mpConstraint] hNE
    ⟨.minimal, hMin, rfl⟩ c hc
  have hcWF := hWF c (mkTableau_optimal_mem candidates _ hNE c hc)
  cases c with | mk o i =>
  cases o <;> cases i
  · rfl
  all_goals simp_all [PrivativePair.wellFormed, todConstraint, presupStrength,
                       PrivativePair.specLevel, Bool.toNat]

/-- `.minimal` is in the optimal set: its profile `[0, maxSpec]` is
    lexicographically ≤ every profile `[k, maxSpec - k]` for k : Nat. -/
theorem tod_mp_minimal_is_optimal (candidates : List PrivativePair)
    (hMin : PrivativePair.minimal ∈ candidates)
    (hNE : candidates ≠ []) :
    PrivativePair.minimal ∈
      (mkTableau candidates [todConstraint, mpConstraint] hNE).optimal := by
  rw [Tableau.mem_optimal_iff]
  refine ⟨List.mem_toFinset.mpr hMin, fun c' _ => ?_⟩
  simp only [mkTableau, buildViolationProfile]
  -- Goal: toLex (fun i => ..minimal..) ≤ toLex (fun i => ..c'..)
  -- Strategy: show ¬ (c' profile < minimal profile) using Pi.Lex
  apply not_lt.mp
  intro ⟨i, hlt_eq, hlt⟩
  -- i is the first position where c' < minimal; all j < i have c' j = minimal j
  have h0 : todConstraint.eval PrivativePair.minimal = 0 := rfl
  have h2 : mpConstraint.eval PrivativePair.minimal = 2 := rfl
  -- `toLex f i` reduces to `f i` definitionally
  change ([todConstraint, mpConstraint].get i).eval c' <
         ([todConstraint, mpConstraint].get i).eval PrivativePair.minimal at hlt
  match i with
  | ⟨0, _⟩ =>
    -- i = 0: c'.eval < minimal.eval on ToD, but minimal has 0 violations
    simp only [List.get, todConstraint] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | ⟨1, _⟩ =>
    -- i = 1: c' agrees on constraint 0, has fewer on constraint 1
    have hc'_tod : todConstraint.eval c' = 0 := by
      have := hlt_eq ⟨0, Nat.zero_lt_succ _⟩ (show (⟨0, _⟩ : Fin 2) < ⟨1, _⟩ from Nat.zero_lt_one)
      change todConstraint.eval c' = todConstraint.eval PrivativePair.minimal at this
      simp [h0] at this; exact this
    have hc'_mp : mpConstraint.eval c' = 2 := by
      simp only [mpConstraint, todConstraint, presupStrength] at hc'_tod ⊢
      simp only [PrivativePair.spec_maximal]; omega
    simp only [List.get] at hlt
    change mpConstraint.eval c' < mpConstraint.eval PrivativePair.minimal at hlt
    rw [hc'_mp, h2] at hlt
    exact lt_irrefl _ hlt

/-- **General ToD >> MP! Theorem**: for any set of well-formed candidates
    containing `.minimal`, the optimal set under ToD >> MP! is exactly
    `{.minimal}`. This is the strongest formulation of @cite{wang-r-2023}'s
    core result — the recruitment of semantically unmarked values is a
    necessary consequence of presuppositional competition under ToD
    dominance, regardless of candidate set size or composition. -/
theorem tod_mp_general (candidates : List PrivativePair)
    (hWF : ∀ c ∈ candidates, c.wellFormed = true)
    (hMin : PrivativePair.minimal ∈ candidates)
    (hNE : candidates ≠ []) :
    PrivativePair.minimal ∈
      (mkTableau candidates [todConstraint, mpConstraint] hNE).optimal ∧
    ∀ c ∈ (mkTableau candidates [todConstraint, mpConstraint] hNE).optimal,
      c = .minimal :=
  ⟨tod_mp_minimal_is_optimal candidates hMin hNE,
   tod_mp_only_minimal candidates hWF hMin hNE⟩

end GeneralTheorem

-- ============================================================================
-- §8  HonLevel ↔ PrivativePair Bridge
-- ============================================================================

/-!
## §8: HonLevel ↔ PrivativePair Bridge

@cite{alok-bhalla-2026}'s `HonLevel` (nh/h/hh) is isomorphic to
`PrivativePair` (minimal/intermediate/maximal). This `PhiFeatures`
instance makes the correspondence structural: `HonLevel` inherits
`specLevel`, `wellFormed`, `no_four_way`, and all presuppositional
machinery from `PrivativePair` by construction.

The mapping:
- `nh`  ↔ `.minimal`       (specLevel 0 — unmarked, weakest presupposition)
- `h`   ↔ `.intermediate`  (specLevel 1)
- `hh`  ↔ `.maximal`       (specLevel 2 — most marked, strongest presupposition)

This makes `ihon_redundant_for_recruitment` structurally precise:
`HonLevel` values are literally `PrivativePair` cells, so the
`tod_mp_general` result from §7 applies directly to `HonLevel`
candidates.
-/

section HonLevelBridge

open Minimalism (HonLevel)

instance : PhiFeatures HonLevel where
  toPair
    | .nh => .minimal
    | .h  => .intermediate
    | .hh => .maximal
  ofPair
    | ⟨true, true⟩  => .hh
    | ⟨true, false⟩ => .h
    | ⟨false, _⟩    => .nh
  roundtrip a := by cases a <;> rfl

/-- All `HonLevel` values are well-formed as `PrivativePair` cells. -/
theorem honLevel_all_wellFormed : ∀ l : HonLevel, PhiFeatures.wellFormed l = true :=
  fun l => by cases l <;> rfl

/-- `specLevel` values: nh = 0, h = 1, hh = 2. -/
theorem honLevel_specLevel :
    PhiFeatures.specLevel HonLevel.nh = 0 ∧
    PhiFeatures.specLevel HonLevel.h = 1 ∧
    PhiFeatures.specLevel HonLevel.hh = 2 :=
  ⟨rfl, rfl, rfl⟩

/-- `nh` maps to `.minimal` — the cell ToD selects. -/
theorem nh_maps_to_minimal : PhiFeatures.toPair HonLevel.nh = PrivativePair.minimal := rfl

/-- `hh` maps to `.maximal` — the cell MP! selects. -/
theorem hh_maps_to_maximal : PhiFeatures.toPair HonLevel.hh = PrivativePair.maximal := rfl

/-- The `HonLevel → specLevel` map is injective: distinct levels have
    distinct specification levels. This means the 3-way honorific distinction
    saturates the `PrivativePair` structure — no finer distinctions are possible. -/
theorem honLevel_specLevel_injective :
    ∀ a b : HonLevel, PhiFeatures.specLevel a = PhiFeatures.specLevel b → a = b :=
  fun a b h => by cases a <;> cases b <;> first | rfl | (simp [PhiFeatures.specLevel,
    PhiFeatures.toPair, PrivativePair.specLevel, PrivativePair.maximal,
    PrivativePair.intermediate, PrivativePair.minimal] at h)

/-- `HonLevel` is **fully discriminatory**: distinct levels ↔ distinct specLevels.
    The forward direction (`≠ → specLevel ≠`) is the contrapositive of injectivity;
    the reverse (`specLevel ≠ → ≠`) is trivial. -/
theorem honLevel_eq_discriminatory_power :
    ∀ a b : HonLevel, a ≠ b ↔ PhiFeatures.specLevel a ≠ PhiFeatures.specLevel b :=
  fun a b => ⟨fun h heq => h (honLevel_specLevel_injective a b heq),
              fun h heq => h (congrArg PhiFeatures.specLevel heq)⟩

/-- **Structural [iHON] eliminability.** The `PhiFeatures HonLevel`
    instance means `tod_mp_general` applies directly to `HonLevel`
    candidates (via `toPair`): ToD >> MP! selects `nh` (= `.minimal`)
    as the unique winner whenever `nh` is among the candidates.

    Combined with `ihon_redundant_for_recruitment`, this shows [iHON]
    is not just empirically redundant but *structurally* so: `HonLevel`
    IS `PrivativePair`, and `PrivativePair` + ToD already determines
    the recruitment pattern. -/
theorem ihon_structurally_redundant :
    -- (1) HonLevel is a PrivativePair instance
    PhiFeatures.toPair HonLevel.nh = .minimal ∧
    PhiFeatures.toPair HonLevel.hh = .maximal ∧
    -- (2) All HonLevel values are well-formed
    (∀ l : HonLevel, PhiFeatures.wellFormed l = true) ∧
    -- (3) tod_mp_general applies: nh wins under ToD >> MP!
    (∀ (candidates : List PrivativePair)
       (_ : ∀ c ∈ candidates, c.wellFormed = true)
       (_ : PrivativePair.minimal ∈ candidates)
       (hNE : candidates ≠ []),
       PrivativePair.minimal ∈
         (mkTableau candidates [todConstraint, mpConstraint] hNE).optimal ∧
       ∀ c ∈ (mkTableau candidates [todConstraint, mpConstraint] hNE).optimal,
         c = .minimal) :=
  ⟨rfl, rfl, honLevel_all_wellFormed, tod_mp_general⟩

end HonLevelBridge

end Wang2023
