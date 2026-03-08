import Linglib.Theories.Semantics.Conditionals.Counterfactual
import Linglib.Core.Logic.Truth3

/-!
# Alternative-Sensitive Conditional Semantics
@cite{santorio-2018}

Alternatives and truthmakers in conditional semantics.
*The Journal of Philosophy* 115(10): 513--549.

## Core Ideas

1. Conditional antecedents denote **sets of propositions** (alternatives),
   not single propositions
2. Each alternative is evaluated separately against the closest worlds
3. An optional **DIST_π** operator distributes the consequent over
   alternatives, carrying a homogeneity presupposition
4. When DIST_π is present → **SDA** (Simplification of Disjunctive Antecedents)
5. When DIST_π is absent → no SDA guarantee (the Spain/Axis reading)

## Connection to Homogeneity

DIST_π is structurally identical to DIST for plural individuals
(@cite{kriz-2016}, @cite{tieu-kriz-chemla-2019}):

| Operator | Domain | TRUE | FALSE | GAP |
|----------|--------|------|-------|-----|
| DIST | atoms of a plurality | all satisfy P | none | mixed |
| DIST_π | alternatives of antecedent | all make C true | none | mixed |

Both are instances of the generic `dist` operator (`Core/Logic/Truth3.lean`).

## Main Definitions

- `altConditionalResults`: per-alternative conditional evaluation
- `homogeneityEval`: DIST_π applied to conditional alternatives (= `dist`)
- `sdaEval` / `dcrEval`: universal / existential resolutions
- `lewisDAC`: Lewis's Boolean-disjunction semantics (for contrast)
- `IsTruthmaker`: the truthmaker relation

## Key Theorems

- `homogeneityEval_eq_dist`: DIST_π = generic `dist`
- `sda_is_universal_homogeneity`: SDA ↔ homogeneity resolves to TRUE
- `spain_sda_fails` / `spain_lewis_true`: SDA is optional without DIST_π
- `hyperintensional`: logically equivalent antecedents can differ
-/

namespace Semantics.Conditionals.AlternativeSensitive

open Core.Duality (Truth3 dist)
open Semantics.Conditionals.Counterfactual (closestWorldsB)


-- ============================================================
-- SECTION 1: Per-Alternative Evaluation
-- ============================================================

/-- Evaluate each alternative antecedent separately against closest worlds.
    Returns one Bool per alternative: true iff all closest worlds for that
    alternative satisfy the consequent. -/
def altConditionalResults {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) : List Bool :=
  alts.map λ A =>
    let closest := closestWorldsB closer domain w (domain.filter A)
    closest.isEmpty || closest.all C


-- ============================================================
-- SECTION 2: DIST_π and Its Resolutions
-- ============================================================

/-- **DIST_π** (@cite{santorio-2018} §V): distribute the consequent over
    antecedent alternatives with a homogeneity presupposition.

    ⟦[if φ] DIST_π [would ψ]⟧ʷ =
      TRUE  if ∀p ∈ Alt(φ) : min_w(p) ⊆ ⟦ψ⟧
      FALSE if ∀p ∈ Alt(φ) : min_w(p) ⊆ ⟦¬ψ⟧
      GAP   otherwise (homogeneity failure)

    This is `dist` applied to per-alternative conditional results,
    making the structural parallel with plural DIST explicit. -/
def homogeneityEval {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) : Truth3 :=
  dist (altConditionalResults closer domain alts C w)

/-- **SDA reading**: universal resolution of DIST_π (conjunction).
    "if A or B, C" is true iff BOTH (if A, C) and (if B, C). -/
def sdaEval {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) : Bool :=
  (altConditionalResults closer domain alts C w).all id

/-- **DCR reading**: existential resolution of DIST_π (disjunction).
    "if A or B, C" is true iff EITHER (if A, C) or (if B, C). -/
def dcrEval {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) : Bool :=
  (altConditionalResults closer domain alts C w).any id

/-- Lewis semantics: Boolean disjunction, not alternative-generating.
    "if A or B, C" evaluates min_w(A ∪ B) against C. -/
def lewisDAC {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (A B C : W → Bool) (w : W) : Bool :=
  let disj := λ v => A v || B v
  let closest := closestWorldsB closer domain w (domain.filter disj)
  closest.isEmpty || closest.all C


-- ============================================================
-- SECTION 3: Structural Theorems
-- ============================================================

/-- DIST_π for conditionals = generic `dist` on per-alternative results. -/
theorem homogeneityEval_eq_dist {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) :
    homogeneityEval closer domain alts C w =
    dist (altConditionalResults closer domain alts C w) := rfl

/-- SDA = homogeneity resolving to TRUE. The universal (SDA) reading
    is exactly the case where the truth-value gap does not arise. -/
theorem sda_is_universal_homogeneity {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) :
    sdaEval closer domain alts C w =
    (homogeneityEval closer domain alts C w == .true) := by
  unfold sdaEval homogeneityEval dist
  generalize altConditionalResults closer domain alts C w = rs
  cases rs.all id <;> cases rs.all (!·) <;> rfl


-- ============================================================
-- SECTION 4: SDA Without DIST_π — the Spain Example
-- ============================================================

/-!
## SDA is optional (@cite{santorio-2018} §V)

"If Spain had fought with the Axis or the Allies, she would have fought
with the Axis." This conditional is acceptable WITHOUT implying "If Spain
had fought with the Allies, she would have fought with the Axis."

The non-SDA reading arises when DIST_π is absent — the modal takes the
disjunctive closure of the antecedent alternatives directly.
-/

section Spain

private inductive SpainW where | actual | axis | allies
  deriving Repr, DecidableEq, BEq

private def spainCloser : SpainW → SpainW → SpainW → Bool
  | _, w₁, w₂ => w₁ == w₂ || (w₁ == .axis && w₂ == .allies)

private def spainDomain : List SpainW := [.actual, .axis, .allies]
private def fightAxis : SpainW → Bool | .axis => true | _ => false
private def fightAllies : SpainW → Bool | .allies => true | _ => false

/-- With DIST_π, SDA fails: the Allies simplification is false. -/
theorem spain_sda_fails :
    sdaEval spainCloser spainDomain [fightAxis, fightAllies]
      fightAxis .actual = false := by native_decide

/-- Homogeneity evaluation returns GAP (mixed results). -/
theorem spain_homogeneity_gap :
    homogeneityEval spainCloser spainDomain [fightAxis, fightAllies]
      fightAxis .actual = .gap := by native_decide

/-- Without DIST_π, Lewis's disjunctive closure gives TRUE: the closest
    (Axis ∨ Allies)-world is the Axis-world, which satisfies C. -/
theorem spain_lewis_true :
    lewisDAC spainCloser spainDomain fightAxis fightAllies
      fightAxis .actual = true := by native_decide

end Spain


-- ============================================================
-- SECTION 5: Hyperintensionality
-- ============================================================

/-!
## Hyperintensionality (@cite{santorio-2018} §VI)

Logically equivalent antecedents can yield different conditional truth
values because they generate different alternatives — and hence different
truthmakers. This drops Substitution of Logical Equivalents, making
conditionals hyperintensional.
-/

section Hyperintensional

private inductive PartyW where | actual | annaOnly | both | ottoOnly
  deriving Repr, DecidableEq, BEq

/-- annaOnly is closest to actual; both is next. -/
private def partyCloser : PartyW → PartyW → PartyW → Bool
  | _, w₁, w₂ => w₁ == w₂ ||
    (w₁ == .annaOnly && w₂ != .actual) ||
    (w₁ == .both && w₂ == .ottoOnly)

private def partyDomain : List PartyW :=
  [.actual, .annaOnly, .both, .ottoOnly]
private def annaCame : PartyW → Bool
  | .annaOnly => true | .both => true | _ => false
private def ottoAndAnnaCame : PartyW → Bool
  | .both => true | _ => false
private def partyFun : PartyW → Bool
  | .annaOnly => true | _ => false

/-- The antecedents are extensionally equivalent:
    annaCame ↔ annaCame ∨ ottoAndAnnaCame at every world. -/
theorem antecedents_equivalent :
    ∀ w : PartyW, annaCame w = (annaCame w || ottoAndAnnaCame w) := by
  intro w; cases w <;> rfl

/-- Simple antecedent [annaCame]: TRUE.
    Closest annaCame-world is annaOnly; the party is fun there. -/
theorem simple_antecedent_true :
    sdaEval partyCloser partyDomain [annaCame] partyFun .actual = true := by
  native_decide

/-- Disjunctive antecedent [annaCame, ottoAndAnnaCame]: FALSE.
    Closest ottoAndAnnaCame-world is both; the party is not fun there. -/
theorem disjunctive_antecedent_false :
    sdaEval partyCloser partyDomain [annaCame, ottoAndAnnaCame]
      partyFun .actual = false := by native_decide

/-- **Hyperintensionality**: logically equivalent antecedents with
    different alternatives yield different conditional truth values. -/
theorem hyperintensional :
    (∀ w : PartyW, annaCame w = (annaCame w || ottoAndAnnaCame w)) ∧
    sdaEval partyCloser partyDomain [annaCame] partyFun .actual ≠
    sdaEval partyCloser partyDomain [annaCame, ottoAndAnnaCame]
      partyFun .actual :=
  ⟨antecedents_equivalent, by native_decide⟩

end Hyperintensional


-- ============================================================
-- SECTION 6: Truthmakers
-- ============================================================

/-!
## Truthmakers (@cite{santorio-2018} §IV)

A truthmaker of S is a proposition p that specifies a "way for S to be
true." Truthmakers are computed from syntactic alternatives via a
**stability algorithm**: a subset σ ⊆ ALT_S is stable iff it is consistent
with the negation of every alternative not in σ. Truthmakers are the
conjunctive closures of minimal stable subsets.

The stability algorithm requires syntactic alternative generation
(@cite{katzir-2007}), which is not yet formalized. The semantic core —
DIST_π over alternatives — is independent of how alternatives are generated.
-/

/-- A proposition p is a truthmaker of sentence S iff p entails S. -/
def IsTruthmaker {W : Type*} (p S : W → Bool) : Prop :=
  ∀ w, p w = true → S w = true

/-- Each disjunct is a truthmaker of the disjunction. -/
theorem disjunct_is_truthmaker {W : Type*} (A B : W → Bool) :
    IsTruthmaker A (λ w => A w || B w) := by
  intro w h; simp [h]

/-- Conjunction of disjuncts is a truthmaker of the disjunction. -/
theorem conj_disjuncts_is_truthmaker {W : Type*} (A B : W → Bool) :
    IsTruthmaker (λ w => A w && B w) (λ w => A w || B w) := by
  intro w h; cases hA : A w <;> cases hB : B w <;> simp_all


end Semantics.Conditionals.AlternativeSensitive
