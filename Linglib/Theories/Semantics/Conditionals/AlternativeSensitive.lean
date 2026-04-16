import Mathlib.Data.Finset.Card
import Linglib.Theories.Semantics.Conditionals.Counterfactual
import Linglib.Core.Logic.Truth3
import Linglib.Theories.Semantics.Alternatives.Structural
import Linglib.Theories.Semantics.Exhaustification.InnocentExclusion

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
- `IsTruthmaker`: the truthmaker entailment relation (condition ii)
- `satisfiable` / `isStable` / `isMinimalStable`: the stability algorithm (§IV.2)
- `conjunctiveClosure`: conjunction of a subset of alternatives
- `IsTruthmakerOf`: full truthmaker definition (stability + entailment)

## Key Theorems

- `homogeneityEval_eq_dist`: DIST_π = generic `dist`
- `sda_is_universal_homogeneity`: SDA ↔ homogeneity resolves to TRUE
- `dcr_is_existential_homogeneity`: DCR ↔ homogeneity does not resolve to FALSE
- `spain_sda_fails` / `spain_lewis_true`: SDA is optional without DIST_π
- `antecedent_strengthening_fails`: Constraint #1 (AS failure)
- `hyperintensional` / `sle_fails`: Constraint #3 (SLE failure)
- `oa_otto_minimal` / `oa_anna_minimal`: minimal stable subsets verified
- `oa_otto_is_truthmaker` / `oa_anna_is_truthmaker`: full truthmakers verified
-/

namespace Semantics.Conditionals.AlternativeSensitive

open Core.Duality (Truth3 dist)
open Semantics.Conditionals (SimilarityOrdering)


-- ============================================================
-- SECTION 1: Per-Alternative Evaluation
-- ============================================================

/-- Evaluate each alternative antecedent separately against closest worlds.
    Returns one Bool per alternative: true iff all closest worlds for that
    alternative satisfy the consequent. -/
def altConditionalResults {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) : List Bool :=
  alts.map λ A =>
    decide (∀ w' ∈ sim.closestWorlds w (Finset.univ.filter (fun w => A w = true)),
      C w' = true)


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
def homogeneityEval {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) : Truth3 :=
  dist (altConditionalResults sim alts C w)

/-- **SDA reading**: universal resolution of DIST_π (conjunction).
    "if A or B, C" is true iff BOTH (if A, C) and (if B, C). -/
def sdaEval {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) : Bool :=
  (altConditionalResults sim alts C w).all id

/-- **DCR reading**: existential resolution of DIST_π (disjunction).
    "if A or B, C" is true iff EITHER (if A, C) or (if B, C). -/
def dcrEval {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) : Bool :=
  (altConditionalResults sim alts C w).any id

/-- Lewis semantics: Boolean disjunction, not alternative-generating.
    "if A or B, C" evaluates min_w(A ∪ B) against C. -/
def lewisDAC {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (A B C : W → Bool) (w : W) : Bool :=
  decide (∀ w' ∈ sim.closestWorlds w
    (Finset.univ.filter (fun v => (A v || B v) = true)), C w' = true)


-- ============================================================
-- SECTION 3: Structural Theorems
-- ============================================================

/-- DIST_π for conditionals = generic `dist` on per-alternative results. -/
theorem homogeneityEval_eq_dist {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) :
    homogeneityEval sim alts C w =
    dist (altConditionalResults sim alts C w) := rfl

/-- SDA = homogeneity resolving to TRUE. The universal (SDA) reading
    is exactly the case where the truth-value gap does not arise. -/
theorem sda_is_universal_homogeneity {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W) :
    sdaEval sim alts C w =
    (homogeneityEval sim alts C w == .true) := by
  unfold sdaEval homogeneityEval dist
  generalize altConditionalResults sim alts C w = rs
  cases rs.all id <;> cases rs.all (!·) <;> rfl

/-- De Morgan for Bool lists: `any id` ↔ `¬ all not`. -/
private theorem any_id_eq_not_all_not : ∀ (rs : List Bool),
    rs.any id = !(rs.all (!·))
  | [] => rfl
  | h :: t => by
    simp only [List.any_cons, List.all_cons, id, any_id_eq_not_all_not t]
    cases h <;> rfl

/-- DCR = homogeneity not resolving to FALSE. The existential (DCR)
    reading succeeds iff at least one alternative's conditional is true.

    | Reading | Eval | Homogeneity condition |
    |---------|------|----------------------|
    | SDA | `sdaEval` | `homogeneityEval == .true` |
    | DCR | `dcrEval` | `homogeneityEval != .false` |

    Dual of `sda_is_universal_homogeneity`. Requires non-empty alternatives
    (for `[] : List Bool`, `any id = false` but `dist [] = .true`). -/
theorem dcr_is_existential_homogeneity {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (alts : List (W → Bool)) (C : W → Bool) (w : W)
    (h : alts ≠ []) :
    dcrEval sim alts C w =
    !(homogeneityEval sim alts C w == .false) := by
  unfold dcrEval homogeneityEval dist
  rw [any_id_eq_not_all_not]
  have hne : (altConditionalResults sim alts C w) ≠ [] := by
    unfold altConditionalResults
    cases alts with
    | nil => exact absurd rfl h
    | cons _ _ => exact List.cons_ne_nil _ _
  generalize altConditionalResults sim alts C w = rs at hne
  cases hid : rs.all id
  · cases rs.all (!·) <;> rfl
  · -- all id = true → all (!·) = false for non-empty rs
    have : rs.all (!·) = false := by
      cases rs with
      | nil => exact absurd rfl hne
      | cons x xs =>
        simp only [List.all_cons, id] at hid ⊢
        cases x <;> simp_all
    rw [this]; rfl


-- ============================================================
-- SECTION 4: SDA Without DIST_π — the Spain Example
-- ============================================================

/-!
## SDA is optional — the Spain example

Example (8) from @cite{santorio-2018} (p. 522; originally from
@cite{mckay-vaninwagen-1977}): "If Spain had fought with the Axis or the Allies, she would
have fought with the Axis." This conditional is acceptable WITHOUT
implying (9): "If Spain had fought with the Allies, she would have fought
with the Axis."

The non-SDA reading arises when DIST_π is absent (§V) — the modal takes
the disjunctive closure of the antecedent alternatives directly.

This example also demonstrates **Failure of Antecedent Strengthening**
(Constraint #1, p. 513): the Lewis reading of (8) is true, but
strengthening to "If Allies, she'd fight Axis" makes it false.
-/

section Spain

private inductive SpainW where | actual | axis | allies
  deriving Repr, DecidableEq

private instance : Fintype SpainW where
  elems := {.actual, .axis, .allies}
  complete x := by cases x <;> simp

private def spainSim : SimilarityOrdering SpainW := .ofBool
  (fun _ w₁ w₂ => w₁ == w₂ || (w₁ == .axis && w₂ == .allies))
  (by decide) (by decide)
private def fightAxis : SpainW → Bool | .axis => true | _ => false
private def fightAllies : SpainW → Bool | .allies => true | _ => false

/-- With DIST_π, SDA fails: the Allies simplification is false. -/
theorem spain_sda_fails :
    sdaEval spainSim [fightAxis, fightAllies]
      fightAxis .actual = false := by native_decide

/-- Homogeneity evaluation returns GAP (mixed results). -/
theorem spain_homogeneity_gap :
    homogeneityEval spainSim [fightAxis, fightAllies]
      fightAxis .actual = .gap := by native_decide

/-- Without DIST_π, Lewis's disjunctive closure gives TRUE: the closest
    (Axis ∨ Allies)-world is the Axis-world, which satisfies C. -/
theorem spain_lewis_true :
    lewisDAC spainSim fightAxis fightAllies
      fightAxis .actual = true := by native_decide

/-- DCR reading gives TRUE: at least one alternative succeeds
    (the Axis simplification is true). -/
theorem spain_dcr_true :
    dcrEval spainSim [fightAxis, fightAllies]
      fightAxis .actual = true := by native_decide

/-- **Failure of Antecedent Strengthening** (Constraint #1, p. 513):
    the Lewis reading of (8) "if Axis or Allies, fought Axis" is true,
    but strengthening the antecedent to just "Allies" (which entails
    "Axis or Allies") reverses the truth value. -/
theorem antecedent_strengthening_fails :
    lewisDAC spainSim fightAxis fightAllies fightAxis .actual = true ∧
    sdaEval spainSim [fightAllies] fightAxis .actual = false :=
  ⟨by native_decide, by native_decide⟩

end Spain


-- ============================================================
-- SECTION 5: Hyperintensionality
-- ============================================================

/-!
## Hyperintensionality — Failure of SLE (@cite{santorio-2018} §VI)

Logically equivalent antecedents can yield different conditional truth
values because they generate different alternatives — and hence different
truthmakers. This drops **Substitution of Logical Equivalents (SLE)**
(Constraint #3, p. 514), making conditionals hyperintensional.

Together with Failure of Antecedent Strengthening (`antecedent_strengthening_fails`)
and optional SDA (`spain_sda_fails` / `spain_lewis_true`), this covers
all three constraints from the paper's introduction (pp. 513–514).
-/

section Hyperintensional

private inductive PartyW where | actual | annaOnly | both | ottoOnly
  deriving Repr, DecidableEq

private instance : Fintype PartyW where
  elems := {.actual, .annaOnly, .both, .ottoOnly}
  complete x := by cases x <;> simp

/-- annaOnly is closest to actual; both is next. -/
private def partySim : SimilarityOrdering PartyW := .ofBool
  (fun _ w₁ w₂ => w₁ == w₂ ||
    (w₁ == .annaOnly && w₂ != .actual) ||
    (w₁ == .both && w₂ == .ottoOnly))
  (by decide) (by decide)
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
    sdaEval partySim [annaCame] partyFun .actual = true := by
  native_decide

/-- Disjunctive antecedent [annaCame, ottoAndAnnaCame]: FALSE.
    Closest ottoAndAnnaCame-world is both; the party is not fun there. -/
theorem disjunctive_antecedent_false :
    sdaEval partySim [annaCame, ottoAndAnnaCame]
      partyFun .actual = false := by native_decide

/-- **Hyperintensionality**: logically equivalent antecedents with
    different alternatives yield different conditional truth values.
    This is **Failure of SLE** (Constraint #3, p. 514). -/
theorem hyperintensional :
    (∀ w : PartyW, annaCame w = (annaCame w || ottoAndAnnaCame w)) ∧
    sdaEval partySim [annaCame] partyFun .actual ≠
    sdaEval partySim [annaCame, ottoAndAnnaCame]
      partyFun .actual :=
  ⟨antecedents_equivalent, by native_decide⟩

/-- Substitution of Logical Equivalents fails: Constraint #3 from
    @cite{santorio-2018} (p. 514). Alias for `hyperintensional`. -/
theorem sle_fails :
    (∀ w : PartyW, annaCame w = (annaCame w || ottoAndAnnaCame w)) ∧
    sdaEval partySim [annaCame] partyFun .actual ≠
    sdaEval partySim [annaCame, ottoAndAnnaCame]
      partyFun .actual := hyperintensional

end Hyperintensional


-- ============================================================
-- SECTION 6: Stability Algorithm (§IV.2, p. 540)
-- ============================================================

/-!
## The Stability Algorithm (@cite{santorio-2018} §IV.2)

The stability algorithm defines truthmakers from syntactic alternatives.
Given ALT_S (the alternatives to sentence S):

1. A subset σ ⊆ ALT_S is **stable** iff σ ∪ (ALT_S \ σ)⁻ is consistent
   (i.e., there exists a world satisfying all propositions in σ AND the
   negation of every alternative NOT in σ)
2. σ is **minimal stable** iff stable, non-empty, and no non-empty proper
   subset is stable
3. **Truthmakers** of S are ⋀σ for each minimal stable σ such that ⋀σ ⊨ S

The stability algorithm requires syntactic alternatives — generated by
@cite{katzir-2007} (formalized in
`Theories/Semantics/Alternatives/Structural.lean`) — to
compute ALT_S. The truthmakers then serve as the alternatives for
DIST_π evaluation (§V): each truthmaker is evaluated separately against
the closest worlds, and DIST_π distributes with a homogeneity
presupposition.

### Duality with Fox's Innocent Exclusion

Santorio's stability is the **dual** of @cite{fox-2007}'s innocent exclusion
(footnote 40, p. 540): minimal stable subsets correspond to maximal
consistent exclusions. This duality is computationally verified in
Section 9 below (`stability_exclusion_duality`, `ie_from_stability`).
-/

section Stability

/-- Satisfiability: some world makes all propositions true. -/
def satisfiable {W : Type*} [Fintype W] (props : List (W → Bool)) : Bool :=
  decide (∃ w : W, (props.all (fun p => p w)) = true)

/-- Stability (p. 540): a subset σ (given by indices into `alts`) is stable
    w.r.t. ALT_S iff σ together with the negation of every non-member
    alternative is satisfiable.

    σ ⊆ ALT_S is stable iff σ ∪ (ALT_S \ σ)⁻ ⊬ ⊥ -/
def isStable {W : Type*} [Fintype W]
    (alts : List (W → Bool)) (σ : List Nat) : Bool :=
  let inσ := σ.filterMap (fun i => alts[i]?)
  let complement := (List.range alts.length).filter (fun i => !σ.contains i)
  let complementProps := complement.filterMap (fun i => alts[i]?)
  let negComplement : List (W → Bool) :=
    complementProps.map (fun (p : W → Bool) => fun (w : W) => !p w)
  satisfiable (inσ ++ negComplement)

/-- All sublists of a list (the power set). Used by both the stability
    algorithm (Santorio) and innocent exclusion (Fox). -/
def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => let p := sublists xs; p ++ p.map (x :: ·)

/-- Minimal stability (p. 540): non-empty, stable, and no non-empty proper
    subset is stable. -/
def isMinimalStable {W : Type*} [Fintype W]
    (alts : List (W → Bool)) (σ : List Nat) : Bool :=
  σ.length > 0 &&
  isStable alts σ &&
  (sublists σ).all (fun τ =>
    τ.length == 0 || τ.length == σ.length || !isStable alts τ)

/-- Conjunctive closure: the conjunction of all propositions at given indices.
    ⋀σ = λw. ∀i ∈ σ, alts[i](w) = true -/
def conjunctiveClosure {W : Type*}
    (alts : List (W → Bool)) (σ : List Nat) : W → Bool :=
  fun w => (σ.filterMap (fun i => alts[i]?)).all (fun p => p w)

end Stability


-- ============================================================
-- SECTION 7: Truthmakers (§IV.2, p. 540)
-- ============================================================

/-- Entailment condition for truthmakers: p entails S.
    This is condition (ii) of the paper's definition (p. 540). -/
def IsTruthmaker {W : Type*} (p S : W → Bool) : Prop :=
  ∀ w, p w = true → S w = true

/-- Full truthmaker definition (p. 540): σ witnesses that its conjunctive
    closure is a truthmaker of S iff (i) σ is a minimal stable subset of
    ALT_S, and (ii) ⋀σ entails S. -/
def IsTruthmakerOf {W : Type*} [Fintype W]
    (alts : List (W → Bool)) (S : W → Bool) (σ : List Nat) : Prop :=
  isMinimalStable alts σ = true ∧
  IsTruthmaker (conjunctiveClosure alts σ) S

/-- Each disjunct is a truthmaker of the disjunction. -/
theorem disjunct_is_truthmaker {W : Type*} (A B : W → Bool) :
    IsTruthmaker A (λ w => A w || B w) := by
  intro w h; simp [h]

/-- Conjunction of disjuncts is a truthmaker of the disjunction. -/
theorem conj_disjuncts_is_truthmaker {W : Type*} (A B : W → Bool) :
    IsTruthmaker (λ w => A w && B w) (λ w => A w || B w) := by
  intro w h; cases hA : A w <;> cases hB : B w <;> simp_all


-- ============================================================
-- SECTION 8: Worked Example — Otto or Anna (§IV.2, pp. 535–537)
-- ============================================================

/-!
## Worked Example: "Otto or Anna went to the party"

Verifies the stability algorithm on the paper's central example
(pp. 535–537).

- S = "Otto or Anna went to the party" = O ∨ A
- ALT_S = {O∨A, O, A, O∧A}
- Stable subsets: {O∨A, O}, {O∨A, A}, ALT_S
- **Minimal** stable: {O∨A, O} and {O∨A, A}
- Truthmakers: O (= ⋀{O∨A, O}) and A (= ⋀{O∨A, A})

The truthmakers are exactly the individual disjuncts — the "ways for
the disjunction to be true." These then feed into `altConditionalResults`
and `homogeneityEval` (DIST_π) for conditional evaluation.
-/

section OttoAnna

private inductive OAWorld where
  | ottoOnly | annaOnly | both | neither
  deriving Repr, DecidableEq

private instance : Fintype OAWorld where
  elems := {.ottoOnly, .annaOnly, .both, .neither}
  complete x := by cases x <;> simp

private def ottoWent : OAWorld → Bool
  | .ottoOnly => true | .both => true | _ => false
private def annaWent : OAWorld → Bool
  | .annaOnly => true | .both => true | _ => false
private def ottoOrAnna : OAWorld → Bool
  | .neither => false | _ => true
private def ottoAndAnna : OAWorld → Bool
  | .both => true | _ => false

/-- ALT_(44) = {O∨A, O, A, O∧A} (p. 536, indices 0–3). -/
private def oaAlts : List (OAWorld → Bool) :=
  [ottoOrAnna, ottoWent, annaWent, ottoAndAnna]

-- ── Stability checks ──────────────────────────────────────────

/-- {O∨A} alone is NOT stable (p. 536): no world satisfies
    O∨A ∧ ¬O ∧ ¬A ∧ ¬(O∧A). -/
theorem oa_singleton_not_stable :
    isStable oaAlts [0] = false := by native_decide

/-- {O∨A, O} IS stable (witness: ottoOnly satisfies
    O∨A ∧ O ∧ ¬A ∧ ¬(O∧A)). -/
theorem oa_otto_stable :
    isStable oaAlts [0, 1] = true := by native_decide

/-- {O∨A, A} IS stable (witness: annaOnly). -/
theorem oa_anna_stable :
    isStable oaAlts [0, 2] = true := by native_decide

/-- {O∨A, O∧A} is NOT stable: O∧A implies O∨A, but ¬O ∧ ¬A
    contradicts O∧A. -/
theorem oa_conj_not_stable :
    isStable oaAlts [0, 3] = false := by native_decide

-- ── Minimality checks ─────────────────────────────────────────

/-- {O∨A, O} is MINIMAL stable: neither {O∨A} nor {O} alone is stable. -/
theorem oa_otto_minimal :
    isMinimalStable oaAlts [0, 1] = true := by native_decide

/-- {O∨A, A} is MINIMAL stable. -/
theorem oa_anna_minimal :
    isMinimalStable oaAlts [0, 2] = true := by native_decide

-- ── Truthmaker identification ─────────────────────────────────

/-- ⋀{O∨A, O} = O (Otto went): the conjunctive closure reduces to
    the stronger conjunct. -/
theorem oa_otto_closure_eq :
    ∀ w : OAWorld, conjunctiveClosure oaAlts [0, 1] w = ottoWent w := by
  intro w; cases w <;> native_decide

/-- ⋀{O∨A, A} = A (Anna went). -/
theorem oa_anna_closure_eq :
    ∀ w : OAWorld, conjunctiveClosure oaAlts [0, 2] w = annaWent w := by
  intro w; cases w <;> native_decide

/-- O is a truthmaker of O∨A via the minimal stable subset {O∨A, O}:
    both conditions of the full definition (p. 540) are satisfied. -/
theorem oa_otto_is_truthmaker :
    IsTruthmakerOf oaAlts ottoOrAnna [0, 1] := by
  unfold IsTruthmakerOf; constructor
  · native_decide
  · intro w h
    have := oa_otto_closure_eq w
    simp [this] at h
    cases w <;> simp_all [ottoWent, ottoOrAnna]

/-- A is a truthmaker of O∨A via {O∨A, A}. -/
theorem oa_anna_is_truthmaker :
    IsTruthmakerOf oaAlts ottoOrAnna [0, 2] := by
  unfold IsTruthmakerOf; constructor
  · native_decide
  · intro w h
    have := oa_anna_closure_eq w
    simp [this] at h
    cases w <;> simp_all [annaWent, ottoOrAnna]

end OttoAnna


-- ============================================================
-- SECTION 9: Duality with Fox 2007 (footnote 40, p. 540)
-- ============================================================

/-!
## Fox–Santorio Duality

@cite{santorio-2018} (footnote 40, p. 540) observes that his stability
algorithm is the **dual** of @cite{fox-2007}'s innocent exclusion: where
Fox finds maximal sets of alternatives that can consistently be
**excluded**, Santorio finds minimal sets that can consistently be
**included** (with the complement negated).

Concretely, for disjunction alternatives {p∨q, p, q, p∧q}:

| Santorio (minimal stable) | Fox (maximal consistent exclusion) |
|---------------------------|------------------------------------|
| {p∨q, p} — include p, negate q,p∧q | {q, p∧q} — exclude q, p∧q |
| {p∨q, q} — include q, negate p,p∧q | {p, p∧q} — exclude p, p∧q |

The complement of each minimal stable subset (restricted to the
non-weaker alternatives NW) equals a maximal consistent exclusion.
This section verifies the duality computationally on both algorithms.
-/

section Duality

open Exhaustification.InnocentExclusion hiding sublists

-- Both algorithms are applied to the same data (InnocentExclusion's public
-- PQWorld/disjAlts) to verify the duality computationally.

private instance : Fintype PQWorld where
  elems := {.pOnly, .qOnly, .both, .neither}
  complete x := by cases x <;> simp

/-- InnocentExclusion's disjunction alternatives, used as input for Santorio's
    stability algorithm. -/
private def dualAlts : List (PQWorld → Bool) := disjAlts

-- ── Santorio's stability on Fox's types ────────────────────────

/-- The two minimal stable subsets of the disjunction alternatives.
    Each includes the prejacent (index 0) plus one disjunct. -/
theorem disj_minStable_sets :
    (sublists (List.range dualAlts.length)).filter
      (isMinimalStable dualAlts) = [[0, 2], [0, 1]] := by
  native_decide

-- ── Fox's exclusions on the same data ──────────────────────────

/-- Fox's maximal consistent exclusions for p∨q. -/
theorem fox_maxExcl_sets :
    maxConsistentExclusions pqDomain pOrQ disjAlts = [[2, 3], [1, 3]] := by
  native_decide

-- ── The duality ────────────────────────────────────────────────

/-- Complement of a subset within NW = {1, 2, 3}. -/
private def complementInNW (σ : List Nat) : List Nat :=
  [1, 2, 3].filter fun i => !σ.contains i

/-- **Duality verified**: the complement (in NW) of each minimal
    stable subset equals the corresponding maximal consistent exclusion.

    - minStable {0,2}: NW \ {2} = {1,3} = MCE₂
    - minStable {0,1}: NW \ {1} = {2,3} = MCE₁ -/
theorem stability_exclusion_duality :
    let santorioSets := [[0, 2], [0, 1]]
    let foxSets := [[1, 3], [2, 3]]
    santorioSets.map complementInNW = foxSets := by
  native_decide

/-- The innocently excludable alternatives (Fox) are exactly those
    NOT in ANY minimal stable subset beyond the prejacent (Santorio).

    Fox: I-E = {3} (= p∧q)
    Santorio: ⋃(minStable ∩ NW) = {1, 2} (= p, q)
    Complement: NW \ {1,2} = {3} = I-E -/
theorem ie_from_stability :
    let includedByStability := [1, 2]
    let foxIE := ieIndices pqDomain pOrQ disjAlts
    complementInNW includedByStability = foxIE := by
  native_decide

end Duality


end Semantics.Conditionals.AlternativeSensitive
