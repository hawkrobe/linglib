import Mathlib.Data.List.Sublists
import Linglib.Semantics.Conditionals.Counterfactual
import Linglib.Core.Logic.Truth3
import Linglib.Core.Logic.Duality
import Linglib.Semantics.Truthmaker.Inexact
import Linglib.Semantics.Truthmaker.Basic
import Linglib.Studies.McKayVanInwagen1977

/-!
# Santorio 2018 — Alternative-Sensitive Conditional Semantics
[santorio-2018]

Self-contained formalization of *Alternatives and truthmakers in
conditional semantics*, *The Journal of Philosophy* 115(10): 513–549.

## Substrate consumption

Built on `Conditionals.Counterfactual.universalCounterfactual` (the
canonical [lewis-1973]/Kratzer universal counterfactual operator)
and on `Truthmaker.ExactEntails` (= `≤` on `TMProp`,
`Truthmaker/Inexact.lean`). Predicates are typed `Prop` with
`DecidablePred` instances throughout — no Bool-vs-Prop adapters. The
per-alternative apparatus uses `DecAlt W := Σ' A : W → Prop,
DecidablePred A` to bundle decidability with each alternative
predicate.

## Sections

- §1 Per-alternative evaluation (`altConditionalResults`)
- §2 DIST_π and its resolutions (`homogeneityEval`, `sdaEval`,
  `disjunctiveCounterfactual` = "would" extracts ⋁S, p. 547)
- §3 Structural theorems
- §4 Lewis bridge (alias to `universalCounterfactual` on disjunctive
  closure)
- §5 Truthmakers (`IsTruthmaker := ExactEntails` directly)
- §6 Stability algorithm (§IV.2 p. 540): `isConsistent`, `isStable`,
  `isMinimalStable`, `conjunctiveClosure`, `IsTruthmakerOf`
- §7 Generic truthmaker lemmas
- §8 Hyperintensionality / SLE failure (§VI)
- §9 Otto/Anna stability worked example (pp. 535–537)
- §10 Spain analysis on top of [mckay-vaninwagen-1977] data
- §11 Cross-framework: Santorio classical truthmaker ≠ [jago-2026]
  Fine-style content parthood

## Faithfulness notes

1. **DIST_π trivalent rendering.** Santorio's own DIST_π is
   bivalent-with-presupposition (p. 547). Footnote 52 p. 545 explicitly
   declines the trivalent collapse: "To switch to a Križ-style
   framework, we would need to divorce homogeneity from the
   distributivity operator and move to a trivalent semantics." We
   render DIST_π via `Trivalent.Truth3` / `distList` because it is
   ergonomic and faithful on the all/none/mixed verdicts; the
   divergence is in how the homogeneity failure is *typed* (gap vs.
   presupposition failure).

2. **Two readings, not three.** Santorio's binary architecture is SDA
   (with DIST_π) vs. asymmetric/Lewis (without DIST_π — modal extracts
   the disjunctive closure, p. 547). The "DCR" (Disjunctive Conditional
   Reading) is **not** Santorio's term; it is named in
   [zani-ciardelli-sanfelici-2026] (p. 10) and lives in that file.

3. **Stability non-emptiness.** Santorio's definition (p. 540) does not
   include a non-empty clause; he discharges the empty-σ case via the
   entailment condition (ii) of the truthmaker definition (since
   `⋀∅ = ⊤` does not entail typical S). The `σ.length > 0` clause in
   `isMinimalStable` here is a Lean-side convenience yielding the same
   truthmaker set.

4. **Fox–Santorio relationship (footnote 40 p. 540).** Santorio
   observes that minimal stability is "something like the converse" of
   [fox-2007]'s **maximal exclusion** (note: not innocent
   exclusion, which is the intersection of maximals). He does not say
   "dual" and hedges. The general theorem
   `santorio_minimal_stable_dual_to_fox_maximal_exclusion` is not
   formalised; it requires either a witness-typed `IsMaximalExclusion`
   predicate in `Semantics/Exhaustification/Innocent.lean`
   (which currently exposes `IE` / `innocentlyExcludable` over
   `Finset (Finset W)`) or a `Finset Nat ↔ List Nat` reflection.

5. **Stability terminology.** Santorio writes `σ ∪ (ALT_S − σ)⁻ ⊭ ⊥`
   ("consistent with the negation of every alternative", p. 540); this
   file inlines the consistency check directly into `isStable` rather
   than expose a separate `isConsistent` predicate.

6. **`disjunctiveCounterfactual` and `would` (p. 547).** The
   DIST_π-absent reading is named for the modal `would`, which "extracts
   the disjunctive closure" `⋁S` of the alternative set. We name the
   operator `disjunctiveCounterfactual` rather than `lewisDAC` because
   p. 547 places this move in the lexical entry of `would`, not in
   Lewis's metatheory.

## Future work (load-bearing Santorio content not yet formalized)

- **§II.2 Raffle / probability-operator argument (pp. 525–527)** —
  Santorio's central anti-scalar argument. Requires a probability
  operator scoping over a counterfactual; `Semantics/Conditionals/`
  has no such operator at present.
- **§II.3 Otto/Anna/Waldo non-closest-worlds (pp. 527–530)** —
  refutes minimal-change. Requires a `WaldoWorld` enum with a tied-
  closest-worlds similarity ordering.
- **§IV.3 Karenina/W&P 8-alternative example (p. 538)** — shows
  Santorio's stability algorithm is global (not local), distinguishing
  it from Alonso-Ovalle 2009 (no bib entry yet).
- **§V full lexical entries (p. 547)** — typed entries for `if`,
  `would`, DIST_π. Requires typed-LF infrastructure.

## Citations engaged in the formalization

[lewis-1973] (universal counterfactual substrate),
[kratzer-1981] / [kratzer-1991] / [kratzer-2012]
(premise/restrictor semantics, sibling no-SDA tradition),
[katzir-2007] (structural alternative generation, source of ALT_S),
[kriz-spector-2021] (homogeneity-style trivalent option declined
by fn 52 p. 545), [chierchia-2013] (domain alternatives, fn 40
p. 540), [cariani-goldstein-2020] (sibling homogeneity account,
see `CarianiGoldstein2020.lean`), [mckay-vaninwagen-1977] (Spain
data, §10), [jago-2026] (Fine-style truthmaker contrast, §11).
Santorio also engages Alonso-Ovalle 2009 (§III precursor, no bib
entry yet), Klinedinst (scalar account refuted in §II, no bib entry
yet), Schlenker 2004 ("Conditionals as Definite Descriptions" — the
fn 24/47 descriptions analogy), and van Fraassen 1969 (truthmaker
ancestor, fn 41) — adding these to `references.bib` is a bib-hygiene
follow-up.
-/

namespace Santorio2018

open Trivalent (Truth3 distList)
open Core.Order (SimilarityOrdering)
open Semantics.Conditionals.Counterfactual (universalCounterfactual)


/-! ## Decidability-bundled alternatives -/

/-- A propositional alternative on `W` paired with its decidability
    witness. Used as the element type of alternative lists (`List (DecAlt W)`)
    so that per-alternative `decide` calls compose without per-element
    typeclass synthesis. -/
abbrev DecAlt (W : Type*) := Σ' A : W → Prop, DecidablePred A

namespace DecAlt
variable {W : Type*}

/-- Underlying predicate of a decidability-bundled alternative. -/
def pred (a : DecAlt W) : W → Prop := a.1

instance (a : DecAlt W) : DecidablePred a.pred := a.2

end DecAlt


variable {W : Type*} [DecidableEq W] [Fintype W]


-- ════════════════════════════════════════════════════
-- § 1. Per-Alternative Evaluation
-- ════════════════════════════════════════════════════

/-- Evaluate each alternative antecedent separately against closest
    worlds via `universalCounterfactual`. Returns one Bool per
    alternative: true iff all closest worlds for that alternative
    satisfy the consequent. -/
def altConditionalResults (sim : SimilarityOrdering W)
    (alts : List (DecAlt W)) (C : W → Prop) [DecidablePred C]
    (w : W) : List Bool :=
  alts.map λ a => decide (universalCounterfactual sim a.pred C w)


-- ════════════════════════════════════════════════════
-- § 2. DIST_π and Its Resolutions
-- ════════════════════════════════════════════════════

/-- **DIST_π** (§V): distribute the consequent over antecedent
    alternatives with a homogeneity presupposition. Rendered as `dist`
    over per-alternative conditional results (faithfulness note 1). -/
def homogeneityEval (sim : SimilarityOrdering W)
    (alts : List (DecAlt W)) (C : W → Prop) [DecidablePred C]
    (w : W) : Truth3 :=
  distList (altConditionalResults sim alts C w) (· = true)

/-- **SDA reading** (Simplification of Disjunctive Antecedents):
    universal resolution of DIST_π. "If A or B, C" is true iff every
    alternative simplification (if A, C) holds. -/
def sdaEval (sim : SimilarityOrdering W)
    (alts : List (DecAlt W)) (C : W → Prop) [DecidablePred C]
    (w : W) : Prop :=
  (altConditionalResults sim alts C w).all id = true

instance (sim : SimilarityOrdering W) (alts : List (DecAlt W))
    (C : W → Prop) [DecidablePred C] (w : W) :
    Decidable (sdaEval sim alts C w) :=
  inferInstanceAs (Decidable (_ = true))

/-- `sdaEval` unfolds to universal quantification over per-alternative
    conditionals — Santorio's intended Simplification reading. -/
theorem sdaEval_iff_forall (sim : SimilarityOrdering W)
    (alts : List (DecAlt W)) (C : W → Prop) [DecidablePred C] (w : W) :
    sdaEval sim alts C w ↔
    ∀ a ∈ alts, universalCounterfactual sim a.pred C w := by
  unfold sdaEval altConditionalResults
  simp [List.all_map, List.all_eq_true, decide_eq_true_eq]

/-- **Disjunctive closure** of an alternative set: `⋁S = λw. ∃A ∈ S, A w`.
    Per §V p. 547, the lexical entry for `would` extracts this when
    DIST_π is absent. -/
def disjunctiveClosure (alts : List (DecAlt W)) (w : W) : Prop :=
  ∃ a ∈ alts, a.pred w

instance (alts : List (DecAlt W)) (w : W) :
    Decidable (disjunctiveClosure alts w) :=
  inferInstanceAs (Decidable (∃ a ∈ alts, _))

instance (alts : List (DecAlt W)) :
    DecidablePred (disjunctiveClosure alts) :=
  fun _ => inferInstance

/-- **DIST_π-absent reading** (§V p. 547): the modal `would` extracts
    the disjunctive closure of the alternatives, evaluating min_w(⋁S)
    against C. Reduces to [lewis-1973]'s universal counterfactual
    on the disjunctive closure. -/
def disjunctiveCounterfactual (sim : SimilarityOrdering W)
    (alts : List (DecAlt W)) (C : W → Prop) [DecidablePred C]
    (w : W) : Prop :=
  universalCounterfactual sim (disjunctiveClosure alts) C w


-- ════════════════════════════════════════════════════
-- § 3. Structural Theorems
-- ════════════════════════════════════════════════════

/-- SDA = homogeneity resolves to TRUE. -/
theorem sda_iff_homogeneity_true (sim : SimilarityOrdering W)
    (alts : List (DecAlt W)) (C : W → Prop) [DecidablePred C] (w : W) :
    sdaEval sim alts C w ↔ homogeneityEval sim alts C w = .true := by
  unfold sdaEval homogeneityEval Trivalent.distList
  generalize altConditionalResults sim alts C w = rs
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hall : ∀ b ∈ rs, b = true := by
      intro b hb
      have := List.all_eq_true.mp h b hb
      simpa using this
    rw [if_pos hall]
  · by_contra hc
    have hnall : ¬ (∀ b ∈ rs, b = true) := by
      intro hall
      apply hc
      exact List.all_eq_true.mpr hall
    rw [if_neg hnall] at h
    split_ifs at h <;> cases h


-- ════════════════════════════════════════════════════
-- § 4. Lewis Bridge
-- ════════════════════════════════════════════════════

/-- `disjunctiveCounterfactual` IS [lewis-1973]'s universal
    counterfactual on the disjunctive closure of the alternatives.
    Definitionally true; named for explicit cross-framework consumption. -/
theorem disjunctiveCounterfactual_eq_universalCounterfactual_disjunctiveClosure
    (sim : SimilarityOrdering W) (alts : List (DecAlt W))
    (C : W → Prop) [DecidablePred C] (w : W) :
    disjunctiveCounterfactual sim alts C w =
    universalCounterfactual sim (disjunctiveClosure alts) C w := rfl


-- ════════════════════════════════════════════════════
-- § 5. Truthmakers (§IV.2 p. 540)
-- ════════════════════════════════════════════════════

/-- Entailment condition for truthmakers: p entails S.

    Defined directly as `Truthmaker.ExactEntails` from
    `Truthmaker/Inexact.lean` (= `≤` on `TMProp`). Santorio is explicit
    (p. 515) that his truthmakers are "cognitive rather than
    metaphysical" and determined by syntactic alternatives, so the
    classical world-extensional formulation is faithful.

    The Up clause that distinguishes Fine's `IsContentPart` from this
    Down-only relation is **not** part of Santorio's notion; the
    inequivalence with Fine is refuted in
    `santorio_truthmaker_neq_fine_content_part` below. -/
abbrev IsTruthmaker {W : Type*} (p S : W → Prop) : Prop :=
  Semantics.Truthmaker.ExactEntails p S


-- ════════════════════════════════════════════════════
-- § 6. Stability Algorithm (§IV.2 p. 540)
-- ════════════════════════════════════════════════════

/-- Stability (p. 540): a subset σ (given by indices into `alts`) is
    stable iff some world satisfies every in-σ alternative AND falsifies
    every out-of-σ alternative. (Santorio's `σ ∪ (ALT_S − σ)⁻ ⊭ ⊥`,
    "consistent" in his prose p. 540.) -/
def isStable (alts : List (DecAlt W)) (σ : List Nat) : Prop :=
  ∃ w : W,
    (∀ i, ∀ h : i < alts.length, i ∈ σ → (alts[i]'h).pred w) ∧
    (∀ i, ∀ h : i < alts.length, i ∉ σ → ¬ (alts[i]'h).pred w)

instance (alts : List (DecAlt W)) (σ : List Nat) :
    Decidable (isStable alts σ) := by
  unfold isStable; exact inferInstance

/-- Minimal stability (p. 540): non-empty (Lean-side, faithfulness
    note 3), stable, and no non-empty proper subset is stable. -/
def isMinimalStable (alts : List (DecAlt W)) (σ : List Nat) : Prop :=
  σ.length > 0 ∧
  isStable alts σ ∧
  ∀ τ ∈ σ.sublists,
    τ.length = 0 ∨ τ.length = σ.length ∨ ¬ isStable alts τ

instance (alts : List (DecAlt W)) (σ : List Nat) :
    Decidable (isMinimalStable alts σ) := by
  unfold isMinimalStable; exact inferInstance

/-- Conjunctive closure: ⋀σ = λw. ∀i ∈ σ, alts[i](w). -/
def conjunctiveClosure (alts : List (DecAlt W)) (σ : List Nat) :
    W → Prop :=
  fun w => ∀ i, ∀ h : i < alts.length, i ∈ σ → (alts[i]'h).pred w

instance (alts : List (DecAlt W)) (σ : List Nat) :
    DecidablePred (conjunctiveClosure alts σ) := fun _ =>
  inferInstanceAs (Decidable (∀ _, _))

/-- Full truthmaker definition (p. 540): σ witnesses that its
    conjunctive closure is a truthmaker of S iff (i) σ is a minimal
    stable subset of ALT_S, and (ii) ⋀σ entails S. -/
structure IsTruthmakerOf (alts : List (DecAlt W)) (S : W → Prop)
    (σ : List Nat) : Prop where
  /-- Condition (i): σ is a minimal stable subset of ALT_S. -/
  minimal_stable : isMinimalStable alts σ
  /-- Condition (ii): ⋀σ entails S (the truthmaker entailment). -/
  closure_entails : IsTruthmaker (conjunctiveClosure alts σ) S


-- ════════════════════════════════════════════════════
-- § 7. Generic Truthmaker Lemmas
-- ════════════════════════════════════════════════════

/-- Each disjunct is a truthmaker of the disjunction. -/
theorem disjunct_is_truthmaker {W : Type*} (A B : W → Prop) :
    IsTruthmaker A (fun w => A w ∨ B w) :=
  fun _ => Or.inl

/-- Conjunction of disjuncts is a truthmaker of the disjunction. -/
theorem conj_disjuncts_is_truthmaker {W : Type*} (A B : W → Prop) :
    IsTruthmaker (fun w => A w ∧ B w) (fun w => A w ∨ B w) :=
  fun _ ⟨hA, _⟩ => Or.inl hA


-- ════════════════════════════════════════════════════
-- § 8. Hyperintensionality (§VI — SLE Failure)
-- ════════════════════════════════════════════════════

/-!
Logically equivalent antecedents can yield different conditional truth
values because they generate different alternatives. This drops
**Substitution of Logical Equivalents (SLE)** (Constraint #3 p. 514).
-/

section Hyperintensional

private inductive PartyW where | actual | annaOnly | both | ottoOnly
  deriving Repr, DecidableEq

private instance : Fintype PartyW where
  elems := {.actual, .annaOnly, .both, .ottoOnly}
  complete x := by cases x <;> simp

private def partySim : SimilarityOrdering PartyW := .ofBool
  (fun _ w₁ w₂ => w₁ == w₂ ||
    (w₁ == .annaOnly && w₂ != .actual) ||
    (w₁ == .both && w₂ == .ottoOnly))
  (by decide) (by decide)

private def annaCame (w : PartyW) : Prop := w = .annaOnly ∨ w = .both
private def ottoAndAnnaCame (w : PartyW) : Prop := w = .both
private def partyFun (w : PartyW) : Prop := w = .annaOnly

private instance : DecidablePred annaCame := fun w => by
  unfold annaCame; exact inferInstance
private instance : DecidablePred ottoAndAnnaCame := fun w => decEq w .both
private instance : DecidablePred partyFun := fun w => decEq w .annaOnly

private def annaCameAlt : DecAlt PartyW := ⟨annaCame, inferInstance⟩
private def ottoAndAnnaCameAlt : DecAlt PartyW := ⟨ottoAndAnnaCame, inferInstance⟩

theorem antecedents_equivalent :
    ∀ w : PartyW, annaCame w ↔ (annaCame w ∨ ottoAndAnnaCame w) := by
  intro w; cases w <;> simp [annaCame, ottoAndAnnaCame]

theorem simple_antecedent_true :
    sdaEval partySim [annaCameAlt] partyFun .actual := by decide

theorem disjunctive_antecedent_false :
    ¬ sdaEval partySim [annaCameAlt, ottoAndAnnaCameAlt] partyFun .actual := by
  decide

/-- **Hyperintensionality** / **SLE Failure** (Constraint #3 p. 514). -/
theorem sle_fails :
    (∀ w : PartyW, annaCame w ↔ (annaCame w ∨ ottoAndAnnaCame w)) ∧
    (sdaEval partySim [annaCameAlt] partyFun .actual ∧
     ¬ sdaEval partySim [annaCameAlt, ottoAndAnnaCameAlt] partyFun .actual) :=
  ⟨antecedents_equivalent, ⟨simple_antecedent_true, disjunctive_antecedent_false⟩⟩

end Hyperintensional


-- ════════════════════════════════════════════════════
-- § 9. Otto/Anna Stability Worked Example (pp. 535–537)
-- ════════════════════════════════════════════════════

/-!
S = "Otto or Anna went to the party" = O ∨ A.
ALT_S = {O∨A, O, A, O∧A} (p. 536).
Stable: {O∨A, O}, {O∨A, A}, ALT_S. Minimal stable: {O∨A, O}, {O∨A, A}.
Truthmakers: O and A (p. 537).
-/

section OttoAnna

private inductive OAWorld where
  | ottoOnly | annaOnly | both | neither
  deriving Repr, DecidableEq

private instance : Fintype OAWorld where
  elems := {.ottoOnly, .annaOnly, .both, .neither}
  complete x := by cases x <;> simp

private def ottoWent (w : OAWorld) : Prop := w = .ottoOnly ∨ w = .both
private def annaWent (w : OAWorld) : Prop := w = .annaOnly ∨ w = .both
private def ottoOrAnna (w : OAWorld) : Prop := w ≠ .neither
private def ottoAndAnna (w : OAWorld) : Prop := w = .both

private instance : DecidablePred ottoWent := fun w => by
  unfold ottoWent; exact inferInstance
private instance : DecidablePred annaWent := fun w => by
  unfold annaWent; exact inferInstance
private instance : DecidablePred ottoOrAnna := fun w => by
  unfold ottoOrAnna; exact inferInstance
private instance : DecidablePred ottoAndAnna := fun w => decEq w .both

private def oaAlts : List (DecAlt OAWorld) :=
  [⟨ottoOrAnna, inferInstance⟩,
   ⟨ottoWent, inferInstance⟩,
   ⟨annaWent, inferInstance⟩,
   ⟨ottoAndAnna, inferInstance⟩]

theorem oa_singleton_not_stable :
    ¬ isStable oaAlts [0] := by decide

theorem oa_otto_stable :
    isStable oaAlts [0, 1] := by decide

theorem oa_anna_stable :
    isStable oaAlts [0, 2] := by decide

theorem oa_conj_not_stable :
    ¬ isStable oaAlts [0, 3] := by decide

theorem oa_otto_minimal :
    isMinimalStable oaAlts [0, 1] := by decide

theorem oa_anna_minimal :
    isMinimalStable oaAlts [0, 2] := by decide

end OttoAnna


-- ════════════════════════════════════════════════════
-- § 10. Spain Analysis on Top of McKay & Van Inwagen 1977
-- ════════════════════════════════════════════════════

/-!
Per CLAUDE.md "chronological dependency": this 2018 study consumes
[mckay-vaninwagen-1977]'s 1977 data (worlds, similarity
ordering, disjunct predicates).
-/

private def spainAlts : List (DecAlt McKayVanInwagen1977.SpainWorld) :=
  [⟨McKayVanInwagen1977.foughtAxis, inferInstance⟩,
   ⟨McKayVanInwagen1977.foughtAllies, inferInstance⟩]

/-- [santorio-2018]'s homogeneity verdict on the
    [mckay-vaninwagen-1977] Spain scenario: `.indet` (mixed
    results across the two alternatives), demonstrating the `Truth3`
    middle column. -/
theorem spain_homogeneity_gap :
    homogeneityEval McKayVanInwagen1977.spainSim
      spainAlts McKayVanInwagen1977.foughtAxis .actual = .indet := by decide

/-- [santorio-2018]'s SDA verdict on the same scenario: FALSE
    (the Allies simplification fails). -/
theorem spain_sda_false :
    ¬ sdaEval McKayVanInwagen1977.spainSim
      spainAlts McKayVanInwagen1977.foughtAxis .actual := by decide


-- ════════════════════════════════════════════════════
-- § 11. Santorio Truthmaker ≠ Fine Content Parthood
-- ════════════════════════════════════════════════════

/-!
[santorio-2018]'s `IsTruthmaker` is `ExactEntails` from
`Truthmaker/Inexact.lean` (the Down clause only). Fine-style
`IsContentPart` adds the Up clause: every part of the truthmade
proposition extends to a part of the truthmaker. The two relations are
non-equivalent.
-/

/-- **Santorio truthmaker ≠ Fine content parthood**: there exist
    propositions `p`, `S` such that Santorio's classical truthmaker
    relation (= `ExactEntails`) holds but Fine's `IsContentPart` (Down
    + Up) fails. Witness: over `Nat` with the usual order, take
    `p = (· = 5)` and `S = (· < 10)`. -/
theorem santorio_truthmaker_neq_fine_content_part :
    ∃ (p S : Semantics.Truthmaker.TMProp Nat),
      Semantics.Truthmaker.ExactEntails p S ∧
      ¬ Semantics.Truthmaker.IsContentPart p S := by
  refine ⟨(· = 5), (· < 10), ?_, ?_⟩
  · intro s hs; subst hs; decide
  · intro ⟨hsub, _⟩
    obtain ⟨t, ht, hle⟩ := hsub 0 (by decide)
    omega


-- ════════════════════════════════════════════════════
-- § 12. The Three Constraints (pp. 513-514)
-- ════════════════════════════════════════════════════

/-!
[santorio-2018]'s introduction (pp. 513–514) lists three
constraints on classical counterfactual logic that the paper refutes:

- **Constraint #1**: Antecedent Strengthening — `(A □→ C) ⊨ (A ∧ B) □→ C`
- **Constraint #2**: Simplification of Disjunctive Antecedents (SDA) —
  `(A ∨ B) □→ C ⊨ A □→ C ∧ B □→ C`
- **Constraint #3**: Substitution of Logical Equivalents (SLE)

The Spain analysis (§10) refutes Constraint #1 via
[mckay-vaninwagen-1977] data; `sle_fails` (§8) refutes
Constraint #3. Constraint #2 is engaged throughout (it IS the central
phenomenon under DIST_π) — the theorem below states it as a structural
witness anchored to the named constraint.
-/

/-- **Constraint #2 = SDA**: under DIST_π, the alternative-sensitive
    semantics validates SDA. If the per-alternative SDA-evaluation
    holds, then each individual simplification holds. Direct
    consequence of `sdaEval_iff_forall`. -/
theorem santorio_constraint_2_sda (sim : SimilarityOrdering W)
    (alts : List (DecAlt W)) (C : W → Prop) [DecidablePred C] (w : W)
    (h : sdaEval sim alts C w) :
    ∀ a ∈ alts, universalCounterfactual sim a.pred C w :=
  (sdaEval_iff_forall sim alts C w).mp h


-- ════════════════════════════════════════════════════
-- § 13. Cross-Framework Divergences
-- ════════════════════════════════════════════════════

/-!
Per CLAUDE.md "no bridge files": cross-framework contrasts go inside
the chronologically-later study. Santorio 2018 is the latest of
{Lewis 1973, Stalnaker 1968, Kratzer 1981, McKay & Van Inwagen 1977}
that this file engages, so the divergence theorems live here.
-/

open Semantics.Conditionals.Counterfactual (homogeneityCounterfactual PresupResult PresupStatus)

section KareninaWP

/-! ### Santorio vs. Alonso-Ovalle on Karenina/W&P (§IV.3 pp. 537–539)

For the prejacent **(35)** "Every student read War and Peace or
Anna Karenina", [santorio-2018]'s stability algorithm (running
on Katzir-generated 8-alternative ALT_S, eqn (48) p. 538) identifies
**three** minimal-stable subsets, each yielding one truthmaker:

- σ₁ = {∀(A), ∀(A∨W), ∃(A), ∃(A∨W)} → "every student read AK"
- σ₂ = {∀(W), ∀(A∨W), ∃(W), ∃(A∨W)} → "every student read W&P"
- σ₃ = {∀(A∨W), ∃(A), ∃(W), ∃(A∨W)} → "**some** students read AK
  and **some** students read W&P" (the **mixed truthmaker**)

[alonso-ovalle-2009]'s pointwise computation (running only on
the disjunct alternatives `{∀(A), ∀(W)}` per his Or Rule (10) p. 212)
identifies only **two** truthmakers (the universals); the mixed
truthmaker is invisible to AO's local algorithm.

[santorio-2018]'s example (39) p. 539:
"If every student read AK or W&P, the world would be a better place.
 **But if some students read AK and some read W&P, the world would
 not be a better place.**"
is felicitous ONLY if the second clause's antecedent is a truthmaker
of the first clause's antecedent — which it is on Santorio's
algorithm but not on AO's. Hence Santorio: "a theory based on the
stability algorithm has an empirical advantage over Hamblin-style
semantics" (p. 539).

`KareninaWorld` enumerates the 5 worlds needed to evaluate the 8
alternatives. The mixed truthmaker is realized at `.mixed`. -/

private inductive KareninaWorld where
  | actual     -- no student reads any book
  | everyAK    -- every student reads (only) AK
  | everyWP    -- every student reads (only) W&P
  | mixed      -- some students read AK only, others read W&P only (no overlap)
  | everyBoth  -- every student reads both AK and W&P
  deriving Repr, DecidableEq

private instance : Fintype KareninaWorld where
  elems := {.actual, .everyAK, .everyWP, .mixed, .everyBoth}
  complete x := by cases x <;> simp

/-! ### Alternative predicates per [santorio-2018] (48) p. 538 -/

/-- ∀(A∧W) — every student read both AK and W&P. -/
private def everyReadAandW (w : KareninaWorld) : Prop := w = .everyBoth
/-- ∀(A) — every student read AK. -/
private def everyReadA (w : KareninaWorld) : Prop :=
  w = .everyAK ∨ w = .everyBoth
/-- ∀(W) — every student read W&P. -/
private def everyReadW (w : KareninaWorld) : Prop :=
  w = .everyWP ∨ w = .everyBoth
/-- ∀(A∨W) — the prejacent: every student read at least one of {AK, W&P}. -/
private def everyReadAorW (w : KareninaWorld) : Prop := w ≠ .actual
/-- ∃(A∧W) — some student read both. -/
private def someReadAandW (w : KareninaWorld) : Prop := w = .everyBoth
/-- ∃(A) — some student read AK. -/
private def someReadA (w : KareninaWorld) : Prop :=
  w = .everyAK ∨ w = .mixed ∨ w = .everyBoth
/-- ∃(W) — some student read W&P. -/
private def someReadW (w : KareninaWorld) : Prop :=
  w = .everyWP ∨ w = .mixed ∨ w = .everyBoth
/-- ∃(A∨W) — some student read at least one. -/
private def someReadAorW (w : KareninaWorld) : Prop := w ≠ .actual

private instance : DecidablePred everyReadAandW := fun w => decEq w .everyBoth
private instance : DecidablePred everyReadA := fun w => by
  unfold everyReadA; exact inferInstance
private instance : DecidablePred everyReadW := fun w => by
  unfold everyReadW; exact inferInstance
private instance : DecidablePred everyReadAorW := fun w => by
  unfold everyReadAorW; exact inferInstance
private instance : DecidablePred someReadAandW := fun w => decEq w .everyBoth
private instance : DecidablePred someReadA := fun w => by
  unfold someReadA; exact inferInstance
private instance : DecidablePred someReadW := fun w => by
  unfold someReadW; exact inferInstance
private instance : DecidablePred someReadAorW := fun w => by
  unfold someReadAorW; exact inferInstance

/-- ALT_S per [santorio-2018] (48) p. 538: the 8 Katzir-
    generated structural alternatives for "every student read AK or
    W&P". Index map: 0=∀(A∧W), 1=∀(A), 2=∀(W), 3=∀(A∨W) [prejacent],
    4=∃(A∧W), 5=∃(A), 6=∃(W), 7=∃(A∨W). -/
private def kareninaAlts : List (DecAlt KareninaWorld) :=
  [⟨everyReadAandW, inferInstance⟩,
   ⟨everyReadA, inferInstance⟩,
   ⟨everyReadW, inferInstance⟩,
   ⟨everyReadAorW, inferInstance⟩,
   ⟨someReadAandW, inferInstance⟩,
   ⟨someReadA, inferInstance⟩,
   ⟨someReadW, inferInstance⟩,
   ⟨someReadAorW, inferInstance⟩]

/-- σ₁ = {∀(A), ∀(A∨W), ∃(A), ∃(A∨W)} — the AK-truthmaker subset. -/
private def kareninaSigmaAK : List Nat := [1, 3, 5, 7]
/-- σ₂ = {∀(W), ∀(A∨W), ∃(W), ∃(A∨W)} — the W&P-truthmaker subset. -/
private def kareninaSigmaWP : List Nat := [2, 3, 6, 7]
/-- σ₃ = {∀(A∨W), ∃(A), ∃(W), ∃(A∨W)} — the **mixed** truthmaker
    subset. The conjunctive closure characterises worlds where every
    student reads at least one book AND some students read AK AND
    some students read W&P. -/
private def kareninaSigmaMixed : List Nat := [3, 5, 6, 7]

/-! ### The three minimal-stable subsets (p. 539) -/

theorem karenina_sigmaAK_minimal :
    isMinimalStable kareninaAlts kareninaSigmaAK := by decide

theorem karenina_sigmaWP_minimal :
    isMinimalStable kareninaAlts kareninaSigmaWP := by decide

theorem karenina_sigmaMixed_minimal :
    isMinimalStable kareninaAlts kareninaSigmaMixed := by decide

/-! ### Truthmaker realizations -/

/-- The AK-truthmaker is realized at `.everyAK` (and at `.everyBoth`). -/
theorem karenina_sigmaAK_realized_at_everyAK :
    conjunctiveClosure kareninaAlts kareninaSigmaAK .everyAK := by decide

/-- The W&P-truthmaker is realized at `.everyWP` (and at `.everyBoth`). -/
theorem karenina_sigmaWP_realized_at_everyWP :
    conjunctiveClosure kareninaAlts kareninaSigmaWP .everyWP := by decide

/-- **The mixed truthmaker is realized at `.mixed`** — the load-bearing
    fact distinguishing [santorio-2018] from
    [alonso-ovalle-2009]. At `.mixed`, every student reads at
    least one book, some students read AK, some students read W&P, and
    no student reads both. -/
theorem karenina_sigmaMixed_realized_at_mixed :
    conjunctiveClosure kareninaAlts kareninaSigmaMixed .mixed := by decide

/-! ### The cross-framework theorem -/

/-- **Santorio finds the mixed truthmaker; Alonso-Ovalle 2009 cannot.**

    [alonso-ovalle-2009]'s alternative set for the prejacent
    "every student read AK or W&P" is just the two disjunct universals
    `{∀(A), ∀(W)}` (from the Hamblin Or Rule (10) p. 212 plus the
    universal force §2.2.3 p. 218). At the `.mixed` world neither AO
    alternative holds. But [santorio-2018]'s `kareninaSigmaMixed`
    truthmaker IS realized at `.mixed`. AO's pointwise alternative
    generation thus undergenerates the truthmaker set: the mixed-
    reading way for the antecedent to be true is invisible to AO but
    visible to Santorio. This is the empirical advantage Santorio
    claims at p. 539. -/
theorem santorio_finds_mixed_truthmaker_ao_misses_it :
    -- Santorio's algorithm finds the mixed truthmaker
    isMinimalStable kareninaAlts kareninaSigmaMixed ∧
    conjunctiveClosure kareninaAlts kareninaSigmaMixed .mixed ∧
    -- But AO's alternative set has neither universal true at .mixed
    ¬ everyReadA .mixed ∧
    ¬ everyReadW .mixed := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end KareninaWP


/-- **Santorio vs. von Fintel/Križ on Spain.** The two homogeneity
    moves differ on cross-alternative aggregation:

    - Santorio per-alternative homogeneity over `[foughtAxis,
      foughtAllies]` yields `.indet` (mixed verdicts: Axis simplification
      true, Allies simplification false).
    - Von Fintel/Križ-style `homogeneityCounterfactual` on the
      disjunctive antecedent `(foughtAxis ∨ foughtAllies)` finds the
      closest such world (the Axis-world, by `spainSim`'s priority),
      checks foughtAxis-homogeneity over closest worlds (trivially
      satisfied — single closest world), and returns
      `presupposition := .satisfied`.

    The two operators thus deliver different verdicts on the same
    scenario: Santorio's homogeneity gap is **at the cross-alternative
    level**, von Fintel/Križ's is **at the within-closest-world level**.
    Both are "homogeneity," but at different scopes. -/
theorem santorio_vs_homogeneityCounterfactual_spain :
    -- Santorio: cross-alternative gap
    homogeneityEval McKayVanInwagen1977.spainSim
      spainAlts McKayVanInwagen1977.foughtAxis .actual = .indet ∧
    -- von Fintel/Križ: closest-world homogeneity satisfied
    (homogeneityCounterfactual McKayVanInwagen1977.spainSim
      (fun w => McKayVanInwagen1977.foughtAxis w ∨
                McKayVanInwagen1977.foughtAllies w)
      McKayVanInwagen1977.foughtAxis .actual).presupposition =
      PresupStatus.satisfied :=
  ⟨spain_homogeneity_gap, by decide⟩


end Santorio2018
