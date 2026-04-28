import Linglib.Phenomena.Morphology.Typology
import Linglib.Core.InformationTheory
import Linglib.Core.Morphology.MorphRule

/-!
# @cite{ackerman-malouf-2013}: The Low Conditional Entropy Conjecture
@cite{ackerman-malouf-2013} @cite{carstairs-mccarthy-2010}

## E-complexity vs. I-complexity

Languages differ dramatically in their **enumerative complexity** (E-complexity):
how many inflection classes, allomorphic variants, and paradigm cells they
have. But this apparent complexity is misleading. The key question is
**integrative complexity** (I-complexity): given that a speaker knows *some*
forms of a lexeme, how hard is it to predict the *rest*?

## The LCEC

The Low Conditional Entropy Conjecture states that the average conditional
entropy of paradigm cells — how uncertain you are about one cell given another —
is uniformly low across typologically diverse languages, regardless of
E-complexity. Formally:

    I-complexity(L) = (1 / n(n-1)) · Σᵢ≠ⱼ H(Cᵢ | Cⱼ)

is low for all natural languages L, where Cᵢ ranges over paradigm cells and
H(Cᵢ | Cⱼ) is the conditional entropy of cell i given cell j.

## Structure

- §0: LCEC substrate (was Theories/Morphology/WP/LCEC.lean, relocated 0.230.455
  — single consumer; WP/ dir dissolves; LCEC is one specific empirical
  conjecture, not the whole WP framework)
- §1: Per-language LCEC verification (all 10 languages)
- §2: E-complexity / I-complexity dissociation
- §3: Mazatec case study (observed vs. random baseline)
-/

-- ============================================================================
-- §0: LCEC Substrate
-- ============================================================================

namespace Morphology.WP

open Core.InformationTheory

/-- An inflection class: function from cell index to surface realization. -/
structure InflectionClass (numCells : Nat) where
  realize : Fin numCells → String

instance {n : Nat} : BEq (InflectionClass n) where
  beq a b := (List.finRange n).all λ i => a.realize i == b.realize i

/-- A paradigm system: inflection classes paired with frequencies. -/
structure ParadigmSystem (numCells : Nat) where
  entries : List (InflectionClass numCells × ℚ)

/-- Group a tagged list by key, summing associated ℚ values. -/
def groupBySum {α : Type} [BEq α] (tagged : List (α × ℚ)) : List (α × ℚ) :=
  tagged.foldl (λ acc (key, f) =>
    match acc.find? (λ (k, _) => k == key) with
    | some _ => acc.map (λ (k, p) => if k == key then (k, p + f) else (k, p))
    | none => acc ++ [(key, f)]
  ) []

def cellDistribution {n : Nat} (ps : ParadigmSystem n) (c : Fin n) :
    List (String × ℚ) :=
  groupBySum (ps.entries.map λ (ic, f) => (ic.realize c, f))

def jointCellDistribution {n : Nat} (ps : ParadigmSystem n)
    (ci cj : Fin n) : List ((String × String) × ℚ) :=
  groupBySum (ps.entries.map λ (ic, f) => ((ic.realize ci, ic.realize cj), f))

def eComplexity {n : Nat} (ps : ParadigmSystem n) : Nat :=
  ps.entries.length

private noncomputable def listToFinsetFn {α : Type*} [DecidableEq α]
    (dist : List (α × ℚ)) : Finset α × (α → ℝ) :=
  ((dist.map Prod.fst).toFinset,
   fun a => (((dist.find? (·.1 == a)).map Prod.snd).getD 0 : ℚ))

noncomputable def cellEntropy {n : Nat} (ps : ParadigmSystem n) (c : Fin n) : ℝ :=
  let (support, prob) := listToFinsetFn (cellDistribution ps c)
  entropy support prob

noncomputable def conditionalCellEntropy {n : Nat} (ps : ParadigmSystem n)
    (ci cj : Fin n) : ℝ :=
  let (sJoint, joint) := listToFinsetFn (jointCellDistribution ps ci cj)
  let (sMargX, margX) := listToFinsetFn (cellDistribution ps cj)
  conditionalEntropy sJoint joint sMargX margX

noncomputable def iComplexity {n : Nat} (ps : ParadigmSystem n) : ℝ :=
  let cells := List.finRange n
  let pairs := cells.flatMap λ ci => (cells.filter (· != ci)).map λ cj => (ci, cj)
  let total := pairs.map λ (ci, cj) => conditionalCellEntropy ps ci cj
  let sum := total.sum
  let numPairs := n * (n - 1)
  if numPairs == 0 then 0 else sum / (numPairs : ℝ)

def LCECHolds {n : Nat} (ps : ParadigmSystem n) (threshold : ℝ) : Prop :=
  iComplexity ps ≤ threshold

def isImplicative {n : Nat} (ps : ParadigmSystem n)
    (ci cj : Fin n) : Prop :=
  conditionalCellEntropy ps ci cj = 0

def isTransparent {n : Nat} (ps : ParadigmSystem n) : Prop :=
  ∀ (ci cj : Fin n), ci ≠ cj → isImplicative ps ci cj

private lemma sum_eq_zero_of_forall_zero {l : List ℝ}
    (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.sum_cons]
    rw [h a (.head as), ih (fun y hy => h y (.tail a hy)), add_zero]

theorem transparent_iComplexity_zero {n : Nat} (ps : ParadigmSystem n)
    (h : isTransparent ps) : iComplexity ps = 0 := by
  have hall : ∀ x ∈ ((List.finRange n).flatMap fun ci =>
      ((List.finRange n).filter (· != ci)).map fun cj =>
      (ci, cj)).map (fun x => conditionalCellEntropy ps x.1 x.2),
      x = 0 := by
    intro x hx
    simp only [List.mem_map, List.mem_flatMap, List.mem_filter] at hx
    obtain ⟨⟨ci, cj⟩, ⟨w, _, f, ⟨_, hfne⟩, hpair⟩, rfl⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact h w f (by intro heq; simp [heq] at hfne)
  have hfold := sum_eq_zero_of_forall_zero hall
  simp only [iComplexity]
  simp only [hfold]; split <;> simp

/-- Extract a `ParadigmSystem` from a list of `Stem`s. -/
def fromStems {σ : Type} (stems : List (Core.Morphology.Stem σ))
    (baseMeaning : σ) (numCells : Nat)
    (cellExtractor : List (String × Features × σ) → Fin numCells → String) :
    ParadigmSystem numCells :=
  let allParadigms := stems.map λ s =>
    let forms := s.allForms baseMeaning
    { realize := cellExtractor forms : InflectionClass numCells }
  let total := stems.length
  let unique := groupBySum (allParadigms.map λ ic => (ic, (1 : ℚ)))
  { entries := unique.map λ (ic, count) => (ic, count / total) }

end Morphology.WP

namespace Phenomena.Morphology.AckermanMalouf2013

open Phenomena.Morphology.Typology

-- ============================================================================
-- §1. Per-language LCEC Verification
-- ============================================================================

/-! Each language's reported I-complexity is below the 1-bit threshold.
    These are "per-datum verification theorems" in linglib's sense:
    changing a language's avgCondEntropy breaks exactly the corresponding
    theorem. -/

theorem fur_lcec : fur.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem ngiti_lcec : ngiti.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem nuer_lcec : nuer.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem kwerba_lcec : kwerba.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem chinantec_lcec : chinantec.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem mazatec_lcec : mazatec.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem finnish_lcec : finnish.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem german_lcec : german.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem russian_lcec : russian.avgCondEntropy ≤ lcecThreshold := by native_decide
theorem spanish_lcec : spanish.avgCondEntropy ≤ lcecThreshold := by native_decide

/-- All 10 languages satisfy the LCEC. -/
theorem all_satisfy_lcec :
    ∀ l ∈ ackermanMalouf2013, l.avgCondEntropy ≤ lcecThreshold := by
  intro l hl
  simp only [ackermanMalouf2013, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals native_decide

-- ============================================================================
-- §2. E-complexity / I-complexity Dissociation
-- ============================================================================

/-! The LCEC's key prediction: E-complexity and I-complexity are dissociated.
    A language can have enormous E-complexity but low I-complexity. -/

/-- Mazatec has maximal E-complexity in the sample (109 classes). -/
theorem mazatec_max_eComplexity :
    ∀ l ∈ ackermanMalouf2013, l.numClasses ≤ mazatec.numClasses := by
  intro l hl
  simp only [ackermanMalouf2013, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [mazatec, fur, ngiti, nuer, kwerba, chinantec, finnish, german, russian, spanish]

/-- Mazatec's I-complexity is still below 1 bit despite 109 classes. -/
theorem mazatec_high_e_low_i :
    mazatec.numClasses = 109 ∧ mazatec.avgCondEntropy ≤ 1 :=
  ⟨rfl, by native_decide⟩

/-- Kwerba has minimal E-complexity (2 classes) but its I-complexity
    is *not* the lowest — German (7 classes) has lower I-complexity.
    This shows E-complexity doesn't predict I-complexity in either direction. -/
theorem eComplexity_doesnt_predict_iComplexity :
    kwerba.numClasses < german.numClasses ∧
    german.avgCondEntropy < kwerba.avgCondEntropy :=
  ⟨by simp [kwerba, german], by native_decide⟩

/-- Spanish has only 3 classes but 57 cells — yet its I-complexity is
    the lowest in the sample (0.003 bits). More cells with fewer classes
    means more implicative structure. -/
theorem spanish_minimal_iComplexity :
    ∀ l ∈ ackermanMalouf2013, spanish.avgCondEntropy ≤ l.avgCondEntropy := by
  intro l hl
  simp only [ackermanMalouf2013, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals native_decide

-- ============================================================================
-- §3. Mazatec Case Study: Observed vs. Random Baseline
-- ============================================================================

/-! The Mazatec case study (§4 of the paper) demonstrates that the observed
    I-complexity is far below what random assignment of inflection-class
    patterns would produce. -/

/-- Mazatec's observed I-complexity is far below the random baseline.
    Observed: 0.709 bits. Random permutation baseline: ~5.25 bits.
    The observed value is less than 14% of the random baseline. -/
theorem mazatec_well_below_random :
    mazatec.avgCondEntropy < mazatecRandomBaseline := by native_decide

/-- The ratio of observed to random I-complexity is less than 1/7.
    (0.709 / 5.25 ≈ 0.135, i.e., ~13.5% of random) -/
theorem mazatec_ratio_to_random :
    mazatec.avgCondEntropy * 7 < mazatecRandomBaseline := by native_decide

/-- Mazatec has nonzero I-complexity: it violates @cite{carstairs-mccarthy-2010}'s synonymy avoidance but satisfies the LCEC. This witnesses
    that the LCEC is strictly weaker than synonymy avoidance. -/
theorem mazatec_violates_synonymyAvoidance :
    mazatec.avgCondEntropy > 0 := by native_decide

end Phenomena.Morphology.AckermanMalouf2013
