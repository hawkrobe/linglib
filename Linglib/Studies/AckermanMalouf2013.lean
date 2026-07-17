import Linglib.Morphology.MorphRule
import Linglib.Morphology.Paradigm.Complexity
import Mathlib.Data.Rat.Defs

/-!
# [ackerman-malouf-2013]: The Low Conditional Entropy Conjecture
[ackerman-malouf-2013] [carstairs-mccarthy-2010]

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

- §0: i-Complexity (paper-specific aggregation; substrate types
  `Paradigm`/`ParadigmSystem`/`cellEntropy`/`conditionalCellEntropy`
  live in `Morphology/Paradigm.lean`, hoisted there 0.230.X for shared
  use with [rathi-hahn-futrell-2026]'s informational fusion)
- §1: Per-language LCEC verification (all 10 languages)
- §2: E-complexity / I-complexity dissociation
- §3: Mazatec case study (observed vs. random baseline)
-/

-- ============================================================================
-- §0: i-Complexity (paper-specific aggregation over substrate primitives)
-- ============================================================================

namespace Morphology.WP

open Morphology

/-- [ackerman-malouf-2013]'s **integrative complexity**: average
    conditional cell entropy across all off-diagonal cell pairs.

    `iComplexity(L) = (1 / n(n-1)) · Σᵢ≠ⱼ H(Cᵢ | Cⱼ)`

    Instantiated at `Form := String` since A&M's paradigms are over
    natural-language surface forms. -/
noncomputable def iComplexity {n : Nat} (ps : ParadigmSystem n String) : ℝ :=
  let cells := List.finRange n
  let pairs := cells.flatMap λ ci => (cells.filter (· != ci)).map λ cj => (ci, cj)
  let total := pairs.map λ (ci, cj) => ps.conditionalCellEntropy ci cj
  let sum := total.sum
  let numPairs := n * (n - 1)
  if numPairs == 0 then 0 else sum / (numPairs : ℝ)

/-- The Low Conditional Entropy Conjecture: i-complexity is bounded by
    a small threshold. The threshold is empirical (typically ≤ 1 nat). -/
def LCECHolds {n : Nat} (ps : ParadigmSystem n String) (threshold : ℝ) : Prop :=
  iComplexity ps ≤ threshold

private lemma sum_eq_zero_of_forall_zero {l : List ℝ}
    (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.sum_cons]
    rw [h a (.head as), ih (fun y hy => h y (.tail a hy)), add_zero]

theorem transparent_iComplexity_zero {n : Nat} (ps : ParadigmSystem n String)
    (h : ps.isTransparent) : iComplexity ps = 0 := by
  have hall : ∀ x ∈ ((List.finRange n).flatMap fun ci =>
      ((List.finRange n).filter (· != ci)).map fun cj =>
      (ci, cj)).map (fun x => ps.conditionalCellEntropy x.1 x.2),
      x = 0 := by
    intro x hx
    simp only [List.mem_map, List.mem_flatMap, List.mem_filter] at hx
    obtain ⟨⟨ci, cj⟩, ⟨w, _, f, ⟨_, hfne⟩, hpair⟩, rfl⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact h w f (by intro heq; simp [heq] at hfne)
  have hfold := sum_eq_zero_of_forall_zero hall
  simp only [iComplexity]
  simp only [hfold]; split <;> simp

end Morphology.WP

namespace AckermanMalouf2013

-- ============================================================================
-- LanguageData Sample (Tables 2--3 of [ackerman-malouf-2013])
-- ============================================================================

/-- Summary statistics for a language's morphological paradigm system,
    as reported in published studies.

    Fields correspond to Tables 2--3 of [ackerman-malouf-2013]. -/
structure LanguageData where
  /-- Language name -/
  name : String
  /-- Language family -/
  family : String
  /-- Number of inflection classes (E-complexity) -/
  numClasses : Nat
  /-- Number of paradigm cells -/
  numCells : Nat
  /-- Average conditional entropy H(Ci|Cj) in bits (I-complexity) -/
  avgCondEntropy : ℚ
  /-- Maximum cell entropy max H(Ci) in bits -/
  maxCellEntropy : ℚ
  deriving Repr

/-- Fur (Nilo-Saharan, Fur; Sudan). 4 classes, 2 cells. -/
def fur : LanguageData where
  name := "Fur"
  family := "Nilo-Saharan"
  numClasses := 4
  numCells := 2
  avgCondEntropy := 489 / 1000  -- 0.489
  maxCellEntropy := 1334 / 1000  -- 1.334

/-- Ngiti (Nilo-Saharan, Central Sudanic; DRC). 8 classes, 2 cells. -/
def ngiti : LanguageData where
  name := "Ngiti"
  family := "Nilo-Saharan"
  numClasses := 8
  numCells := 2
  avgCondEntropy := 380 / 1000  -- 0.380
  maxCellEntropy := 1741 / 1000  -- 1.741

/-- Nuer (Nilo-Saharan, Nilotic; Sudan/South Sudan). 31 classes, 4 cells. -/
def nuer : LanguageData where
  name := "Nuer"
  family := "Nilo-Saharan"
  numClasses := 31
  numCells := 4
  avgCondEntropy := 513 / 1000  -- 0.513
  maxCellEntropy := 3224 / 1000  -- 3.224

/-- Kwerba (Trans-New Guinea; Papua, Indonesia). 2 classes, 2 cells. -/
def kwerba : LanguageData where
  name := "Kwerba"
  family := "Trans-New Guinea"
  numClasses := 2
  numCells := 2
  avgCondEntropy := 469 / 1000  -- 0.469
  maxCellEntropy := 529 / 1000  -- 0.529

/-- Chinantec (Oto-Manguean; Oaxaca, Mexico). 62 classes, 4 cells.
    Comaltepec Chinantec tonal verb paradigms. -/
def chinantec : LanguageData where
  name := "Chinantec"
  family := "Oto-Manguean"
  numClasses := 62
  numCells := 4
  avgCondEntropy := 426 / 1000  -- 0.426
  maxCellEntropy := 4266 / 1000  -- 4.266

/-- Chiquihuitlan Mazatec (Oto-Manguean; Oaxaca, Mexico).
    109 classes, 4 cells. The paper's primary case study (section 4). -/
def mazatec : LanguageData where
  name := "Chiquihuitlan Mazatec"
  family := "Oto-Manguean"
  numClasses := 109
  numCells := 4
  avgCondEntropy := 709 / 1000  -- 0.709
  maxCellEntropy := 5248 / 1000  -- 5.248

/-- Finnish (Uralic, Finnic). 51 classes, 8 cells. -/
def finnish : LanguageData where
  name := "Finnish"
  family := "Uralic"
  numClasses := 51
  numCells := 8
  avgCondEntropy := 209 / 1000  -- 0.209
  maxCellEntropy := 3803 / 1000  -- 3.803

/-- German (Indo-European, Germanic). 7 classes, 8 cells. -/
def german : LanguageData where
  name := "German"
  family := "Indo-European"
  numClasses := 7
  numCells := 8
  avgCondEntropy := 45 / 1000  -- 0.045
  maxCellEntropy := 1906 / 1000  -- 1.906

/-- Russian (Indo-European, Slavic). 8 classes, 8 cells. -/
def russian : LanguageData where
  name := "Russian"
  family := "Indo-European"
  numClasses := 8
  numCells := 8
  avgCondEntropy := 89 / 1000  -- 0.089
  maxCellEntropy := 2170 / 1000  -- 2.170

/-- Spanish (Indo-European, Romance). 3 classes, 57 cells. -/
def spanish : LanguageData where
  name := "Spanish"
  family := "Indo-European"
  numClasses := 3
  numCells := 57
  avgCondEntropy := 3 / 1000  -- 0.003
  maxCellEntropy := 1522 / 1000  -- 1.522

/-- All 10 languages in the [ackerman-malouf-2013] sample (Table 3). -/
def ackermanMalouf2013 : List LanguageData :=
  [fur, ngiti, nuer, kwerba, chinantec, mazatec, finnish, german, russian, spanish]

/-- The LCEC threshold: all 10 languages fall below 1 bit of average
    conditional entropy. Even the most complex system (Mazatec, 109 classes)
    has I-complexity < 1 bit. -/
def lcecThreshold : ℚ := 1

/-- Expected I-complexity under random class assignment for Mazatec
    (Monte Carlo baseline). The paper reports the mean of 1000 random
    permutations as ~5.25 bits, far above the observed 0.709 bits. -/
def mazatecRandomBaseline : ℚ := 525 / 100  -- 5.25

-- ============================================================================
-- §1. Per-language LCEC Verification
-- ============================================================================

/-! Each language's reported I-complexity is below the 1-bit threshold.
    These are "per-datum verification theorems" in linglib's sense:
    changing a language's avgCondEntropy breaks exactly the corresponding
    theorem. -/

theorem fur_lcec : fur.avgCondEntropy ≤ lcecThreshold := by
  unfold fur lcecThreshold; norm_num
theorem ngiti_lcec : ngiti.avgCondEntropy ≤ lcecThreshold := by
  unfold ngiti lcecThreshold; norm_num
theorem nuer_lcec : nuer.avgCondEntropy ≤ lcecThreshold := by
  unfold nuer lcecThreshold; norm_num
theorem kwerba_lcec : kwerba.avgCondEntropy ≤ lcecThreshold := by
  unfold kwerba lcecThreshold; norm_num
theorem chinantec_lcec : chinantec.avgCondEntropy ≤ lcecThreshold := by
  unfold chinantec lcecThreshold; norm_num
theorem mazatec_lcec : mazatec.avgCondEntropy ≤ lcecThreshold := by
  unfold mazatec lcecThreshold; norm_num
theorem finnish_lcec : finnish.avgCondEntropy ≤ lcecThreshold := by
  unfold finnish lcecThreshold; norm_num
theorem german_lcec : german.avgCondEntropy ≤ lcecThreshold := by
  unfold german lcecThreshold; norm_num
theorem russian_lcec : russian.avgCondEntropy ≤ lcecThreshold := by
  unfold russian lcecThreshold; norm_num
theorem spanish_lcec : spanish.avgCondEntropy ≤ lcecThreshold := by
  unfold spanish lcecThreshold; norm_num

/-- All 10 languages satisfy the LCEC. -/
theorem all_satisfy_lcec :
    ∀ l ∈ ackermanMalouf2013, l.avgCondEntropy ≤ lcecThreshold := by
  intro l hl
  simp only [ackermanMalouf2013, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fur_lcec
  · exact ngiti_lcec
  · exact nuer_lcec
  · exact kwerba_lcec
  · exact chinantec_lcec
  · exact mazatec_lcec
  · exact finnish_lcec
  · exact german_lcec
  · exact russian_lcec
  · exact spanish_lcec

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
  ⟨rfl, by unfold mazatec; norm_num⟩

/-- Kwerba has minimal E-complexity (2 classes) but its I-complexity
    is *not* the lowest — German (7 classes) has lower I-complexity.
    This shows E-complexity doesn't predict I-complexity in either direction. -/
theorem eComplexity_doesnt_predict_iComplexity :
    kwerba.numClasses < german.numClasses ∧
    german.avgCondEntropy < kwerba.avgCondEntropy :=
  ⟨by simp [kwerba, german], by unfold german kwerba; norm_num⟩

/-- Spanish has only 3 classes but 57 cells — yet its I-complexity is
    the lowest in the sample (0.003 bits). More cells with fewer classes
    means more implicative structure. -/
theorem spanish_minimal_iComplexity :
    ∀ l ∈ ackermanMalouf2013, spanish.avgCondEntropy ≤ l.avgCondEntropy := by
  intro l hl
  simp only [ackermanMalouf2013, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (first
    | (unfold spanish fur; norm_num)
    | (unfold spanish ngiti; norm_num)
    | (unfold spanish nuer; norm_num)
    | (unfold spanish kwerba; norm_num)
    | (unfold spanish chinantec; norm_num)
    | (unfold spanish mazatec; norm_num)
    | (unfold spanish finnish; norm_num)
    | (unfold spanish german; norm_num)
    | (unfold spanish russian; norm_num)
    | (unfold spanish; norm_num))

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
    mazatec.avgCondEntropy < mazatecRandomBaseline := by
  unfold mazatec mazatecRandomBaseline; norm_num

/-- The ratio of observed to random I-complexity is less than 1/7.
    (0.709 / 5.25 ≈ 0.135, i.e., ~13.5% of random) -/
theorem mazatec_ratio_to_random :
    mazatec.avgCondEntropy * 7 < mazatecRandomBaseline := by
  unfold mazatec mazatecRandomBaseline; norm_num

/-- Mazatec has nonzero I-complexity: it violates [carstairs-mccarthy-2010]'s synonymy avoidance but satisfies the LCEC. This witnesses
    that the LCEC is strictly weaker than synonymy avoidance. -/
theorem mazatec_violates_synonymyAvoidance :
    mazatec.avgCondEntropy > 0 := by
  unfold mazatec; norm_num

end AckermanMalouf2013
