import Linglib.Core.Agent.Learning
import Linglib.Theories.Phonology.HarmonicGrammar.OTLimit
import Linglib.Theories.Phonology.HarmonicGrammar.MaxEnt

/-!
# @cite{jaeger-2007}: Maximum Entropy Models and Stochastic Optimality Theory
@cite{jaeger-2007}

@cite{jaeger-2007} demonstrates that @cite{boersma-1998}'s Gradual Learning
Algorithm (GLA) for Stochastic OT is mathematically identical to Stochastic
Gradient Ascent (SGA) for Maximum Entropy models. This unifies two traditions:

- **StOT** (Boersma): adds Gaussian noise to constraint ranks, learns via
  the GLA (online, cognitively plausible)
- **MaxEnt** (@cite{goldwater-johnson-2003}): log-linear model over
  constraint violations, learns via batch gradient ascent or SGA

## Key contributions formalized here

1. **GLA = SGA** (§4): The GLA update rule is SGA with single-sample
   estimates. Both adjust each weight by `η · (observed − expected)`.
   This is `gla_eq_sga` from `Core.Agent.Learning`.

2. **Correct gradient** (§4, eq (2)): The per-weight gradient of MaxEnt
   log-likelihood is `E_emp[cⱼ] − E_r̄[cⱼ]` — observed minus expected
   feature value. This is `hasDerivAt_logConditional` from
   `Core.Agent.RationalAction`, instantiated as `gradient` in
   @cite{goldwater-johnson-2003}.

3. **Convergence guarantee** (§4): SGA converges to the global maximum
   because log-likelihood is concave (`logConditional_concaveOn`). StOT's
   GLA has no such guarantee — this is the main formal advantage of MaxEnt.

4. **Ganging-up** (§3): Both MaxEnt and StOT admit ganging-up effects
   (multiple weak constraints overriding a strong one), unlike classical OT.
   This is `Ganging` from `OTLimit.lean`.

5. **Dutch syllable acquisition** (§5): Replication of Boersma & Levelt
   (2000) with MaxEnt+SGA produces the same acquisition order as the GLA,
   consistent with child language data.
-/

namespace Phenomena.PhonologicalAlternation.Studies.Jaeger2007

open Core Phonology.HarmonicGrammar Real

-- ============================================================================
-- § 1: GLA = SGA (Main Theorem)
-- ============================================================================

/-- The main theorem of @cite{jaeger-2007}: the Gradual Learning Algorithm
    is Stochastic Gradient Ascent by definition.

    Both update weight j by `η · (c_j(observed) − c_j(hypothesis))`.
    For MaxEnt, this is an unbiased estimate of the log-likelihood gradient
    `E_emp[c_j] − E_r̄[c_j]` (see `sga_uses_correct_gradient`). -/
theorem gla_is_sga (r_j η : ℝ) (obs hyp : ℕ) :
    glaUpdate r_j η obs hyp = sgaUpdate r_j η obs hyp :=
  gla_eq_sga r_j η obs hyp

-- ============================================================================
-- § 2: Convergence Advantage of MaxEnt
-- ============================================================================

/-- **MaxEnt convergence guarantee**: the per-weight log-likelihood is concave,
    so gradient-based learning converges to the unique global maximum.

    @cite{jaeger-2007} §4: "The log-likelihood has the desirable property
    of being convex [sic — concave], which means that it does not have local
    maxima. Gradient Ascent is thus guaranteed to find the global maximum."

    StOT's GLA lacks this guarantee — no proof of convergence exists for the
    general case (@cite{jaeger-2007} §2, fn. 1). -/
theorem maxent_convergence_guarantee {ι : Type*} [Fintype ι] [Nonempty ι]
    (s r : ι → ℝ) (y : ι) :
    ConcaveOn ℝ Set.univ
      (fun wⱼ => (wⱼ * s y + r y) - logSumExpOffset s r wⱼ) :=
  logConditional_concaveOn s r y

-- ============================================================================
-- § 3: Ganging-Up (§3 — shared by MaxEnt and StOT)
-- ============================================================================

/-- Both MaxEnt and StOT admit ganging-up: two weak constraints can jointly
    override a strong one. Classical OT precludes this when weights are
    exponentially separated (`exponential_separation_precludes_ganging`).

    @cite{jaeger-2007}: "Both StOT and ME diverge from classical OT in
    admitting ganging-up effects." -/
theorem ganging_possible_without_separation :
    Ganging (1 : ℚ) 1 (3/2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- ============================================================================
-- § 4: Dutch Syllable Acquisition Data (§5, Table 1)
-- ============================================================================

/-- Dutch syllable types from @cite{jaeger-2007} Table 1
    (Boersma & Levelt 2000, data from Joost van de Weijer). -/
inductive DutchSyllable
  | CV | CVC | VC | V | CVCC | CCVC | CCV | VCC | CCVCC
  deriving DecidableEq, Repr

open DutchSyllable

-- UNVERIFIED: exact frequency values from Table 1
/-- Frequency of Dutch syllable types in child-directed speech (%). -/
def syllableFreq : DutchSyllable → ℚ
  | CV    => 4481/100  -- 44.81%
  | CVC   => 3205/100  -- 32.05%
  | VC    => 1199/100  -- 11.99%
  | V     => 385/100   -- 3.85%
  | CVCC  => 325/100   -- 3.25%
  | CCVC  => 198/100   -- 1.98%
  | CCV   => 138/100   -- 1.38%
  | VCC   => 42/100    -- 0.42%
  | CCVCC => 26/100    -- 0.26%

/-- Constraints for Dutch syllable structure (§5). -/
inductive SyllableConstraint
  | starCoda        -- *CODA: violated by -C and -CC syllables
  | onset           -- ONSET: violated by V-initial syllables
  | starComplexCoda -- *COMPLEXCODA: violated by -CC syllables
  | starComplexOnset -- *COMPLEXONSET: violated by CC- syllables
  | faith           -- FAITH: violated when input ≠ output
  deriving DecidableEq, Repr

open SyllableConstraint

/-- Violation count: how many times each constraint is violated by each
    syllable type (assuming faithful mapping, so FAITH = 0). -/
def violations : SyllableConstraint → DutchSyllable → ℕ
  | starCoda,        CV    => 0 | starCoda,        CVC   => 1
  | starCoda,        VC    => 1 | starCoda,        V     => 0
  | starCoda,        CVCC  => 1 | starCoda,        CCVC  => 1
  | starCoda,        CCV   => 0 | starCoda,        VCC   => 1
  | starCoda,        CCVCC => 1
  | onset,           CV    => 0 | onset,           CVC   => 0
  | onset,           VC    => 1 | onset,           V     => 1
  | onset,           CVCC  => 0 | onset,           CCVC  => 0
  | onset,           CCV   => 0 | onset,           VCC   => 1
  | onset,           CCVCC => 0
  | starComplexCoda, CV    => 0 | starComplexCoda, CVC   => 0
  | starComplexCoda, VC    => 0 | starComplexCoda, V     => 0
  | starComplexCoda, CVCC  => 1 | starComplexCoda, CCVC  => 0
  | starComplexCoda, CCV   => 0 | starComplexCoda, VCC   => 1
  | starComplexCoda, CCVCC => 1
  | starComplexOnset, CV   => 0 | starComplexOnset, CVC  => 0
  | starComplexOnset, VC   => 0 | starComplexOnset, V    => 0
  | starComplexOnset, CVCC => 0 | starComplexOnset, CCVC => 1
  | starComplexOnset, CCV  => 1 | starComplexOnset, VCC  => 0
  | starComplexOnset, CCVCC => 1
  | faith,           _     => 0  -- faithful mapping assumed

/-- CV violates no markedness constraints. -/
theorem cv_no_violations (c : SyllableConstraint) : violations c CV = 0 := by
  cases c <;> rfl

/-- CCVCC violates three markedness constraints (*Coda, *ComplexCoda, *ComplexOnset). -/
theorem ccvcc_three_violations :
    violations starCoda CCVCC + violations starComplexCoda CCVCC +
    violations starComplexOnset CCVCC = 3 := by native_decide

-- ============================================================================
-- § 5: Acquisition Order Predictions
-- ============================================================================

/-- The converged constraint ranking from §5:
    FAITH ≫ *COMPLEXONSET ≫ *COMPLEXCODA ≫ ONSET ≫ *CODA

    We represent this as learned weights (higher weight = higher priority).
    The exact values are from Jäger's simulation (Fig. 1). -/
-- UNVERIFIED: exact converged weight values from Fig. 1
def convergedWeights : SyllableConstraint → ℚ
  | faith            => 13
  | starComplexOnset => 8
  | starComplexCoda  => 7
  | onset            => 5
  | starCoda         => 0

/-- FAITH outranks all markedness constraints at convergence. -/
theorem faith_highest : ∀ c : SyllableConstraint,
    c ≠ faith → convergedWeights c < convergedWeights faith := by
  intro c hc; cases c <;> simp_all [convergedWeights] <;> norm_num

/-- The markedness constraints are ranked in the predicted order. -/
theorem markedness_ranking :
    convergedWeights starCoda < convergedWeights onset ∧
    convergedWeights onset < convergedWeights starComplexCoda ∧
    convergedWeights starComplexCoda < convergedWeights starComplexOnset := by
  simp [convergedWeights]; norm_num

/-- Simpler syllables (fewer violations) are acquired first because they have
    higher harmony. CV has harmony 0 (no violations), while CCVCC has the
    lowest harmony (3 violations). -/
theorem cv_dominates_ccvcc :
    violations starCoda CV + violations onset CV +
    violations starComplexCoda CV + violations starComplexOnset CV <
    violations starCoda CCVCC + violations onset CCVCC +
    violations starComplexCoda CCVCC + violations starComplexOnset CCVCC := by
  native_decide

end Phenomena.PhonologicalAlternation.Studies.Jaeger2007
