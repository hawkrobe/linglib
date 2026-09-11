import Linglib.Data.Examples.Jaeger2007
import Linglib.Core.Learning.Luce
import Linglib.Studies.GoldwaterJohnson2003
import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
import Mathlib.Data.Sign.Basic

/-!
# Jäger (2007): Maximum Entropy Models and Stochastic Optimality Theory

This file formalizes [jaeger-2007], the demonstration that the Gradual Learning Algorithm of
[boersma-1998] for Stochastic Optimality Theory is Stochastic Gradient Ascent on the
log-likelihood of a maximum entropy model of the kind [goldwater-johnson-2003] propose. The GLA
raises the rank of a constraint by the plasticity times the sign of the excess of a sampled
hypothesis's violations over the observation's, Section 2, which on binary constraints is the
plain excess (`glaSign_eq_glaUpdate`); its expected adjustment is the plasticity times the excess
of the expected violations over the observed, (1) (`expected_glaUpdate`), and the learner is at
rest exactly when the two agree (`expected_glaUpdate_eq_self_iff`), the convergence criterion of
Section 4. The per-weight gradient of the log-likelihood of an observation under the log-linear
model is the observed feature less its expectation, (2) (`hasDerivAt_log_gjProb_update`), so the
GLA step is the stochastic gradient step once violations are read as non-positive features
(`Core.gla_eq_sga`); the log-likelihood is concave
(`GoldwaterJohnson2003.concaveOn_log_gjProb_update`), so the maximum entropy learner reaches its
global maximum, the guarantee Stochastic OT lacks. Section 5 reruns the acquisition simulation of
Boersma and Levelt over the five syllable-structure constraints (`con`): a ranking produces an
input faithfully exactly when every markedness constraint the input violates is ranked below FAITH
(`faithful_iff`), so the stages at which FAITH overtakes the markedness constraints one by one,
from *CODA to *COMPLEXONSET, produce the syllable types in the nested order CV, CVC, {V, VC},
{CVCC, VCC}, {CCV, CCVC, CCVCC} (`produced_stages`); and a learner producing CV, the initial state,
lowers each markedness rank by the plasticity times the observation's violations
(`initial_glaUpdate`), so over the corpus of Table 1 the ranks fall in the order of their violation
rates, *CODA first and *COMPLEXONSET last (`corpusRate_order`), the order in which the simulation
has FAITH overtake them.

## Implementation notes

* The maximum entropy probabilities are `GoldwaterJohnson2003.gjProb`; the sampled estimate of
  the expected violations is stated over an arbitrary distribution on the candidates.
* Table 1 is the paper's data, in permyriad; the initial ranks, 0 for FAITH and 10 for the
  markedness constraints, the learning rate 0.1 and the trajectory of Figure 1 are reported, not
  derived. The simulation's acquisition order refines the stages' ties by frequency, placing
  CVCC before VCC; the stages alone leave them tied.

## References

* [jaeger-2007]
* [boersma-1998]
* [goldwater-johnson-2003]
-/

namespace Jaeger2007

open Core Constraints OptimalityTheory Finset Real Data.Examples GoldwaterJohnson2003

/-! ### The Gradual Learning Algorithm as Stochastic Gradient Ascent -/

/-- The GLA update of Section 2 on a single rank: the plasticity times the sign of the excess of
the sampled hypothesis's violations over the observation's. -/
noncomputable def glaSign (r η : ℝ) (obs hyp : ℕ) : ℝ :=
  r + η * SignType.sign ((hyp : ℝ) - obs)

/-- On binary constraints the sign is idle: the GLA update is the plain excess
(`Core.glaUpdate`). -/
theorem glaSign_eq_glaUpdate (r η : ℝ) {obs hyp : ℕ} (ho : obs ≤ 1) (hh : hyp ≤ 1) :
    glaSign r η obs hyp = glaUpdate r η obs hyp := by
  unfold glaSign glaUpdate
  interval_cases obs <;> interval_cases hyp <;> norm_num [sign_apply]

variable {O : Type*} [Fintype O]

/-- (1): over a distribution on the hypotheses, the expected GLA update of a rank is the plasticity
times the excess of the expected violations over the observed. -/
theorem expected_glaUpdate (p : O → ℝ) (hp : ∑ h, p h = 1) (c : O → ℕ) (o : O) (r η : ℝ) :
    ∑ h, p h * glaUpdate r η (c o) (c h) = r + η * (∑ h, p h * c h - c o) := by
  have key : ∀ h, p h * glaUpdate r η (c o) (c h) = p h * r + η * (p h * c h) - η * (p h * c o) :=
    λ h => by simp only [glaUpdate]; ring
  simp only [key, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hp]
  ring

/-- The learner is at rest exactly when the expected and the observed violations agree: the
convergence criterion of Section 4, shared by the GLA and Stochastic Gradient Ascent. -/
theorem expected_glaUpdate_eq_self_iff (p : O → ℝ) (hp : ∑ h, p h = 1) (c : O → ℕ) (o : O)
    (r : ℝ) {η : ℝ} (hη : η ≠ 0) :
    ∑ h, p h * glaUpdate r η (c o) (c h) = r ↔ ∑ h, p h * c h = c o := by
  rw [expected_glaUpdate p hp c o r η]
  constructor
  · intro h
    have h' : η * (∑ h, p h * c h - c o) = 0 := by linarith
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact absurd h0 hη
    · linarith
  · intro h
    rw [h, sub_self, mul_zero, add_zero]

variable {I : Type*} {n : ℕ}

/-- (2): with the other weights held fixed, the derivative of the log probability of an
observation in weight j is its expected violations of constraint j less the observed ones, the
observed feature less its expectation once violations are read as non-positive features. -/
theorem hasDerivAt_log_gjProb_update (con : CON (I × O) n) (w : Fin n → ℝ) (j : Fin n) (i : I)
    (o : O) (t : ℝ) :
    HasDerivAt (λ t => log (gjProb con (Function.update w j t) i o))
      (∑ o', gjProb con (Function.update w j t) i o' * con j (i, o') - con j (i, o)) t := by
  have : Nonempty O := ⟨o⟩
  simp_rw [gjProb_update]
  convert hasDerivAt_log_softmax _ _ o t using 1
  simp only [mul_neg, sum_neg_distrib]
  ring

/-! ### The Dutch syllable types of Table 1 -/

/-- A syllable type: the number of consonants in its onset and in its coda, at most two each. -/
abbrev Syl := Fin 3 × Fin 3

/-- The nine types of Table 1. -/
def cv : Syl := (1, 0)
def cvc : Syl := (1, 1)
def vc : Syl := (0, 1)
def v : Syl := (0, 0)
def cvcc : Syl := (1, 2)
def ccvc : Syl := (2, 1)
def ccv : Syl := (2, 0)
def vcc : Syl := (0, 2)
def ccvcc : Syl := (2, 2)

/-- A row of Table 1: the syllable type and its frequency in permyriad. -/
def Row.ofExample (e : LinguisticExample) : Option (Syl × ℕ) := do
  let on ← e.nat? "onset"
  let co ← e.nat? "coda"
  let f ← e.nat? "permyriad"
  if h : on < 3 ∧ co < 3 then some ((⟨on, h.1⟩, ⟨co, h.2⟩), f) else none

/-- Table 1. -/
def rows : List (Syl × ℕ) := Examples.all.filterMap Row.ofExample

/-! ### The constraints of Section 5 -/

/-- *CODA: no coda. -/
def starCoda : Constraint (Syl × Syl) := Constraint.binary λ c => 1 ≤ c.2.2

/-- ONSET: no vowel-initial syllable. -/
def onset : Constraint (Syl × Syl) := Constraint.binary λ c => c.2.1 = 0

/-- *COMPLEXCODA: no complex coda. -/
def starComplexCoda : Constraint (Syl × Syl) := Constraint.binary λ c => c.2.2 = 2

/-- *COMPLEXONSET: no complex onset. -/
def starComplexOnset : Constraint (Syl × Syl) := Constraint.binary λ c => c.2.1 = 2

/-- FAITH: the output is the input. -/
def faith : Constraint (Syl × Syl) := Constraint.binary λ c => c.1 ≠ c.2

/-- The constraint set, in the order of the converged ranking FAITH ≫ *COMPLEXONSET ≫
*COMPLEXCODA ≫ ONSET ≫ *CODA. -/
def con : CON (Syl × Syl) 5 := ![faith, starComplexOnset, starComplexCoda, onset, starCoda]

/-- Violation profiles. -/
def vp (i o : Syl) (k : Fin 5) : ℕ := con k (i, o)

/-- Every syllable type is a candidate output for every input. -/
def cands : Syl → Finset Syl := λ _ => univ

/-- A ranking produces an input faithfully exactly when every markedness constraint the input
violates is ranked below FAITH. -/
theorem faithful_iff (σ : Ranking 5) (i : Syl) :
    PicksAt cands vp σ i i ↔ ∀ k, vp i i k = 1 → σ.Dominates 0 k := by
  revert σ i; decide +kernel

/-- The syllable types produced faithfully once the markedness constraints in `S` are below
FAITH: those violating no other markedness constraint. -/
def produced (S : Finset (Fin 5)) : Finset Syl := univ.filter λ i => ∀ k, vp i i k = 1 → k ∈ S

/-- The types a ranking produces faithfully are those of the stage it is at. -/
theorem mem_produced_iff (σ : Ranking 5) (i : Syl) :
    i ∈ produced (univ.filter (σ.Dominates 0)) ↔ PicksAt cands vp σ i i := by
  simp [produced, faithful_iff]

/-- The stages at which FAITH overtakes *CODA, ONSET, *COMPLEXCODA and *COMPLEXONSET in turn:
the syllable types come in the nested order CV; CVC; V, VC; CVCC, VCC; CCV, CCVC, CCVCC. -/
theorem produced_stages :
    produced ∅ = {cv} ∧ produced {4} = {cv, cvc} ∧ produced {4, 3} = {cv, cvc, v, vc} ∧
    produced {4, 3, 2} = {cv, cvc, v, vc, cvcc, vcc} ∧ produced {4, 3, 2, 1} = univ := by
  decide

/-- CV violates no markedness constraint. -/
theorem cv_unmarked : ∀ i : Syl, ∀ k : Fin 5, k ≠ 0 → vp i cv k = 0 := by decide

/-- A learner producing CV with certainty, the initial state with FAITH at 0 and the markedness
constraints at 10, lowers each markedness rank by the plasticity times the observation's
violations, (1). -/
theorem initial_glaUpdate (r η : ℝ) (o : Syl) (k : Fin 5) (hk : k ≠ 0) :
    ∑ h, Pi.single (M := λ _ => ℝ) cv 1 h * glaUpdate r η (vp o o k) (vp o h k) =
      r - η * vp o o k := by
  have h := expected_glaUpdate (Pi.single (M := λ _ => ℝ) cv 1) (by simp) (λ h => vp o h k) o r η
  rw [h]
  simp [Pi.single_apply, cv_unmarked o k hk]
  ring

/-- The violation rate of a constraint in the corpus of Table 1, in permyriad. -/
def corpusRate (k : Fin 5) : ℕ := (rows.map λ r => r.2 * vp r.1 r.1 k).sum

/-- FAITH is never violated in the corpus, and the markedness ranks fall fastest for *CODA, then
ONSET, *COMPLEXCODA and *COMPLEXONSET: the order in which FAITH overtakes them. -/
theorem corpusRate_order :
    corpusRate 0 = 0 ∧ corpusRate 1 < corpusRate 2 ∧ corpusRate 2 < corpusRate 3 ∧
    corpusRate 3 < corpusRate 4 := by
  decide

end Jaeger2007
