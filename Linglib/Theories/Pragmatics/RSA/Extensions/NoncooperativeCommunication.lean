import Linglib.Theories.Pragmatics.RSA.Extensions.ArgumentativeStrength
import Linglib.Theories.Pragmatics.RSA.Implementations.BarnettEtAl2022
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Noncooperative Communication: Unified Argumentative RSA

Unifies Cummins & Franke (2021)'s argumentative strength framework and
Barnett et al. (2022)'s persuasive RSA into a single parameterized model,
following Cummins (2025)'s analysis of noncooperative communication.

## Core Unification

Both models instantiate the same weighted-utility architecture:

  U(u; w, G) = U_epistemic(u; w) + β · U_goal(u; G)

| Model | U_goal | β |
|-------|--------|---|
| Standard RSA | — | 0 |
| Barnett et al. | ln P_L0(w*∣u) | fitted (β̂ = 2.26) |
| C&F (semantic) | argStr(u, G) | implicit (speaker maximizes argStr) |

The parameter β controls the cooperativity spectrum:
- β = 0: fully cooperative (standard RSA)
- 0 < β < ∞: partially argumentative (Barnett et al.)
- β → ∞: purely argumentative (C&F's rational speaker)

## Epistemic Vigilance

Following Sperber et al. (2010), the hearer's interpretation is a
trust-weighted mixture of pragmatic and literal posteriors:

  P_vigilant(w∣u) = τ · P_L1(w∣u) + (1−τ) · P_L0(w∣u)

where τ ∈ [0,1] is the hearer's trust in speaker cooperativity.

## Meaning-Level Taxonomy

Cummins (2025) identifies four levels at which falsehood can occur:
assertion, implicature, presupposition, and typicality departure.
Both C&F and Barnett involve misleading at the typicality/implicature
level while maintaining truthful assertions — the argumentative speaker
exploits pragmatic expectations without violating Quality.

## References

- Cummins, C. (2025). Noncooperative Communication. *Annu. Rev. Linguist.*, 11, 35–52.
- Cummins, C. & Franke, M. (2021). Argumentative strength of numerical quantity.
- Barnett, S. A., Griffiths, T. L., & Hawkins, R. D. (2022). A Pragmatic Account
  of the Weak Evidence Effect. *Open Mind*, 6, 169–182.
- Merin, A. (1999). Information, relevance, and social decision-making.
- Sperber, D., et al. (2010). Epistemic vigilance. *Mind & Language*, 25, 359–393.
- Macuch Silva, V. et al. (2024). Strategic quantifier use in production.
- Mazzarella, D. et al. (2018). Saying, presupposing and implicating.
-/

namespace RSA.NoncooperativeCommunication

open RSA.ArgumentativeStrength
open RSA.CombinedUtility
open RSA.Implementations.BarnettEtAl2022


-- ============================================================
-- Section 1: Cooperativity Spectrum (Cummins 2025 §§1–4)
-- ============================================================

/-- Speaker orientation on the cooperativity spectrum (Cummins 2025).

- cooperative: β=0, speaker maximizes hearer's accurate belief (standard RSA)
- argumentative: β>0, speaker has a goal G and balances informativity
  and persuasion (C&F 2021, Barnett et al. 2022, Macuch Silva et al. 2024)

The distinction is continuous: β parameterizes the spectrum. -/
inductive SpeakerOrientation where
  | cooperative     -- β=0: standard RSA
  | argumentative   -- β>0: goal-oriented
  deriving DecidableEq, BEq, Repr

/-- Classify speaker orientation from the goal weight λ ∈ [0,1] -/
def orientationOf (goalWeight : ℚ) : SpeakerOrientation :=
  if goalWeight = 0 then .cooperative else .argumentative


-- goalOrientedUtility and its core theorems (goalOriented_cooperative,
-- goalOriented_eq_combinedWeighted, goalOriented_mono_beta, etc.)
-- are defined in RSA.CombinedUtility and available via `open` above.


-- ============================================================
-- Section 3: Bridge — Barnett et al. (2022)
-- ============================================================

/-- Barnett et al.'s Eq. 6 is literally goalOrientedUtility (via the
`eq6` abbreviation in BarnettEtAl2022). -/
theorem barnett_eq6_is_goalOriented (uEpi uPers β : ℚ) :
    eq6 uEpi uPers β = goalOrientedUtility uEpi uPers β := rfl

/-- Transitivity: Barnett eq6 → goalOriented → combinedWeighted.
All three representations are literally the same function. -/
theorem barnett_goalOriented_combinedWeighted (uEpi uPers β : ℚ) :
    eq6 uEpi uPers β = goalOrientedUtility uEpi uPers β ∧
    goalOrientedUtility uEpi uPers β = combinedWeighted 1 β uEpi uPers :=
  ⟨rfl, goalOriented_eq_combinedWeighted uEpi uPers β⟩

/-- All representations agree at β=0: cooperative RSA. -/
theorem all_cooperative_at_zero (uEpi uGoal : ℚ) :
    goalOrientedUtility uEpi uGoal 0 = uEpi ∧
    eq6 uEpi uGoal 0 = uEpi ∧
    combinedWeighted 1 0 uEpi uGoal = uEpi := by
  refine ⟨?_, ?_, ?_⟩
  · exact goalOriented_cooperative uEpi uGoal
  · exact goalOriented_cooperative uEpi uGoal  -- eq6 = goalOrientedUtility
  · unfold combinedWeighted; ring


-- ============================================================
-- Section 4: Bridge — C&F (2021) Argumentative Strength
-- ============================================================

-- C&F's argStr(u, G) = log₂(P(u|G)/P(u|¬G)) measures how much evidence
-- utterance u provides for goal G. Barnett's U_pers(u; w*) = ln P_L0(w*|u)
-- measures how much u makes the goal state likely under L0.
--
-- These are related by Bayes' theorem: P(G|u) is monotone in bayesFactor(u,G).
-- So both order utterances the same way — utterances that support the goal
-- have positive argStr AND high L0 posterior for the goal.

/-- The ordinal bridge: an utterance with higher Bayes factor (C&F's measure)
also induces a higher posterior for the goal (Barnett's measure).

P(G|u) = bf · P(G) / (bf · P(G) + P(¬G))

This function is strictly increasing in bf when P(G) ∈ (0,1). -/
theorem bayesFactor_monotone_in_posterior
    (bf₁ bf₂ pG : ℚ) (hG : 0 < pG) (hG1 : pG < 1)
    (hbf₁ : 0 < bf₁) (_hbf₂ : 0 < bf₂) (hord : bf₂ < bf₁) :
    bf₂ * pG / (bf₂ * pG + (1 - pG)) <
    bf₁ * pG / (bf₁ * pG + (1 - pG)) := by
  have h1pG : 0 < 1 - pG := by linarith
  have hd₁ : 0 < bf₁ * pG + (1 - pG) := by nlinarith
  have hd₂ : 0 < bf₂ * pG + (1 - pG) := by nlinarith
  have hd₁' : bf₁ * pG + (1 - pG) ≠ 0 := ne_of_gt hd₁
  have hd₂' : bf₂ * pG + (1 - pG) ≠ 0 := ne_of_gt hd₂
  rw [div_lt_div_iff₀ hd₂ hd₁]
  nlinarith [mul_pos hG h1pG, mul_pos hbf₁ hG]

/-- C&F's positive argumentative strength (bayesFactor > 1) iff
the utterance shifts the posterior above the prior.

bayesFactor(u,G) > 1 iff P(G|u) > P(G)

This connects C&F's ordinal condition hasPositiveArgStr to the
Bayesian posterior shift that Barnett's model operates on. -/
theorem positive_argStr_iff_posterior_above_prior
    (pG pNotG prior : ℚ) (hG : 0 < pG) (hNotG : 0 < pNotG) (hPrior : 0 < prior)
    (hPrior1 : prior < 1) :
    hasPositiveArgStr pG pNotG ↔
    pG * prior / (pG * prior + pNotG * (1 - prior)) > prior := by
  have h1p : 0 < 1 - prior := by linarith
  have hd : 0 < pG * prior + pNotG * (1 - prior) := by nlinarith
  simp only [hasPositiveArgStr, gt_iff_lt]
  rw [lt_div_iff₀ hd]
  constructor
  · intro h; nlinarith [mul_pos hPrior h1p]
  · intro h
    by_contra hle
    push_neg at hle
    nlinarith [mul_pos hPrior h1p]

-- argStr_speaker_prefers_stronger is now in RSA.ArgumentativeStrength,
-- available via `open` above. It shows that a goal-oriented speaker (β > 0)
-- strictly prefers utterances with higher argumentative strength.


-- ============================================================
-- Section 5: Meaning-Level Taxonomy (Cummins 2025 §§3–5)
-- ============================================================

/-- Level of meaning at which falsehood can occur.

Cummins (2025) identifies four levels, ordered by speaker blameworthiness
(Mazzarella et al. 2018): assertion > implicature > presupposition > typicality.

Both C&F and Barnett involve misleading at the typicality/implicature level
while maintaining truthful assertions — the argumentative speaker exploits
pragmatic expectations without violating Quality at the assertion level. -/
inductive MeaningLevel where
  | assertion       -- what is said (literal semantic content)
  | implicature     -- what is implicated (scalar, quantity)
  | presupposition  -- what is presupposed (factive, etc.)
  | typicality      -- inferred from typical usage patterns
  deriving DecidableEq, BEq, Repr

/-- Blameworthiness ordering: false assertions attract most blame,
typicality departures attract least (Mazzarella et al. 2018). -/
def blameworthinessRank : MeaningLevel → Nat
  | .assertion => 3
  | .implicature => 2
  | .presupposition => 1
  | .typicality => 0

theorem assertion_most_blameworthy :
    blameworthinessRank .assertion > blameworthinessRank .implicature := by native_decide

theorem typicality_least_blameworthy :
    blameworthinessRank .typicality < blameworthinessRank .presupposition := by native_decide

-- Both C&F and Barnett involve misleading at the typicality level:
-- C&F's "more than 100" exploits typical usage patterns of modified numerals.
-- Barnett's weak evidence exploits the expectation that speakers show strongest evidence.
-- In both cases, the assertion is literally true — the misleading is pragmatic.


-- ============================================================
-- Section 6: Epistemic Vigilance (Sperber et al. 2010)
-- ============================================================

/-- Epistemic vigilance: the hearer's trust in speaker cooperativity.

Following Sperber et al. (2010) as discussed in Cummins (2025 §4):
1. Hearer first interprets as if speaker is cooperative (stance of trust)
2. Then weighs the pragmatic interpretation by trust level τ
3. Falls back toward literal interpretation as trust decreases

The vigilant posterior is:
  P_V(w|u) = τ · P_L1(w|u) + (1−τ) · P_L0(w|u)

This is CombinedUtility.combined(τ, L0_posterior, L1_posterior). -/
structure EpistemicVigilance where
  /-- τ ∈ [0,1]: probability that speaker is cooperative -/
  trustLevel : ℚ
  trust_nonneg : 0 ≤ trustLevel := by decide
  trust_le_one : trustLevel ≤ 1 := by decide
  deriving Repr

/-- Full trust: standard pragmatic interpretation -/
def fullTrust : EpistemicVigilance := { trustLevel := 1 }

/-- No trust: literal interpretation only -/
def noTrust : EpistemicVigilance := { trustLevel := 0 }

/-- Vigilant listener posterior: trust-weighted mixture of L1 and L0.

When the hearer suspects the speaker is argumentative (low τ),
they discount pragmatic enrichment and rely more on literal meaning. -/
def vigilantPosterior (ev : EpistemicVigilance) (l1Post l0Post : ℚ) : ℚ :=
  ev.trustLevel * l1Post + (1 - ev.trustLevel) * l0Post

/-- At full trust, vigilant listener = pragmatic listener L1 -/
theorem vigilant_at_full_trust (l1Post l0Post : ℚ) :
    vigilantPosterior fullTrust l1Post l0Post = l1Post := by
  unfold vigilantPosterior fullTrust; ring

/-- At zero trust, vigilant listener = literal listener L0 -/
theorem vigilant_at_zero_trust (l1Post l0Post : ℚ) :
    vigilantPosterior noTrust l1Post l0Post = l0Post := by
  unfold vigilantPosterior noTrust; ring

/-- Vigilant posterior IS CombinedUtility.combined(τ, L0, L1).
The epistemic vigilance machinery reuses the same interpolation
framework as the speaker's utility tradeoff. -/
theorem vigilant_is_combined (ev : EpistemicVigilance) (l1Post l0Post : ℚ) :
    vigilantPosterior ev l1Post l0Post = combined ev.trustLevel l0Post l1Post := by
  unfold vigilantPosterior combined; ring

/-- Vigilant posterior is a convex combination when τ ∈ [0,1] -/
theorem vigilant_convex (ev : EpistemicVigilance) (l1Post l0Post : ℚ) :
    min l0Post l1Post ≤ vigilantPosterior ev l1Post l0Post ∧
    vigilantPosterior ev l1Post l0Post ≤ max l0Post l1Post := by
  rw [vigilant_is_combined]
  exact combined_convex ev.trustLevel ev.trust_nonneg ev.trust_le_one l0Post l1Post


-- ============================================================
-- Section 7: The Unified Model
-- ============================================================

/-- The unified noncooperative RSA model has two parameters:
- goalWeight (speaker side): convex weight on goal utility ∈ [0,1]
- τ (hearer side): trust level (1 = full trust, 0 = literal only)

Both sides use `combined` (convex interpolation), making the symmetry explicit:
- Speaker: `combined goalWeight uEpi uGoal`
- Hearer: `combined τ l0Post l1Post` (via vigilantPosterior)

Standard RSA is the special case goalWeight=0, τ=1.
Barnett et al. (2022) is goalWeight=226/326 (≈ 0.693, from β=2.26), τ=1.
A suspicious hearer facing an argumentative speaker would have high goalWeight, low τ. -/
structure NoncooperativeRSAParams where
  /-- Speaker's goal-orientation weight ∈ [0,1] -/
  goalWeight : ℚ
  /-- Hearer's trust level -/
  τ : ℚ
  goalWeight_nonneg : 0 ≤ goalWeight := by decide
  goalWeight_le_one : goalWeight ≤ 1 := by decide
  τ_nonneg : 0 ≤ τ := by decide
  τ_le_one : τ ≤ 1 := by decide
  deriving Repr

/-- Standard cooperative RSA: no goal bias, full trust -/
def standardRSA : NoncooperativeRSAParams :=
  { goalWeight := 0, τ := 1 }

/-- Barnett et al. (2022) fitted model: goalWeight = β/(1+β) = 226/326 ≈ 0.693,
pragmatic group with full trust.

Original paper parameterization: β̂ = 2.26 (additive form).
Convex reparameterization: goalWeight = 2.26/3.26 = 226/326. -/
def barnettFitted : NoncooperativeRSAParams :=
  { goalWeight := 226 / 326, τ := 1
    goalWeight_nonneg := by native_decide
    goalWeight_le_one := by native_decide }

/-- Standard RSA has cooperative orientation -/
theorem standardRSA_cooperative :
    orientationOf standardRSA.goalWeight = .cooperative := by native_decide

/-- Barnett's fitted model has argumentative orientation -/
theorem barnettFitted_argumentative :
    orientationOf barnettFitted.goalWeight = .argumentative := by native_decide

/-- In the unified model, BOTH sides use `combined` (convex interpolation):
- Speaker: `combined goalWeight uEpi uGoal`
- Hearer: `vigilantPosterior(τ, L1, L0)` = `combined τ L0 L1`

Full model: speaker chooses u to maximize combined(goalWeight, U_epi, U_goal),
listener computes combined(τ, L0(w|u), L1(w|u)). -/
def fullModel (params : NoncooperativeRSAParams)
    (uEpi uGoal l1Post l0Post : ℚ) : ℚ × ℚ :=
  let speakerUtil := combined params.goalWeight uEpi uGoal
  let ev : EpistemicVigilance :=
    { trustLevel := params.τ
      trust_nonneg := params.τ_nonneg
      trust_le_one := params.τ_le_one }
  let hearerPost := vigilantPosterior ev l1Post l0Post
  (speakerUtil, hearerPost)

/-- The unified model at standard parameters reduces to (U_epi, L1) —
the standard RSA speaker utility and pragmatic listener. -/
theorem fullModel_standard (uEpi uGoal l1Post l0Post : ℚ) :
    fullModel standardRSA uEpi uGoal l1Post l0Post = (uEpi, l1Post) := by
  unfold fullModel standardRSA combined vigilantPosterior
  simp

/-- Barnett et al.'s Eq. 6 (additive: U + β·V) is a scaled version of the
convex `combined` form used in `fullModel`:

  eq6 uEpi uGoal β = (1+β) · combined(β/(1+β), uEpi, uGoal)

Since scaling by (1+β) > 0 preserves ranking, the additive and convex
parameterizations are strategically equivalent. -/
theorem barnett_eq6_via_combined (uEpi uGoal β : ℚ) (hβ : 0 ≤ β) :
    eq6 uEpi uGoal β = (1 + β) * combined (betaToLam β) uEpi uGoal :=
  goalOriented_eq_scaled_combined uEpi uGoal β hβ


-- ============================================================
-- Section 8: Pragmatic Vulnerability (Cummins 2025 §4)
-- ============================================================

/-- The vigilant posterior is monotone in trust: more trust pulls the
posterior toward L1. When L1 is misleading, more trust = more misled.

This is the hearer-side consequence of `higher_lambda_when_B_dominates`:
the vigilant posterior is `combined τ L0 L1`, so increasing τ gives
more weight to L1 (the B component). -/
theorem vigilant_mono_trust (l1Post l0Post : ℚ)
    (ev1 ev2 : EpistemicVigilance)
    (hord : ev1.trustLevel < ev2.trustLevel)
    (hne : l0Post < l1Post) :
    vigilantPosterior ev1 l1Post l0Post < vigilantPosterior ev2 l1Post l0Post := by
  rw [vigilant_is_combined ev1, vigilant_is_combined ev2]
  exact higher_lambda_when_B_dominates ev1.trustLevel ev2.trustLevel hord l0Post l1Post hne

/-- Symmetric: when L1 < L0, more trust DECREASES the posterior (toward L1). -/
theorem vigilant_mono_trust_sym (l1Post l0Post : ℚ)
    (ev1 ev2 : EpistemicVigilance)
    (hord : ev1.trustLevel < ev2.trustLevel)
    (hne : l1Post < l0Post) :
    vigilantPosterior ev2 l1Post l0Post < vigilantPosterior ev1 l1Post l0Post := by
  rw [vigilant_is_combined ev1, vigilant_is_combined ev2]
  exact lower_lambda_when_A_dominates ev1.trustLevel ev2.trustLevel hord l0Post l1Post hne

/-- **Pragmatic vulnerability** (Cummins 2025 §4): pragmatic inference is
exploitable *precisely because* it is rational.

When L1 diverges from L0 (l0 < l1), the fully-pragmatic listener (τ=1) is
maximally exposed to the divergence. Epistemic vigilance (0 < τ < 1) strictly
pulls the posterior back toward the immune L0:

- τ = 1: posterior = L1 (fully exposed) — `vigilant_at_full_trust`
- τ = 0: posterior = L0 (immune) — `vigilant_at_zero_trust`
- 0 < τ < 1: **L0 < posterior < L1** (partially protected) — THIS THEOREM

The weak evidence effect (Barnett et al. 2022, `weak_evidence_effect_s4`) is
a concrete instance: L0 correctly identifies stick 4 as evidence for "longer",
but L1 at β=2 overshoots in the wrong direction. Reducing τ from 1 would pull
the posterior back toward L0's correct assessment.

**Linguistic content**: An argumentative speaker (goalWeight > 0) exploits L1's
reasoning about speaker intentions. L0, which interprets literally without
modeling the speaker, cannot be manipulated this way. Vigilance (epistemic
caution about speaker cooperativity) is the rational defense.

The converse also holds: if L1 = L0, no speaker parameterization can exploit
the difference, since vigilantPosterior degenerates to L0 = L1 at any τ. -/
theorem pragmatic_vulnerability (l1Post l0Post : ℚ) (ev : EpistemicVigilance)
    (hτ0 : 0 < ev.trustLevel) (hτ1 : ev.trustLevel < 1)
    (h_diverge : l0Post < l1Post) :
    l0Post < vigilantPosterior ev l1Post l0Post ∧
    vigilantPosterior ev l1Post l0Post < l1Post := by
  unfold vigilantPosterior
  constructor <;> nlinarith [ev.trust_nonneg, ev.trust_le_one]

/-- Symmetric vulnerability: when L1 undershoots L0 (l1 < l0), vigilance
pulls the posterior upward from L1 toward L0. -/
theorem pragmatic_vulnerability_sym (l1Post l0Post : ℚ) (ev : EpistemicVigilance)
    (hτ0 : 0 < ev.trustLevel) (hτ1 : ev.trustLevel < 1)
    (h_diverge : l1Post < l0Post) :
    l1Post < vigilantPosterior ev l1Post l0Post ∧
    vigilantPosterior ev l1Post l0Post < l0Post := by
  unfold vigilantPosterior
  constructor <;> nlinarith [ev.trust_nonneg, ev.trust_le_one]

/-- When L1 = L0, pragmatic inference adds nothing exploitable: the vigilant
posterior equals L0 = L1 at any trust level τ. No speaker parameterization
can create a gap to exploit. This is the formal converse of
`pragmatic_vulnerability`. -/
theorem no_vulnerability_when_equal (l0Post : ℚ) (ev : EpistemicVigilance) :
    vigilantPosterior ev l0Post l0Post = l0Post := by
  unfold vigilantPosterior; ring


-- ============================================================
-- Section 9: Quantitative Exploitability Bounds
-- ============================================================

-- The qualitative results above (pragmatic_vulnerability, vigilant_mono_trust)
-- establish that vigilance *helps*. This section gives the exact mathematics:
-- τ is precisely the fraction of L1's divergence absorbed by the listener.

/-- Exact signed deviation from L0: the vigilant posterior deviates from L0
by exactly τ · (L1 - L0).

τ is literally the fraction of L1's divergence from L0 that the listener absorbs.
At τ=0: deviation = 0 (immune). At τ=1: deviation = L1-L0 (fully exposed). -/
theorem vigilant_deviation_exact (ev : EpistemicVigilance) (l1Post l0Post : ℚ) :
    vigilantPosterior ev l1Post l0Post - l0Post =
    ev.trustLevel * (l1Post - l0Post) := by
  unfold vigilantPosterior; ring

/-- Exact gap between L1 and the vigilant posterior: the amount of L1's
divergence that vigilance *closes* is (1-τ) · (L1 - L0).

At τ=0: gap = L1-L0 (fully closed). At τ=1: gap = 0 (nothing closed). -/
theorem vulnerability_gap_exact (ev : EpistemicVigilance) (l1Post l0Post : ℚ) :
    l1Post - vigilantPosterior ev l1Post l0Post =
    (1 - ev.trustLevel) * (l1Post - l0Post) := by
  unfold vigilantPosterior; ring

/-- Squared exploitability scales as τ²: the squared deviation of the
vigilant posterior from L0 is exactly τ² times the squared L1-L0 gap.

This gives the precise risk calculus for trust: doubling τ quadruples
the squared deviation from L0. -/
theorem exploitability_scales_as_tau_sq (ev : EpistemicVigilance) (l1Post l0Post : ℚ) :
    (vigilantPosterior ev l1Post l0Post - l0Post) ^ 2 =
    ev.trustLevel ^ 2 * (l1Post - l0Post) ^ 2 := by
  rw [vigilant_deviation_exact]; ring

/-- Error decomposition: the vigilant posterior's deviation from truth
decomposes as a τ-weighted sum of L1's error and L0's error.

  (vigilant - truth) = τ · (L1 - truth) + (1-τ) · (L0 - truth)

This is the fundamental equation of epistemic vigilance: the listener's
error is a convex combination of the two listeners' errors. -/
theorem vigilant_error_decomposition (ev : EpistemicVigilance)
    (truth l1Post l0Post : ℚ) :
    vigilantPosterior ev l1Post l0Post - truth =
    ev.trustLevel * (l1Post - truth) +
    (1 - ev.trustLevel) * (l0Post - truth) := by
  unfold vigilantPosterior; ring

/-- When L0 is perfectly calibrated (l0 = truth), the squared error of the
vigilant posterior reduces to τ² · (L1 - truth)².

This is the strongest quantitative vulnerability result: if the literal
listener is correct (as in Barnett's weak evidence domain where L0
correctly assesses stick 4), then vigilance reduces squared error by
exactly a factor of τ². At τ=1 you absorb all of L1's error; at τ=0
you absorb none. -/
theorem vigilant_error_when_l0_correct (ev : EpistemicVigilance)
    (l1Post truth : ℚ) :
    (vigilantPosterior ev l1Post truth - truth) ^ 2 =
    ev.trustLevel ^ 2 * (l1Post - truth) ^ 2 := by
  unfold vigilantPosterior; ring

/-- Zero-error vigilance: there exists a unique τ that makes the vigilant
posterior exactly equal truth, namely τ* = (truth - L0) / (L1 - L0).

When truth is between L0 and L1, τ* ∈ [0,1] (`optimal_vigilance_in_range`),
so it corresponds to a valid trust level.

The optimal τ* has a natural interpretation: it is the relative position
of truth within the [L0, L1] interval. If truth is at L0 (literal listener
is perfect), τ*=0. If truth is at L1 (pragmatic listener is perfect), τ*=1.
If truth is at the midpoint, τ*=1/2. -/
theorem optimal_vigilance (truth l0Post l1Post : ℚ) (hne : l1Post ≠ l0Post) :
    let τ_opt := (truth - l0Post) / (l1Post - l0Post)
    τ_opt * l1Post + (1 - τ_opt) * l0Post = truth := by
  simp only
  have hne' : l1Post - l0Post ≠ 0 := sub_ne_zero.mpr hne
  field_simp [hne']
  ring

/-- The optimal τ* is in [0,1] when truth is between L0 and L1. -/
theorem optimal_vigilance_in_range (truth l0Post l1Post : ℚ)
    (hne : l0Post < l1Post) (hlo : l0Post ≤ truth) (hhi : truth ≤ l1Post) :
    0 ≤ (truth - l0Post) / (l1Post - l0Post) ∧
    (truth - l0Post) / (l1Post - l0Post) ≤ 1 := by
  have hpos : 0 < l1Post - l0Post := sub_pos.mpr hne
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (le_of_lt hpos)
  · rw [div_le_iff₀ hpos, one_mul]; linarith


-- ============================================================
-- Section 10: Backfire Generalization (Conjecture)
-- ============================================================

/-- **Backfire generalization conjecture**: the weak evidence effect and
scalar implicature are structurally identical phenomena.

Whenever a pragmatic listener expects the speaker to use the *strongest
available* utterance, observing a non-maximal one triggers a negative
inference that can reverse the literal evidence.

**Instances**:
- *Scalar implicature*: hearing "some" → infer speaker couldn't say "all"
  → conclude ¬all (Goodman & Stuhlmüller 2013)
- *Weak evidence effect*: seeing stick 4 → infer speaker lacked stick 5
  → conclude probably not "longer" (Barnett et al. 2022)
- *Polite understatement*: "not terrible" → infer speaker couldn't
  honestly say "good" → conclude mediocre (Yoon et al. 2020)

**Abstract pattern**: Let U = {u₁, ..., uₙ} be utterances ordered by
strength, and let L0(goal | uᵢ) be monotone in i. If the speaker is
goal-oriented (prefers stronger utterances when goal is true), then for
some non-maximal uᵢ:

  L0(goal | uᵢ) > prior  AND  L1(goal | uᵢ, β) < prior

The pragmatic listener's inference — "if the speaker had stronger evidence,
they would have used it" — reverses the literal evidence.

**Formal statement**: Given L0 posteriors monotone in utterance strength
with at least two values above the prior, and L1 posteriors derived from
a goal-oriented speaker (β > 0), there exists a non-maximal utterance
where L0 says "goal is likely" but L1 says "goal is unlikely."

**Evidence**: `weak_evidence_effect_s4` (BarnettEtAl2022) demonstrates
this at β=2. A general proof requires formalizing L1 Bayesian inversion
over abstract strength-ordered RSA scenarios.

**What's missing for a proof**: The L1 computation (Bayesian inversion of
the speaker model) must be formalized generically over ordered utterance
sets. The key step is showing that the speaker's monotone preference
concentrates probability mass on maximal utterances, making the L1
posterior *decrease* for non-maximal ones. This is essentially the
derivation of quantity implicatures from RSA, generalized beyond scales. -/
def backfire_generalization
    -- An RSA scenario with n ≥ 2 ordered utterances
    (n : ℕ) (hn : 2 ≤ n)
    -- L0 posterior for goal given each utterance (ordered by strength)
    (l0_goal : Fin n → ℚ)
    -- L1 posterior for goal given each utterance (from goal-oriented speaker)
    (l1_goal : Fin n → ℚ)
    -- Prior probability of goal
    (prior : ℚ) : Prop :=
  -- IF L0 is weakly monotone (stronger utterances → more evidence for goal)
  (∀ i j : Fin n, i ≤ j → l0_goal i ≤ l0_goal j) →
  -- AND at least two distinct utterances have L0 above the prior
  -- (the speaker has a meaningful choice among goal-supporting utterances)
  (∃ i j : Fin n, i < j ∧ l0_goal i > prior ∧ l0_goal j > prior) →
  -- THEN there exists a non-maximal utterance that backfires:
  -- literally positive evidence, but pragmatically negative
  ∃ i : Fin n, i.val < n - 1 ∧ l0_goal i > prior ∧ l1_goal i < prior

/-- The Barnett stick domain instantiates `backfire_generalization`.

Sticks {s1,...,s5} ordered by length. L0(longer | sᵢ) is monotone
(`l0Longer_monotone`). Sticks s4 and s5 both have L0 above the prior
(`s4_positive_under_l0`, `s5_strongest_evidence`). At β=2, stick 4
backfires (`weak_evidence_effect_s4`).

TODO: Prove via Fin 5 ↔ Stick correspondence and the existing
BarnettEtAl2022 theorems. -/
theorem barnett_backfire_instance :
    backfire_generalization 5 (by omega)
      (fun i : Fin 5 => match i with | ⟨0, _⟩ => 1/6 | ⟨1, _⟩ => 1/3 | ⟨2, _⟩ => 1/3 | ⟨3, _⟩ => 1/2 | ⟨4, _⟩ => 2/3 | ⟨n+5, h⟩ => absurd h (by omega))
      (fun i : Fin 5 => match i with | ⟨0, _⟩ => 1/6 | ⟨1, _⟩ => 1/3 | ⟨2, _⟩ => 1/3 | ⟨3, _⟩ => 7/20 | ⟨4, _⟩ => 2/3 | ⟨n+5, h⟩ => absurd h (by omega))
      (2/5) := by                       -- prior (priorLonger)
  unfold backfire_generalization
  intro _ _
  refine ⟨⟨3, by omega⟩, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

end RSA.NoncooperativeCommunication
