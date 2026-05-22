import Linglib.Core.Probability.Posterior
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{spinoso-di-piano-etal-2025} — (RSA)² on mathlib `PMF`
@cite{spinoso-di-piano-etal-2025} @cite{kao-goodman-2015}

(RSA)²: A Rhetorical-Strategy-Aware Rational Speech Act Framework for
Figurative Language Understanding (ACL 2025).

## What this file is

A **headline-focused** PMF formalisation of the (RSA)² model's central
architectural claim. The paper's deepest result (worth a Lean theorem):

> For non-midpoint utterances, the entire (RSA)² model's behavior
> reduces to a single prior comparison.

We formalise this as `irony_iff_prior_favors_antonym`:

  L1(u)(opposite u) > L1(u)(literal u)  ↔  wp(opposite u) > wp(literal u)

This explains WHY (RSA)² agrees with @cite{kao-goodman-2015} (affect-aware
RSA) on cross-context predictions: both reduce to the world-prior
asymmetry, but (RSA)² achieves this WITHOUT modeling affect dimensions
or QUD projection. Affect is unnecessary for irony.

## (RSA)² in three lines

The paper's key generalisation: replace RSA's literal indicator
`𝟙_{m ∈ ⟦u⟧}` with a **rhetorical strategy function** `f_r(c, m, u)`
parameterised by strategy `r ∈ R`:

* `L0(m | c, u, r) ∝ f_r(c, m, u) · P(m | c)` (Eq. 4)
* `S1(u | c, m, r) ∝ L0(m | c, u, r)^α · P(u | c)` (Eq. 5)
* `L1(m | c, u) = Σ_r L1(m | c, u, r) · P(r | c, u)` (Eq. 7 — strategy
  marginalisation)

In our binary irony fragment, R = {literal, ironic}; `f_literal`
is the standard indicator and `f_ironic(u, w) = 𝟙_{w = opposite(meaning(u))}`.

## Why the binary-strategy fragment reduces to a prior comparison

For non-midpoint `u` (where `u.toWeather ≠ opposite u.toWeather`):

* `mixedS1 u.toWeather u = 1/2` — only the literal strategy contributes.
* `mixedS1 (opposite u.toWeather) u = 1/2` — only the ironic strategy
  contributes.
* `mixedS1 w u = 0` everywhere else.

So `posterior mixedS1 worldPrior u` puts all its mass on those two
worlds, with relative ratio determined by `worldPrior` — exactly the
content of the headline theorem.

## Connection to QUD-RSA (Appendix A.3)

The paper proves QUD-RSA (`RSA.QUD.proj` in our substrate, used by Kao
metaphor / hyperbole / irony) is a strict special case of (RSA)²
(Lemma 1: every QUD-RSA instance arises from a specific `f_r`; Lemma 2:
not all (RSA)² instances arise from any QUD-RSA instance). This file
formalises the (RSA)² side; `RSA/QUD.lean` formalises the QUD-RSA side.

## Scope

The 10 numerical predictions from the paper (`ironic_reading`,
`literal_reading`, `infer_ironic`, ...) are corollaries of the headline
theorem at specific `worldPrior` values. They are paper-finding content
(empirical-fit) — out of scope for this architectural migration.
-/

set_option autoImplicit false

namespace SpinosoDiPiano2025.PMF

open scoped ENNReal

/-! ## §0. Domain types -/

/-- Weather scale: 5-point ordered set from terrible to amazing.
Mirrors @cite{kao-goodman-2015}'s weather scale. -/
inductive Weather where
  | terrible | bad | ok | good | amazing
  deriving DecidableEq, Repr, Fintype

/-- Utterance type: weather descriptions used as speech acts. Structurally
isomorphic to `Weather` but distinct for type discipline (utterance space
vs meaning space). -/
inductive Utterance where
  | terrible | bad | ok | good | amazing
  deriving DecidableEq, Repr, Fintype

/-- The two rhetorical strategies in the paper's binary fragment. -/
inductive Strategy where
  | literal | ironic
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Weather := ⟨.amazing⟩
instance : Nonempty Utterance := ⟨.amazing⟩
instance : Nonempty Strategy := ⟨.literal⟩

/-- The Utterance ↔ Weather bijection: each utterance has a unique literal
weather meaning. -/
def Utterance.toWeather : Utterance → Weather
  | .terrible => .terrible
  | .bad      => .bad
  | .ok       => .ok
  | .good     => .good
  | .amazing  => .amazing

/-- Inverse of `Utterance.toWeather`. -/
def Utterance.fromWeather : Weather → Utterance
  | .terrible => .terrible
  | .bad      => .bad
  | .ok       => .ok
  | .good     => .good
  | .amazing  => .amazing

@[simp] theorem Utterance.toWeather_fromWeather (w : Weather) :
    (Utterance.fromWeather w).toWeather = w := by cases w <;> rfl

@[simp] theorem Utterance.fromWeather_toWeather (u : Utterance) :
    Utterance.fromWeather u.toWeather = u := by cases u <;> rfl

/-! ## §1. Evaluative antonym (involutive) -/

/-- The evaluative antonym on the weather scale: flip endpoints, fix
the midpoint. This IS the ironic interpretation function: "amazing"
ironically conveys "terrible" because they are evaluative antonyms. -/
def opposite : Weather → Weather
  | .terrible => .amazing
  | .bad      => .good
  | .ok       => .ok
  | .good     => .bad
  | .amazing  => .terrible

theorem opposite_involutive (w : Weather) : opposite (opposite w) = w := by
  cases w <;> rfl

/-! ## §2. Per-strategy speakers (deterministic kernels)

In the binary-strategy fragment with indicator meanings, each strategy
maps a world to a unique utterance:

* literal: pick the utterance whose literal meaning is `w`
* ironic: pick the utterance whose literal meaning is `opposite w`

Because `Utterance ≅ Weather` (via `toWeather`), these are well-defined
total functions, and the per-strategy speaker collapses to `PMF.pure`. -/

/-- The literal speaker: at world `w`, deterministically emit the
utterance whose literal meaning is `w`. -/
noncomputable def literalSpeaker (w : Weather) : PMF Utterance :=
  PMF.pure (Utterance.fromWeather w)

/-- The ironic speaker: at world `w`, deterministically emit the
utterance whose ironic meaning is `w` (i.e., whose literal meaning is
`opposite w`). -/
noncomputable def ironicSpeaker (w : Weather) : PMF Utterance :=
  PMF.pure (Utterance.fromWeather (opposite w))

/-- The per-strategy speaker dispatch. -/
noncomputable def speakerByStrategy : Strategy → Weather → PMF Utterance
  | .literal => literalSpeaker
  | .ironic  => ironicSpeaker

/-! ## §3. Strategy-marginalised speaker (Eq. 7) -/

/-- Uniform strategy prior — paper's default for the binary fragment. -/
noncomputable def strategyPrior : PMF Strategy := PMF.uniformOfFintype Strategy

theorem strategyPrior_apply (s : Strategy) :
    strategyPrior s = (Fintype.card Strategy : ℝ≥0∞)⁻¹ := by
  rw [strategyPrior, PMF.uniformOfFintype_apply]

theorem strategyPrior_eq_half (s : Strategy) : strategyPrior s = 1 / 2 := by
  rw [strategyPrior_apply]
  show ((Fintype.card Strategy : ℕ) : ℝ≥0∞)⁻¹ = 1 / 2
  rw [show Fintype.card Strategy = 2 from rfl]
  rw [show ((2 : ℕ) : ℝ≥0∞) = 2 from by norm_cast]
  rw [one_div]

/-- The strategy-marginalised speaker (Eq. 7's mixture): at world `w`,
sample a strategy then emit an utterance. This is the L1 likelihood. -/
noncomputable def mixedS1 (w : Weather) : PMF Utterance :=
  strategyPrior.bind (fun s => speakerByStrategy s w)

/-! ## §4. Computing `mixedS1` at the matching worlds

The two architectural lemmas the headline theorem hinges on. -/

/-- `mixedS1` at `u.toWeather` (the literal-matching world) for `u`:
only the literal strategy contributes (the ironic strategy emits a
DIFFERENT utterance there, namely `Utterance.fromWeather (opposite u.toWeather)`,
which differs from `u` because the world is non-midpoint). -/
theorem mixedS1_at_literal_world (u : Utterance)
    (hne : u.toWeather ≠ opposite u.toWeather) :
    mixedS1 u.toWeather u = 1 / 2 := by
  show (strategyPrior.bind _) u = _
  rw [PMF.bind_apply, tsum_fintype]
  show ∑ s : Strategy,
      strategyPrior s * speakerByStrategy s u.toWeather u = 1 / 2
  rw [show (Finset.univ : Finset Strategy) = {.literal, .ironic} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]
  -- (1/2) * literalSpeaker u.toWeather u + (1/2) * ironicSpeaker u.toWeather u
  -- = (1/2) * 1 + (1/2) * 0 = 1/2
  rw [strategyPrior_eq_half, strategyPrior_eq_half]
  -- speakerByStrategy .literal u.toWeather u = pure (Utterance.fromWeather u.toWeather) u
  --   = pure u u = 1
  show (1 / 2) * literalSpeaker u.toWeather u
       + (1 / 2) * ironicSpeaker u.toWeather u = 1 / 2
  rw [show literalSpeaker u.toWeather u = 1 from by
        unfold literalSpeaker
        rw [Utterance.fromWeather_toWeather, PMF.pure_apply_self]]
  -- ironicSpeaker u.toWeather u = pure (Utterance.fromWeather (opposite u.toWeather)) u
  --   = 0  (since u ≠ Utterance.fromWeather (opposite u.toWeather) by non-midpoint)
  rw [show ironicSpeaker u.toWeather u = 0 from by
        unfold ironicSpeaker
        exact PMF.pure_apply_of_ne _ _ (fun h => hne <| by
          have : u.toWeather = (Utterance.fromWeather (opposite u.toWeather)).toWeather :=
            congrArg Utterance.toWeather h
          rw [Utterance.toWeather_fromWeather] at this
          exact this)]
  rw [mul_one, mul_zero, add_zero]

/-- `mixedS1` at `opposite u.toWeather` (the ironic-matching world) for `u`:
only the ironic strategy contributes. Symmetric to
`mixedS1_at_literal_world`, hinging on `opposite_involutive`. -/
theorem mixedS1_at_ironic_world (u : Utterance)
    (hne : u.toWeather ≠ opposite u.toWeather) :
    mixedS1 (opposite u.toWeather) u = 1 / 2 := by
  show (strategyPrior.bind _) u = _
  rw [PMF.bind_apply, tsum_fintype]
  show ∑ s : Strategy,
      strategyPrior s * speakerByStrategy s (opposite u.toWeather) u = 1 / 2
  rw [show (Finset.univ : Finset Strategy) = {.literal, .ironic} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [strategyPrior_eq_half, strategyPrior_eq_half]
  show (1 / 2) * literalSpeaker (opposite u.toWeather) u
       + (1 / 2) * ironicSpeaker (opposite u.toWeather) u = 1 / 2
  -- literalSpeaker (opposite u.toWeather) u = pure (Utterance.fromWeather (opposite u.toWeather)) u
  --   = 0  (since u ≠ Utterance.fromWeather (opposite u.toWeather) by non-midpoint)
  rw [show literalSpeaker (opposite u.toWeather) u = 0 from by
        unfold literalSpeaker
        exact PMF.pure_apply_of_ne _ _ (fun h => hne <| by
          have : u.toWeather = (Utterance.fromWeather (opposite u.toWeather)).toWeather :=
            congrArg Utterance.toWeather h
          rw [Utterance.toWeather_fromWeather] at this
          exact this)]
  -- ironicSpeaker (opposite u.toWeather) u
  --   = pure (Utterance.fromWeather (opposite (opposite u.toWeather))) u
  --   = pure (Utterance.fromWeather u.toWeather) u  [opposite_involutive]
  --   = pure u u = 1
  rw [show ironicSpeaker (opposite u.toWeather) u = 1 from by
        unfold ironicSpeaker
        rw [opposite_involutive, Utterance.fromWeather_toWeather, PMF.pure_apply_self]]
  rw [mul_zero, mul_one, zero_add]

/-! ## §5. The L1 posterior -/

/-- Pragmatic listener L1: posterior over worlds given an utterance. -/
noncomputable def L1 (worldPrior : PMF Weather) (u : Utterance)
    (h_marg : PMF.marginal mixedS1 worldPrior u ≠ 0) : PMF Weather :=
  PMF.posterior mixedS1 worldPrior u h_marg

/-! ## §6. Architectural payoff — irony reduces to prior comparison -/

/-- **Headline theorem (Spinoso–Di Piano et al. 2025)**: For any non-midpoint
utterance `u`, the L1 posterior orders the two candidate weather states
strictly by the world prior at those states.

This is the paper's core architectural insight, formalised: the entire
(RSA)² model behavior — for non-midpoint utterances — reduces to a
single prior comparison. Affect dimensions and QUD projection are
unnecessary for irony; context (the world prior) alone determines
whether an utterance is interpreted ironically.

The shared `1/2` factor (the strategy-prior weight on each strategy)
cancels via `posterior_lt_iff_score_lt` + `mul_lt_mul_iff_right`. -/
theorem irony_iff_prior_favors_antonym
    (worldPrior : PMF Weather) (u : Utterance)
    (hne : u.toWeather ≠ opposite u.toWeather)
    (h_marg : PMF.marginal mixedS1 worldPrior u ≠ 0) :
    L1 worldPrior u h_marg u.toWeather < L1 worldPrior u h_marg (opposite u.toWeather) ↔
      worldPrior u.toWeather < worldPrior (opposite u.toWeather) := by
  unfold L1
  rw [PMF.posterior_lt_iff_score_lt]
  rw [mixedS1_at_literal_world u hne, mixedS1_at_ironic_world u hne]
  -- Goal: worldPrior u.toWeather * (1/2) < worldPrior (opposite u.toWeather) * (1/2) ↔ ...
  -- mathlib's `mul_lt_mul_iff_left` cancels the RIGHT factor (despite the name).
  have h1 : (1 / 2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2 : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  exact ENNReal.mul_lt_mul_iff_left h1 h2

end SpinosoDiPiano2025.PMF
