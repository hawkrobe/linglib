import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# @cite{cohn-gordon-goodman-potts-2019} — Incremental Iterated Response Model

Cohn-Gordon, R., Goodman, N. D., & Potts, C. (2019). An Incremental Iterated
Response Model of Pragmatics. *Proceedings of the Society for Computation in
Linguistics (SCiL)* 2, 81–90.

## The Model

The incremental RSA model extends the standard RSA framework to word-by-word
production. The speaker produces referring expressions incrementally, choosing
each word to maximize the listener's posterior probability for the target:

  S1^inc(wₖ | [w₁,...,wₖ₋₁], r) ∝ L0(r | w₁,...,wₖ)^α

The full utterance probability factors via the chain rule:

  S1(w₁,...,wₙ | r) = ∏ₖ S1^inc(wₖ | [w₁,...,wₖ₋₁], r)

L0 uses continuous/noisy semantics (@cite{degen-etal-2020}) where each word
applies with reliability v (correct application) or 1 − v (noise).

**Key property**: With strictly positive noisy semantics, L0 is
order-independent — the posterior after hearing all words is the same
regardless of production order (commutativity of ℝ multiplication). Therefore
the trajectory score comparison reduces to first-word informativity.

## Formalization

This is the first formalization to use `RSAConfig`'s sequential infrastructure:

- `Ctx = List Word` — the prefix produced so far
- `transition ctx w = ctx ++ [w]` — append the new word
- `initial = []` — start with empty prefix
- `meaning ctx _ w r = ∏_{w' ∈ ctx ++ [w]} noisyWordMeaning(w', r)`

Predictions are stated as `trajectoryProb` comparisons, proved via
`rsa_predict`'s generic reflection path.

## Findings

| # | Finding | Status |
|---|---------|--------|
| 1 | Color-first preferred when color more reliable | `rsa_predict` |
| 2 | L0 is order-independent (commutative product) | `cases r <;> rsa_predict` |
| 3 | Both orderings identify the target | `cases r` + `rsa_predict` |

## Note on Parameters

The paper uses uniform referent priors and a general Bayesian update
framework. Our formalization uses simplified noisy semantics with reliability
parameters. The specific values (colorRel = 9/10, shapeRel = 4/5) demonstrate
the qualitative prediction — they are not taken from the paper.
-/

set_option autoImplicit false

namespace Phenomena.Reference.Studies.CohnGordonEtAl2019

open RSA Real

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Words available to the incremental speaker. -/
inductive Word where
  | blue | green | circle | square
  deriving DecidableEq, Fintype, Repr

/-- Referents in the reference game scene.

    Scene: {blue circle, green circle, blue square}

    "blue" applies to 2/3 objects; "circle" applies to 2/3 objects.
    Both dimensions discriminate equally at the coarse level — the
    reliability parameter breaks the tie. -/
inductive Referent where
  | blueCircle | greenCircle | blueSquare
  deriving DecidableEq, Fintype, Repr

-- ============================================================================
-- §2. Noisy Semantics
-- ============================================================================

/-- Whether a word is veridically true of a referent. -/
def wordApplies : Word → Referent → Bool
  | .blue,   .blueCircle  => true
  | .blue,   .blueSquare  => true
  | .green,  .greenCircle => true
  | .circle, .blueCircle  => true
  | .circle, .greenCircle => true
  | .square, .blueSquare  => true
  | _,       _            => false

/-- Perceptual reliability for color adjectives. -/
noncomputable def colorRel : ℝ := 9 / 10

/-- Perceptual reliability for shape nouns. Lower than color. -/
noncomputable def shapeRel : ℝ := 4 / 5

/-- Noisy word meaning: P(word correctly applies to referent).
    Returns reliability v if the word is true of the referent,
    noise floor 1 − v otherwise.
    Simplified from @cite{degen-etal-2020}'s continuous semantics. -/
noncomputable def noisyWordMeaning (w : Word) (r : Referent) : ℝ :=
  let v := match w with
    | .blue | .green => colorRel
    | .circle | .square => shapeRel
  if wordApplies w r then v else 1 - v

private theorem noisyWordMeaning_nonneg (w : Word) (r : Referent) :
    0 ≤ noisyWordMeaning w r := by
  unfold noisyWordMeaning
  cases w <;> cases r <;> simp [wordApplies, colorRel, shapeRel] <;> norm_num

-- ============================================================================
-- §3. Meaning Function
-- ============================================================================

/-- Incremental meaning: product of noisy word meanings over the full prefix.

    meaning(ctx, _, nextWord, r) = ∏_{w' ∈ ctx ++ [nextWord]} noisyWordMeaning(w', r)

    This encodes the incremental L0 belief update: after hearing the prefix
    plus the next word, L0's posterior over referents is proportional to this
    product (with uniform prior). -/
noncomputable def prefixMeaning
    (ctx : List Word) (_ : Unit) (w : Word) (r : Referent) : ℝ :=
  (ctx ++ [w]).foldl (λ acc w' => acc * noisyWordMeaning w' r) 1

private theorem foldl_nonneg (ws : List Word) (r : Referent)
    (init : ℝ) (hinit : 0 ≤ init) :
    0 ≤ ws.foldl (λ acc w' => acc * noisyWordMeaning w' r) init := by
  induction ws generalizing init with
  | nil => exact hinit
  | cons w ws ih =>
    simp only [List.foldl]
    exact ih _ (mul_nonneg hinit (noisyWordMeaning_nonneg w r))

-- ============================================================================
-- §4. RSAConfig
-- ============================================================================

/-- Incremental RSA for a reference game with noisy semantics.

    This is the first `RSAConfig` to use the sequential infrastructure
    (`Ctx`, `transition`, `initial`). The model produces referring expressions
    word-by-word, with each step choosing the next word to maximize L0's
    posterior for the target referent.

    Architecture:
    - L0_at(ctx): literal listener given prefix ctx + next word
    - S1_at(ctx): speaker choosing next word given prefix ctx
    - trajectoryProb: chain-rule product of S1_at probabilities

    Parameters: α = 1, colorRel = 9/10, shapeRel = 4/5, uniform priors. -/
noncomputable def incRSA : RSAConfig Word Referent where
  Ctx := List Word
  meaning := prefixMeaning
  meaning_nonneg ctx _ u w := by
    unfold prefixMeaning
    exact foldl_nonneg _ w _ zero_le_one
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl _ := rpow_nonneg (hl _ _) _
  α := 1
  α_pos := one_pos
  transition ctx w := ctx ++ [w]
  initial := []
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

-- ============================================================================
-- §5. Findings
-- ============================================================================

/-- Qualitative findings from the incremental RSA model. -/
inductive Finding where
  /-- When color is more perceptually reliable than shape, the incremental
      speaker prefers the color adjective first. -/
  | color_first_when_more_reliable
  /-- L0 is order-independent: the posterior after both words is the same
      regardless of production order. -/
  | l0_order_independent
  /-- After hearing both adjectives, L0 assigns highest probability to the
      target (blueCircle) in the scene. -/
  | both_words_identify_target
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §6. Predictions
-- ============================================================================

/-- **Finding 1**: When color is more perceptually reliable than shape
    (colorRel = 9/10 > shapeRel = 4/5), the incremental speaker prefers
    to produce the color adjective first.

    Mechanism: Both "blue" and "circle" narrow the referent set from 3 to 2
    objects, but "blue" has higher reliability, giving it a higher L0
    posterior for the target after one word:

      L0(blueCircle | blue) = (9/10) / (9/10 + 1) ≈ 0.474
      L0(blueCircle | circle) = (4/5) / (4/5 + 1) ≈ 0.444

    Since L0 is order-independent, the trajectory scores differ only in
    their first factor, favoring blue-first.

    Proved via `rsa_predict`: generic reflection unfolds both trajectory
    expressions to product-of-policies, reifies to RExpr, checks ℚ interval
    separation. -/
set_option maxHeartbeats 800000 in
theorem color_first_preferred :
    incRSA.trajectoryProb () .blueCircle [.blue, .circle] >
    incRSA.trajectoryProb () .blueCircle [.circle, .blue] := by
  rsa_predict

/-- **Finding 2**: L0 is order-independent — the posterior after hearing
    both words is the same regardless of order.

    This follows from commutativity of ℝ multiplication: both the numerator
    (product of word meanings for one referent) and each summand of the
    denominator are commutative products.

    Proved by case-splitting on `r` (3 concrete referents), then `rsa_predict`
    evaluates each equality via exact ℚ computation. -/
theorem l0_order_independent (r : Referent) :
    (incRSA.L0agent_at [.blue] ()).policy .circle r =
    (incRSA.L0agent_at [.circle] ()).policy .blue r := by
  cases r <;> rsa_predict

/-- **Finding 3**: After hearing both adjectives, L0 assigns the highest
    probability to blueCircle (the target).

    "blue circle" uniquely identifies blueCircle: only blueCircle has
    both high color-match and high shape-match scores.

    Proved by case-splitting on `r`: the `.blueCircle` case contradicts `hr`,
    and the remaining 2 cases are concrete GT goals handled by `rsa_predict`. -/
theorem both_words_identify_target (r : Referent) (hr : r ≠ .blueCircle) :
    (incRSA.L0agent_at [.blue] ()).policy .circle .blueCircle >
    (incRSA.L0agent_at [.blue] ()).policy .circle r := by
  cases r with
  | blueCircle => exact absurd rfl hr
  | _ => rsa_predict

-- ============================================================================
-- §7. Verification
-- ============================================================================

/-- Map each finding to the model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .color_first_when_more_reliable =>
      incRSA.trajectoryProb () .blueCircle [.blue, .circle] >
      incRSA.trajectoryProb () .blueCircle [.circle, .blue]
  | .l0_order_independent =>
      ∀ r, (incRSA.L0agent_at [.blue] ()).policy .circle r =
           (incRSA.L0agent_at [.circle] ()).policy .blue r
  | .both_words_identify_target =>
      ∀ r, r ≠ .blueCircle →
        (incRSA.L0agent_at [.blue] ()).policy .circle .blueCircle >
        (incRSA.L0agent_at [.blue] ()).policy .circle r

/-- All 3 findings verified (pending tactic extension). -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact color_first_preferred
  · exact l0_order_independent
  · exact fun r hr => both_words_identify_target r hr

end Phenomena.Reference.Studies.CohnGordonEtAl2019
