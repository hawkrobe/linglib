import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.Basic
import Linglib.Semantics.Exhaustification.Operators.Basic

/-!
# [potts-levy-2015]: lexical uncertainty and speaker expertise with disjunction

Hurford-violating disjunctions ("X or A" with A ⊆ ⟦X⟧) are felicitous and
carry ignorance implicatures. The paper derives both from RSA with lexical
uncertainty (BLS 41, pp. 417–445): the listener jointly infers the world and
the speaker's lexicon (eq. 14), and an expertise speaker (eq. 15) signals
both world knowledge (α term) and lexicon knowledge (β term). Domain: 5
utterances × 3 states (w₁, w₂, and the uncertainty join w₁₂, where truth
requires truth at both atoms) × 3 lexica for X (`base` = A ∪ B, `excl` = B,
`syn` = A).

## Main results

* `uncertainty_w12_vs_w1` / `_w2` / `w1_vs_w2`: hearing "A or X", the joint
  listener infers speaker uncertainty — w₁₂ > w₁ > w₂ (Figure 10 world
  margins: .91 > .09 > 0).
* `lexicon_excl_vs_base` / `_syn`: the exclusivized lexicon dominates —
  excl > base > syn (Figure 10 lexicon margins: .49 > .34 > .17).
* `s1_w12_AorX_vs_A` / `_X`, `s1_w1_A_vs_AorX`: the eq. 11 speaker uses the
  disjunction exactly when uncertain.
* `L2_AorX_*` / `S2_expertise_*`: the same orderings at the stacked
  expertise level (eq. 15, Figure 10's regime α = 2, β = 1, C(or) = 1;
  p. 436: "S₂'s preferred message given observed state w₁∨w₂ and lexicon
  L₁ from Figure 10 is A or X").
* `excl_is_base_minus_A`: the `excl` lexicon is exhaustification —
  excl(X) = base(X) ∧ ¬A.
* `all_findings_verified`: the full qualitative inventory.

## Implementation notes

α = 2 and β = 1 are natural powers, so every agent in the tower — l₀, s₁,
the joint L₁ (eq. 14; its per-lexicon normaliser cancels, giving scores
P(w)·P(L)·s₁), the stacked l₁/S₂/L₂, and the eq. 17 speaker marginal — is
an exact-ℚ score vector normalized by `pmfOfScores`. The disjunction cost
`exp(−1)` is rationalized as `37/100` (qualitative predictions robust,
paper §5.4). `s2PMF` is the endorsement reading of S₂ over the level-1
listener (an informativity-component decomposition); `s2ExpPMF` is the
paper's eq. 17 lexicon-marginalized expertise speaker.

The definitional regime (syn dominating, "wine lover or oenophile")
requires β > α (paper §5.4) and is not modeled.

## TODO

Model the definitional regime (β > α) and the implicature-blocking
simulations of paper §5.3. Relate the lexica to
`Semantics.Presupposition`-layer exhaustification operators.
-/

namespace PottsLevy2015

/-! ### Domain -/

/-- World states. w₁ = only A-state, w₂ = only B-state,
    w₁₂ = speaker uncertain (both A and B possible). -/
inductive World where
  | w₁ | w₂ | w₁₂
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Utterances: A, B, X (the ambiguous term), "A or X", and null. -/
inductive Utterance where
  | A | B | X | AorX | null
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Lexica for X.
    - base: X = A ∪ B (unrefined)
    - excl: X = B only (exhaustified, disjoint from A)
    - syn:  X = A (synonymous with A) -/
inductive Lex where
  | base | excl | syn
  deriving DecidableEq, Repr, Inhabited, Fintype

/-! ### Truth conditions -/

/-- Truth of atomic (non-disjunctive) utterances at atomic worlds. -/
def atomicTruth : Lex → Utterance → World → Bool
  -- A is true at w₁ only
  | _, .A, .w₁ => true
  -- B is true at w₂ only
  | _, .B, .w₂ => true
  -- X depends on lexicon:
  | .base, .X, .w₁ => true   -- base: X = {w₁, w₂}
  | .base, .X, .w₂ => true
  | .excl, .X, .w₂ => true   -- excl: X = {w₂} only
  | .syn,  .X, .w₁ => true   -- syn:  X = {w₁} only
  -- null is always true
  | _, .null, _ => true
  | _, _, _ => false

/-- Truth at all worlds including the join state w₁₂.
    AorX is computed compositionally: A ∨ X.
    At w₁₂, an utterance is true iff true at BOTH w₁ and w₂
    (speaker can only assert what holds across all epistemically
    accessible worlds — the "must" reading). -/
def truth (l : Lex) (u : Utterance) (w : World) : Bool :=
  let base (w' : World) :=
    match u with
    | .AorX => atomicTruth l .A w' || atomicTruth l .X w'
    | other => atomicTruth l other w'
  match w with
  | .w₁ => base .w₁
  | .w₂ => base .w₂
  | .w₁₂ => base .w₁ && base .w₂

/-! ### Exhaustification grounding -/

/-! The `excl` lexicon is the exhaustified reading of X relative to
alternatives {A, X}. We prove this structurally: at every atomic world,
excl(X) = base(X) ∧ ¬A, which is what `exh_mw({A, X}, X)` yields
when there are exactly two alternatives with A ⊂ X. -/

/-- excl(X) = base(X) ∧ ¬base(A): X minus A. -/
theorem excl_is_base_minus_A :
    ∀ w, atomicTruth .excl .X w =
      (atomicTruth .base .X w && !atomicTruth .base .A w) := by
  decide

/-- syn(X) = base(A): X narrowed to overlap with A. -/
theorem syn_is_base_A :
    ∀ w, atomicTruth .syn .X w = atomicTruth .base .A w := by
  decide

/-- Base X strictly entails excl X (excl is a proper refinement). -/
theorem base_entails_excl :
    (∀ w, atomicTruth .excl .X w = true → atomicTruth .base .X w = true) ∧
    ∃ w, atomicTruth .base .X w = true ∧ atomicTruth .excl .X w = false := by
  decide

/-! ### The exact-ℚ model and its PMF face (local pending the RSA API pass) -/

/-! Every agent in the tower is a rational function of the truth table:
α = 2 and β = 1 are natural powers and the cost factor is rational, so the
scores are computed in exact ℚ (division by zero yields 0, matching the
zero-normaliser convention of `Core.RationalAction.policy`). Listeners and
speakers are `PMF.normalize` of these scores via `pmfOfScores`. -/

section QModel

/-- Literal listener (eq. 10, uniform world prior). -/
def l0Q (l : Lex) (u : Utterance) (w : World) : ℚ :=
  (if truth l u w then 1 else 0) /
    (∑ w', if truth l u w' then (1 : ℚ) else 0)

/-- Speaker weight (eq. 11 at α = 2, zero cost). -/
def s1WQ (l : Lex) (w : World) (u : Utterance) : ℚ := (l0Q l u w) ^ 2

/-- Normalized speaker (eq. 11). -/
def s1Q (l : Lex) (w : World) (u : Utterance) : ℚ :=
  s1WQ l w u / ∑ u', s1WQ l w u'

/-- Joint listener world score (eq. 14/16, uniform priors). -/
def l1ScoreQ (u : Utterance) (w : World) : ℚ := ∑ l, s1Q l w u

/-- Normalized world posterior (eq. 16). -/
def l1Q (u : Utterance) (w : World) : ℚ :=
  l1ScoreQ u w / ∑ w', l1ScoreQ u w'

/-- Lexicon score of the joint listener (eq. 14). -/
def l1LatScoreQ (u : Utterance) (l : Lex) : ℚ := ∑ w, s1Q l w u

/-- Normalized lexicon posterior (eq. 14). -/
def l1LatQ (u : Utterance) (l : Lex) : ℚ :=
  l1LatScoreQ u l / ∑ l', l1LatScoreQ u l'

/-- Disjunction cost factor `exp(−C(m))` with C(or) = 1, rationalized as
`37/100 ≈ exp(−1)` (qualitative predictions are robust, paper §5.4). -/
def disjCostQ : Utterance → ℚ
  | .AorX => 37/100
  | _ => 1

/-- Per-lexicon pragmatic listener (eq. 12), the stacked literal layer. -/
def l02Q (l : Lex) (u : Utterance) (w : World) : ℚ :=
  s1Q l w u / ∑ w', s1Q l w' u

/-- Expertise speaker weight (eq. 15 at α = 2, β = 1):
`l₁(w|m,L)² · L₁(L|m) · exp(−C(m))`. -/
def s2WQ (l : Lex) (w : World) (u : Utterance) : ℚ :=
  (l02Q l u w) ^ 2 * l1LatQ u l * disjCostQ u

/-- Normalized expertise speaker (eq. 15). -/
def s2Q (l : Lex) (w : World) (u : Utterance) : ℚ :=
  s2WQ l w u / ∑ u', s2WQ l w u'

/-- L₂ world score (eq. 14/16 at k = 2). -/
def l2ScoreQ (u : Utterance) (w : World) : ℚ := ∑ l, s2Q l w u

/-- L₂ lexicon score (eq. 14 at k = 2). -/
def l2LatScoreQ (u : Utterance) (l : Lex) : ℚ := ∑ w, s2Q l w u

private theorem l0Q_nonneg (l : Lex) (u : Utterance) (w : World) : 0 ≤ l0Q l u w :=
  div_nonneg (by split <;> norm_num)
    (Finset.sum_nonneg fun _ _ => by split <;> norm_num)

private theorem s1WQ_nonneg (l : Lex) (w : World) (u : Utterance) : 0 ≤ s1WQ l w u :=
  pow_nonneg (l0Q_nonneg l u w) 2

private theorem s1Q_nonneg (l : Lex) (w : World) (u : Utterance) : 0 ≤ s1Q l w u :=
  div_nonneg (s1WQ_nonneg l w u) (Finset.sum_nonneg fun u' _ => s1WQ_nonneg l w u')

private theorem l1ScoreQ_nonneg (u : Utterance) (w : World) : 0 ≤ l1ScoreQ u w :=
  Finset.sum_nonneg fun l _ => s1Q_nonneg l w u

private theorem l1Q_nonneg (u : Utterance) (w : World) : 0 ≤ l1Q u w :=
  div_nonneg (l1ScoreQ_nonneg u w)
    (Finset.sum_nonneg fun w' _ => l1ScoreQ_nonneg u w')

private theorem l1LatScoreQ_nonneg (u : Utterance) (l : Lex) : 0 ≤ l1LatScoreQ u l :=
  Finset.sum_nonneg fun w _ => s1Q_nonneg l w u

private theorem l1LatQ_nonneg (u : Utterance) (l : Lex) : 0 ≤ l1LatQ u l :=
  div_nonneg (l1LatScoreQ_nonneg u l)
    (Finset.sum_nonneg fun l' _ => l1LatScoreQ_nonneg u l')

private theorem disjCostQ_nonneg (u : Utterance) : 0 ≤ disjCostQ u := by
  cases u <;> norm_num [disjCostQ]

private theorem l02Q_nonneg (l : Lex) (u : Utterance) (w : World) : 0 ≤ l02Q l u w :=
  div_nonneg (s1Q_nonneg l w u) (Finset.sum_nonneg fun w' _ => s1Q_nonneg l w' u)

private theorem s2WQ_nonneg (l : Lex) (w : World) (u : Utterance) : 0 ≤ s2WQ l w u :=
  mul_nonneg (mul_nonneg (pow_nonneg (l02Q_nonneg l u w) 2) (l1LatQ_nonneg u l))
    (disjCostQ_nonneg u)

private theorem s2Q_nonneg (l : Lex) (w : World) (u : Utterance) : 0 ≤ s2Q l w u :=
  div_nonneg (s2WQ_nonneg l w u) (Finset.sum_nonneg fun u' _ => s2WQ_nonneg l w u')

private theorem l2ScoreQ_nonneg (u : Utterance) (w : World) : 0 ≤ l2ScoreQ u w :=
  Finset.sum_nonneg fun l _ => s2Q_nonneg l w u

private theorem l2LatScoreQ_nonneg (u : Utterance) (l : Lex) : 0 ≤ l2LatScoreQ u l :=
  Finset.sum_nonneg fun w _ => s2Q_nonneg l w u

end QModel

section PMFFace

open scoped ENNReal

/-- Normalize a rational score vector into a PMF (uniform at zero mass). -/
noncomputable def pmfOfScores {σ : Type*} [Fintype σ] [Nonempty σ]
    (f : σ → ℚ) : PMF σ :=
  if h : (∑' x, ENNReal.ofReal ((f x : ℝ))) ≠ 0 then
    PMF.normalize (fun x => ENNReal.ofReal ((f x : ℝ))) h
      (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)
  else PMF.uniformOfFintype σ

private theorem pmfOfScores_apply {σ : Type*} [Fintype σ] [Nonempty σ]
    {f : σ → ℚ} (hf : ∀ x, 0 ≤ f x) (hpos : 0 < ∑ x, f x) (x : σ) :
    pmfOfScores f x = ENNReal.ofReal ((f x / ∑ x', f x' : ℚ) : ℝ) := by
  have hsum : (∑' x, ENNReal.ofReal ((f x : ℝ)))
      = ENNReal.ofReal ((∑ x, f x : ℚ) : ℝ) := by
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun x _ => by exact_mod_cast hf x)]
    push_cast
    rfl
  rw [pmfOfScores, dif_pos (by
      rw [hsum, ENNReal.ofReal_ne_zero_iff]; exact_mod_cast hpos),
    PMF.normalize_apply, hsum,
    ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hpos),
    ← ENNReal.ofReal_mul (by exact_mod_cast hf x)]
  congr 1
  push_cast
  rw [div_eq_mul_inv]

/-- Strict comparison of `pmfOfScores` values via the exact-ℚ scores. -/
private theorem pmf_lt {σ : Type*} [Fintype σ] [Nonempty σ] {f : σ → ℚ}
    (hf : ∀ x, 0 ≤ f x) (hpos : 0 < ∑ x, f x) {a b : σ}
    (hb : 0 < f b / ∑ x, f x) (hab : f a / ∑ x, f x < f b / ∑ x, f x) :
    pmfOfScores f a < pmfOfScores f b := by
  rw [pmfOfScores_apply hf hpos, pmfOfScores_apply hf hpos]
  exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hb)).mpr
    (by exact_mod_cast hab)

/-- Joint-listener world posterior (eq. 16). -/
noncomputable def l1PMF (u : Utterance) : PMF World :=
  pmfOfScores (l1ScoreQ u)

/-- Joint-listener lexicon posterior (eq. 14). -/
noncomputable def l1LatPMF (u : Utterance) : PMF Lex :=
  pmfOfScores (l1LatScoreQ u)

/-- Speaker (eq. 11). -/
noncomputable def s1PMF (l : Lex) (w : World) : PMF Utterance :=
  pmfOfScores (s1WQ l w)

/-- Endorsement speaker: renormalizes the L1 world posterior per world. -/
noncomputable def s2PMF (w : World) : PMF Utterance :=
  pmfOfScores (fun u => l1Q u w)

/-- L₂ world posterior (eq. 16 at k = 2). -/
noncomputable def l2PMF (u : Utterance) : PMF World :=
  pmfOfScores (l2ScoreQ u)

/-- L₂ lexicon posterior (eq. 14 at k = 2). -/
noncomputable def l2LatPMF (u : Utterance) : PMF Lex :=
  pmfOfScores (l2LatScoreQ u)

/-- Marginal expertise speaker (eq. 17 at k = 2, uniform lexicon prior). -/
noncomputable def s2ExpPMF (w : World) : PMF Utterance :=
  pmfOfScores (fun u => l2ScoreQ u w)

end PMFFace

/-! ### Structural properties -/

/-- Under syn lexicon, "A or X" has the same extension as "A" alone.
    This is the Hurford violation: the disjunction is redundant. -/
theorem syn_AorX_eq_A :
    ∀ w, truth .syn .AorX w = truth .syn .A w := by decide

/-- Under excl lexicon, A and X are semantically disjoint.
    This is the exhaustified reading that rescues the disjunction. -/
theorem excl_disjoint :
    ¬∃ w, truth .excl .A w = true ∧ truth .excl .X w = true := by decide

/-- Under excl, "A or X" is true at w₁₂ and is the only non-null
    utterance true there. A, B, X alone each fail at w₁₂ because
    they cannot cover both atomic states. -/
theorem excl_w12_AorX_unique :
    truth .excl .AorX .w₁₂ = true ∧
    truth .excl .A .w₁₂ = false ∧
    truth .excl .B .w₁₂ = false ∧
    truth .excl .X .w₁₂ = false := by decide

/-- Under syn, "A or X" is FALSE at w₁₂ (syn X = A, so AorX = A,
    and A fails the "must" check because A is false at w₂). -/
theorem syn_w12_AorX_false :
    truth .syn .AorX .w₁₂ = false := by decide

/-- Under base, "A or X" is true at w₁₂ (base X covers both w₁
    and w₂, so the disjunction holds at both atomic states). -/
theorem base_w12_AorX_true :
    truth .base .AorX .w₁₂ = true := by decide

/-! ### Uncertainty implicature -/

/-! The key prediction: hearing "A or X", L1 infers the speaker is
uncertain (w₁₂), not that the speaker knows A (w₁) or knows B (w₂).

This is the ignorance/uncertainty implicature. The speaker could have
said just "A" if they knew w₁, or just "X" if they knew w₂ (under the
excl lexicon). By choosing the disjunction, the speaker signals that
they cannot commit to either disjunct — i.e., they are in w₁₂. -/

/-- Uncertainty implicature: w₁₂ > w₁ given "A or X". -/
theorem uncertainty_w12_vs_w1 :
    l1PMF .AorX .w₁ < l1PMF .AorX .w₁₂ :=
  pmf_lt (l1ScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Uncertainty implicature: w₁₂ > w₂ given "A or X". -/
theorem uncertainty_w12_vs_w2 :
    l1PMF .AorX .w₂ < l1PMF .AorX .w₁₂ :=
  pmf_lt (l1ScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Complete uncertainty ordering: w₁ > w₂. The listener assigns
    higher posterior to w₁ than w₂ because under excl, "A or X"
    at w₁ has A as the operative disjunct (a natural reading),
    while at w₂ only excl-X contributes (a refined reading). -/
theorem uncertainty_w1_vs_w2 :
    l1PMF .AorX .w₂ < l1PMF .AorX .w₁ :=
  pmf_lt (l1ScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### Lexicon inference -/

/-! L1 also infers which lexicon the speaker is using. For "A or X",
the excl lexicon dominates: it makes the disjunction maximally
informative (A and X partition the space). The syn lexicon makes the
disjunction redundant (Hurford violation), so L1 disprefers it. -/

/-- Lexicon inference: excl preferred over base for "A or X". -/
theorem lexicon_excl_vs_base :
    l1LatPMF .AorX .base < l1LatPMF .AorX .excl :=
  pmf_lt (l1LatScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Lexicon inference: excl preferred over syn for "A or X". -/
theorem lexicon_excl_vs_syn :
    l1LatPMF .AorX .syn < l1LatPMF .AorX .excl :=
  pmf_lt (l1LatScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Lexicon inference: base preferred over syn for "A or X".
    Completes the full ordering: excl > base > syn.
    The syn lexicon makes "A or X" redundant (= "A"),
    so it gets the least support from L1. -/
theorem lexicon_base_vs_syn :
    l1LatPMF .AorX .syn < l1LatPMF .AorX .base :=
  pmf_lt (l1LatScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### Speaker rationality -/

/-! The paper argues that a rational speaker at w₁₂ (uncertain)
should prefer the disjunction "A or X" over simpler utterances.
This is the production-side counterpart to the L1 uncertainty
implicature: the speaker KNOWS they're in w₁₂ and chooses AorX
because it is the most informative utterance at that world. -/

/-- Speaker at w₁₂ prefers "A or X" over "A" (under excl lexicon).
    If the speaker only said "A", the listener would infer w₁
    (since A is only true at w₁ under excl). The disjunction
    conveys the uncertainty. -/
theorem s1_w12_AorX_vs_A :
    s1PMF .excl .w₁₂ .A < s1PMF .excl .w₁₂ .AorX :=
  pmf_lt (s1WQ_nonneg _ _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Speaker at w₁₂ prefers "A or X" over "X" (under excl lexicon).
    "X" alone would lead to inference of w₂. -/
theorem s1_w12_AorX_vs_X :
    s1PMF .excl .w₁₂ .X < s1PMF .excl .w₁₂ .AorX :=
  pmf_lt (s1WQ_nonneg _ _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Speaker at w₁ prefers "A" over "A or X" (under excl lexicon).
    When the speaker KNOWS w₁, saying just "A" is more informative
    than the disjunction. -/
theorem s1_w1_A_vs_AorX :
    s1PMF .excl .w₁ .AorX < s1PMF .excl .w₁ .A :=
  pmf_lt (s1WQ_nonneg _ _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### Hurford disjunctions -/

/-! Hurford disjunctions like "some or all" are felicitous, rescued by
exhaustification. This is exactly the phenomenon [potts-levy-2015]
models: the `excl` lexicon plays the role of exhaustification, making
the disjuncts non-overlapping and the sentence informative (proved by
`excl_disjoint` and the L1 predictions above).

The connection: exh(some) = some-but-not-all corresponds to our
`excl_is_base_minus_A` theorem, which shows excl(X) = base(X) ∧ ¬A —
the same operation as exh. -/

/-! ### Endorsement decomposition -/

/-! Eq. 15's two utility terms verified as independent components: the
informativity term via the endorsement speaker (`s2PMF`, S₂(u|w) ∝ L₁(w|u))
and the expertise term via lexicon signaling (`AorX_signals_excl_vs_A`).
With β > 0 the speaker has both reasons to use the disjunction. -/

/-- Endorsement at w₁₂: "A or X" is the more informative choice ("A" is
false at w₁₂ under every lexicon). -/
theorem s2_w12_AorX_vs_A :
    s2PMF .w₁₂ .A < s2PMF .w₁₂ .AorX :=
  pmf_lt (fun u => l1Q_nonneg u _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- S2 endorsement at w₁: the pragmatic speaker prefers "A" over "A or X".

    When the speaker knows w₁, "A" is the most informative utterance.
    The expertise model does not override this — even with β > 0,
    an expert at w₁ prefers the direct utterance. -/
theorem s2_w1_A_vs_AorX :
    s2PMF .w₁ .AorX < s2PMF .w₁ .A :=
  pmf_lt (fun u => l1Q_nonneg u _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- "A or X" signals the excl lexicon more strongly than "A" does.

    Under "A", all three lexica agree on truth conditions (A is true at
    w₁ only), so L1_latent is approximately uniform. Under "A or X",
    the excl lexicon dominates because it makes the disjunction maximally
    informative (§5). This asymmetry is the mechanism by which β > 0
    amplifies the speaker's preference for the disjunction.

    Combined with `s2_w12_AorX_vs_A`, this shows that an expert speaker
    at w₁₂ has TWO reasons to use "A or X": informativity (S2) and
    lexicon signaling (this theorem). -/
theorem AorX_signals_excl_vs_A :
    l1LatPMF .A .excl < l1LatPMF .AorX .excl := by
  rw [l1LatPMF, l1LatPMF, pmfOfScores_apply (l1LatScoreQ_nonneg _) (by decide +kernel),
    pmfOfScores_apply (l1LatScoreQ_nonneg _) (by decide +kernel)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast
      (by decide +kernel : (0:ℚ) < l1LatScoreQ .AorX .excl / ∑ l', l1LatScoreQ .AorX l'))).mpr
    (by exact_mod_cast (by decide +kernel :
      l1LatScoreQ .A .excl / ∑ l', l1LatScoreQ .A l' <
      l1LatScoreQ .AorX .excl / ∑ l', l1LatScoreQ .AorX l'))

/-! ### The stacked expertise model (eq. 15) -/

/-! Eq. 15, `S₂(m|w,L) ∝ l₁(w|m,L)^α · L₁(L|m)^β · exp(−C(m))`, at
Figure 10's regime α = 2, β = 1, C(or) = 1: `s2WQ` scores the per-lexicon
listener squared, times the lexicon posterior, times `disjCostQ`. -/

/-- L₂ hearing "A or X": uncertainty state w₁₂ dominates w₁. -/
theorem L2_AorX_w12_vs_w1 :
    l2PMF .AorX .w₁ < l2PMF .AorX .w₁₂ :=
  pmf_lt (l2ScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- L₂ hearing "A or X": uncertainty state w₁₂ dominates w₂. -/
theorem L2_AorX_w12_vs_w2 :
    l2PMF .AorX .w₂ < l2PMF .AorX .w₁₂ :=
  pmf_lt (l2ScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- L₂ hearing "A or X": w₁ > w₂. -/
theorem L2_AorX_w1_vs_w2 :
    l2PMF .AorX .w₂ < l2PMF .AorX .w₁ :=
  pmf_lt (l2ScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)



/-- L₂ lexicon inference: excl dominates base for "A or X". -/
theorem L2_AorX_excl_vs_base :
    l2LatPMF .AorX .base < l2LatPMF .AorX .excl :=
  pmf_lt (l2LatScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- L₂ lexicon inference: excl dominates syn for "A or X". -/
theorem L2_AorX_excl_vs_syn :
    l2LatPMF .AorX .syn < l2LatPMF .AorX .excl :=
  pmf_lt (l2LatScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- L₂ lexicon inference: base > syn. Full ordering: excl > base > syn. -/
theorem L2_AorX_base_vs_syn :
    l2LatPMF .AorX .syn < l2LatPMF .AorX .base :=
  pmf_lt (l2LatScoreQ_nonneg _) (by decide +kernel) (by decide +kernel) (by decide +kernel)



/-- S₂ at w₁₂ prefers "A or X" over "A" (marginalized over lexica). -/
theorem S2_expertise_w12_AorX_vs_A :
    s2ExpPMF .w₁₂ .A < s2ExpPMF .w₁₂ .AorX :=
  pmf_lt (fun u => l2ScoreQ_nonneg u _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- S₂ at w₁ prefers "A" over "A or X" (marginalized over lexica). -/
theorem S2_expertise_w1_A_vs_AorX :
    s2ExpPMF .w₁ .AorX < s2ExpPMF .w₁ .A :=
  pmf_lt (fun u => l2ScoreQ_nonneg u _) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### Findings -/

/-- The qualitative findings from the [potts-levy-2015] LU + expertise model. -/
inductive Finding where
  /-- L1 -/
  | uncertainty_w12_vs_w1
  | uncertainty_w12_vs_w2
  | uncertainty_w1_vs_w2
  | lexicon_excl_vs_base
  | lexicon_excl_vs_syn
  | lexicon_base_vs_syn
  /-- S1 -/
  | s1_w12_prefers_AorX
  | s1_w1_prefers_A
  /-- S2 endorsement -/
  | s2_w12_AorX
  | s2_w1_A
  | AorX_signals_excl
  /-- L2 expertise (stacked) -/
  | L2_w12_vs_w1
  | L2_w12_vs_w2
  | L2_w1_vs_w2
  | L2_excl_vs_base
  | L2_excl_vs_syn
  | L2_base_vs_syn
  | S2_expertise_w12_AorX
  | S2_expertise_w1_A
  deriving Repr

/-- Verification: each finding is backed by a proved theorem. -/
def Finding.verified : Finding → Prop
  | .uncertainty_w12_vs_w1 => l1PMF .AorX .w₁ < l1PMF .AorX .w₁₂
  | .uncertainty_w12_vs_w2 => l1PMF .AorX .w₂ < l1PMF .AorX .w₁₂
  | .uncertainty_w1_vs_w2 => l1PMF .AorX .w₂ < l1PMF .AorX .w₁
  | .lexicon_excl_vs_base => l1LatPMF .AorX .base < l1LatPMF .AorX .excl
  | .lexicon_excl_vs_syn => l1LatPMF .AorX .syn < l1LatPMF .AorX .excl
  | .lexicon_base_vs_syn => l1LatPMF .AorX .syn < l1LatPMF .AorX .base
  | .s1_w12_prefers_AorX => s1PMF .excl .w₁₂ .A < s1PMF .excl .w₁₂ .AorX
  | .s1_w1_prefers_A => s1PMF .excl .w₁ .AorX < s1PMF .excl .w₁ .A
  | .s2_w12_AorX => s2PMF .w₁₂ .A < s2PMF .w₁₂ .AorX
  | .s2_w1_A => s2PMF .w₁ .AorX < s2PMF .w₁ .A
  | .AorX_signals_excl => l1LatPMF .A .excl < l1LatPMF .AorX .excl
  | .L2_w12_vs_w1 => l2PMF .AorX .w₁ < l2PMF .AorX .w₁₂
  | .L2_w12_vs_w2 => l2PMF .AorX .w₂ < l2PMF .AorX .w₁₂
  | .L2_w1_vs_w2 => l2PMF .AorX .w₂ < l2PMF .AorX .w₁
  | .L2_excl_vs_base => l2LatPMF .AorX .base < l2LatPMF .AorX .excl
  | .L2_excl_vs_syn => l2LatPMF .AorX .syn < l2LatPMF .AorX .excl
  | .L2_base_vs_syn => l2LatPMF .AorX .syn < l2LatPMF .AorX .base
  | .S2_expertise_w12_AorX => s2ExpPMF .w₁₂ .A < s2ExpPMF .w₁₂ .AorX
  | .S2_expertise_w1_A => s2ExpPMF .w₁ .AorX < s2ExpPMF .w₁ .A

theorem all_findings_verified (f : Finding) : f.verified := by
  cases f <;> simp only [Finding.verified]
  · exact uncertainty_w12_vs_w1
  · exact uncertainty_w12_vs_w2
  · exact uncertainty_w1_vs_w2
  · exact lexicon_excl_vs_base
  · exact lexicon_excl_vs_syn
  · exact lexicon_base_vs_syn
  · exact s1_w12_AorX_vs_A
  · exact s1_w1_A_vs_AorX
  · exact s2_w12_AorX_vs_A
  · exact s2_w1_A_vs_AorX
  · exact AorX_signals_excl_vs_A
  · exact L2_AorX_w12_vs_w1
  · exact L2_AorX_w12_vs_w2
  · exact L2_AorX_w1_vs_w2
  · exact L2_AorX_excl_vs_base
  · exact L2_AorX_excl_vs_syn
  · exact L2_AorX_base_vs_syn
  · exact S2_expertise_w12_AorX_vs_A
  · exact S2_expertise_w1_A_vs_AorX

end PottsLevy2015
