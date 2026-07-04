import Linglib.Core.Probability.Scores
import Linglib.Pragmatics.RSA.ScoreChain

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
  listener infers speaker uncertainty — w₁₂ > w₁ > w₂.
* `lexicon_excl_vs_base` / `_syn`: the exclusivized lexicon dominates —
  excl > base > syn.
* `s1_w12_AorX_vs_A` / `_X`, `s1_w1_A_vs_AorX`: the eq. 11 speaker uses the
  disjunction exactly when uncertain.
* `l2_AorX_*` / `s2Exp_*`: the same orderings at the stacked expertise
  level, Figure 10's regime α = 2, β = 1, C(or) = 1 (its L₂ world margins
  are .91 > .09 > 0 and lexicon margins .49 > .34 > .17; p. 436: "S₂'s
  preferred message given observed state w₁∨w₂ and lexicon L₁ from
  Figure 10 is A or X").
* `excl_is_base_minus_A`: the `excl` lexicon is exhaustification —
  excl(X) = base(X) ∧ ¬A.

## Implementation notes

α = 2 and β = 1 are natural powers, so every agent in the tower — l₀, s₁,
the joint L₁ (eq. 14; its per-lexicon normaliser cancels, giving scores
P(w)·P(L)·s₁), the stacked l₁/S₂/L₂, and the eq. 17 speaker marginal — is
an exact-`ℚ≥0` score vector normalized by `PMF.ofScores`. No utterance row
is dead (`null` is true everywhere), so mid-chain normalizations are plain
`÷0 = 0` divisions rather than fallback-completed `PMF.scoresWith`. The
disjunction cost `exp(−1)` is rationalized as `37/100` (qualitative
predictions robust, paper §5.4). `s2PMF` is the endorsement reading of S₂
over the level-1 listener (an informativity-component decomposition);
`s2ExpPMF` is the paper's eq. 17 lexicon-marginalized expertise speaker.

The definitional regime (syn dominating, "wine lover or oenophile")
requires β > α (paper §5.4) and is not modeled.

## TODO

Model the definitional regime (β > α) and the implicature-blocking
simulations of paper §5.3. Relate the lexica to
`Semantics.Exhaustification` operators (`excl_is_base_minus_A` is the
`exh` clause over alternatives {A, X}).
-/

open scoped NNRat

namespace PottsLevy2015

/-! ### Domain -/

/-- World states: `w₁` (only A), `w₂` (only B), and the uncertainty join
`w₁₂` (both possible). -/
inductive World where
  | w₁ | w₂ | w₁₂
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Utterances: the atoms A, B, the ambiguous term X, the disjunction, and
the designated null message. -/
inductive Utterance where
  | A | B | X | AorX | null
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Lexica for X: `base` (X = A ∪ B), `excl` (X = B, exhaustified), `syn`
(X = A, synonymous). -/
inductive Lex where
  | base | excl | syn
  deriving DecidableEq, Repr, Inhabited, Fintype

/-! ### Truth conditions -/

/-- Truth of non-disjunctive utterances at atomic worlds. -/
def atomicTruth : Lex → Utterance → World → Bool
  | _, .A, .w₁ => true
  | _, .B, .w₂ => true
  | .base, .X, .w₁ => true
  | .base, .X, .w₂ => true
  | .excl, .X, .w₂ => true
  | .syn,  .X, .w₁ => true
  | _, .null, _ => true
  | _, _, _ => false

/-- Truth at all worlds: "A or X" is A ∨ X, and truth at the join `w₁₂`
requires truth at both atoms (the speaker asserts only what holds across
all epistemically accessible worlds). -/
def truth (l : Lex) (u : Utterance) (w : World) : Bool :=
  let atWorld (w' : World) :=
    match u with
    | .AorX => atomicTruth l .A w' || atomicTruth l .X w'
    | other => atomicTruth l other w'
  match w with
  | .w₁ => atWorld .w₁
  | .w₂ => atWorld .w₂
  | .w₁₂ => atWorld .w₁ && atWorld .w₂

/-! ### Exhaustification grounding -/

/-- excl(X) = base(X) ∧ ¬A: the `excl` lexicon is the exhaustification of
X relative to the alternative A. -/
theorem excl_is_base_minus_A :
    ∀ w, atomicTruth .excl .X w =
      (atomicTruth .base .X w && !atomicTruth .base .A w) := by
  decide

/-- syn(X) = A: the `syn` lexicon narrows X to its overlap with A. -/
theorem syn_is_base_A :
    ∀ w, atomicTruth .syn .X w = atomicTruth .base .A w := by
  decide

/-- `excl` is a proper refinement of `base`. -/
theorem base_entails_excl :
    (∀ w, atomicTruth .excl .X w = true → atomicTruth .base .X w = true) ∧
    ∃ w, atomicTruth .base .X w = true ∧ atomicTruth .excl .X w = false := by
  decide

/-! ### Exact-ℚ scores

Division by zero yields 0, matching the zero-normaliser convention of
`Core.RationalAction.policy`; no row here is in fact dead. -/

/-- Speaker weight: the squared literal listener (eqs. 10–11 at α = 2,
uniform world prior, zero cost). -/
def s1WQ (l : Lex) (w : World) (u : Utterance) : ℚ≥0 :=
  RSA.Score.l0 (truth l) (fun _ => 1) u w ^ 2

/-- Normalized speaker (eq. 11). -/
def s1Q (l : Lex) (w : World) (u : Utterance) : ℚ≥0 :=
  s1WQ l w u / ∑ u', s1WQ l w u'

/-- Joint-listener world score (eq. 14/16, uniform priors). -/
def l1ScoreQ (u : Utterance) (w : World) : ℚ≥0 := ∑ l, s1Q l w u

/-- Normalized world posterior (eq. 16). -/
def l1Q (u : Utterance) (w : World) : ℚ≥0 :=
  l1ScoreQ u w / ∑ w', l1ScoreQ u w'

/-- Lexicon score of the joint listener (eq. 14). -/
def l1LatScoreQ (u : Utterance) (l : Lex) : ℚ≥0 := ∑ w, s1Q l w u

/-- Normalized lexicon posterior (eq. 14). -/
def l1LatQ (u : Utterance) (l : Lex) : ℚ≥0 :=
  l1LatScoreQ u l / ∑ l', l1LatScoreQ u l'

/-- Disjunction cost factor `exp(−C(m))` with C(or) = 1, rationalized as
`37/100 ≈ exp(−1)`. -/
def disjCostQ : Utterance → ℚ≥0
  | .AorX => 37/100
  | _ => 1

/-- Per-lexicon pragmatic listener (eq. 12), the stacked literal layer. -/
def l02Q (l : Lex) (u : Utterance) (w : World) : ℚ≥0 :=
  s1Q l w u / ∑ w', s1Q l w' u

/-- Expertise speaker weight (eq. 15 at α = 2, β = 1):
`l₁(w|m,L)² · L₁(L|m) · exp(−C(m))`. -/
def s2WQ (l : Lex) (w : World) (u : Utterance) : ℚ≥0 :=
  l02Q l u w ^ 2 * l1LatQ u l * disjCostQ u

/-- Normalized expertise speaker (eq. 15). -/
def s2Q (l : Lex) (w : World) (u : Utterance) : ℚ≥0 :=
  s2WQ l w u / ∑ u', s2WQ l w u'

/-- L₂ world score (eq. 14/16 at k = 2). -/
def l2ScoreQ (u : Utterance) (w : World) : ℚ≥0 := ∑ l, s2Q l w u

/-- L₂ lexicon score (eq. 14 at k = 2). -/
def l2LatScoreQ (u : Utterance) (l : Lex) : ℚ≥0 := ∑ w, s2Q l w u

/-! ### Distributions -/

/-- Joint-listener world posterior (eq. 16). -/
noncomputable def l1PMF (u : Utterance) : PMF World :=
  PMF.ofScores .uniform (l1ScoreQ u)

/-- Joint-listener lexicon posterior (eq. 14). -/
noncomputable def l1LatPMF (u : Utterance) : PMF Lex :=
  PMF.ofScores .uniform (l1LatScoreQ u)

/-- Speaker (eq. 11). -/
noncomputable def s1PMF (l : Lex) (w : World) : PMF Utterance :=
  PMF.ofScores .uniform (s1WQ l w)

/-- Endorsement speaker: renormalizes the L₁ world posterior per world. -/
noncomputable def s2PMF (w : World) : PMF Utterance :=
  PMF.ofScores .uniform (fun u => l1Q u w)

/-- L₂ world posterior (eq. 16 at k = 2). -/
noncomputable def l2PMF (u : Utterance) : PMF World :=
  PMF.ofScores .uniform (l2ScoreQ u)

/-- L₂ lexicon posterior (eq. 14 at k = 2). -/
noncomputable def l2LatPMF (u : Utterance) : PMF Lex :=
  PMF.ofScores .uniform (l2LatScoreQ u)

/-- Marginal expertise speaker (eq. 17 at k = 2, uniform lexicon prior). -/
noncomputable def s2ExpPMF (w : World) : PMF Utterance :=
  PMF.ofScores .uniform (fun u => l2ScoreQ u w)

/-! ### Structural properties -/

/-- Under `syn`, "A or X" is extensionally "A": the Hurford violation. -/
theorem syn_AorX_eq_A :
    ∀ w, truth .syn .AorX w = truth .syn .A w := by decide

/-- Under `excl`, A and X are disjoint: the exhaustified reading that
rescues the disjunction. -/
theorem excl_disjoint :
    ¬∃ w, truth .excl .A w = true ∧ truth .excl .X w = true := by decide

/-- Under `excl`, "A or X" is the only non-null utterance true at `w₁₂`. -/
theorem excl_w12_AorX_unique :
    truth .excl .AorX .w₁₂ = true ∧
    truth .excl .A .w₁₂ = false ∧
    truth .excl .B .w₁₂ = false ∧
    truth .excl .X .w₁₂ = false := by decide

/-- Under `syn`, "A or X" is false at `w₁₂` (it reduces to A, which fails
at w₂). -/
theorem syn_w12_AorX_false :
    truth .syn .AorX .w₁₂ = false := by decide

/-- Under `base`, "A or X" is true at `w₁₂`. -/
theorem base_w12_AorX_true :
    truth .base .AorX .w₁₂ = true := by decide

/-! ### Uncertainty implicature

Hearing "A or X", L₁ infers the speaker is uncertain (w₁₂): they could
have said "A" knowing w₁ or "X" knowing w₂ (under `excl`), so the
disjunction signals commitment to neither disjunct. -/

/-- w₁₂ > w₁ given "A or X". -/
theorem uncertainty_w12_vs_w1 : l1PMF .AorX .w₁ < l1PMF .AorX .w₁₂ :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- w₁₂ > w₂ given "A or X". -/
theorem uncertainty_w12_vs_w2 : l1PMF .AorX .w₂ < l1PMF .AorX .w₁₂ :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- w₁ > w₂ given "A or X": at w₁ the natural disjunct A operates, at w₂
only the refined excl-X does. -/
theorem uncertainty_w1_vs_w2 : l1PMF .AorX .w₂ < l1PMF .AorX .w₁ :=
  PMF.ofScores_lt _ (by decide +kernel)

/-! ### Lexicon inference

For "A or X" the `excl` lexicon dominates — it makes the disjunction
maximally informative — while `syn` renders it redundant (the Hurford
violation) and is dispreferred. -/

/-- excl > base for "A or X". -/
theorem lexicon_excl_vs_base : l1LatPMF .AorX .base < l1LatPMF .AorX .excl :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- excl > syn for "A or X". -/
theorem lexicon_excl_vs_syn : l1LatPMF .AorX .syn < l1LatPMF .AorX .excl :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- base > syn for "A or X", completing excl > base > syn. -/
theorem lexicon_base_vs_syn : l1LatPMF .AorX .syn < l1LatPMF .AorX .base :=
  PMF.ofScores_lt _ (by decide +kernel)

/-! ### Speaker rationality -/

/-- At w₁₂ the speaker prefers "A or X" over "A" (under `excl`): "A" alone
would signal w₁. -/
theorem s1_w12_AorX_vs_A : s1PMF .excl .w₁₂ .A < s1PMF .excl .w₁₂ .AorX :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- At w₁₂ the speaker prefers "A or X" over "X": "X" alone would signal
w₂. -/
theorem s1_w12_AorX_vs_X : s1PMF .excl .w₁₂ .X < s1PMF .excl .w₁₂ .AorX :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- Knowing w₁, the speaker prefers the bare "A" over the disjunction. -/
theorem s1_w1_A_vs_AorX : s1PMF .excl .w₁ .AorX < s1PMF .excl .w₁ .A :=
  PMF.ofScores_lt _ (by decide +kernel)

/-! ### Endorsement decomposition

Eq. 15's two utility terms as independent components: informativity via
the endorsement speaker `s2PMF` (S₂(u|w) ∝ L₁(w|u)) and expertise via
lexicon signaling (`AorX_signals_excl_vs_A`). With β > 0 the speaker has
both reasons to use the disjunction. -/

/-- Endorsement at w₁₂: "A or X" beats "A" ("A" is false at w₁₂ under
every lexicon). -/
theorem s2_w12_AorX_vs_A : s2PMF .w₁₂ .A < s2PMF .w₁₂ .AorX := PMF.ofScores_lt _ (by decide +kernel)

/-- Endorsement at w₁: the direct "A" beats the disjunction. -/
theorem s2_w1_A_vs_AorX : s2PMF .w₁ .AorX < s2PMF .w₁ .A := PMF.ofScores_lt _ (by decide +kernel)

/-- "A or X" signals the `excl` lexicon more strongly than "A" does (all
lexica agree on "A", so its lexicon posterior is near-uniform). This
asymmetry is what β > 0 amplifies. -/
theorem AorX_signals_excl_vs_A : l1LatPMF .A .excl < l1LatPMF .AorX .excl :=
  PMF.ofScores_lt_cross _ _ (by decide +kernel)

/-! ### The stacked expertise model

Eq. 15, `S₂(m|w,L) ∝ l₁(w|m,L)^α · L₁(L|m)^β · exp(−C(m))`, at Figure 10's
regime α = 2, β = 1, C(or) = 1. -/

/-- L₂ hearing "A or X": w₁₂ > w₁. -/
theorem l2_AorX_w12_vs_w1 : l2PMF .AorX .w₁ < l2PMF .AorX .w₁₂ :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- L₂ hearing "A or X": w₁₂ > w₂. -/
theorem l2_AorX_w12_vs_w2 : l2PMF .AorX .w₂ < l2PMF .AorX .w₁₂ :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- L₂ hearing "A or X": w₁ > w₂. -/
theorem l2_AorX_w1_vs_w2 : l2PMF .AorX .w₂ < l2PMF .AorX .w₁ :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- L₂ lexicon inference: excl > base for "A or X". -/
theorem l2_AorX_excl_vs_base : l2LatPMF .AorX .base < l2LatPMF .AorX .excl :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- L₂ lexicon inference: excl > syn for "A or X". -/
theorem l2_AorX_excl_vs_syn : l2LatPMF .AorX .syn < l2LatPMF .AorX .excl :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- L₂ lexicon inference: base > syn, completing excl > base > syn. -/
theorem l2_AorX_base_vs_syn : l2LatPMF .AorX .syn < l2LatPMF .AorX .base :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- Marginalized S₂ at w₁₂ prefers "A or X" over "A" (p. 436). -/
theorem s2Exp_w12_AorX_vs_A : s2ExpPMF .w₁₂ .A < s2ExpPMF .w₁₂ .AorX :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- Marginalized S₂ at w₁ prefers "A" over the disjunction. -/
theorem s2Exp_w1_A_vs_AorX : s2ExpPMF .w₁ .AorX < s2ExpPMF .w₁ .A :=
  PMF.ofScores_lt _ (by decide +kernel)

end PottsLevy2015
