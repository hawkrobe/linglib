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

* `l1_uncertainty`, `l1_lexicon`: hearing "A or X", the joint listener
  infers speaker uncertainty (w₁₂ > w₁ > w₂) and the exclusivized lexicon
  (excl > base > syn).
* `s1_disjunction_iff_uncertain`: the eq. 11 speaker uses the disjunction
  exactly when uncertain.
* `s2End_disjunction_iff_uncertain`, `AorX_signals_excl_vs_A`: eq. 15's
  informativity and expertise components verified independently.
* `l2_uncertainty`, `l2_lexicon`, `s2Exp_disjunction_iff_uncertain`: the
  same at the stacked expertise level, Figure 10's regime α = 2, β = 1,
  C(or) = 1 (its L₂ margins are .91 > .09 > 0 over worlds and
  .49 > .34 > .17 over lexica; p. 436: "S₂'s preferred message given
  observed state w₁∨w₂ and lexicon L₁ from Figure 10 is A or X").
* `excl_is_base_minus_A`: the `excl` lexicon is exhaustification —
  excl(X) = base(X) ∧ ¬A.

## Implementation notes

α = 2 and β = 1 are natural powers, so each agent is a `PMF.ofScores`
cast of an exact-`ℚ≥0` score function the kernel computes with; the tower
recurses through the score functions. No utterance row is dead (`null` is
true everywhere), so the uniform fallback never fires.
The disjunction cost `exp(−1)` is rationalized as `37/100` (qualitative
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

/-! ### Truth-conditional facts -/

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

/-! ### The agent tower (eqs. 10–17)

Agents are `PMF`s, each with one `ℚ≥0` score function as its computational
face: the tower recurses through the normalized scores (`÷0 = 0`, though
no row here is dead), the `PMF` is their `PMF.ofScores` cast, and
`PMF.ofScores_apply` is the pointwise hom between the two. -/

/-- Speaker scores (eq. 11 at α = 2, uniform world prior, zero cost): the
normalized squared literal listener of eq. 10. -/
def s1Score (l : Lex) (w : World) : Utterance → ℚ≥0 :=
  PMF.normalizeScores fun u => RSA.Score.l0 (truth l) (fun _ => 1) u w ^ 2

/-- Speaker (eq. 11). -/
noncomputable def s1 (l : Lex) (w : World) : PMF Utterance :=
  .ofScores .uniform (s1Score l w)

/-- Fixed-lexicon pragmatic listener (the paper's lowercase l₁, eq. 12):
the speaker renormalized over worlds — Bayes with a uniform prior, at a
single lexicon (Figure 2's "fixed 𝓛" column). -/
def l1FixedScore (l : Lex) (u : Utterance) : World → ℚ≥0 :=
  PMF.normalizeScores fun w => s1Score l w u

/-- Lexical-uncertainty listener over worlds (the paper's uppercase L₁,
eq. 14/16): the per-lexicon normaliser cancels under uniform priors,
leaving `∑ s₁`. -/
def l1Score (u : Utterance) : World → ℚ≥0 :=
  PMF.normalizeScores fun w => ∑ l, s1Score l w u

/-- Joint listener over worlds (eq. 16). -/
noncomputable def l1 (u : Utterance) : PMF World :=
  .ofScores .uniform (l1Score u)

/-- Joint-listener lexicon-posterior scores (eq. 14). -/
def l1LatScore (u : Utterance) : Lex → ℚ≥0 :=
  PMF.normalizeScores fun l => ∑ w, s1Score l w u

/-- Joint listener over lexica (eq. 14). -/
noncomputable def l1Lat (u : Utterance) : PMF Lex :=
  .ofScores .uniform (l1LatScore u)

/-- Disjunction cost factor `exp(−C(m))` with C(or) = 1, rationalized as
`37/100 ≈ exp(−1)`. -/
def disjCost : Utterance → ℚ≥0
  | .AorX => 37/100
  | _ => 1

/-- Expertise-speaker scores (eq. 15 at α = 2, β = 1):
normalized `l₁(w|m,L)² · L₁(L|m) · exp(−C(m))`. -/
def s2Score (l : Lex) (w : World) : Utterance → ℚ≥0 :=
  PMF.normalizeScores fun u => l1FixedScore l u w ^ 2 * l1LatScore u l * disjCost u

/-- Endorsement speaker: the L₁ world posterior renormalized per world
(the informativity component of eq. 15 in isolation). -/
noncomputable def s2End (w : World) : PMF Utterance :=
  .ofScores .uniform fun u => l1Score u w

/-- L₂ scores (eq. 14 at k = 2): summed expertise speakers. At fixed `u`
they are the world-posterior scores; at fixed `w`, the eq. 17
lexicon-marginalized speaker scores. -/
def l2Score (u : Utterance) (w : World) : ℚ≥0 := ∑ l, s2Score l w u

/-- L₂ listener over worlds (eq. 16 at k = 2). -/
noncomputable def l2 (u : Utterance) : PMF World :=
  .ofScores .uniform (l2Score u)

/-- L₂ listener over lexica (eq. 14 at k = 2). -/
noncomputable def l2Lat (u : Utterance) : PMF Lex :=
  .ofScores .uniform fun l => ∑ w, s2Score l w u

/-- Marginal expertise speaker (eq. 17 at k = 2, uniform lexicon prior). -/
noncomputable def s2Exp (w : World) : PMF Utterance :=
  .ofScores .uniform fun u => l2Score u w

/-! ### The L₁ inferences -/

/-- The ignorance implicature: hearing "A or X", L₁ ranks the uncertainty
state on top — w₁₂ > w₁ > w₂. The speaker could have said "A" knowing w₁
or "X" knowing w₂ (under `excl`), so the disjunction signals commitment
to neither disjunct. -/
theorem l1_uncertainty :
    l1 .AorX .w₂ < l1 .AorX .w₁ ∧ l1 .AorX .w₁ < l1 .AorX .w₁₂ :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-- The Hurford rescue: hearing "A or X", L₁ ranks the exclusivized
lexicon on top — excl > base > syn. `excl` makes the disjunction maximally
informative; `syn` makes it redundant. -/
theorem l1_lexicon :
    l1Lat .AorX .syn < l1Lat .AorX .base ∧ l1Lat .AorX .base < l1Lat .AorX .excl :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-! ### Speaker rationality -/

/-- The eq. 11 speaker (under `excl`) uses the disjunction exactly when
uncertain: at w₁₂ it beats both bare disjuncts, while knowing w₁ the bare
"A" wins. -/
theorem s1_disjunction_iff_uncertain :
    s1 .excl .w₁₂ .A < s1 .excl .w₁₂ .AorX ∧
    s1 .excl .w₁₂ .X < s1 .excl .w₁₂ .AorX ∧
    s1 .excl .w₁ .AorX < s1 .excl .w₁ .A :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel),
    PMF.ofScores_lt _ (by decide +kernel)⟩

/-! ### Endorsement decomposition

Eq. 15's two utility terms as independent components: informativity via
the endorsement speaker `s2End` (S₂(u|w) ∝ L₁(w|u)) and expertise via
lexicon signaling. With β > 0 the speaker has both reasons to use the
disjunction. -/

/-- The informativity component alone already selects the disjunction
exactly when uncertain ("A" is false at w₁₂ under every lexicon). -/
theorem s2End_disjunction_iff_uncertain :
    s2End .w₁₂ .A < s2End .w₁₂ .AorX ∧ s2End .w₁ .AorX < s2End .w₁ .A :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-- The expertise component: "A or X" signals the `excl` lexicon more
strongly than "A" does (all lexica agree on "A", so its lexicon posterior
is near-uniform). This asymmetry is what β > 0 amplifies. -/
theorem AorX_signals_excl_vs_A : l1Lat .A .excl < l1Lat .AorX .excl :=
  PMF.ofScores_lt_cross _ _ (by decide +kernel)

/-! ### Predictions at the stacked level (Figure 10) -/

/-- L₂ hearing "A or X" reproduces the uncertainty ordering
w₁₂ > w₁ > w₂ (Figure 10 world margins .91 > .09 > 0). -/
theorem l2_uncertainty :
    l2 .AorX .w₂ < l2 .AorX .w₁ ∧ l2 .AorX .w₁ < l2 .AorX .w₁₂ :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-- L₂ hearing "A or X" reproduces the lexicon ordering excl > base > syn
(Figure 10 lexicon margins .49 > .34 > .17). -/
theorem l2_lexicon :
    l2Lat .AorX .syn < l2Lat .AorX .base ∧ l2Lat .AorX .base < l2Lat .AorX .excl :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-- The eq. 17 marginal speaker uses the disjunction exactly when
uncertain (p. 436). -/
theorem s2Exp_disjunction_iff_uncertain :
    s2Exp .w₁₂ .A < s2Exp .w₁₂ .AorX ∧ s2Exp .w₁ .AorX < s2Exp .w₁ .A :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

end PottsLevy2015
