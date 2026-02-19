import Linglib.Core.DecisionTheory
import Linglib.Theories.Semantics.Questions.Partition
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# NPIs in Questions: Entropy as Strength

Van Rooy (2003): for assertions, strength = informativity; for questions,
strength = entropy. NPIs are licensed when they increase entropy by reducing bias.

## Architecture

All entropy definitions use ℝ-valued `Real.negMulLog` from Mathlib, which gives
`negMulLog(x) = -x * log(x)` with `negMulLog(0) = 0`. Shannon entropy of a
question `H(Q) = ∑_cell negMulLog(P(cell))` where cell probabilities are computed
via `Fintype`-based sums.

- van Rooy (2003). Negative Polarity Items in Questions: Strength as Relevance.
- Shannon (1948). Mathematical Theory of Communication.
- Krifka (1995). The semantics and pragmatics of polarity items.
- Kadmon & Landman (1993). Any.
-/

namespace Semantics.Questions.EntropyNPIs

open Core.DecisionTheory Real BigOperators Finset

section ShannonEntropy

/-- Cell probability: P(cell) = ∑_{w ∈ cell} prior(w). -/
noncomputable def cellProb {W : Type*} [Fintype W] (prior : W → ℝ) (cell : W → Bool) : ℝ :=
  ∑ w : W, if cell w then prior w else 0

/-- Shannon entropy of a question: H(Q) = ∑_cell negMulLog(P(cell)).

Each cell contributes `negMulLog(P(cell)) = -P(cell) · log(P(cell))` to the total.
Degenerate cells (P = 0 or P = 1) contribute 0 by `negMulLog` boundary behavior. -/
noncomputable def questionEntropy {W : Type*} [Fintype W] (prior : W → ℝ)
    (q : Question W) : ℝ :=
  q.foldl (λ acc cell => acc + negMulLog (cellProb prior cell)) 0

/-- Binary entropy function: H(p) = negMulLog(p) + negMulLog(1 - p). -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  negMulLog p + negMulLog (1 - p)

/-- A question is maximally entropic when answers are equiprobable. -/
def isMaximalEntropy {W : Type*} [Fintype W] (prior : W → ℝ)
    (q : Question W) : Prop :=
  ∀ c₁ c₂, c₁ ∈ q → c₂ ∈ q → cellProb prior c₁ = cellProb prior c₂

/-- A question has zero entropy iff it is already settled (one cell has probability 1). -/
def isSettled {W : Type*} [Fintype W] (prior : W → ℝ)
    (q : Question W) : Prop :=
  ∃ c ∈ q, cellProb prior c = 1

/-- Binary entropy is maximized at p = 1/2.

Proof: By strict concavity of `negMulLog` on `[0, 1]`. For any `p ∈ [0, 1]`,
`negMulLog(p) + negMulLog(1-p) ≤ 2 · negMulLog(1/2)` by Jensen's inequality,
with equality iff `p = 1/2`. -/
theorem binaryEntropy_le_half (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryEntropy p ≤ binaryEntropy (1/2) := by
  unfold binaryEntropy
  have hconcave := Real.concaveOn_negMulLog
  have hp_mem : p ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hp0
  have hq_mem : 1 - p ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  -- concaveOn_negMulLog.2 : x ∈ Ici 0 → y ∈ Ici 0 → 0 ≤ a → 0 ≤ b → a + b = 1
  --   → a • negMulLog x + b • negMulLog y ≤ negMulLog (a • x + b • y)
  have h := hconcave.2 hp_mem hq_mem (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 + 1 / 2 = 1 by ring)
  simp only [smul_eq_mul] at h
  have hmid : (1 : ℝ) / 2 * p + 1 / 2 * (1 - p) = 1 / 2 := by ring
  rw [hmid] at h
  -- h : 1/2 * negMulLog(p) + 1/2 * negMulLog(1-p) ≤ negMulLog(1/2)
  show negMulLog p + negMulLog (1 - p) ≤ negMulLog (1 / 2) + negMulLog (1 - 1 / 2)
  have h1half : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
  rw [h1half]
  linarith

/-- Binary entropy is maximal at equiprobable: for any binary partition,
    `H([½, ½]) ≥ H([p, 1−p])`.

Proof: `H([pos, neg]) = binaryEntropy(P(pos)) ≤ binaryEntropy(½)` by concavity. -/
theorem entropy_maximal_equiprobable {W : Type*} [Fintype W] (prior : W → ℝ)
    (pos neg : W → Bool)
    (hEqui : cellProb prior pos = cellProb prior neg)
    (hPartition : cellProb prior pos + cellProb prior neg = 1)
    (pos' neg' : W → Bool)
    (hPartition' : cellProb prior pos' + cellProb prior neg' = 1)
    (hBound' : 0 ≤ cellProb prior pos' ∧ cellProb prior pos' ≤ 1) :
    questionEntropy prior [pos, neg] ≥ questionEntropy prior [pos', neg'] := by
  unfold questionEntropy
  simp only [List.foldl_cons, List.foldl_nil, zero_add]
  have hHalf : cellProb prior pos = 1 / 2 := by linarith
  have hHalfNeg : cellProb prior neg = 1 / 2 := by linarith
  rw [hHalf, hHalfNeg]
  have hNeg' : cellProb prior neg' = 1 - cellProb prior pos' := by linarith
  rw [hNeg']
  have h := binaryEntropy_le_half (cellProb prior pos') hBound'.1 hBound'.2
  unfold binaryEntropy at h
  linarith

/-- Binary entropy increases when probability moves closer to ½.

If `p ≤ q ≤ 1 - p` (q is between p and its "mirror" 1-p), then
`binaryEntropy(q) ≥ binaryEntropy(p)`. This is the mathematical core of
van Rooy's argument: reducing bias increases entropy.

Proof: write `q = (1−t)p + t(1−p)` where `t = (q−p)/(1−2p)`.
By concavity of `negMulLog`, applied to both `q` and `1−q`:
- `negMulLog(q) ≥ (1−t)·negMulLog(p) + t·negMulLog(1−p)`
- `negMulLog(1−q) ≥ (1−t)·negMulLog(1−p) + t·negMulLog(p)`
Summing gives `binaryEntropy(q) ≥ binaryEntropy(p)`. -/
theorem binaryEntropy_mono_of_closer_to_half (p q : ℝ)
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1p : q ≤ 1 - p) (hp_half : p < 1 / 2) :
    negMulLog p + negMulLog (1 - p) ≤ negMulLog q + negMulLog (1 - q) := by
  set t := (q - p) / (1 - 2 * p) with ht_def
  have h12p : (0 : ℝ) < 1 - 2 * p := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (le_of_lt h12p)
  have ht1 : t ≤ 1 := by rw [div_le_one h12p]; linarith
  have h1t0 : 0 ≤ 1 - t := by linarith
  have htmul : t * (1 - 2 * p) = q - p :=
    div_mul_cancel₀ (q - p) (ne_of_gt h12p)
  have hq_combo : (1 - t) * p + t * (1 - p) = q := by linarith
  have h1q_combo : (1 - t) * (1 - p) + t * p = 1 - q := by linarith
  have hp_mem : p ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hp0
  have h1p_mem : (1 - p) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have hc1 := concaveOn_negMulLog.2 hp_mem h1p_mem h1t0 ht0
    (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul] at hc1
  rw [hq_combo] at hc1
  have hc2 := concaveOn_negMulLog.2 h1p_mem hp_mem h1t0 ht0
    (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul] at hc2
  rw [h1q_combo] at hc2
  linarith

end ShannonEntropy

section BiasReduction

/-- A polar question is biased toward negative if P(neg) > P(pos). -/
def isBiasedNegative {W : Type*} [Fintype W] (prior : W → ℝ)
    (positive negative : W → Bool) : Prop :=
  cellProb prior negative > cellProb prior positive

/-- Degree of bias: |P(pos) - P(neg)|. -/
noncomputable def biasDegree {W : Type*} [Fintype W] (prior : W → ℝ)
    (positive negative : W → Bool) : ℝ :=
  |cellProb prior positive - cellProb prior negative|

/-- NPI effect on a polar question: widens the positive answer's domain -/
structure NPIQuestionEffect (W : Type*) where
  /-- Positive answer without NPI (e.g., "someone called") -/
  posWithoutNPI : W → Bool
  /-- Positive answer with NPI (e.g., "anyone called") -/
  posWithNPI : W → Bool
  /-- NPI widens domain: withNPI ⊇ withoutNPI -/
  widens : ∀ w, posWithoutNPI w → posWithNPI w

/-- Negative answer is complement of positive -/
def NPIQuestionEffect.negWithoutNPI {W : Type*} (e : NPIQuestionEffect W) : W → Bool :=
  λ w => !e.posWithoutNPI w

def NPIQuestionEffect.negWithNPI {W : Type*} (e : NPIQuestionEffect W) : W → Bool :=
  λ w => !e.posWithNPI w

/-- Question without NPI -/
def NPIQuestionEffect.questionWithoutNPI {W : Type*} (e : NPIQuestionEffect W) : Question W :=
  [e.posWithoutNPI, e.negWithoutNPI]

/-- Question with NPI -/
def NPIQuestionEffect.questionWithNPI {W : Type*} (e : NPIQuestionEffect W) : Question W :=
  [e.posWithNPI, e.negWithNPI]

/-- NPI increases entropy when question is negatively biased. -/
def npiIncreasesEntropy {W : Type*} [Fintype W] (prior : W → ℝ)
    (e : NPIQuestionEffect W) : Prop :=
  questionEntropy prior e.questionWithNPI ≥
  questionEntropy prior e.questionWithoutNPI

/--
**Van Rooy's Key Result**: When negatively biased, domain widening that reduces
bias increases entropy.

The key hypotheses are:
- **Partition**: both questions' cells sum to 1 (proper probability distributions)
- **Negative bias**: P(pos) < ½ (negative answer is more likely)
- **Widening increases positive prob**: P(pos') ≥ P(pos)
- **Bounded widening**: P(pos') ≤ 1 - P(pos) (widening doesn't overshoot
  past the "mirror" of the original bias)

Under these conditions, `|P(pos') - ½| ≤ |P(pos) - ½|`, so by concavity of
`negMulLog`, `binaryEntropy(P(pos')) ≥ binaryEntropy(P(pos))`.

The proof applies `binaryEntropy_mono_of_closer_to_half`: since P(pos) < ½ and
P(pos) ≤ P(pos') ≤ 1 - P(pos), the widened question has higher binary entropy. -/
theorem npi_increases_entropy_when_negatively_biased {W : Type*} [Fintype W]
    (prior : W → ℝ) (e : NPIQuestionEffect W)
    (hPriorNN : ∀ w, 0 ≤ prior w)
    (hPartW : cellProb prior e.posWithoutNPI + cellProb prior e.negWithoutNPI = 1)
    (hPartN : cellProb prior e.posWithNPI + cellProb prior e.negWithNPI = 1)
    (hBiased : cellProb prior e.posWithoutNPI < 1 / 2)
    (hWider : cellProb prior e.posWithNPI ≥ cellProb prior e.posWithoutNPI)
    (hBoundedWidening : cellProb prior e.posWithNPI ≤ 1 - cellProb prior e.posWithoutNPI) :
    npiIncreasesEntropy prior e := by
  unfold npiIncreasesEntropy questionEntropy NPIQuestionEffect.questionWithNPI
    NPIQuestionEffect.questionWithoutNPI
  simp only [List.foldl_cons, List.foldl_nil, zero_add]
  have hNegW : cellProb prior e.negWithoutNPI = 1 - cellProb prior e.posWithoutNPI := by linarith
  have hNegN : cellProb prior e.negWithNPI = 1 - cellProb prior e.posWithNPI := by linarith
  rw [hNegW, hNegN]
  have hPosNN : 0 ≤ cellProb prior e.posWithoutNPI := by
    unfold cellProb; apply Finset.sum_nonneg; intro i _; split_ifs <;> simp [hPriorNN]
  exact binaryEntropy_mono_of_closer_to_half _ _ hPosNN hWider hBoundedWidening hBiased

/-- Converse: In positively biased questions, widening the positive cell moves
further from balance, DECREASING entropy. NPIs are not licensed.

Proof: By symmetry of `binaryEntropy`, this reduces to the negatively biased
case on the complementary probabilities. Since P(neg) < ½ and P(neg') ≤ P(neg),
the neg probabilities move AWAY from ½, decreasing entropy. -/
theorem ppi_increases_entropy_when_positively_biased {W : Type*} [Fintype W]
    (prior : W → ℝ) (e : NPIQuestionEffect W)
    (hPriorNN : ∀ w, 0 ≤ prior w)
    (hPartW : cellProb prior e.posWithoutNPI + cellProb prior e.negWithoutNPI = 1)
    (hPartN : cellProb prior e.posWithNPI + cellProb prior e.negWithNPI = 1)
    (hBiased : cellProb prior e.posWithoutNPI > 1 / 2)
    (hWider : cellProb prior e.posWithNPI ≥ cellProb prior e.posWithoutNPI) :
    questionEntropy prior e.questionWithNPI ≤
    questionEntropy prior e.questionWithoutNPI := by
  unfold questionEntropy NPIQuestionEffect.questionWithNPI
    NPIQuestionEffect.questionWithoutNPI
  simp only [List.foldl_cons, List.foldl_nil, zero_add]
  have hNegW : cellProb prior e.negWithoutNPI = 1 - cellProb prior e.posWithoutNPI := by linarith
  have hNegN : cellProb prior e.negWithNPI = 1 - cellProb prior e.posWithNPI := by linarith
  rw [hNegW, hNegN]
  -- Goal: negMulLog(q) + negMulLog(1-q) ≤ negMulLog(p) + negMulLog(1-p)
  -- where p = cellProb posWithoutNPI, q = cellProb posWithNPI, p ≤ q, p > 1/2
  -- By binaryEntropy_mono_of_closer_to_half on (1-q) and (1-p):
  -- 1-q ≤ 1-p < 1/2, and 1-p ≤ 1-(1-p) = p, so the "mirror" bound holds trivially
  -- negMulLog(1-p) + negMulLog(p) ≤ negMulLog(1-q)... wait, that's wrong direction
  -- Actually: 1-q ≤ 1-p < 1/2. We need binaryEntropy(1-p) ≥ binaryEntropy(1-q).
  -- But binaryEntropy is symmetric: binaryEntropy(x) = binaryEntropy(1-x), so
  -- binaryEntropy(p) = binaryEntropy(1-p) ≥ binaryEntropy(1-q) = binaryEntropy(q).
  -- Use mono lemma: p' = 1-q, q' = 1-p, p' ≤ q' ≤ 1-p' = q.
  have hNegNPI_nn : 0 ≤ cellProb prior e.negWithNPI := by
    unfold cellProb; apply Finset.sum_nonneg; intro i _; split_ifs <;> simp [hPriorNN]
  have hPosLeOne : cellProb prior e.posWithNPI ≤ 1 := by linarith
  have h := binaryEntropy_mono_of_closer_to_half
    (1 - cellProb prior e.posWithNPI) (1 - cellProb prior e.posWithoutNPI)
    (by linarith) (by linarith) (by linarith) (by linarith)
  -- h has 1-(1-x) terms; simplify to x
  simp only [sub_sub_cancel] at h
  linarith


/-!
## Entropy Properties

Non-negativity and reduction to binary entropy.

Note: Van Rooy (2003, Section 5.3) shows that entropy equals expected utility
for the log-scoring decision problem, grounding the entropy measure in decision
theory. A formal bridge to the ℚ-valued `questionUtility` in `Core.DecisionTheory`
requires ℝ-valued decision theory infrastructure.
-/

/-- Question entropy is non-negative when cell probabilities are in [0, 1].

Each cell contributes `negMulLog(P(c)) ≥ 0` by `negMulLog_nonneg`, and the
foldl sum of non-negative terms is non-negative. -/
theorem questionEntropy_nonneg {W : Type*} [Fintype W] (prior : W → ℝ)
    (q : Question W)
    (hBound : ∀ c ∈ q, 0 ≤ cellProb prior c ∧ cellProb prior c ≤ 1) :
    0 ≤ questionEntropy prior q := by
  unfold questionEntropy
  suffices h : ∀ (cs : List (W → Bool)) (init : ℝ), (∀ c ∈ cs, 0 ≤ cellProb prior c ∧ cellProb prior c ≤ 1) →
      0 ≤ init →
      0 ≤ cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell)) init from
    h q 0 hBound le_rfl
  intro cs
  induction cs with
  | nil => intro init _ h; exact h
  | cons c cs ih =>
    intro init hcs hinit
    simp only [List.foldl_cons]
    apply ih _ (λ c' hc' => hcs c' (List.mem_cons_of_mem c hc'))
    have hnn := negMulLog_nonneg (hcs c List.mem_cons_self).1 (hcs c List.mem_cons_self).2
    linarith

/-- For binary partitions, question entropy reduces to the binary entropy function.

`H([pos, neg]) = binaryEntropy(P(pos))` when `P(pos) + P(neg) = 1`. -/
theorem questionEntropy_binary {W : Type*} [Fintype W] (prior : W → ℝ)
    (pos neg : W → Bool)
    (hPartition : cellProb prior pos + cellProb prior neg = 1) :
    questionEntropy prior [pos, neg] = binaryEntropy (cellProb prior pos) := by
  unfold questionEntropy binaryEntropy
  simp only [List.foldl_cons, List.foldl_nil, zero_add]
  have hNeg : cellProb prior neg = 1 - cellProb prior pos := by linarith
  rw [hNeg]


/-!
## Rhetorical Questions and Even-NPIs

Strong NPIs (lift a finger, bat an eye) create rhetorical readings because:
1. They denote MINIMAL scalar values
2. They share a presupposition with EVEN:
   "For all non-minimal alternatives, the question is already settled"

Van Rooy's analysis:
- If alternatives are settled, only the minimal value is questionable
- But if minimal value is least likely to be true, only negative answer reasonable
- This creates rhetorical force
-/

/-- A strong NPI has EVEN-like presupposition. -/
structure StrongNPIEffect (W : Type*) extends NPIQuestionEffect W where
  /-- The NPI denotes a minimal scalar value -/
  isMinimal : True  -- Placeholder for scalar structure
  /-- Set of non-minimal alternatives -/
  alternatives : List (W → Bool)
  /-- Presupposition: all alternatives are settled (known false or true) -/
  alternativesSettled : ∀ alt ∈ alternatives, ∀ w, alt w ∨ ¬alt w

/-- A question is rhetorical if it has near-zero entropy. -/
def isRhetorical {W : Type*} [Fintype W] (prior : W → ℝ)
    (q : Question W) (threshold : ℝ := 1/10) : Prop :=
  questionEntropy prior q < threshold

/-- **Theorem**: Strong NPIs create rhetorical readings.

When a strong NPI is used in a question and the positive cell has probability
`P(pos) ≤ ε ≤ ½`, the question entropy is bounded by `binaryEntropy(ε)`.
Since `binaryEntropy(0) = 0` and `binaryEntropy` is continuous and increasing
on `[0, ½]`, small `ε` gives small entropy — a rhetorical reading.

The proof reduces to `binaryEntropy` being monotone on `[0, ½]`:
`questionEntropy [pos, neg] = binaryEntropy(P(pos)) ≤ binaryEntropy(ε)`.

The proof applies `binaryEntropy_mono_of_closer_to_half` when P(pos) < ½,
and handles the degenerate case P(pos) = ½ (forcing ε = ½) separately. -/
theorem strong_npi_creates_rhetorical {W : Type*} [Fintype W]
    (prior : W → ℝ) (e : StrongNPIEffect W) (ε : ℝ)
    (hPartition : cellProb prior e.posWithNPI + cellProb prior e.negWithNPI = 1)
    (hPosProb : cellProb prior e.posWithNPI ≤ ε)
    (hPosNN : 0 ≤ cellProb prior e.posWithNPI)
    (hεhalf : ε ≤ 1 / 2) :
    questionEntropy prior e.questionWithNPI ≤ binaryEntropy ε := by
  unfold questionEntropy NPIQuestionEffect.questionWithNPI binaryEntropy
  simp only [List.foldl_cons, List.foldl_nil, zero_add]
  have hNeg : cellProb prior e.negWithNPI = 1 - cellProb prior e.posWithNPI := by linarith
  rw [hNeg]
  by_cases hlt : cellProb prior e.posWithNPI < 1 / 2
  · exact binaryEntropy_mono_of_closer_to_half _ ε hPosNN hPosProb (by linarith) hlt
  · -- cellProb pos = 1/2 (since cellProb pos ≤ ε ≤ 1/2 and ¬(cellProb pos < 1/2))
    have heq : cellProb prior e.posWithNPI = 1 / 2 := by linarith
    have hεeq : ε = 1 / 2 := by linarith
    rw [heq, hεeq]


/-!
## K&L's Question Strengthening

Kadmon & Landman (1990) propose that stressed "any" strengthens questions:

Q' strengthens Q iff Q is already answered but Q' is still unanswered.

Van Rooy: This is a special case of entropy increase.
- If Q is settled (entropy 0) but Q' is not (entropy > 0)
- Then Q' has higher entropy
- Domain widening achieves this when Q is biased toward negative
-/

/-- K&L's notion: Q' strengthens Q if Q is settled but Q' is open. -/
def klStrengthens {W : Type*} [Fintype W] (prior : W → ℝ)
    (q q' : Question W) : Prop :=
  isSettled prior q ∧ ¬isSettled prior q'

/-- Settled question has zero entropy: if one cell has P = 1, then all cells
have P ∈ {0, 1}, and negMulLog(0) = negMulLog(1) = 0. -/
private theorem foldl_add_negMulLog_eq_zero {W : Type*} [Fintype W]
    (cs : List (W → Bool)) (prior : W → ℝ)
    (init : ℝ) (hinit : init = 0)
    (h : ∀ c ∈ cs, negMulLog (cellProb prior c) = 0) :
    cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell)) init = 0 := by
  induction cs generalizing init with
  | nil => exact hinit
  | cons c cs ih =>
    simp only [List.foldl_cons]
    apply ih (init + negMulLog (cellProb prior c))
    · rw [h c List.mem_cons_self, hinit, add_zero]
    · intro c' hc'; exact h c' (List.mem_cons_of_mem c hc')

/-- foldl of non-negative additions preserves lower bounds. -/
private theorem foldl_add_nonneg_ge_init {W : Type*} [Fintype W]
    (cs : List (W → Bool)) (prior : W → ℝ) (init : ℝ)
    (hnn : ∀ c ∈ cs, 0 ≤ negMulLog (cellProb prior c)) :
    init ≤ cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell)) init := by
  induction cs generalizing init with
  | nil => exact le_refl _
  | cons c cs ih =>
    simp only [List.foldl_cons]
    calc init ≤ init + negMulLog (cellProb prior c) := by
              linarith [hnn c List.mem_cons_self]
      _ ≤ cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell))
            (init + negMulLog (cellProb prior c)) :=
          ih _ (λ c' hc' => hnn c' (List.mem_cons_of_mem c hc'))

/-- foldl of non-negative additions is monotone in init. -/
private theorem foldl_add_mono_init {W : Type*} [Fintype W]
    (cs : List (W → Bool)) (prior : W → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hnn : ∀ c ∈ cs, 0 ≤ negMulLog (cellProb prior c)) :
    cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell)) a ≤
    cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell)) b := by
  induction cs generalizing a b with
  | nil => exact hab
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (by linarith) (λ c' hc' => hnn c' (List.mem_cons_of_mem c hc'))

/-- foldl of non-negative additions with one positive member is positive. -/
private theorem foldl_add_pos_of_mem {W : Type*} [Fintype W]
    (cs : List (W → Bool)) (prior : W → ℝ)
    (c : W → Bool) (hcmem : c ∈ cs)
    (hcpos : 0 < negMulLog (cellProb prior c))
    (hnn : ∀ c' ∈ cs, 0 ≤ negMulLog (cellProb prior c')) :
    0 < cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell)) 0 := by
  induction cs with
  | nil => exact absurd hcmem (by simp)
  | cons c' cs ih =>
    simp only [List.foldl_cons, zero_add]
    rcases List.mem_cons.mp hcmem with rfl | hmem
    · -- c = c', first addition gives > 0, rest preserves via monotonicity
      calc 0 < negMulLog (cellProb prior c) := hcpos
        _ ≤ cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell))
              (negMulLog (cellProb prior c)) :=
            foldl_add_nonneg_ge_init cs prior _ (λ c'' hc'' => hnn c'' (List.mem_cons_of_mem c hc''))
    · -- c ∈ cs; foldl starting from negMulLog(c') ≥ foldl starting from 0 (by monotonicity)
      -- and foldl on cs starting from 0 > 0 (by IH)
      have hcs_pos := ih hmem (λ c'' hc'' => hnn c'' (List.mem_cons_of_mem c' hc''))
      calc 0 < cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell)) 0 := hcs_pos
        _ ≤ cs.foldl (λ acc cell => acc + negMulLog (cellProb prior cell))
              (negMulLog (cellProb prior c')) :=
            foldl_add_mono_init cs prior 0 _ (hnn c' List.mem_cons_self)
              (λ c'' hc'' => hnn c'' (List.mem_cons_of_mem c' hc''))

theorem settled_entropy_zero {W : Type*} [Fintype W] (prior : W → ℝ)
    (q : Question W) (_hSettled : isSettled prior q)
    (_hPriorNN : ∀ w, 0 ≤ prior w)
    (hCellBound : ∀ c ∈ q, cellProb prior c = 0 ∨ cellProb prior c = 1) :
    questionEntropy prior q = 0 := by
  unfold questionEntropy
  apply foldl_add_negMulLog_eq_zero _ _ 0 rfl
  intro c hc
  rcases hCellBound c hc with h0 | h1
  · rw [h0, negMulLog_zero]
  · rw [h1, negMulLog_one]

/-- K&L strengthening implies higher entropy.

When Q is settled (all cells have P ∈ {0,1}), its entropy is 0.
When Q' is not settled, it has some cell with 0 < P < 1, giving entropy > 0. -/
theorem kl_strengthens_implies_higher_entropy {W : Type*} [Fintype W]
    (prior : W → ℝ) (q q' : Question W)
    (hStrengthens : klStrengthens prior q q')
    (hPriorNN : ∀ w, 0 ≤ prior w)
    (hSettledCells : ∀ c ∈ q, cellProb prior c = 0 ∨ cellProb prior c = 1)
    (hOpenCell : ∃ c ∈ q', 0 < cellProb prior c ∧ cellProb prior c < 1)
    (hCellBound : ∀ c ∈ q', 0 ≤ cellProb prior c ∧ cellProb prior c ≤ 1) :
    questionEntropy prior q' > questionEntropy prior q := by
  rw [settled_entropy_zero prior q hStrengthens.1 hPriorNN hSettledCells]
  -- Need to show questionEntropy prior q' > 0
  obtain ⟨c, hcmem, hcpos, hclt⟩ := hOpenCell
  -- negMulLog is positive on (0, 1)
  have hpos : 0 < negMulLog (cellProb prior c) := by
    have hlog_neg : Real.log (cellProb prior c) < 0 := Real.log_neg hcpos hclt
    simp only [negMulLog, neg_mul]
    linarith [neg_pos.mpr (mul_neg_of_pos_of_neg hcpos hlog_neg)]
  -- All cells contribute negMulLog ≥ 0
  have hnn : ∀ c' ∈ q', 0 ≤ negMulLog (cellProb prior c') :=
    λ c' hc' => negMulLog_nonneg (hCellBound c' hc').1 (hCellBound c' hc').2
  unfold questionEntropy
  exact foldl_add_pos_of_mem q' prior c hcmem hpos hnn

/-- Stressed "any" achieves K&L strengthening via domain widening.

If the question without NPI is settled, and widening adds a new world to the
positive cell, then the question with NPI is not settled (the new world moves
probability mass, breaking the P = 1 condition). -/
theorem stressed_any_achieves_kl_strengthening {W : Type*} [Fintype W]
    (prior : W → ℝ) (e : NPIQuestionEffect W)
    (hSettledWithout : isSettled prior e.questionWithoutNPI)
    (hProperWidening : ∃ w, e.posWithNPI w ∧ !e.posWithoutNPI w)
    (hPriorPos : ∀ w, e.posWithNPI w → ¬e.posWithoutNPI w → 0 < prior w)
    (hPriorNN : ∀ w, 0 ≤ prior w)
    (hPriorSum : ∑ w : W, prior w = 1)
    (hNotAllPos : ∃ w, e.negWithNPI w ∧ 0 < prior w) :
    klStrengthens prior e.questionWithoutNPI e.questionWithNPI := by
  constructor
  · exact hSettledWithout
  · -- Need to show ¬isSettled for questionWithNPI = [posWithNPI, negWithNPI]
    intro ⟨c, hcmem, hcprob⟩
    obtain ⟨w, hwpos, hwneg⟩ := hProperWidening
    -- w satisfies posWithNPI but not posWithoutNPI
    have hwneg' : ¬(e.posWithoutNPI w = true) := by
      simp only [Bool.not_eq_true'] at hwneg; exact Bool.eq_false_iff.mp hwneg
    have hw_pos_prior : 0 < prior w := hPriorPos w hwpos hwneg'
    -- c ∈ [posWithNPI, negWithNPI], so c is one of them
    simp only [NPIQuestionEffect.questionWithNPI, List.mem_cons,
               List.mem_nil_iff, or_false] at hcmem
    rcases hcmem with rfl | rfl
    · -- c = posWithNPI has prob 1; contradiction via hNotAllPos
      obtain ⟨w', hw'neg, hw'prior⟩ := hNotAllPos
      have hneg_pos : 0 < cellProb prior e.negWithNPI := by
        unfold cellProb
        have h1 : (if e.negWithNPI w' then prior w' else 0) = prior w' := by
          simp [show e.negWithNPI w' = true from hw'neg]
        have h2 : prior w' ≤ ∑ x : W, if e.negWithNPI x then prior x else 0 := by
          rw [← h1]
          apply Finset.single_le_sum _ (Finset.mem_univ w')
          intro i _; split_ifs <;> [exact hPriorNN i; exact le_refl 0]
        linarith
      have hsum : cellProb prior e.posWithNPI + cellProb prior e.negWithNPI = 1 := by
        unfold cellProb NPIQuestionEffect.negWithNPI
        rw [← hPriorSum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : e.posWithNPI x
        · simp [h]
        · have hf := Bool.eq_false_iff.mpr h; simp [hf]
      linarith
    · -- c = negWithNPI has prob 1; cellProb(posWithNPI) > 0 contradicts sum = 1
      have hpos_pos : 0 < cellProb prior e.posWithNPI := by
        unfold cellProb
        have h1 : (if e.posWithNPI w then prior w else 0) = prior w := by simp [hwpos]
        have h2 : prior w ≤ ∑ x : W, if e.posWithNPI x then prior x else 0 := by
          rw [← h1]
          apply Finset.single_le_sum _ (Finset.mem_univ w)
          intro i _; split_ifs <;> [exact hPriorNN i; exact le_refl 0]
        linarith
      have hsum : cellProb prior e.posWithNPI + cellProb prior e.negWithNPI = 1 := by
        unfold cellProb NPIQuestionEffect.negWithNPI
        rw [← hPriorSum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : e.posWithNPI x
        · simp [h]
        · have hf := Bool.eq_false_iff.mpr h; simp [hf]
      linarith


/-!
## Strength as Relevance: The Unification

Van Rooy's key contribution: a UNIFIED notion of strength.

| Speech Act | Strength Measure | NPI Effect |
|------------|------------------|------------|
| Assertion  | Informativity (entailment) | Wider domain → stronger in DE |
| Question   | Entropy (avg informativity) | Wider domain → less biased |

Both are instances of **utility maximization**:
- Assertions: direct informativity maximization
- Questions: expected informativity (entropy) maximization

The connection to decision theory (Section 5.3) shows this is rational:
agents should choose utterances that maximize expected utility.
-/

/-- The unified strength measure. -/
inductive SpeechAct where
  | assertion : SpeechAct
  | question : SpeechAct

/-- Strength for assertions: surprisal = −log P(φ).

Van Rooy (2003): informativity of an assertion is its surprisal, `-log P(φ)`.
In DE contexts, the assertion is negated, so strength should be computed on the
negated form. Surprisal is strictly decreasing for `P > 0`, so narrower
propositions (lower probability) have higher informativity. -/
noncomputable def assertionStrength {W : Type*} [Fintype W] (prior : W → ℝ)
    (p : W → Bool) : ℝ :=
  -Real.log (cellProb prior p)

/-- Strength for questions: entropy. -/
noncomputable def questionStrength {W : Type*} [Fintype W] (prior : W → ℝ)
    (q : Question W) : ℝ :=
  questionEntropy prior q

/-- NPI licensing condition: increases strength under appropriate polarity/bias.

For assertions in DE contexts (polarity = false), strength is computed on the
NEGATED form: wider domain under negation = narrower negation = more informative.
For questions with negative bias (polarity = false), wider domain increases entropy. -/
def npiLicensed {W : Type*} [Fintype W] (prior : W → ℝ)
    (act : SpeechAct) (e : NPIQuestionEffect W)
    (polarity : Bool) -- true = UE/positive bias, false = DE/negative bias
    : Prop :=
  match act with
  | .assertion =>
    if polarity then
      assertionStrength prior e.posWithNPI ≤
      assertionStrength prior e.posWithoutNPI
    else
      -- DE context: compare negated forms (wider pos ⟹ narrower neg ⟹ more informative)
      assertionStrength prior e.negWithNPI ≥
      assertionStrength prior e.negWithoutNPI
  | .question =>
    if polarity then
      questionStrength prior e.questionWithNPI ≤
      questionStrength prior e.questionWithoutNPI
    else
      questionStrength prior e.questionWithNPI ≥
      questionStrength prior e.questionWithoutNPI

/-- NPI assertion licensing in DE contexts: wider domain under negation narrows
the negated proposition, making it more informative (higher surprisal).

Proof: Since `cellProb negWithNPI ≤ cellProb negWithoutNPI` and `-log` is
order-reversing on `(0, ∞)`, the narrower negation has higher surprisal. -/
theorem npi_assertion_licensed_de {W : Type*} [Fintype W]
    (prior : W → ℝ) (e : NPIQuestionEffect W)
    (hNarrowsNeg : cellProb prior e.negWithNPI ≤ cellProb prior e.negWithoutNPI)
    (hNegPos : 0 < cellProb prior e.negWithNPI) :
    assertionStrength prior e.negWithNPI ≥ assertionStrength prior e.negWithoutNPI := by
  unfold assertionStrength
  have h := Real.log_le_log hNegPos hNarrowsNeg
  linarith

/--
**The Grand Unification**: NPI licensing follows the same principle
for assertions and questions—maximize strength under current polarity/bias.

For assertions: DE context → wider domain under negation is MORE informative → NPI licensed.
  Wider positive domain ⟹ narrower negation ⟹ lower P(neg) ⟹ higher surprisal.
For questions: Negative bias → wider domain increases entropy → NPI licensed.

The hypotheses suffice for both cases:
- **Assertion**: `hNegPos` and `hWider` + partition give `cellProb neg↓ ≤ cellProb neg`,
  then `npi_assertion_licensed_de` applies.
- **Question**: `npi_increases_entropy_when_negatively_biased` applies directly. -/
theorem unified_npi_licensing {W : Type*} [Fintype W]
    (prior : W → ℝ) (e : NPIQuestionEffect W)
    (act : SpeechAct)
    (hPriorNN : ∀ w, 0 ≤ prior w)
    (hPartW : cellProb prior e.posWithoutNPI + cellProb prior e.negWithoutNPI = 1)
    (hPartN : cellProb prior e.posWithNPI + cellProb prior e.negWithNPI = 1)
    (hBiased : cellProb prior e.posWithoutNPI < 1 / 2)
    (hWider : cellProb prior e.posWithNPI ≥ cellProb prior e.posWithoutNPI)
    (hBoundedWidening : cellProb prior e.posWithNPI ≤ 1 - cellProb prior e.posWithoutNPI)
    (hNegPos : 0 < cellProb prior e.negWithNPI) :
    npiLicensed prior act e false := by
  cases act with
  | assertion =>
    simp only [npiLicensed]
    exact npi_assertion_licensed_de prior e (by linarith) hNegPos
  | question =>
    simp only [npiLicensed, questionStrength]
    exact npi_increases_entropy_when_negatively_biased prior e hPriorNN hPartW hPartN
      hBiased hWider hBoundedWidening


/-!
## Wh-Questions (Section 3.1)

Van Rooy notes that wh-questions ARE downward entailing in subject position:

"Who of John, Mary and Sue are sick?" entails
"Who of John and Mary are sick?"

(Every complete answer to the wider question entails an answer to the narrower.)

But this DOESN'T explain NPI licensing in predicate position or polar questions.
That's why we need the entropy-based account.
-/

/-- Wh-question with domain D and predicate P. -/
structure WhQuestion (W Entity : Type*) where
  domain : List Entity
  predicate : Entity → W → Bool

/-- Wh-question entailment: Q entails Q' if every complete answer to Q
determines a complete answer to Q'.

When Q' has a subset domain of Q (Q'.domain ⊆ Q.domain), knowing the
predicate's extension over Q.domain determines its extension over Q'.domain.
This is the sense in which wider wh-questions are stronger. -/
def whQuestionEntails {W Entity : Type*}
    (q q' : WhQuestion W Entity)
    (_hSubset : ∀ e, e ∈ q'.domain → e ∈ q.domain) : Prop :=
  ∀ (w : W), ∀ e ∈ q'.domain,
    q.predicate e w = true → q'.predicate e w = true

/-- Domain widening in wh-subject position is DE when predicates agree.

When Q and Q' share the same predicate and Q'.domain ⊇ Q.domain,
knowing the predicate for all of Q'.domain determines it for Q.domain.
The `hSamePred` hypothesis ensures the predicate is the same function. -/
theorem wh_subject_is_de {W Entity : Type*}
    (q q' : WhQuestion W Entity)
    (hWider : ∀ e, e ∈ q.domain → e ∈ q'.domain)
    (hSamePred : ∀ e w, q.predicate e w = q'.predicate e w) :
    whQuestionEntails q' q hWider := by
  intro w e he hq'
  rw [← hSamePred e w] at hq'
  exact hq'

/-- NPIs licensed in wh-subject position via standard DE reasoning.

The NPI widens the domain (Q'.domain ⊇ Q.domain). In subject position this
is downward-entailing: the wider question entails the narrower one, because
every complete answer to the wider question determines an answer to the
narrower question. Requires predicates to agree. -/
theorem npi_licensed_wh_subject {W Entity : Type*}
    (q q' : WhQuestion W Entity)
    (hWider : ∀ e, e ∈ q.domain → e ∈ q'.domain)
    (hSamePred : ∀ e w, q.predicate e w = q'.predicate e w) :
    whQuestionEntails q' q hWider :=
  wh_subject_is_de q q' hWider hSamePred

end BiasReduction

end Semantics.Questions.EntropyNPIs
