import Linglib.Theories.Pragmatics.RSA.InformationTheory
import Linglib.Theories.Processing.Cost.Profile
import Linglib.Theories.Processing.PredictiveUncertainty.Config

/-!
# Memory-Surprisal Trade-off Framework
@cite{futrell-2019} @cite{hahn-degen-futrell-2021} @cite{zaslavsky-hu-levy-2020}

Core formalization of @cite{hahn-degen-futrell-2021} "Modeling Word and Morpheme
Order as an Efficient Trade-Off of Memory and Surprisal", *Psychological Review*
128(4):726–756.

## Key Idea

Bounded memory forces a trade-off between memory usage (H_M) and processing
difficulty (surprisal S_M). At each time step, the processor stores a lossy
encoding of the past. Better encoding reduces surprisal but costs more memory.
The optimal trade-off forms a convex curve in (H_M, S_M) space.

## Information Locality

The curve's shape is determined by the **mutual information profile** I_t:
how much mutual information exists between the current word and the word
t steps back. Languages that concentrate predictive information locally
(information locality) achieve steeper, more efficient trade-off curves.

## Mathematical Structure

The central mathematical insight is the **marginal rate of substitution**:
at distance t, each bit of surprisal reduction costs exactly (t+1) bits
of memory. This is why information locality matters — short-distance
information is cheap (1 bit of memory per bit of surprisal at t=0),
while long-distance information is expensive ((t+1) bits per bit at
distance t). The increasing marginal rate makes the bound curve convex.

§3 proves the marginal rate theorem and its consequences from the
definitions, without requiring measure theory. The bound itself
(Theorem 1, §4) — that the I_t profile determines the *achievable*
region of (H_M, S_M) pairs — is stated as comprehension postulates
requiring the data processing inequality and chain rule for stationary
processes.

## Connection to DLM

Information locality generalizes dependency length minimization: DLM
minimizes the *structural* distance between syntactically related words,
while information locality minimizes the *information-theoretic* distance
at which predictive information concentrates.

## Sections

- §1: Memory-surprisal framework (MemoryEncoding, averageSurprisal, memoryEntropy)
- §2: Mutual information profile (MutualInfoProfile, surplusSurprisal, memoryCost)
- §3: Marginal analysis (surplus_step, memoryCost_step, marginal_rate)
- §4: Information locality bound (comprehension postulates, Theorem 1)
- §5: Trade-off curve (TradeoffPoint, TradeoffCurve, AUC)
- §6: Concrete profiles and efficiency comparison
- §7: Bridges (rate-distortion, processing model, dependency locality)

-/

namespace Processing.MemorySurprisal

-- ============================================================================
-- §1: Memory-Surprisal Framework
-- ============================================================================

/-! ### Memory Encoding

A memory encoding maps the history of observed words to a finite memory
state. At each time step t, the processor sees word w_t and updates its
memory state m_t = encode(m_{t-1}, w_t). The memory's entropy H_M measures
how much information the processor retains about the past. -/

/-- A memory encoding compresses the past into a finite memory state.

`W` is the word type, `Mem` is the memory state type.
The encoding function takes a memory state and a new word and returns
the updated memory state. -/
structure MemoryEncoding (W : Type) (Mem : Type) where
  /-- Update memory state given a new word -/
  encode : Mem → W → Mem
  /-- Initial memory state (before any words are seen) -/
  initial : Mem

/-- Iterate a `MemoryEncoding` over an entire history to produce the
final memory state. This is the *context-summary function* that, when
paired with a predictor `Mem → FinitePMF (Option W)`, induces a Dirac
`MemoryProcess` (in `Theories.Processing.Memory`). Such a
process is lossless for its own virtual LM
(`MemoryProcess.expectedSurprisal_eq_virtualLM_surprisal`), so
classical surprisal arises *exactly* when memory is encoded
deterministically. -/
def MemoryEncoding.summary {W Mem : Type} (me : MemoryEncoding W Mem)
    (history : List W) : Mem :=
  history.foldl me.encode me.initial

/-- Average surprisal under a memory encoding.

This is the conditional entropy of the next word given the current
memory state: S_M = H(W_t | M_t).

Lower memory → less information about the past → higher surprisal.
When memory is unlimited, S_M = S_∞ (the entropy rate of the language).

Uses `conditionalEntropy` from `Core.InformationTheory`. -/
def averageSurprisal {W Mem : Type} [BEq W] [BEq Mem]
    (joint : List ((Mem × W) × ℚ))
    (marginalMem : List (Mem × ℚ)) : ℚ :=
  RSA.InformationTheory.conditionalEntropy joint marginalMem

/-- Memory entropy: the entropy of the memory state distribution.

H_M = H(M_t), measuring how many bits the processor uses.

Uses `entropy` from `Core.InformationTheory`. -/
def memoryEntropy {Mem : Type} [BEq Mem]
    (memDist : List (Mem × ℚ)) : ℚ :=
  RSA.InformationTheory.entropy memDist

-- ============================================================================
-- §2: Mutual Information Profile
-- ============================================================================

/-! ### Mutual Information Profile

The mutual information profile I_t measures how much information
the word at position n provides about the word at position n + t
(at distance t). This determines the shape of the memory-surprisal
trade-off curve.

Key insight: I_t = S_t - S_{t+1}, where S_t is the surprisal when
the processor remembers only t steps of context. So I_t measures
the *marginal value* of remembering one more step.

The profile connects to `Core.InformationTheory.mutualInformation`:
each I_t is I(W_n; W_{n+t}), the mutual information between words
at distance t in the stationary process. -/

/-- Mutual information at distance t between words.

I_t represents how much mutual information exists between a word and
the word t steps back. Higher I_t at small t means information is
concentrated locally (good for memory-efficient processing).

Stored as I_t × 1000 for decidable computation. -/
structure MutualInfoProfile where
  /-- Name for this profile (e.g., "English", "Japanese", "Baseline") -/
  name : String
  /-- I_t × 1000 for distances t = 1, 2, 3,... -/
  values : List Nat
  deriving Repr, DecidableEq

/-- Sum of I_t values (total predictive information × 1000). -/
def MutualInfoProfile.totalInfo (p : MutualInfoProfile) : Nat :=
  p.values.foldl (· + ·) 0

/-- A profile is **information-local with bound `L`** if all predictive
information lies within distance `L`, i.e., I_t = 0 for t ≥ L.

This is the information-theoretic analog of a dependency-length bound:
short structural dependencies make I_t decay rapidly, so a syntax with
maximum dependency length L produces a profile that is local with that
same bound. -/
def MutualInfoProfile.IsLocal (p : MutualInfoProfile) (L : Nat) : Prop :=
  ∀ i (h : i < p.values.length), L ≤ i → p.values[i] = 0

/-- Surplus surprisal when the processor remembers T steps of context:
the predictive information lost beyond the memory window.
Equals Σ_{t≥T} I_t (the tail sum of the profile). -/
def MutualInfoProfile.surplusSurprisal (p : MutualInfoProfile) (T : Nat) : Nat :=
  (p.values.drop T).foldl (· + ·) 0

/-- Weighted prefix sum: Σ_{i<|l|} (t₀+i+1)·l[i].

Non-accumulator formulation for easier proofs. Structurally recursive
on the list, so properties follow directly by induction. -/
def weightedPrefixSum : List Nat → Nat → Nat
  | [], _ => 0
  | it :: rest, t => (t + 1) * it + weightedPrefixSum rest (t + 1)

/-- Memory cost of remembering T steps of context: Σ_{t=0}^{T-1} (t+1)·I_t.
This is the prefix of the weighted sum up to distance T. -/
def MutualInfoProfile.memoryCost (p : MutualInfoProfile) (T : Nat) : Nat :=
  weightedPrefixSum (p.values.take T) 0

/-- Weighted sum Σ (t+1)·I_t (total memory cost × 1000).

This is the memory cost of storing the entire profile: `memoryCost p p.values.length`.
Languages with lower weighted sums concentrate information
at shorter distances. -/
def MutualInfoProfile.weightedSum (p : MutualInfoProfile) : Nat :=
  weightedPrefixSum p.values 0

-- ============================================================================
-- §3: Marginal Analysis of the Trade-off Bound
-- ============================================================================

/-! ### Marginal Analysis

The trade-off bound maps memory capacity T to a point
(memoryCost(T), surplusSurprisal(T)). As T increases by 1:
- Surplus surprisal decreases by I_T (one more distance is remembered)
- Memory cost increases by (T+1)·I_T (the weight of that distance)

The ratio — (T+1) bits of memory per bit of surprisal reduction — is
the **marginal rate of substitution**. It increases with T, which is
why the bound curve is convex: short-distance information is cheap,
long-distance information is expensive.

This is the mathematical core of the information locality argument.
Languages that concentrate I_t at small t exploit the "cheap" region
of the curve, achieving low surprisal without high memory cost. -/

-- Helper: foldl with addition shifts the accumulator
private theorem foldl_add_shift (l : List Nat) (a : Nat) :
    l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (a + x), ih (0 + x)]
    omega

-- Helper: weightedPrefixSum distributes over append
private theorem weightedPrefixSum_append (l₁ l₂ : List Nat) (t₀ : Nat) :
    weightedPrefixSum (l₁ ++ l₂) t₀ =
    weightedPrefixSum l₁ t₀ + weightedPrefixSum l₂ (t₀ + l₁.length) := by
  induction l₁ generalizing t₀ with
  | nil => simp [weightedPrefixSum]
  | cons x xs ih =>
    simp only [List.cons_append, weightedPrefixSum, List.length_cons]
    rw [ih (t₀ + 1)]
    have : t₀ + 1 + xs.length = t₀ + (xs.length + 1) := by omega
    rw [this]; omega

-- Helper: take extends by one element (unwrapped from Option)
private theorem take_succ_eq_append {α : Type} (l : List α) (n : Nat) (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l[n]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp [Option.toList]

/-- **Surplus step**: stepping from capacity T to T+1 reduces surplus
surprisal by exactly I_T.

`surplusSurprisal(T) = I_T + surplusSurprisal(T+1)` -/
theorem surplus_step (p : MutualInfoProfile) (T : Nat) (hT : T < p.values.length) :
    p.surplusSurprisal T = p.values[T] + p.surplusSurprisal (T + 1) := by
  simp only [MutualInfoProfile.surplusSurprisal]
  rw [List.drop_eq_getElem_cons hT]
  simp only [List.foldl]
  rw [foldl_add_shift]
  omega

/-- **Memory cost step**: stepping from capacity T to T+1 increases
memory cost by exactly (T+1)·I_T.

`memoryCost(T+1) = memoryCost(T) + (T+1)·I_T` -/
theorem memoryCost_step (p : MutualInfoProfile) (T : Nat) (hT : T < p.values.length) :
    p.memoryCost (T + 1) = p.memoryCost T + (T + 1) * p.values[T] := by
  simp only [MutualInfoProfile.memoryCost]
  rw [take_succ_eq_append p.values T hT, weightedPrefixSum_append]
  congr 1
  have hlen : (List.take T p.values).length = T := by
    rw [List.length_take]; exact Nat.min_eq_left (le_of_lt hT)
  simp [weightedPrefixSum, hlen]

/-- **Marginal rate of substitution**: at distance T, each bit of
surprisal reduction costs exactly (T+1) bits of memory.

This is the deep content of the information locality argument.
The marginal memory cost is `(T+1) * I_T`, and the marginal
surprisal reduction is `I_T`, so the cost ratio is `T+1`.

Short-distance information (small T) is cheap: 1 bit of memory per
bit of surprisal at T=0. Long-distance information is expensive:
(T+1) bits of memory per bit of surprisal at distance T.

This increasing cost is why information locality matters:
languages that concentrate I_t at small t exploit the cheap
end of the curve. -/
theorem marginal_rate (p : MutualInfoProfile) (T : Nat) (hT : T < p.values.length) :
    p.memoryCost (T + 1) - p.memoryCost T =
    (T + 1) * (p.surplusSurprisal T - p.surplusSurprisal (T + 1)) := by
  rw [memoryCost_step p T hT, surplus_step p T hT]
  have h1 : p.memoryCost T + (T + 1) * p.values[T] - p.memoryCost T =
    (T + 1) * p.values[T] := by omega
  have h2 : p.values[T] + p.surplusSurprisal (T + 1) - p.surplusSurprisal (T + 1) =
    p.values[T] := by omega
  rw [h1, h2]

/-- Surplus at capacity 0 equals total information: when the processor
remembers nothing, all predictive information is lost. -/
theorem surplus_zero (p : MutualInfoProfile) :
    p.surplusSurprisal 0 = p.totalInfo := by
  simp [MutualInfoProfile.surplusSurprisal, MutualInfoProfile.totalInfo, List.drop]

/-- Surplus at full capacity is zero: when the processor remembers
everything, no predictive information is lost. -/
theorem surplus_full (p : MutualInfoProfile) :
    p.surplusSurprisal p.values.length = 0 := by
  simp [MutualInfoProfile.surplusSurprisal, List.drop_length]

/-- Memory cost at capacity 0 is zero: remembering nothing costs nothing. -/
theorem memoryCost_zero (p : MutualInfoProfile) :
    p.memoryCost 0 = 0 := by
  simp [MutualInfoProfile.memoryCost, weightedPrefixSum, List.take]

/-- Memory cost at full capacity equals the weighted sum. -/
theorem memoryCost_full (p : MutualInfoProfile) :
    p.memoryCost p.values.length = p.weightedSum := by
  simp [MutualInfoProfile.memoryCost, MutualInfoProfile.weightedSum, List.take_length]

/-- The marginal rate of substitution (T+1) is strictly increasing:
each additional step of memory is more expensive per unit of surprisal
reduction than the last. This makes the bound curve convex. -/
theorem marginal_rate_increasing (T₁ T₂ : Nat) (h : T₁ < T₂) :
    T₁ + 1 < T₂ + 1 := by omega

-- Helper: foldl with addition starting from `0 + x` equals `x + foldl 0`.
private theorem foldl_cons_eq_add (x : Nat) (xs : List Nat) :
    (x :: xs).foldl (· + ·) 0 = x + xs.foldl (· + ·) 0 := by
  show xs.foldl (· + ·) (0 + x) = x + xs.foldl (· + ·) 0
  rw [Nat.zero_add, foldl_add_shift]

-- Helper: a weighted-prefix-sum over a list whose entries past the
-- L-bound are zero is bounded by `L · sum(list)`.
private theorem weightedPrefixSum_local_bound
    (l : List Nat) (L t₀ : Nat)
    (h_zero : ∀ i (hi : i < l.length), L ≤ t₀ + i → l[i] = 0) :
    weightedPrefixSum l t₀ ≤ L * l.foldl (· + ·) 0 := by
  induction l generalizing t₀ with
  | nil => simp [weightedPrefixSum]
  | cons x xs ih =>
    simp only [weightedPrefixSum]
    have ih_app : weightedPrefixSum xs (t₀ + 1) ≤ L * xs.foldl (· + ·) 0 := by
      apply ih
      intro i hi hL
      have h_at_succ : i + 1 < (x :: xs).length := by
        simp [List.length_cons]; omega
      have hL' : L ≤ t₀ + (i + 1) := by omega
      have heq := h_zero (i + 1) h_at_succ hL'
      simpa using heq
    by_cases hcase : t₀ + 1 ≤ L
    · have h1 : (t₀ + 1) * x ≤ L * x := Nat.mul_le_mul_right x hcase
      rw [foldl_cons_eq_add, Nat.mul_add]
      omega
    · have hLt : L ≤ t₀ + 0 := by omega
      have h_at_0 : 0 < (x :: xs).length := by simp
      have hx_zero : x = 0 := by
        have := h_zero 0 h_at_0 hLt
        simpa using this
      rw [hx_zero, foldl_cons_eq_add]
      simp only [Nat.mul_zero, Nat.zero_add]
      simpa using ih_app

/-- **Information locality bounds memory cost.**

For any information-local profile with bound `L` (i.e., I_t = 0 for
t ≥ L), the memory-cost weighted sum is at most `L · totalInfo` —
at most `L` bits of memory per bit of total predictive information.

This is the information-theoretic analog of dependency length
minimization: when syntactic dependencies are short (capped at length
`L`), the corresponding I_t profile is local with bound `L`, and the
memory cost grows at most linearly in `L`. The memory-surprisal
trade-off (@cite{hahn-degen-futrell-2021}) is thus *strictly more
general* than DLM (@cite{futrell-mahowald-gibson-2015}): DLM optimizes
the structural distance `L`; information locality optimizes the entire
I_t profile, of which DLM is the bound-`L` special case. -/
theorem MutualInfoProfile.weightedSum_le_of_isLocal
    (p : MutualInfoProfile) (L : Nat) (h : p.IsLocal L) :
    p.weightedSum ≤ L * p.totalInfo :=
  weightedPrefixSum_local_bound p.values L 0
    (fun i hi hL => h i hi (by simpa using hL))

-- ============================================================================
-- §4: Information Locality Bound (Theorem 1)
-- ============================================================================

/-! ### Information Locality Bound

**Theorem 1** of @cite{hahn-degen-futrell-2021} establishes that the mutual
information profile I_t determines a lower bound on the achievable
memory-surprisal trade-off. Specifically, for any memory encoding with
capacity T:

  H_M ≤ Σ_{t≤T} t · I_t       (memory cost of storing T steps)
  S_M ≥ S_∞ + Σ_{t>T} I_t     (surplus surprisal from forgetting)

The proof requires three comprehension postulates about the underlying
stationary ergodic process, which we cannot derive without measure theory:

1. **Data Processing Inequality**: Processing (lossy compression) cannot
   increase mutual information. If X → M → Y is a Markov chain, then
   I(X;Y) ≤ I(X;M). This bounds how much information the memory state
   can preserve about the past.

2. **Chain Rule for Mutual Information**: I(X; Y₁, Y₂) = I(X; Y₁) + I(X; Y₂|Y₁).
   This decomposes the total information into distance-specific contributions I_t,
   enabling the per-distance accounting that underlies the marginal rate theorem.

3. **Memory Entropy Bound**: H(M_t) ≥ I(M_t; W_{t-1}, ..., W_{t-T}).
   The memory must have enough entropy to carry the mutual information
   it preserves.

Given these postulates, the bound follows: the memory cost of storing T
distances of context is Σ_{t≤T} t·I_t (from the chain rule applied
iteratively), and the surplus surprisal from forgetting distances > T
is Σ_{t>T} I_t (from the data processing inequality). The marginal
analysis in §3 shows the consequences of this bound — the increasing
cost ratio (T+1) — purely from the definitions, without needing the
postulates.

TODO: Full derivation requires formalizing stationary ergodic processes,
the data processing inequality, and the chain rule for mutual information.
These are available in principle via Mathlib's measure theory, but the
connection to discrete stochastic processes is substantial. -/

/-- **Comprehension postulates for the information locality bound.**

Witnesses that a mutual information profile correctly bounds the
achievable (memory, surprisal) region for a language process.

The `Achievable` predicate abstracts over "the pair (H_M, S_M) can be
realized by some memory encoding of the underlying process." The bound
states: any achievable pair with memory at most `memoryCost(T)` must
have surprisal at least `S_∞ + surplusSurprisal(T)`. Geometrically,
all achievable pairs lie above the bound curve parameterized by T. -/
structure InformationLocalityPostulates where
  /-- The mutual information profile derived from the process -/
  profile : MutualInfoProfile
  /-- Entropy rate of the process (S_∞ × 1000) -/
  entropyRate1000 : Nat
  /-- Predicate: (H_M, S_M) is achievable by some memory encoding -/
  Achievable : Nat → Nat → Prop
  /-- **The bound**: any achievable pair lies above the trade-off curve.
      If memory ≤ memoryCost(T), then surprisal ≥ S_∞ + surplusSurprisal(T).
      Derived from DPI (bounding surprisal from below) and chain rule
      (decomposing memory cost into per-distance contributions). -/
  bound : ∀ (T : Nat) (H_M S_M : Nat),
    Achievable H_M S_M →
    H_M ≤ profile.memoryCost T →
    S_M ≥ entropyRate1000 + profile.surplusSurprisal T

-- ============================================================================
-- §5: Trade-off Curve
-- ============================================================================

/-! ### Trade-off Curve

The memory-surprisal trade-off curve plots (H_M, S_M) pairs achievable
by different memory encodings. Languages with more efficient word orders
have curves closer to the origin (lower AUC).

Values are stored as Nat × 1000 for decidable computation. -/

/-- A single point on the memory-surprisal trade-off curve.

`memoryBits1000` = H_M × 1000 (memory in millibits)
`surprisal1000` = S_M × 1000 (surprisal in millibits) -/
structure TradeoffPoint where
  memoryBits1000 : Nat
  surprisal1000 : Nat
  deriving Repr, DecidableEq

/-- A memory-surprisal trade-off curve for a language or baseline. -/
structure TradeoffCurve where
  name : String
  /-- Points ordered by increasing memory (decreasing surprisal) -/
  points : List TradeoffPoint
  deriving Repr, DecidableEq

/-- Approximate area under the trade-off curve via trapezoidal rule.

AUC × 1000000 (millibits²). Lower AUC = more efficient trade-off.
The curve should have points ordered by increasing memory. -/
def TradeoffCurve.auc (c : TradeoffCurve) : Nat :=
  let pairs := c.points.zip c.points.tail
  pairs.foldl (λ acc (p1, p2) =>
    let dx := p2.memoryBits1000 - p1.memoryBits1000
    let avgY := (p1.surprisal1000 + p2.surprisal1000) / 2
    acc + dx * avgY
  ) 0

/-- The efficient trade-off hypothesis: a real language's AUC is smaller
than its random baseline's AUC. -/
def efficientTradeoffHypothesis (real baseline : TradeoffCurve) : Bool :=
  real.auc < baseline.auc

/-- The trade-off bound curve implied by the mutual information profile
(Theorem 1). Point T maps to (memoryCost(T), surplusSurprisal(T)) for
T = 0, 1, ..., n. -/
def MutualInfoProfile.toTradeoffBound (p : MutualInfoProfile) : TradeoffCurve :=
  { name := p.name ++ " (bound)"
    points := (List.range (p.values.length + 1)).map (λ T =>
      { memoryBits1000 := p.memoryCost T
        surprisal1000 := p.surplusSurprisal T }) }

-- ============================================================================
-- §6: Concrete Profiles and Efficiency Comparison
-- ============================================================================

/-! ### Concrete profiles

Illustrative profiles demonstrating the information locality effect.
The "efficient" profile concentrates I_t at short distances (rapid decay),
while the "inefficient" profile spreads I_t across many distances (slow
decay). Both have comparable total information, but the efficient profile
achieves a strictly lower AUC on the trade-off bound. -/

/-- A language with high information locality: I_t decays rapidly.
Predictive information concentrated at short distances.
Represents an efficient language like English or Japanese. -/
def efficientProfile : MutualInfoProfile :=
  { name := "Efficient"
    values := [500, 200, 80, 30, 10, 5, 2, 1] }

/-- A language with low information locality: I_t decays slowly.
Predictive information spread across many distances.
Represents a less efficient baseline. -/
def inefficientProfile : MutualInfoProfile :=
  { name := "Inefficient"
    values := [200, 180, 150, 120, 90, 60, 30, 10] }

/-- The efficient profile has lower weighted sum (less memory for same info). -/
theorem efficient_lower_weighted_sum :
    efficientProfile.weightedSum < inefficientProfile.weightedSum := by native_decide

/-- Both profiles have comparable total information. -/
theorem profiles_similar_total_info :
    efficientProfile.totalInfo > 700 ∧ inefficientProfile.totalInfo > 700 := by
  constructor <;> native_decide

/-- **Information locality determines trade-off efficiency.**

Profiles with faster I_t decay (more information locality) produce
strictly lower trade-off bound AUC. This is the deep content of
@cite{hahn-degen-futrell-2021}: the memory-surprisal trade-off is
*determined* by the mutual information profile, and languages whose
word orders concentrate predictive information at short distances
achieve more efficient bounds.

The two profiles have comparable total predictive information
(`profiles_similar_total_info`) but the efficient profile concentrates
it at shorter distances (`efficient_lower_weighted_sum`), producing a
steeper trade-off curve and lower AUC. -/
theorem information_locality_determines_efficiency :
    efficientTradeoffHypothesis
      efficientProfile.toTradeoffBound
      inefficientProfile.toTradeoffBound = true := by
  native_decide

/-- Verify the marginal rate theorem on the efficient profile:
at T=0, memory cost step = 1 × I_0 = 500, surplus step = I_0 = 500.
Cost ratio = 1. -/
theorem efficient_marginal_at_zero :
    efficientProfile.memoryCost 1 - efficientProfile.memoryCost 0 =
    1 * (efficientProfile.surplusSurprisal 0 - efficientProfile.surplusSurprisal 1) := by
  native_decide

/-- At T=3, memory cost step = 4 × I_3 = 120, surplus step = I_3 = 30.
Cost ratio = 4: four bits of memory per bit of surprisal. -/
theorem efficient_marginal_at_three :
    efficientProfile.memoryCost 4 - efficientProfile.memoryCost 3 =
    4 * (efficientProfile.surplusSurprisal 3 - efficientProfile.surplusSurprisal 4) := by
  native_decide

-- ============================================================================
-- §7: Bridges
-- ============================================================================

/-! ### Bridge: Memory-Surprisal ↔ Rate-Distortion

The memory-surprisal trade-off is structurally analogous to rate-distortion
theory:

| Memory-Surprisal | Rate-Distortion |
|-------------------|-----------------|
| Memory H_M        | Rate R          |
| Surprisal S_M     | Distortion D    |
| Trade-off curve   | RD curve        |
| Info locality     | Structural constraint |

Both characterize optimal lossy compression: the memory encoding
compresses the past (lossy), and the trade-off curve is the achievable
region boundary.

TODO: Formal proof requires showing that the memory-surprisal trade-off
curve equals the rate-distortion function for the appropriate source
and distortion measure. See @cite{hahn-degen-futrell-2021} SI §1.3. -/
theorem memory_surprisal_rate_distortion_correspondence :
    -- The memory-surprisal framework is a special case of rate-distortion
    -- where the source is the past context and the distortion is surprisal
    True := by
  trivial
  -- TODO: Formal statement requires RD types from RateDistortion.lean.
  -- Proof sketch: Define source X = past context, reproduction Y = memory state,
  -- distortion d(x,y) = -log P(w_t | y). Then R(D) = min_{P(Y|X): E[d]≤D} I(X;Y)
  -- which is exactly the memory-surprisal trade-off.

/-! ### Bridge: Memory ↔ Processing Locality

The memory dimension H_M connects to the `locality` dimension of
`ProcessingModel.ProcessingProfile`: higher memory means the processor
can track longer-distance dependencies, which is equivalent to tolerating
higher locality costs. -/

/-- Map a memory capacity (in bits × 1000) to a processing profile.

Higher memory capacity → processor can handle longer dependencies
→ maps to `locality` (the maximum dependency distance the processor
can comfortably handle). -/
def memoryToLocality (memoryBits1000 : Nat) : ProcessingModel.ProcessingProfile :=
  { locality := memoryBits1000 / 100  -- rough mapping: 1 bit ≈ 10 words
    boundaries := 0
    referentialLoad := 0
    ease := 0 }

/-- More memory → can handle longer locality. -/
theorem more_memory_more_locality (m1 m2 : Nat) (h : m1 < m2) :
    (memoryToLocality m1).locality ≤ (memoryToLocality m2).locality := by
  simp [memoryToLocality]
  omega

/-! ### Bridge: Information Locality ↔ Dependency Locality

Information locality (I_t concentrated at small t) generalizes
dependency locality (short structural distances between related words).
When syntactic dependencies are short, the words that carry predictive
information about each other are close together, making I_t decay
rapidly.

The structural content of this bridge is `MutualInfoProfile.weightedSum_le_of_isLocal`
(§3): for any profile that is information-local with bound `L`, the
memory cost is bounded by `L · totalInfo`. DLM (which caps `L`
structurally) is therefore the dependency-graph-level instantiation of
information-locality optimization. See @cite{futrell-2019} and
@cite{hahn-degen-futrell-2021} §2.3 for the broader empirical case. -/

/-- **Universal length bound on memory cost** (vacuous case of
`weightedSum_le_of_isLocal`). For any profile, the weighted sum is
bounded by `length · totalInfo`. The interesting case is when the
profile is information-local with `L < length`, giving a tighter bound. -/
theorem MutualInfoProfile.weightedSum_le_length_mul_totalInfo
    (p : MutualInfoProfile) :
    p.weightedSum ≤ p.values.length * p.totalInfo :=
  p.weightedSum_le_of_isLocal p.values.length
    (fun _ hi hL => absurd hL (Nat.not_le.mpr hi))

-- ============================================================================
-- §8: Bridge to Generalised Surprisal
-- ============================================================================

/-! ### Bridge: Memory-Surprisal ↔ Generalised Surprisal

The memory-surprisal trade-off operates at the standard surprisal
configuration: negLog warping, indicator scoring, horizon 1, predictive
level. The trade-off curve varies *memory capacity* while holding the
prediction resolution fixed.

@cite{giulianelli-etal-2026} generalizes this by also varying the
resolution parameters (forecast horizon h and representational level l),
showing that different psycholinguistic measures are best predicted at
different resolutions. The memory-surprisal trade-off is the special case
where prediction resolution is held constant and only the memory budget
varies. -/

/-- The generalised surprisal configuration used by the memory-surprisal
trade-off: standard surprisal (negLog × indicator × h=1 × predictive).

The trade-off curve parametrizes over memory encodings while holding
this resolution fixed. IAS extends this by also parametrizing over the
prediction resolution (horizon and representational level). -/
def memorySurprisalConfig : Theories.Processing.PredictiveUncertainty.SurprisalConfig :=
  Theories.Processing.PredictiveUncertainty.standardSurprisal

end Processing.MemorySurprisal
