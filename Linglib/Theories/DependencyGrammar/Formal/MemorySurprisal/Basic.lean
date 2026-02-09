import Linglib.Theories.RSA.Extensions.InformationTheory.Basic
import Linglib.Core.ProcessingModel

/-!
# Memory-Surprisal Trade-off Framework

Core formalization of Hahn, Degen & Futrell (2021) "Modeling Word and Morpheme
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

## Connection to DLM

Information locality generalizes dependency length minimization: DLM
minimizes the *structural* distance between syntactically related words,
while information locality minimizes the *information-theoretic* distance
at which predictive information concentrates.

## Sections

- §1: Memory-surprisal framework (MemoryEncoding, averageSurprisal, memoryEntropy)
- §2: Mutual information profile and information locality bound (Theorem 1)
- §3: Trade-off curve (TradeoffPoint, TradeoffCurve, AUC)
- §4: Bridges (rate-distortion, processing model, dependency locality)

## References

- Hahn, M., Degen, J. & Futrell, R. (2021). Modeling word and morpheme order
  as an efficient trade-off of memory and surprisal. *Psychological Review*
  128(4):726–756.
- Futrell, R. (2019). Information-theoretic locality properties of natural
  language. *EMNLP*.
- Zaslavsky, N., Hu, J. & Levy, R. (2020). A rate-distortion view of human
  pragmatic reasoning.
-/

namespace DepGrammar.MemorySurprisal

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

/-- Average surprisal under a memory encoding.

This is the conditional entropy of the next word given the current
memory state: S_M = H(W_t | M_t).

Lower memory → less information about the past → higher surprisal.
When memory is unlimited, S_M = S_∞ (the entropy rate of the language).

We reuse `conditionalEntropy` from InformationTheory/Basic.lean. -/
def averageSurprisal {W Mem : Type} [BEq W] [BEq Mem]
    (joint : List ((Mem × W) × ℚ))
    (marginalMem : List (Mem × ℚ)) : ℚ :=
  RSA.InformationTheory.conditionalEntropy joint marginalMem

/-- Memory entropy: the entropy of the memory state distribution.

H_M = H(M_t), measuring how many bits the processor uses.

We reuse `entropy` from InformationTheory/Basic.lean. -/
def memoryEntropy {Mem : Type} [BEq Mem]
    (memDist : List (Mem × ℚ)) : ℚ :=
  RSA.InformationTheory.entropy memDist

-- ============================================================================
-- §2: Mutual Information Profile and Information Locality
-- ============================================================================

/-! ### Mutual Information Profile

The mutual information profile I_t measures how much information
the word at position t provides about the word at position t + d
(at distance d). This determines the shape of the memory-surprisal
trade-off curve.

Key insight: I_t = S_t - S_{t+1}, where S_t is the surprisal when
the processor remembers only t steps of context. So I_t measures
the *marginal value* of remembering one more step. -/

/-- Mutual information at distance t between words.

I_t represents how much mutual information exists between a word and
the word t steps back. Higher I_t at small t means information is
concentrated locally (good for memory-efficient processing).

Stored as I_t × 1000 for decidable computation. -/
structure MutualInfoProfile where
  /-- Name for this profile (e.g., "English", "Japanese", "Baseline") -/
  name : String
  /-- I_t × 1000 for distances t = 1, 2, 3, ... -/
  values : List Nat
  deriving Repr, DecidableEq, BEq

/-- Sum of I_t values (total predictive information × 1000). -/
def MutualInfoProfile.totalInfo (p : MutualInfoProfile) : Nat :=
  p.values.foldl (· + ·) 0

/-- Weighted sum Σ t·I_t (memory cost × 1000).

This is the key quantity in the information locality bound:
the memory needed to store T steps of context is bounded by
Σ_{t≤T} t·I_t. Languages with lower weighted sums concentrate
information at shorter distances. -/
def MutualInfoProfile.weightedSum (p : MutualInfoProfile) : Nat :=
  let rec go : List Nat → Nat → Nat → Nat
    | [], _, acc => acc
    | it :: rest, t, acc => go rest (t + 1) (acc + (t + 1) * it)
  go p.values 0 0

/-- **Information Locality Bound (Theorem 1, eq. 4)**

The memory required to achieve surprisal S_M is bounded below by:
  H_M ≥ Σ_{t : I_t > threshold} t · I_t

where the threshold is determined by S_M.

More precisely: for a processor with memory capacity T steps,
  H_M ≤ Σ_{t≤T} t · I_t    (memory cost of storing T steps)
  S_M ≥ S_∞ + Σ_{t>T} I_t   (surplus surprisal from forgetting)

Languages with steeper I_t decay (more information locality)
achieve better trade-offs: less memory for the same surprisal.

TODO: Full proof requires formalizing stationary ergodic processes
and the chain rule for mutual information. See paper SI §1.2. -/
theorem information_locality_bound
    (p : MutualInfoProfile)
    (memoryCapacity : Nat)
    (_h : memoryCapacity ≤ p.values.length) :
    -- The memory cost up to T is at most the weighted sum up to T
    -- and the surplus surprisal is at least the sum of I_t for t > T
    True := by
  trivial
  -- TODO: The real theorem would state:
  -- memoryCost(T) ≤ Σ_{t≤T} t·I_t  ∧  surplusSurprisal(T) ≥ Σ_{t>T} I_t
  -- Proof sketch: By the chain rule for mutual information applied to
  -- the stationary process, and the data processing inequality.

-- ============================================================================
-- §2a: Concrete Mutual Information Profiles (Figure 3)
-- ============================================================================

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

-- ============================================================================
-- §3: Trade-off Curve
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
  deriving Repr, DecidableEq, BEq

/-- A memory-surprisal trade-off curve for a language or baseline. -/
structure TradeoffCurve where
  name : String
  /-- Points ordered by increasing memory (decreasing surprisal) -/
  points : List TradeoffPoint
  deriving Repr, DecidableEq, BEq

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

-- ============================================================================
-- §4: Bridges
-- ============================================================================

/-! ### Bridge: Memory-Surprisal ↔ Rate-Distortion

The memory-surprisal trade-off is structurally analogous to rate-distortion
theory (Zaslavsky et al. 2020):

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
and distortion measure. See Hahn et al. (2021) SI §1.3. -/
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

TODO: Formal proof requires connecting the structural notion of
dependency length to the information-theoretic notion of mutual
information at distance t. See Futrell (2019) and Hahn et al. (2021)
§2.3 for the argument that DLM is a special case of information
locality optimization. -/
theorem information_locality_generalizes_dep_locality :
    -- Short dependencies → high I_1, low I_t for large t
    -- → steep decay → efficient trade-off curve
    True := by
  trivial
  -- TODO: Proof sketch from Futrell (2019):
  -- If dependency length is bounded by L, then I_t ≈ 0 for t > L.
  -- The weighted sum Σ t·I_t is then bounded by L · Σ I_t = L · I_total.
  -- Minimizing dependency length minimizes this bound.

end DepGrammar.MemorySurprisal
