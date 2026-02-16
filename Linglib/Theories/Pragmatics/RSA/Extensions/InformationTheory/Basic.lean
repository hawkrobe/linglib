/-
# Information-Theoretic Foundations of RSA

Formalizes the information-theoretic analysis of RSA from Zaslavsky et al. (2020).

## Results

1. **RSA as alternating maximization**: RSA optimizes G_α = H_S(U|M) + α·E[V_L]
2. **G_α monotonicity**: G_α(S_t, L_t) ≤ G_α(S_{t+1}, L_{t+1})
3. **Critical α = 1**: Phase transition at α = 1 (informative communication threshold)
4. **Utility non-monotonicity**: E[V_L] can decrease even as G_α increases

## The G_α Objective

The RSA dynamics maximize:

  G_α(S, L) = H_S(U|M) + α · E_S[V_L]

where:
- H_S(U|M) = conditional entropy of speaker (lexicon compressibility)
- V_L(u, m) = log L(m|u) (listener's log-probability of correct meaning)
- α = rationality parameter (tradeoff between informativity and cost)

## Connection to Rate-Distortion Theory

At α = 1, the RSA objective coincides with the negative rate-distortion functional:
  G_1(S, L) = -R[D] where D is meaning distortion

This connects pragmatic reasoning to optimal lossy compression.

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human pragmatic
  reasoning. arXiv:2005.06641.
- Frank, M. C. & Goodman, N. D. (2012). Predicting pragmatic reasoning in language games.
- Cover, T. M. & Thomas, J. A. (2006). Elements of Information Theory.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.BasicQ
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Pragmatics.RSA.Core.RationalPower
import Mathlib.Data.Rat.Defs

namespace RSA.InformationTheory

open RSA.Eval
open RationalPower


/--
Natural logarithm approximated as a rational (for decidable proofs).

We use a simple linear approximation log2(x) ≈ (x - 1) / (x + 1) * 2.885
This is only used for concrete computations; proofs use abstract properties.
For exact proofs about limiting behavior, we would need Mathlib.Analysis.
-/
def log2Approx (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else
    -- Linear approximation around x=1: log2(x) ≈ 2.885 * (x-1)/(x+1)
    -- Reasonably accurate for 0.5 < x < 2
    let ratio := (x - 1) / (x + 1)
    -- 2.885 ≈ 2/ln(2) but we use 3 for simplicity
    3 * ratio

/--
Shannon entropy of a distribution (in bits).

H(X) = -Σ_x P(x) log P(x)

Note: 0 log 0 is defined as 0 (standard convention).
-/
def entropy {α : Type} [BEq α] (dist : List (α × ℚ)) : ℚ :=
  let terms := dist.map λ (_, p) =>
    if p ≤ 0 then 0
    else -p * log2Approx p
  terms.foldl (· + ·) 0

/--
Conditional entropy H(Y|X) given joint distribution.

H(Y|X) = Σ_x P(x) H(Y|X=x)
       = -Σ_{x,y} P(x,y) log P(y|x)
-/
def conditionalEntropy {α β : Type} [BEq α] [BEq β]
    (joint : List ((α × β) × ℚ))
    (marginalX : List (α × ℚ)) : ℚ :=
  let terms := joint.map λ ((x, _), pxy) =>
    let px := getScore marginalX x
    if pxy ≤ 0 || px ≤ 0 then 0
    else -pxy * log2Approx (pxy / px)
  terms.foldl (· + ·) 0

/--
Mutual information I(X;Y) = H(X) + H(Y) - H(X,Y).

Alternative: I(X;Y) = H(X) - H(X|Y) = H(Y) - H(Y|X)
-/
def mutualInformation {α β : Type} [BEq α] [BEq β]
    (joint : List ((α × β) × ℚ))
    (marginalX : List (α × ℚ))
    (marginalY : List (β × ℚ)) : ℚ :=
  entropy marginalX + entropy marginalY - entropy joint

/--
KL divergence D_KL(P || Q) = Σ_x P(x) log(P(x)/Q(x)).
-/
def klDivergence {α : Type} [BEq α]
    (p : List (α × ℚ)) (q : List (α × ℚ)) : ℚ :=
  let terms := p.map λ (x, px) =>
    let qx := getScore q x
    if px ≤ 0 then 0
    else if qx ≤ 0 then 1000  -- Infinity approximation for undefined KL
    else px * log2Approx (px / qx)
  terms.foldl (· + ·) 0


/--
Speaker entropy: H_S(U|M).

This measures the "cost" or "compressibility" of the speaker's lexicon.
Lower entropy = more deterministic (less costly) utterance choice.
-/
def speakerEntropy (S : RSA.RSAScenarioQ)
    (speaker : S.World → S.Interp → S.QUD → List (S.Utterance × ℚ))
    (worldPrior : List (S.World × ℚ)) : ℚ :=
  -- H_S(U|M) = Σ_m P(m) H(U|M=m)
  -- Use first interp and QUD (for basic scenarios these are Unit)
  match S.interps, S.quds with
  | i :: _, q :: _ =>
    let terms := worldPrior.map λ (w, pw) =>
      let s1Dist := speaker w i q
      pw * entropy s1Dist
    terms.foldl (· + ·) 0
  | _, _ => 0  -- Empty interps or quds returns 0

/--
Listener utility: V_L(u, m) = log L(m|u).

This is the listener's "value" of correctly inferring meaning m from utterance u.
-/
def listenerUtility (S : RSA.RSAScenarioQ)
    (listener : S.Utterance → List (S.World × ℚ))
    (u : S.Utterance) (m : S.World) : ℚ :=
  let pm := getScore (listener u) m
  if pm ≤ 0 then -1000  -- Negative infinity approximation
  else log2Approx pm

/--
Expected listener utility: E_S[V_L].

E_S[V_L] = Σ_{m,u} P(m) S(u|m) V_L(u, m)
         = Σ_{m,u} P(m) S(u|m) log L(m|u)
-/
def expectedListenerUtility (S : RSA.RSAScenarioQ)
    (speaker : S.World → S.Interp → S.QUD → List (S.Utterance × ℚ))
    (listener : S.Utterance → List (S.World × ℚ))
    (worldPrior : List (S.World × ℚ)) : ℚ :=
  match S.interps, S.quds with
  | i :: _, q :: _ =>
    let terms := worldPrior.flatMap λ (m, pm) =>
      let s1 := speaker m i q
      s1.map λ (u, su) =>
        let vl := listenerUtility S listener u m
        pm * su * vl
    terms.foldl (· + ·) 0
  | _, _ => 0  -- Empty interps or quds returns 0


/--
The G_α objective function from Zaslavsky et al. (2020).

G_α(S, L) = H_S(U|M) + α · E_S[V_L]

This is the quantity that RSA implicitly maximizes through alternating updates.

- α = 0: Pure compression (minimize utterance entropy)
- α = 1: Rate-distortion optimum (balance cost and informativity)
- α → ∞: Maximum informativity (NeoGricean limit)
-/
def G_alpha (S : RSA.RSAScenarioQ) (α : ℚ)
    (speaker : S.World → S.Interp → S.QUD → List (S.Utterance × ℚ))
    (listener : S.Utterance → List (S.World × ℚ))
    (worldPrior : List (S.World × ℚ)) : ℚ :=
  let h_s := speakerEntropy S speaker worldPrior
  let e_vl := expectedListenerUtility S speaker listener worldPrior
  h_s + α * e_vl

/--
Build the world prior distribution from an RSAScenario.
-/
def worldPriorDist (S : RSA.RSAScenarioQ) : List (S.World × ℚ) :=
  let scores := S.worlds.map λ w => (w, S.worldPrior w)
  normalize scores

/--
G_α using the S1 speaker and L1 listener from an RSAScenarioQ.

This extracts the implicit G_α value that the standard RSA dynamics optimize.
-/
def G_alpha_RSA (S : RSA.RSAScenarioQ) (α : ℚ) : ℚ :=
  let speaker := λ w i q => RSA.Q.S1Q S w i q
  let listener := λ u => RSA.Q.L1Q_world S u
  let prior := worldPriorDist S
  G_alpha S α speaker listener prior


/--
RSA iteration level.

Track the depth of pragmatic reasoning:
- L0 = literal listener
- S1 = pragmatic speaker (responds to L0)
- L1 = pragmatic listener (responds to S1)
- S2 = second-order speaker (responds to L1)
- etc.
-/
inductive RSALevel where
  | L : Nat → RSALevel  -- Listener level n
  | S : Nat → RSALevel  -- Speaker level n
  deriving DecidableEq, BEq, Repr

/--
The RSA dynamics as a sequence of (speaker, listener) pairs.

At each iteration t:
- L_t(m|u) ∝ P(m) S_{t-1}(u|m)
- S_t(u|m) ∝ L_t(m|u)^α
-/
structure RSADynamics (S : RSA.RSAScenarioQ) where
  /-- Iteration count -/
  iteration : Nat
  /-- Current speaker distribution S_t(u|m) -/
  speaker : S.World → List (S.Utterance × ℚ)
  /-- Current listener distribution L_t(m|u) -/
  listener : S.Utterance → List (S.World × ℚ)

/--
Initialize RSA dynamics at iteration 0.

L_0 = literal listener (from semantics)
S_0 = uniform speaker (or literal speaker)

Note: Uses first available interpretation and QUD.
-/
def initDynamics (S : RSA.RSAScenarioQ) : RSADynamics S where
  iteration := 0
  speaker := λ _ => normalize (S.utterances.map λ u => (u, 1))
  listener := λ u =>
    match S.interps with
    | i :: _ => RSA.Q.L0Q S u i
    | [] => normalize (S.worlds.map λ w => (w, 1))  -- Uniform fallback

/--
One step of RSA dynamics.

L_{t+1}(m|u) ∝ P(m) S_t(u|m)
S_{t+1}(u|m) ∝ L_{t+1}(m|u)^α
-/
def stepDynamics (S : RSA.RSAScenarioQ) (d : RSADynamics S) : RSADynamics S :=
  -- New listener: L_{t+1}(m|u) ∝ P(m) S_t(u|m)
  let newListener := λ u =>
    let scores := S.worlds.map λ m =>
      let prior := S.worldPrior m
      let su := getScore (d.speaker m) u
      (m, prior * su)
    normalize scores
  -- New speaker: S_{t+1}(u|m) ∝ L_{t+1}(m|u)^α
  let newSpeaker := λ m =>
    let scores := S.utterances.map λ u =>
      let lm := getScore (newListener u) m
      (u, RationalPower.powApprox lm S.α S.precision)
    normalize scores
  { iteration := d.iteration + 1
    speaker := newSpeaker
    listener := newListener }

/--
Run RSA dynamics for n iterations.
-/
def runDynamics (S : RSA.RSAScenarioQ) (n : Nat) : RSADynamics S :=
  (List.range n).foldl (λ d _ => stepDynamics S d) (initDynamics S)

/--
G_α value at a given dynamics state.
-/
def G_alpha_at (S : RSA.RSAScenarioQ) (α : ℚ) (d : RSADynamics S) : ℚ :=
  let speaker := λ w _ _ => d.speaker w
  let prior := worldPriorDist S
  G_alpha S α speaker d.listener prior


/--
Expected listener utility at a given dynamics state.
-/
def E_VL_at (S : RSA.RSAScenarioQ) (d : RSADynamics S) : ℚ :=
  let speaker := λ w _ _ => d.speaker w
  let prior := worldPriorDist S
  expectedListenerUtility S speaker d.listener prior

/--
Speaker entropy at a given dynamics state.
-/
def H_S_at (S : RSA.RSAScenarioQ) (d : RSADynamics S) : ℚ :=
  let speaker := λ w _ _ => d.speaker w
  let prior := worldPriorDist S
  speakerEntropy S speaker prior


/--
Trace G_α over iterations.
-/
def traceG_alpha (S : RSA.RSAScenarioQ) (α : ℚ) (maxIter : Nat) : List (Nat × ℚ) :=
  (List.range (maxIter + 1)).map λ n =>
    let d := runDynamics S n
    (n, G_alpha_at S α d)

/--
Trace E[V_L] over iterations.
-/
def traceE_VL (S : RSA.RSAScenarioQ) (maxIter : Nat) : List (Nat × ℚ) :=
  (List.range (maxIter + 1)).map λ n =>
    let d := runDynamics S n
    (n, E_VL_at S d)

/--
Check if G_α is monotonically increasing over iterations.
-/
def isMonotoneG_alpha (S : RSA.RSAScenarioQ) (α : ℚ) (maxIter : Nat) : Bool :=
  let trace := traceG_alpha S α maxIter
  let pairs := trace.zip trace.tail
  pairs.all λ ((_, g1), (_, g2)) => g1 ≤ g2

/--
Check if E[V_L] is monotonically increasing over iterations.
-/
def isMonotoneE_VL (S : RSA.RSAScenarioQ) (maxIter : Nat) : Bool :=
  let trace := traceE_VL S maxIter
  let pairs := trace.zip trace.tail
  pairs.all λ ((_, v1), (_, v2)) => v1 ≤ v2


/--
RSA dynamics with rational α support.

This allows tracking iterations for scenarios where α < 1,
which is required for Zaslavsky et al. (2020) Proposition 2.
-/
structure RSADynamicsQ (S : RSA.RSAScenarioQ) where
  /-- Iteration count -/
  iteration : Nat
  /-- Current speaker distribution S_t(u|m) -/
  speaker : S.World → List (S.Utterance × ℚ)
  /-- Current listener distribution L_t(m|u) -/
  listener : S.Utterance → List (S.World × ℚ)

/--
Initialize RSA dynamics at iteration 0 for RSAScenarioQ.
Uses uniform speaker distribution (maximal entropy).
-/
def initDynamicsQ (S : RSA.RSAScenarioQ) : RSADynamicsQ S where
  iteration := 0
  speaker := λ _ => normalize (S.utterances.map λ u => (u, 1))
  listener := λ u =>
    match S.interps with
    | i :: _ => RSA.Q.L0Q S u i
    | [] => normalize (S.worlds.map λ w => (w, 1))

/--
One step of RSA dynamics with rational α.

Following Zaslavsky et al. (2020), the update order is:
1. S_t(u|m) ∝ L_{t-1}(m|u)^α  (speaker from OLD listener)
2. L_t(m|u) ∝ P(m) S_t(u|m)   (listener from NEW speaker)

This order is crucial for utility non-monotonicity (Prop 2).
-/
def stepDynamicsQ (S : RSA.RSAScenarioQ) (d : RSADynamicsQ S) : RSADynamicsQ S :=
  -- Step 1: New speaker from OLD listener: S_t(u|m) ∝ L_{t-1}(m|u)^α
  let newSpeaker := λ m =>
    let scores := S.utterances.map λ u =>
      let lm := getScore (d.listener u) m  -- Use OLD listener
      (u, RationalPower.powApprox lm S.α S.precision)
    normalize scores
  -- Step 2: New listener from NEW speaker: L_t(m|u) ∝ P(m) S_t(u|m)
  let newListener := λ u =>
    let scores := S.worlds.map λ m =>
      let prior := S.worldPrior m
      let su := getScore (newSpeaker m) u  -- Use NEW speaker
      (m, prior * su)
    normalize scores
  { iteration := d.iteration + 1
    speaker := newSpeaker
    listener := newListener }

/--
Run RSA dynamics for n iterations with rational α.
-/
def runDynamicsQ (S : RSA.RSAScenarioQ) (n : Nat) : RSADynamicsQ S :=
  (List.range n).foldl (λ d _ => stepDynamicsQ S d) (initDynamicsQ S)

/--
Initialize RSA dynamics from lexicon values (NOT maximal entropy).

This is required for Zaslavsky et al. (2020) Proposition 2:
utility non-monotonicity only occurs when starting from a non-maximal
entropy state. The lexicon φ(u,m) provides such an initialization.

From the paper: "RSA initializations are typically already high in speaker
conditional entropy" - but the counterexample needs lower initial entropy.
-/
def initFromLexiconQ (S : RSA.RSAScenarioQ) : RSADynamicsQ S where
  iteration := 0
  -- Speaker initialized from lexicon: S_0(u|m) ∝ φ(u,m)
  speaker := λ m =>
    match S.interps with
    | i :: _ =>
      let scores := S.utterances.map λ u => (u, S.φ i u m)
      normalize scores
    | [] => normalize (S.utterances.map λ u => (u, 1))
  -- Listener from Bayes: L_0(m|u) ∝ P(m) S_0(u|m)
  listener := λ u =>
    match S.interps with
    | i :: _ =>
      let scores := S.worlds.map λ m =>
        let prior := S.worldPrior m
        let phiVal := S.φ i u m
        (m, prior * phiVal)
      normalize scores
    | [] => normalize (S.worlds.map λ w => (w, 1))

/--
Run RSA dynamics for n iterations starting from LEXICON (not uniform).

This initialization is required for utility non-monotonicity (Prop 2).
-/
def runFromLexiconQ (S : RSA.RSAScenarioQ) (n : Nat) : RSADynamicsQ S :=
  (List.range n).foldl (λ d _ => stepDynamicsQ S d) (initFromLexiconQ S)

/--
Build the world prior distribution from an RSAScenarioQ.
-/
def worldPriorDistQ (S : RSA.RSAScenarioQ) : List (S.World × ℚ) :=
  let scores := S.worlds.map λ w => (w, S.worldPrior w)
  normalize scores

/--
Speaker entropy at a given dynamics state (for RSAScenarioQ).
-/
def speakerEntropyQ (S : RSA.RSAScenarioQ)
    (speaker : S.World → List (S.Utterance × ℚ))
    (worldPrior : List (S.World × ℚ)) : ℚ :=
  let terms := worldPrior.map λ (w, pw) =>
    let s1Dist := speaker w
    pw * entropy s1Dist
  terms.foldl (· + ·) 0

/--
Expected listener utility at a given dynamics state (for RSAScenarioQ).
-/
def expectedListenerUtilityQ (S : RSA.RSAScenarioQ)
    (speaker : S.World → List (S.Utterance × ℚ))
    (listener : S.Utterance → List (S.World × ℚ))
    (worldPrior : List (S.World × ℚ)) : ℚ :=
  let terms := worldPrior.flatMap λ (m, pm) =>
    let s1 := speaker m
    s1.map λ (u, su) =>
      let lm := getScore (listener u) m
      let vl := if lm ≤ 0 then -1000 else log2Approx lm
      pm * su * vl
  terms.foldl (· + ·) 0

/--
G_α value at a given dynamics state for RSAScenarioQ.
-/
def G_alpha_at_Q (S : RSA.RSAScenarioQ) (d : RSADynamicsQ S) : ℚ :=
  let prior := worldPriorDistQ S
  let h_s := speakerEntropyQ S d.speaker prior
  let e_vl := expectedListenerUtilityQ S d.speaker d.listener prior
  h_s + S.α * e_vl

/--
Expected listener utility at a given dynamics state for RSAScenarioQ.
-/
def E_VL_at_Q (S : RSA.RSAScenarioQ) (d : RSADynamicsQ S) : ℚ :=
  let prior := worldPriorDistQ S
  expectedListenerUtilityQ S d.speaker d.listener prior

/--
Speaker entropy at a given dynamics state for RSAScenarioQ.
-/
def H_S_at_Q (S : RSA.RSAScenarioQ) (d : RSADynamicsQ S) : ℚ :=
  let prior := worldPriorDistQ S
  speakerEntropyQ S d.speaker prior


/--
Trace G_α over iterations for RSAScenarioQ.
-/
def traceG_alpha_Q (S : RSA.RSAScenarioQ) (maxIter : Nat) : List (Nat × ℚ) :=
  (List.range (maxIter + 1)).map λ n =>
    let d := runDynamicsQ S n
    (n, G_alpha_at_Q S d)

/--
Trace E[V_L] over iterations for RSAScenarioQ.
-/
def traceE_VL_Q (S : RSA.RSAScenarioQ) (maxIter : Nat) : List (Nat × ℚ) :=
  (List.range (maxIter + 1)).map λ n =>
    let d := runDynamicsQ S n
    (n, E_VL_at_Q S d)

/--
Check if G_α is monotonically increasing over iterations for RSAScenarioQ.
-/
def isMonotoneG_alpha_Q (S : RSA.RSAScenarioQ) (maxIter : Nat) : Bool :=
  let trace := traceG_alpha_Q S maxIter
  let pairs := trace.zip trace.tail
  pairs.all λ ((_, g1), (_, g2)) => g1 ≤ g2

/--
Check if E[V_L] is monotonically increasing over iterations for RSAScenarioQ.
-/
def isMonotoneE_VL_Q (S : RSA.RSAScenarioQ) (maxIter : Nat) : Bool :=
  let trace := traceE_VL_Q S maxIter
  let pairs := trace.zip trace.tail
  pairs.all λ ((_, v1), (_, v2)) => v1 ≤ v2

/--
Check if E[V_L] has a strict decrease at some iteration for RSAScenarioQ.
Returns true if there exists an iteration where E[V_L] decreases.
-/
def hasUtilityDecrease (S : RSA.RSAScenarioQ) (maxIter : Nat) : Bool :=
  let trace := traceE_VL_Q S maxIter
  let pairs := trace.zip trace.tail
  pairs.any λ ((_, v1), (_, v2)) => v2 < v1


/--
Trace E[V_L] over iterations starting from LEXICON initialization.

This is required for Zaslavsky et al. (2020) Proposition 2:
utility non-monotonicity only occurs from non-maximal entropy starts.
-/
def traceE_VL_fromLexicon (S : RSA.RSAScenarioQ) (maxIter : Nat) : List (Nat × ℚ) :=
  (List.range (maxIter + 1)).map λ n =>
    let d := runFromLexiconQ S n
    (n, E_VL_at_Q S d)

/--
Trace G_α over iterations starting from LEXICON initialization.
-/
def traceG_alpha_fromLexicon (S : RSA.RSAScenarioQ) (maxIter : Nat) : List (Nat × ℚ) :=
  (List.range (maxIter + 1)).map λ n =>
    let d := runFromLexiconQ S n
    (n, G_alpha_at_Q S d)

/--
Check if E[V_L] decreases starting from LEXICON initialization.

This is the key test for Zaslavsky et al. (2020) Proposition 2.
-/
def hasUtilityDecreaseFromLexicon (S : RSA.RSAScenarioQ) (maxIter : Nat) : Bool :=
  let trace := traceE_VL_fromLexicon S maxIter
  let pairs := trace.zip trace.tail
  pairs.any λ ((_, v1), (_, v2)) => v2 < v1

/--
Check if G_α is monotone starting from LEXICON initialization.
Should be true for all α ≥ 0 (Equation 9 in Zaslavsky et al.).
-/
def isMonotoneG_alpha_fromLexicon (S : RSA.RSAScenarioQ) (maxIter : Nat) : Bool :=
  let trace := traceG_alpha_fromLexicon S maxIter
  let pairs := trace.zip trace.tail
  pairs.all λ ((_, g1), (_, g2)) => g1 ≤ g2

end RSA.InformationTheory
