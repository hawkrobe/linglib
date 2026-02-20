import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Domains.Quantities
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics

/-!
# Goodman & Stuhlmuller (2013): Knowledge and Implicature @cite{goodman-stuhlmuller-2013}

Topics in Cognitive Science 5(1): 173-184

Scalar implicature and upper-bounded numeral interpretations are modulated by
speaker knowledge. When the speaker has full access, listeners draw upper-bounded
inferences; when access is partial, these weaken or disappear.

## Architecture

This implementation uses `RSAConfig` with a compositional S1 score that
references L0 directly, matching the WebPPL/memo reference implementation:

    S1(u | obs) ∝ exp(α · E_belief[log L0(s | u)])

where `belief` is the speaker's posterior from the hypergeometric observation
model. The quality filter (utterances must be true at all believed worlds) is
explicit because `Real.log 0 = 0` in Lean/Mathlib, unlike WebPPL where
`log(0) = -∞` makes quality emerge from the expected utility computation.

Two RSAConfig instances (quantifiers, lower-bound numerals) share the same
observation model, speaker belief, and S1 structure. All proofs use `rsa_predict`.

## References

- Goodman, N.D. & Stuhlmuller, A. (2013). Knowledge and implicature. *TopiCS* 5(1).
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
  *Semantics & Pragmatics* 8(10), 1-44.
-/

set_option autoImplicit false

namespace RSA.GoodmanStuhlmuller2013

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- World states: how many of 3 objects have the property. -/
inductive WorldState where
  | s0 | s1 | s2 | s3
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

def WorldState.toNat : WorldState → Nat
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3

/-- Speaker access: how many of 3 objects the speaker can observe. -/
inductive Access where
  | a1 | a2 | a3
  deriving DecidableEq, BEq, Repr

/-- Observations: (number of red seen, access level).
    Latent variable in L1 — L1 marginalizes over observations. -/
inductive Obs where
  | o0a1 | o1a1                      -- access=1: saw 0 or 1 red
  | o0a2 | o1a2 | o2a2              -- access=2: saw 0, 1, or 2 red
  | o0a3 | o1a3 | o2a3 | o3a3      -- access=3: saw 0, 1, 2, or 3 red
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

def Obs.access : Obs → Access
  | .o0a1 | .o1a1 => .a1
  | .o0a2 | .o1a2 | .o2a2 => .a2
  | .o0a3 | .o1a3 | .o2a3 | .o3a3 => .a3

-- ============================================================================
-- §2. Observation Model (Hypergeometric)
-- ============================================================================

/-- P(obs | access, world). Hypergeometric probability of observing k red apples
    when sampling n from 3 total with K red:
    P(k | N=3, K, n) = C(K,k) · C(3-K, n-k) / C(3,n).
    Defined as a match table for `extractRat` compatibility. -/
noncomputable def obsPriorTable (a : Access) (w : WorldState) (obs : Obs) : ℝ :=
  if obs.access != a then 0 else
  match a, w, obs with
  -- access=1: C(K,k) · C(3-K,1-k) / C(3,1)
  | .a1, .s0, .o0a1 => 1     | .a1, .s0, .o1a1 => 0
  | .a1, .s1, .o0a1 => 2/3   | .a1, .s1, .o1a1 => 1/3
  | .a1, .s2, .o0a1 => 1/3   | .a1, .s2, .o1a1 => 2/3
  | .a1, .s3, .o0a1 => 0     | .a1, .s3, .o1a1 => 1
  -- access=2: C(K,k) · C(3-K,2-k) / C(3,2)
  | .a2, .s0, .o0a2 => 1     | .a2, .s0, .o1a2 => 0     | .a2, .s0, .o2a2 => 0
  | .a2, .s1, .o0a2 => 1/3   | .a2, .s1, .o1a2 => 2/3   | .a2, .s1, .o2a2 => 0
  | .a2, .s2, .o0a2 => 0     | .a2, .s2, .o1a2 => 2/3   | .a2, .s2, .o2a2 => 1/3
  | .a2, .s3, .o0a2 => 0     | .a2, .s3, .o1a2 => 0     | .a2, .s3, .o2a2 => 1
  -- access=3: deterministic (full knowledge)
  | .a3, .s0, .o0a3 => 1     | .a3, .s1, .o1a3 => 1
  | .a3, .s2, .o2a3 => 1     | .a3, .s3, .o3a3 => 1
  | _, _, _ => 0

-- ============================================================================
-- §3. Speaker Belief
-- ============================================================================

/-- Speaker's posterior over world states given observation:
    P(state | obs, access) ∝ P(obs | state, access) · P(state).
    With uniform world prior, this is just the normalized hypergeometric. -/
noncomputable def speakerBelief (a : Access) (obs : Obs) (s : WorldState) : ℝ :=
  obsPriorTable a s obs / ∑ s' : WorldState, obsPriorTable a s' obs

-- ============================================================================
-- §4. Quality Filter
-- ============================================================================

/-- Is state s compatible with observation obs?
    True iff the hypergeometric probability P(obs | s, access) > 0,
    i.e. enough red apples to produce the observation. -/
def obsCompatible (obs : Obs) (s : WorldState) : Bool :=
  match obs, s with
  -- access=1 (n=1)
  | .o0a1, .s0 => true  | .o0a1, .s1 => true  | .o0a1, .s2 => true  | .o0a1, .s3 => false
  | .o1a1, .s0 => false | .o1a1, .s1 => true  | .o1a1, .s2 => true  | .o1a1, .s3 => true
  -- access=2 (n=2)
  | .o0a2, .s0 => true  | .o0a2, .s1 => true  | .o0a2, .s2 => false | .o0a2, .s3 => false
  | .o1a2, .s0 => false | .o1a2, .s1 => true  | .o1a2, .s2 => true  | .o1a2, .s3 => false
  | .o2a2, .s0 => false | .o2a2, .s1 => false | .o2a2, .s2 => true  | .o2a2, .s3 => true
  -- access=3 (n=3): exact match
  | .o0a3, .s0 => true  | .o1a3, .s1 => true  | .o2a3, .s2 => true  | .o3a3, .s3 => true
  | _, _ => false

/-- Quality filter: the utterance must be true at all worlds the speaker
    considers possible. This is the explicit formalization of the condition
    that emerges from exp(E_belief[log L0]) when log(0) = -∞. -/
def qualityOk {U : Type} (meaning : U → WorldState → Bool) (obs : Obs) (u : U) : Bool :=
  (List.finRange 4 |>.map fun i =>
    let s := match i with | ⟨0, _⟩ => WorldState.s0 | ⟨1, _⟩ => WorldState.s1
                          | ⟨2, _⟩ => WorldState.s2 | _ => WorldState.s3
    !obsCompatible obs s || meaning u s
  ).all id

-- ============================================================================
-- §5. Quantifier Model
-- ============================================================================

inductive QUtt where
  | none_ | some_ | all
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

def qMeaning : QUtt → WorldState → Bool
  | .none_, s => s.toNat == 0
  | .some_, s => s.toNat ≥ 1
  | .all,   s => s.toNat == 3

open RSA in
/-- Quantifier RSA model parametric in speaker access.

    S1 score is compositional: `exp(α · E_belief[log L0(s|u)])`, matching
    the WebPPL/memo implementation. The quality filter is explicit (needed
    because `Real.log 0 = 0` in Lean). -/
noncomputable def gsCfgQ (a : Access) : RSAConfig QUtt WorldState where
  Latent := Obs
  meaning _obs u w := if qMeaning u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α obs _w u :=
    if qualityOk qMeaning obs u then
      Real.exp (α * ∑ s : WorldState, speakerBelief a obs s * Real.log (l0 u s))
    else 0
  s1Score_nonneg _ _ _ _ _ _ _ := by
    split
    · exact le_of_lt (Real.exp_pos _)
    · exact le_refl 0
  α := 1
  α_pos := one_pos
  latentPrior w obs := obsPriorTable a w obs
  latentPrior_nonneg w obs := by
    unfold obsPriorTable
    split
    · exact le_refl 0
    · (repeat' split) <;> positivity
  worldPrior_nonneg _ := by positivity

-- ============================================================================
-- §6. Numeral Model (Lower-Bound Semantics)
-- ============================================================================

inductive NumUtt where
  | one | two | three
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

def lbMeaning : NumUtt → WorldState → Bool
  | .one,   s => s.toNat ≥ 1
  | .two,   s => s.toNat ≥ 2
  | .three, s => s.toNat ≥ 3

open RSA in
/-- Lower-bound numeral RSA model parametric in speaker access. -/
noncomputable def gsCfgN (a : Access) : RSAConfig NumUtt WorldState where
  Latent := Obs
  meaning _obs u w := if lbMeaning u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
  s1Score l0 α obs _w u :=
    if qualityOk lbMeaning obs u then
      Real.exp (α * ∑ s : WorldState, speakerBelief a obs s * Real.log (l0 u s))
    else 0
  s1Score_nonneg _ _ _ _ _ _ _ := by
    split
    · exact le_of_lt (Real.exp_pos _)
    · exact le_refl 0
  α := 1
  α_pos := one_pos
  latentPrior w obs := obsPriorTable a w obs
  latentPrior_nonneg w obs := by
    unfold obsPriorTable
    split
    · exact le_refl 0
    · (repeat' split) <;> positivity
  worldPrior_nonneg _ := by positivity

-- ============================================================================
-- §7. Grounding
-- ============================================================================

/-- Quantifier meaning derives from Montague semantics (not stipulated). -/
theorem quantifier_meaning_grounded (u : QUtt) (s : WorldState) :
    qMeaning u s =
    RSA.Domains.Quantity.meaning 3
      (match u with | .none_ => .none_ | .some_ => .some_ | .all => .all)
      ⟨s.toNat, by cases u <;> cases s <;> decide⟩ := by
  cases u <;> cases s <;> native_decide

/-- Lower-bound numeral meaning derives from NumeralTheory.meaning. -/
theorem lb_meaning_grounded (u : NumUtt) (s : WorldState) :
    lbMeaning u s =
    Semantics.Lexical.Numeral.LowerBound.meaning
      (match u with | .one => .one | .two => .two | .three => .three)
      s.toNat := by
  cases u <;> cases s <;> rfl

end RSA.GoodmanStuhlmuller2013
