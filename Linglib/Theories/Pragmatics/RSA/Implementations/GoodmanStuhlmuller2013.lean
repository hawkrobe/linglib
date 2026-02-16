import Linglib.Theories.Pragmatics.RSA.Domains.Quantities
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Mathlib.Data.Rat.Defs

/-!
# Goodman & Stuhlmuller (2013): Knowledge and Implicature

Topics in Cognitive Science 5(1): 173-184

Two contributions:
1. **Basic scalar implicature**: L0 → S1 → L1 derives "some → not all"
2. **Knowledge-state interaction**: speaker access affects interpretation

## Quality-Filtered S1 (Eq. 2-3)

G&S Eq. (2)-(3) define speaker utility as U(w;u) = ln P_lex(u|w) — log-probability
of the literal listener assigning the correct world. The ln(0) = -∞ penalty means
any utterance false at a world the speaker considers possible gets utility -∞ and
S1 probability 0. For uniform L0, exp(E_b[ln L0]) reduces to:
- **Quality filter**: utterance must be true at ALL worlds with positive belief mass
- **Informativity**: score = 1/|compatible worlds|

This is implemented via the core `RSA.Eval.ksS1` / `RSA.Eval.ksL1` functions.

## Numeral Semantics: Kennedy (2015) as Primary

The original G&S paper predates Kennedy's de-Fregean proposal. We integrate
the two: Kennedy exact (`maxMeaning .eq`) is the primary bare-numeral semantics,
with Class A/B modified numerals as the alternative set (not other bare numerals
on a Horn scale). The quality filter derives Kennedy's ignorance implicatures for
Class B at partial access: uncertain speakers are FORCED to use "at least" (the
only utterance true at all believed worlds), and L1 reads this signal.

## References

- Goodman, N.D. & Stuhlmuller, A. (2013). Knowledge and implicature. *TopiCS* 5(1).
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
  *Semantics & Pragmatics* 8(10), 1-44.
-/

namespace RSA.GoodmanStuhlmuller2013

open RSA RSA.Domains.Quantity RSA.Eval
open TruthConditional.Numeral

-- ============================================================================
-- Section 1: Basic Scalar Implicature (Quantifiers)
-- ============================================================================

section BasicImplicature

/-- 3-person quantity domain from Domains.Quantity -/
def threePerson : Domain 3 := standard 3

def l0_some : List (Fin 4 × ℚ) := l0 threePerson .some_
def l1_some : List (Fin 4 × ℚ) := l1 threePerson .some_
def s1_w3 : List (Utterance × ℚ) := s1 threePerson (wAll (n := 3))
def s1_w1 : List (Utterance × ℚ) := s1 threePerson (w1 (n := 3))

/-- L1("some") prefers w1 (some but not all) over w3 (all). -/
theorem scalar_implicature :
    RSA.Eval.getScore l1_some (w1 (n := 3)) > RSA.Eval.getScore l1_some (wAll (n := 3)) := by
  native_decide

/-- L0 assigns equal mass to w1 and w3 -- no implicature at literal level. -/
theorem l0_no_implicature :
    RSA.Eval.getScore l0_some (w1 (n := 3)) = RSA.Eval.getScore l0_some (wAll (n := 3)) := by
  native_decide

/-- In w3, speaker prefers "all" over "some". -/
theorem s1_prefers_all_in_w3 :
    RSA.Eval.getScore s1_w3 .all > RSA.Eval.getScore s1_w3 .some_ := by
  native_decide

/-- In w1, speaker uses "some" and not "all". -/
theorem s1_uses_some_in_w1 :
    RSA.Eval.getScore s1_w1 .some_ > 0 ∧ RSA.Eval.getScore s1_w1 .all = 0 := by
  native_decide

/-- Quantifier meaning derives from Montague (not stipulated). -/
theorem some_meaning_from_montague (n : Nat) (w : Fin (n + 1)) :
    RSA.Domains.Quantity.meaning n .some_ w ↔ w.val ≥ 1 := by
  simp [RSA.Domains.Quantity.meaning]

end BasicImplicature

-- ============================================================================
-- Section 2: Knowledge-State Infrastructure
-- ============================================================================

namespace KnowledgeState

/-- World states: how many (of 3) have the property -/
inductive WorldState where
  | s0 | s1 | s2 | s3
  deriving DecidableEq, BEq, Repr, Inhabited

def WorldState.toNat : WorldState → Nat
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3

def allWorldStates : List WorldState := [.s0, .s1, .s2, .s3]

/-- Access: how many objects the speaker can see -/
inductive Access where
  | a1 | a2 | a3
  deriving DecidableEq, BEq, Repr

def Access.toNat : Access → Nat
  | .a1 => 1 | .a2 => 2 | .a3 => 3

/-- Observations: what the speaker actually sees -/
structure Observation where
  seen : Nat
  access : Access
  deriving DecidableEq, BEq, Repr

def observationsFor (a : Access) : List Observation :=
  match a with
  | .a1 => [⟨0, .a1⟩, ⟨1, .a1⟩]
  | .a2 => [⟨0, .a2⟩, ⟨1, .a2⟩, ⟨2, .a2⟩]
  | .a3 => [⟨0, .a3⟩, ⟨1, .a3⟩, ⟨2, .a3⟩, ⟨3, .a3⟩]

/-- Binomial coefficient -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Hypergeometric probability (closed form).
P(observe k red | sample n from population with K red out of N total) -/
def hypergeomℚ (totalN totalK sampleN observedK : Nat) : ℚ :=
  let num := choose totalK observedK * choose (totalN - totalK) (sampleN - observedK)
  let den := choose totalN sampleN
  if den > 0 then (num : ℚ) / (den : ℚ) else 0

def obsProb (o : Observation) (a : Access) (s : WorldState) : ℚ :=
  hypergeomℚ 3 s.toNat a.toNat o.seen

/-- Speaker's belief state given observation (Bayesian update via hypergeometric) -/
def speakerBelief (o : Observation) (s : WorldState) : ℚ :=
  let numerator := obsProb o o.access s
  let totalScore := RSA.Eval.sumScores (allWorldStates.map (obsProb o o.access))
  if totalScore > 0 then numerator / totalScore else 0

-- ============================================================================
-- Section 3: Knowledge-Sensitive RSA (Parameterized by Meaning)
-- ============================================================================

/-! Generic knowledge-sensitive RSA chain, parameterized by meaning function
and utterance list. Instantiated for both quantifiers and numerals.

Uses the core `RSA.Eval.ksL1` chain with quality-filtered S1 (G&S 2013 Eq. 2-3).
The quality filter implements log-utility: U(w;u) = ln P_lex(u|w), where ln(0) = -∞
kills any utterance false at a world the speaker considers possible. For uniform L0,
this reduces to: pass quality filter, then score by 1/|compat(u)| (informativity). -/

/-- Standalone L0 for direct semantic queries (not used in the RSA chain). -/
def L0_param {U : Type} (meaning : U → WorldState → Bool)
    (u : U) (s : WorldState) : ℚ :=
  let compat := allWorldStates.filter (meaning u)
  if compat.length > 0 ∧ meaning u s then
    1 / compat.length
  else 0

/-- Knowledge-state L1 via unified core.
    L1(s|u,a) ∝ prior(s) × Σ_o P(o|a,s) × ksS1(u|belief_o). -/
def L1_scores {U : Type} [BEq U] (meaning : U → WorldState → Bool) (allUtts : List U)
    (u : U) (a : Access) : List (WorldState × ℚ) :=
  RSA.Eval.ksL1 allUtts allWorldStates (observationsFor a)
    meaning (λ _ => 1) (obsProb · a) speakerBelief u

end KnowledgeState

-- ============================================================================
-- Section 4: Quantifier Knowledge-State Results
-- ============================================================================

section QuantifierKnowledgeState

open KnowledgeState

inductive QUtt where
  | none_ | some_ | all
  deriving DecidableEq, BEq, Repr

def allQUtts : List QUtt := [.none_, .some_, .all]

/-- Quantifier meaning (matches Domains.Quantity.meaning, proved in Grounding) -/
def quantifierMeaning : QUtt → WorldState → Bool
  | .none_, s => s.toNat == 0
  | .some_, s => s.toNat ≥ 1
  | .all,   s => s.toNat == 3

def l1q (u : QUtt) (a : Access) := L1_scores quantifierMeaning allQUtts u a

/-- With full access, implicature holds: L1("some") prefers s1 over s3. -/
theorem implicature_with_full_access :
    getScore (l1q .some_ .a3) .s1 > getScore (l1q .some_ .a3) .s3 := by
  native_decide

/-- With partial access (a=1), implicature is canceled. -/
theorem implicature_canceled_access1 :
    ¬(getScore (l1q .some_ .a1) .s2 > getScore (l1q .some_ .a1) .s3) := by
  native_decide

/-- Basic and knowledge-state RSA agree on full-access implicature. -/
theorem models_consistent_on_implicature :
    (RSA.Eval.getScore (l1 threePerson .some_) (w1 (n := 3)) >
     RSA.Eval.getScore (l1 threePerson .some_) (wAll (n := 3)))
    ↔
    (getScore (l1q .some_ .a3) .s1 > getScore (l1q .some_ .a3) .s3) := by
  constructor <;> intro _ <;> native_decide

end QuantifierKnowledgeState

-- ============================================================================
-- Section 5: Kennedy Numeral Semantics through RSA
-- ============================================================================

section KennedyNumerals

open KnowledgeState
open TruthConditional.Numeral

/-! ## Kennedy's Alternative Structure (Section 4.1)

Numerals do NOT form Horn scales (they are non-monotonic under de-Fregean
semantics). The alternatives for numeral n are the Class A/B variants:

  ALT("n P") = { bare n P,  more than n P,  at least n P }

All three are instances of `maxMeaning rel m` with different `rel`:
- Bare: max{d | P(d)} = n   (`.eq`)
- Class A "more than": max{d | P(d)} > n  (`.gt`)
- Class B "at least": max{d | P(d)} >= n  (`.ge`)

Ignorance implicatures arise for Class B because it is asymmetrically
entailed by both bare and Class A. -/

/-- Kennedy alternative utterances for numeral n: bare, more-than, at-least -/
inductive KennedyUtt where
  | bare      -- max = n  (exact / de-Fregean)
  | moreThan  -- max > n  (Class A)
  | atLeast   -- max >= n (Class B)
  deriving DecidableEq, BEq, Repr

def allKennedyUtts : List KennedyUtt := [.bare, .moreThan, .atLeast]

/-- Kennedy meaning for a fixed numeral value m, applied to world-state cardinality.
Note: maxMeaning takes (rel) (threshold m) (cardinality n). -/
def kennedyMeaning (m : Nat) : KennedyUtt → WorldState → Bool
  | .bare,     s => maxMeaning .eq m s.toNat
  | .moreThan, s => maxMeaning .gt m s.toNat
  | .atLeast,  s => maxMeaning .ge m s.toNat

/-- Lift a NumeralTheory to the knowledge-state domain. -/
def liftTheory (T : NumeralTheory) : BareNumeral → WorldState → Bool :=
  λ u s => T.meaning u s.toNat

-- Number word utterances (for lower-bound comparison)
inductive NumUtterance where
  | one | two | three
  deriving DecidableEq, BEq, Repr

def allNumUtterances : List NumUtterance := [.one, .two, .three]

def uttToBareNumeral : NumUtterance → BareNumeral
  | .one => .one | .two => .two | .three => .three

-- ============================================================================
-- Section 5a: Kennedy Alternative-Set Theorems
-- ============================================================================

/-- Bare numeral "two" under Kennedy: exact, only s2 compatible. -/
theorem kennedy_bare_two_exact :
    kennedyMeaning 2 .bare .s2 = true ∧
    kennedyMeaning 2 .bare .s1 = false ∧
    kennedyMeaning 2 .bare .s3 = false := by native_decide

/-- Class B "at least two" is weaker: compatible with s2 AND s3. -/
theorem kennedy_atLeast_two_weaker :
    kennedyMeaning 2 .atLeast .s2 = true ∧
    kennedyMeaning 2 .atLeast .s3 = true := by native_decide

/-- Class A "more than two" excludes the bare world: only s3. -/
theorem kennedy_moreThan_two_excludes_bare :
    kennedyMeaning 2 .moreThan .s2 = false ∧
    kennedyMeaning 2 .moreThan .s3 = true := by native_decide

/-- Entailment: bare asymmetrically entails at-least (Class B).
This is why Class B generates ignorance implicatures. -/
theorem bare_entails_atLeast :
    (allWorldStates.filter (kennedyMeaning 2 .bare)).length = 1 ∧
    (allWorldStates.filter (kennedyMeaning 2 .atLeast)).length = 2 ∧
    (allWorldStates.all λ s => !kennedyMeaning 2 .bare s || kennedyMeaning 2 .atLeast s) := by
  native_decide

/-- Class A "more than" is NOT entailed by bare (disjoint denotations).
So Class A generates no ignorance implicatures. -/
theorem classA_no_entailment :
    ¬(allWorldStates.all λ s => !kennedyMeaning 2 .bare s || kennedyMeaning 2 .moreThan s) := by
  native_decide

-- ============================================================================
-- Section 5b: Kennedy Alternatives through Knowledge-State RSA
-- ============================================================================

/-- L1 scores for Kennedy alternatives to "two" -/
def l1k (u : KennedyUtt) (a : Access) := L1_scores (kennedyMeaning 2) allKennedyUtts u a

/-- Class B "at least two" is uninformative at full access: L1 assigns equal mass
to s2 and s3. When the speaker knows the true world, both s2- and s3-speakers
use "at least" with equal probability (alongside their preferred bare/moreThan),
so hearing it carries no differential signal. -/
theorem kennedy_classB_uninformative_full_access :
    getScore (l1k .atLeast .a3) .s2 = getScore (l1k .atLeast .a3) .s3 := by
  native_decide

/-- Class B IS informative with partial access: quality filter forces uncertain
speakers (who can't assert bare or moreThan without risking falsehood) to use
"at least". Since observations are asymmetrically distributed (seeing 2-of-2 is
more likely under s3 than s2), L1 can read this signal. This derives Kennedy's
ignorance implicature from RSA + quality filter, without neo-Gricean machinery. -/
theorem kennedy_classB_informative_partial_access :
    getScore (l1k .atLeast .a2) .s2 ≠ getScore (l1k .atLeast .a2) .s3 := by
  native_decide

/-- Bare "two" under Kennedy: L0 gives all mass to s2. -/
theorem kennedy_bare_no_l0_ambiguity :
    L0_param (kennedyMeaning 2) .bare .s2 > 0 ∧
    L0_param (kennedyMeaning 2) .bare .s1 = 0 ∧
    L0_param (kennedyMeaning 2) .bare .s3 = 0 := by
  native_decide

/-! ### Key finding: quality filter derives Kennedy's knowledge-sensitivity

Two effects of the quality-filtered S1 on Kennedy numerals:

1. **Bare "two" is knowledge-sensitive via belief channel**: Even though L0 maps
   bare "two" to exactly s2, the speaker's choice among {bare, moreThan, atLeast}
   depends on observations. A speaker uncertain between s2 and s3 CANNOT use bare
   (false at s3) or moreThan (false at s2) — only "at least" survives quality.
   L1 reads this signal.

2. **Class B "at least" is informative at partial access**: With the quality filter,
   uncertain speakers are FORCED to use "at least" (the only utterance true at all
   worlds they consider possible). Since observations are asymmetrically distributed,
   L1 hearing "at least" can discriminate s2 from s3 — deriving Kennedy's ignorance
   implicature from RSA alone. At full access, "at least" remains uninformative
   (symmetric S1 usage from s2- and s3-knowing speakers). -/

/-- Bare "two" under Kennedy IS knowledge-sensitive (through the belief channel). -/
theorem kennedy_bare_knowledge_sensitive :
    getScore (l1k .bare .a3) .s2 ≠ getScore (l1k .bare .a1) .s2 := by
  native_decide

-- ============================================================================
-- Section 5c: Lower-Bound Comparison
-- ============================================================================

def lbMeaning : NumUtterance → WorldState → Bool :=
  λ u s => LowerBound.meaning (uttToBareNumeral u) s.toNat

def l1_lb (u : NumUtterance) (a : Access) := L1_scores lbMeaning allNumUtterances u a

/-- Lower-bound: "two" is ambiguous at L0 (compatible with s2 AND s3). -/
theorem lb_has_ambiguity :
    (allWorldStates.filter (lbMeaning .two)).length = 2 := by native_decide

/-- Lower-bound + full access: implicature emerges. -/
theorem lb_full_access_implicature :
    getScore (l1_lb .two .a3) .s2 > getScore (l1_lb .two .a3) .s3 := by
  native_decide

/-- Lower-bound + partial access: implicature weakens. -/
theorem lb_partial_access_weakens :
    getScore (l1_lb .two .a3) .s2 - getScore (l1_lb .two .a3) .s3 >
    getScore (l1_lb .two .a2) .s2 - getScore (l1_lb .two .a2) .s3 := by
  native_decide

-- ============================================================================
-- Section 5d: Empirical Predictions
-- ============================================================================

/-! ## Kennedy vs Lower-Bound: Different Mechanisms for Knowledge-Sensitivity

Both theories predict knowledge-sensitivity for bare numerals, but through
different mechanisms:

| Theory      | Bare "two"                     | Class B "at least two"          |
|-------------|--------------------------------|---------------------------------|
| Lower-bound | KS via implicature cancellation| N/A (not in alt set)            |
| Kennedy     | KS via belief channel + quality| Informative at partial access   |

The quality-filtered S1 (G&S 2013 Eq. 2-3) changes the Kennedy predictions:
- Bare "two" is knowledge-sensitive via quality filter + belief channel (a speaker
  uncertain between s2 and s3 cannot use bare or moreThan — both fail quality)
- Class B "at least" is uninformative at full access but INFORMATIVE at partial
  access: the quality filter forces uncertain speakers to use "at least", and L1
  reads the asymmetric observation distribution. This derives Kennedy's ignorance
  implicature from RSA alone.
-/

/-- Both theories predict knowledge-sensitivity for bare numerals. -/
theorem both_predict_knowledge_sensitivity :
    -- Kennedy bare: belief-channel effect
    getScore (l1k .bare .a3) .s2 ≠ getScore (l1k .bare .a1) .s2
    ∧
    -- Lower-bound bare: implicature cancellation
    getScore (l1_lb .two .a3) .s2 ≠ getScore (l1_lb .two .a1) .s2 := by
  native_decide

/-- At full access, Kennedy Class B is uninformative while lower-bound
bare shows standard implicature. At partial access, both are informative
but through different mechanisms (quality filter vs implicature cancellation). -/
theorem kennedy_classB_vs_lowerbound_bare :
    -- Kennedy Class B full access: no discrimination between s2 and s3
    getScore (l1k .atLeast .a3) .s2 = getScore (l1k .atLeast .a3) .s3
    ∧
    -- Lower-bound bare full access: implicature discriminates s2 from s3
    getScore (l1_lb .two .a3) .s2 > getScore (l1_lb .two .a3) .s3 := by
  native_decide

-- ============================================================================
-- Section 5e: Quality Filter Regression Tests
-- ============================================================================

/-! These theorems would have been FALSE under the old buggy E[L0] chain,
which computed E_belief[L0] (arithmetic mean) instead of the correct
exp(E_belief[ln L0]) (geometric mean via log utility). The arithmetic mean
allowed speakers to "gamble" on utterances that were potentially false at
believed worlds. The quality filter kills such utterances. -/

/-- REGRESSION: Quality enforcement — a speaker uncertain between s2 and s3
(observation: seen=2, access=2) CANNOT say "more than two" (false at s2).
Old buggy E[L0] allowed this with nonzero probability. -/
theorem quality_blocks_moreThan_uncertain :
    let o : Observation := ⟨2, .a2⟩
    getScore (RSA.Eval.ksS1 allKennedyUtts allWorldStates
      (kennedyMeaning 2) (speakerBelief o)) .moreThan = 0 := by
  native_decide

/-- REGRESSION: Same uncertain speaker cannot say bare "two" (false at s3).
Only "at least two" survives quality. -/
theorem quality_blocks_bare_uncertain :
    let o : Observation := ⟨2, .a2⟩
    getScore (RSA.Eval.ksS1 allKennedyUtts allWorldStates
      (kennedyMeaning 2) (speakerBelief o)) .bare = 0 := by
  native_decide

/-- REGRESSION: "at least two" is the ONLY utterance for an uncertain speaker.
This derives Kennedy's ignorance implicature from RSA. -/
theorem only_atLeast_survives_uncertain :
    let o : Observation := ⟨2, .a2⟩
    getScore (RSA.Eval.ksS1 allKennedyUtts allWorldStates
      (kennedyMeaning 2) (speakerBelief o)) .atLeast > 0 := by
  native_decide

-- ============================================================================
-- Section 5f: Kennedy Type-Shifting Ambiguity (G&S Experiment 2 Rescue)
-- ============================================================================

/-! ## De-Fregean Ambiguity: Exact vs Type-Lowered

Kennedy (2015, Section 3.1) shows bare numerals are systematically ambiguous:
- **De-Fregean (exact)**: `max{n | D(n)} = m` — two-sided (basic meaning)
- **Type-lowered (lower-bound)**: via Partee's BE + iota → `∃x[P(x) ∧ #(x) = m]`

Both meanings are available; the de-Fregean one is basic, the lower-bounded one
derived via type-shifting. This is a genuine interpretation ambiguity, handled by
marginalizing over interpretations (cf. Scontras & Pearl 2021).

**Key prediction for G&S Experiment 2**:
- Full access: speaker can commit to exact interp → L1 selects exact → exact reading
- Partial access: exact interp carries quality risk (false at some believed worlds),
  lower-bound interp is safe → L1 selects lower-bound → lower-bound reading

This derives the G&S finding from Kennedy semantics without abandoning exactness. -/

/-- Kennedy interpretation dimension: de-Fregean exact vs type-lowered lower-bound. -/
inductive KennedyInterp where
  | exact      -- max{n | D(n)} = m  (de-Fregean, basic)
  | lowerBound -- ∃x[P(x) ∧ #(x) = m] (type-lowered via BE + iota)
  deriving DecidableEq, BEq, Repr

def allKennedyInterps : List KennedyInterp := [.exact, .lowerBound]

/-- Kennedy meaning parametrized by interpretation.
    Under exact interp: bare = max{d | P(d)} = m (Kennedy max semantics).
    Under lower-bound interp: bare = max{d | P(d)} ≥ m (type-lowered).
    moreThan and atLeast are unambiguous across interpretations. -/
def kennedyMeaningInterp (m : Nat) (interp : KennedyInterp)
    : KennedyUtt → WorldState → Bool
  | .bare, s => match interp with
    | .exact      => maxMeaning .eq m s.toNat
    | .lowerBound => maxMeaning .ge m s.toNat
  | .moreThan, s => maxMeaning .gt m s.toNat
  | .atLeast, s  => maxMeaning .ge m s.toNat

/-- Kennedy L1 with interpretation ambiguity via unified `ksL1Interp`.
    Uses the core infrastructure that every RSA model should use:
    the interpretation space is a standard latent variable, not a special case. -/
def l1ka (u : KennedyUtt) (a : Access)
    (interpPrior : KennedyInterp → ℚ := λ _ => 1)
    : List (WorldState × ℚ) :=
  RSA.Eval.ksL1Interp allKennedyUtts allWorldStates (observationsFor a) allKennedyInterps
    (kennedyMeaningInterp 2) (λ _ => 1) (obsProb · a) speakerBelief interpPrior u

/-- Which interpretation does L1 select? Joint distribution over (world, interp). -/
def l1ka_interp (u : KennedyUtt) (a : Access) :=
  RSA.Eval.ksL1InterpMarginal allKennedyUtts allWorldStates (observationsFor a) allKennedyInterps
    (kennedyMeaningInterp 2) (λ _ => 1) (obsProb · a) speakerBelief (λ _ => 1) u

-- Key predictions

/-- Full access, bare "two": exact reading (s2 >> s3).
    Speaker knows the world, can commit to exact interp, so L1 selects exact. -/
theorem kennedy_ambig_bare_full_exact :
    RSA.Eval.getScore (l1ka .bare .a3) .s2 >
    RSA.Eval.getScore (l1ka .bare .a3) .s3 := by
  native_decide

/-- Partial access, bare "two": lower-bound reading (s3 gets substantial mass).
    Exact interp has quality risk → lower-bound interp preferred → s3 viable.
    This is the G&S Experiment 2 finding derived from Kennedy + type-shifting. -/
theorem kennedy_ambig_bare_partial_lowerbound :
    RSA.Eval.getScore (l1ka .bare .a2) .s3 > 0 := by
  native_decide

/-- The lower-bound effect: s3 mass increases from full to partial access.
    Under full access, exact interp dominates → s3 ≈ 0.
    Under partial access, lower-bound interp contributes → s3 > 0. -/
theorem kennedy_ambig_exactness_weakens :
    RSA.Eval.getScore (l1ka .bare .a2) .s3 >
    RSA.Eval.getScore (l1ka .bare .a3) .s3 := by
  native_decide

end KennedyNumerals

-- ============================================================================
-- Section 6: Grounding
-- ============================================================================

section Grounding

open KnowledgeState
open TruthConditional.Numeral

/-- Kennedy meaning derives from maxMeaning (not hand-rolled). -/
theorem kennedy_meaning_from_maxMeaning (m : Nat) (u : KennedyUtt) (s : WorldState) :
    kennedyMeaning m u s = match u with
      | .bare => maxMeaning .eq m s.toNat
      | .moreThan => maxMeaning .gt m s.toNat
      | .atLeast => maxMeaning .ge m s.toNat := by
  cases u <;> rfl

/-- Lower-bound meaning derives from NumeralTheory.meaning. -/
theorem lb_meaning_grounded (u : NumUtterance) (s : WorldState) :
    lbMeaning u s = LowerBound.meaning (uttToBareNumeral u) s.toNat := by
  rfl

/-- liftTheory Exact = maxMeaning .eq composed with type maps. -/
theorem liftTheory_exact_eq (w : BareNumeral) (s : WorldState) :
    liftTheory Exact w s = maxMeaning .eq w.toNat s.toNat := by
  rfl

/-- liftTheory LowerBound = maxMeaning .ge composed with type maps. -/
theorem liftTheory_lb_eq (w : BareNumeral) (s : WorldState) :
    liftTheory LowerBound w s = maxMeaning .ge w.toNat s.toNat := by
  rfl

/-- Quantifier meaning matches Domains.Quantity.meaning. -/
theorem quantifier_meaning_grounded (u : QUtt) (s : WorldState) :
    quantifierMeaning u s =
    RSA.Domains.Quantity.meaning 3
      (match u with | .none_ => .none_ | .some_ => .some_ | .all => .all)
      ⟨s.toNat, by cases u <;> cases s <;> decide⟩ := by
  cases u <;> cases s <;> native_decide

end Grounding

end RSA.GoodmanStuhlmuller2013
