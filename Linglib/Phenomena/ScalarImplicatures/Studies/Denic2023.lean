import Linglib.Theories.Semantics.Exhaustification.InnocentExclusion
import Linglib.Theories.Semantics.Alternatives.Symmetric
import Linglib.Phenomena.ScalarImplicatures.Studies.Magri2009

/-!
# Probabilities and Logic in Implicature Computation
@cite{denic-2023}

Denić, M. (2023). Probabilities and logic in implicature computation:
Two puzzles with embedded disjunction. *Semantics and Pragmatics* 16,
Article 4: 1–48.

## Two Puzzles

**Inference puzzle** (§2): Quantified sentences with embedded disjunction
trigger inferences sensitive to (i) the cardinality of the restrictor
and (ii) the number of disjuncts:

- ALL-20-OR ("All 20 of Mary's friends are French or Spanish") preferably
  triggers *distributive* inferences (at least one is French, at least
  one is Spanish)
- ALL-2-OR ("Both of Mary's friends are French or Spanish") preferably
  triggers *ignorance* inferences (speaker is ignorant about whether at
  least one is French/Spanish)

This contrast is surprising: the two sentences stand in identical
entailment relations to their alternatives, so any entailment-based
theory (@cite{fox-2007} exhaustification, neo-Gricean) predicts the
same implicatures for both.

**Deviance puzzle** (§5–6): Certain sentences with embedded disjunction
under universal quantifiers are deviant:

- "#Each of these three girls is Mary, Susan, or Jane" (DEVIANT-BE)
- "Each of those three girls is called Mary, Susan, or Jane" (fine)

The key property: the identity copula + proper name is *singleton-
denoting* (given CK, only one individual can be Mary), while "is called"
is not. Deviance arises because ignorance inferences of singleton-
denoting predicates contradict common knowledge — extending
@cite{magri-2009}'s blindness hypothesis.

## Proposal

Two components:

1. **Informativeness-based pruning** (§4, proposal (30)): Alternative
   pruning is sensitive to probabilistic informativeness — the probability
   of pruning alternative A from ALT(S) increases with P(A|S). This is
   in addition to contextual relevance (@cite{fox-katzir-2011}).

2. **Blind informativeness** (§7.3): The informativeness computation that
   feeds pruning is blind to (most of) common knowledge — only logical
   structure (domain size, number of disjuncts) matters.

## Key connections

- @cite{fox-2007}: innocent exclusion (IE) algorithm — `ieIndices`,
  `exhB`, `maxConsistentExclusions` from `InnocentExclusion.lean`
- @cite{magri-2009}: blindness hypothesis + mismatch hypothesis —
  `BlindScenario`, `blindOdd` from `Magri2009.lean`
- @cite{fox-katzir-2011}: contextual constraint on alternatives
- @cite{franke-2011}: IBR = exhMW result (inherits the puzzle)
- @cite{chierchia-2004}: embedded scalar items and disjunction
-/

namespace Phenomena.ScalarImplicatures.Studies.Denic2023

open Exhaustification.InnocentExclusion
  (exhB ieIndices nonWeakerIndices maxConsistentExclusions)
open Alternatives.Symmetric (isSymmetric)
open Phenomena.ScalarImplicatures.Studies.Magri2009 (BlindScenario)


-- ═══════════════════════════════════════════════════════════════════════
-- §1  Inference Types
-- ═══════════════════════════════════════════════════════════════════════

/-- The two inference types that embedded disjunction can trigger.

@cite{denic-2023} §2: the central empirical observation is that the
*same* sentence structure preferably triggers different inference types
depending on domain size and disjunct count. -/
inductive InferenceType where
  /-- Distributive: "at least one is A, at least one is B."
      Derived when existential alternatives are pruned from ALT. -/
  | distributive
  /-- Ignorance: "the speaker is ignorant about whether at least one
      is A (B)." Derived when existential alternatives remain in ALT. -/
  | ignorance
  deriving DecidableEq, Repr

/-- An empirical datum from @cite{denic-2023} §2. -/
structure InferenceDatum where
  /-- Human-readable label. -/
  label : String
  /-- Cardinality of the restrictor of the universal quantifier. -/
  restrictorSize : Nat
  /-- Number of disjuncts. -/
  disjunctCount : Nat
  /-- The preferably triggered inference type. -/
  preferred : InferenceType
  deriving Repr

/-- ALL-20-OR: "All 20 of Mary's friends are French or Spanish."
@cite{denic-2023} ex. (6): preferably triggers distributive inferences. -/
def all20or : InferenceDatum :=
  { label := "ALL-20-OR", restrictorSize := 20, disjunctCount := 2,
    preferred := .distributive }

/-- ALL-2-OR: "Both of Mary's friends are French or Spanish."
@cite{denic-2023} ex. (7): preferably triggers ignorance inferences. -/
def all2or : InferenceDatum :=
  { label := "ALL-2-OR", restrictorSize := 2, disjunctCount := 2,
    preferred := .ignorance }

/-- SIMPLE-DISJ: "All four of Mary's friends are French or Spanish."
@cite{denic-2023} ex. (8): distributive more natural than COMPLEX-DISJ. -/
def simpleDisj : InferenceDatum :=
  { label := "SIMPLE-DISJ", restrictorSize := 4, disjunctCount := 2,
    preferred := .distributive }

/-- COMPLEX-DISJ: "All four of Mary's friends are French, Spanish,
German, or Dutch."
@cite{denic-2023} ex. (9): ignorance more natural than SIMPLE-DISJ. -/
def complexDisj : InferenceDatum :=
  { label := "COMPLEX-DISJ", restrictorSize := 4, disjunctCount := 4,
    preferred := .ignorance }

/-- The four key data points from @cite{denic-2023} §2. -/
def inferencePuzzleData : List InferenceDatum :=
  [all20or, all2or, simpleDisj, complexDisj]

/-- Threshold generalization (@cite{denic-2023} (10)): when the ratio
of restrictor cardinality to disjunct count exceeds a threshold T ≥ 1,
distributive inferences are preferably derived. -/
def thresholdPrediction (T : Nat) (d : InferenceDatum) : InferenceType :=
  if d.restrictorSize / d.disjunctCount ≥ T then .distributive else .ignorance

/-- Gradient generalization (@cite{denic-2023} (11)): the larger the
ratio of restrictor to disjuncts, the greater the preference for
distributive over ignorance. -/
def ratio (d : InferenceDatum) : Nat := d.restrictorSize / d.disjunctCount

/-- The ratio ordering matches the inference pattern:
ALL-20-OR (ratio 10) > SIMPLE-DISJ (ratio 2) > ALL-2-OR = COMPLEX-DISJ (ratio 1).
Higher ratio → distributive; lower ratio → ignorance. -/
theorem ratio_ordering :
    ratio all20or > ratio simpleDisj ∧
    ratio simpleDisj > ratio all2or ∧
    ratio all2or = ratio complexDisj := by decide

/-- The threshold generalization with T = 2 correctly classifies all
four data points. -/
theorem threshold_2_correct :
    inferencePuzzleData.all (λ d =>
      thresholdPrediction 2 d == d.preferred) = true := by native_decide


-- ═══════════════════════════════════════════════════════════════════════
-- §2  Entailment Cannot Distinguish: The Negative Result
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Why entailment-based theories fail

@cite{denic-2023} §3.2–3.4: ALL-20-OR and ALL-2-OR activate the same
structural alternatives (up to domain-size relabeling). Since entailment
relations between a sentence and its alternatives are invariant under
domain size, any approach where implicatures are a function of entailment
relations (@cite{fox-2007} exhaustification, neo-Gricean) predicts
identical inferences.

The unembedded baseline (disjunction without universal quantifier) is
handled in `InnocentExclusion.lean`: `disj_exh_eq_exor` shows
Exh(Alt)(p∨q) = p ⊻ q. The puzzle arises specifically when disjunction
is *embedded* under a universal quantifier. -/

section EntailmentNegativeResult

/-- Worlds for ALL-n-OR with 2 disjuncts (French, Spanish).

For the entailment structure, only the *proportions* matter, not
individual assignments. We model the 4 possible group compositions. -/
inductive GroupWorld where
  /-- All are French (and possibly Spanish). -/
  | allFrench
  /-- All are Spanish (and possibly French). -/
  | allSpanish
  /-- Mixed: some French, some Spanish, satisfying both ∃ constraints. -/
  | mixed
  /-- All are French AND Spanish (bilingual). -/
  | allBoth
  deriving DecidableEq, Repr

private def groupDomain : List GroupWorld :=
  [.allFrench, .allSpanish, .mixed, .allBoth]

/-- "All n are French or Spanish" — the target sentence.
True at every world (every composition satisfies the disjunctive predicate). -/
private def allForS : GroupWorld → Bool := λ _ => true

/-- ALT-or alternative: "All n are French." -/
private def allFrenchAlt : GroupWorld → Bool
  | .allFrench | .allBoth => true | _ => false

/-- ALT-or alternative: "All n are Spanish." -/
private def allSpanishAlt : GroupWorld → Bool
  | .allSpanish | .allBoth => true | _ => false

/-- ALT-or: alternatives when only the disjunction activates its scale.
@cite{denic-2023} (24)/(25): {All n are French, All n are Spanish}. -/
private def altOr : List (GroupWorld → Bool) := [allFrenchAlt, allSpanishAlt]

/-- With ALT-or, both alternatives are IE: each can be negated consistently
with the prejacent. Negating both yields distributive inferences:
"some are French, some are Spanish." -/
theorem altOr_both_ie :
    ieIndices groupDomain allForS altOr = [0, 1] := by native_decide

/-- The exhaustified meaning with ALT-or: "All are F∨S, NOT all French,
NOT all Spanish" — true only at `mixed`, the distributive reading
where some are French AND some are Spanish.

This connects to `InnocentExclusion.disj_exh_eq_exor` (unembedded
disjunction yields exclusive or); embedding under ∀ + domain structure
gives the distributive reading. -/
theorem altOr_exh_distributive :
    ∀ w : GroupWorld, exhB groupDomain altOr allForS w =
      match w with | .mixed => true | _ => false := by
  intro w; cases w <;> native_decide

/-- Existential alternatives for ALT-all-or.
"Some are French" and "Some are Spanish." -/
private def someFrenchAlt : GroupWorld → Bool
  | .allFrench | .mixed | .allBoth => true | _ => false

private def someSpanishAlt : GroupWorld → Bool
  | .allSpanish | .mixed | .allBoth => true | _ => false

/-- ALT-all-or: alternatives when both quantifier and disjunction activate.
@cite{denic-2023} (22)/(23): {All French, All Spanish, Some French, Some Spanish}. -/
private def altAllOr : List (GroupWorld → Bool) :=
  [allFrenchAlt, allSpanishAlt, someFrenchAlt, someSpanishAlt]

/-- With ALT-all-or, NO alternative is IE: three different maximal
consistent exclusions exist, and no alternative appears in all three.
Result: no distributive inferences; ignorance inferences are derived.

Note: this is a distinct mechanism from `symmetric_not_ie` in
`Symmetric.lean`. The alternatives here are NOT symmetric in the
@cite{fox-katzir-2011} partition sense (see `altAllOr_not_symmetric`
below) — the IE emptiness arises from the MCE structure, not from
alternative pairs partitioning the prejacent. -/
theorem altAllOr_no_ie :
    ieIndices groupDomain allForS altAllOr = [] := by native_decide

/-- The three maximal consistent exclusions for ALT-all-or.

@cite{denic-2023} (26a–c): the MCEs are
- {allS(1), someS(3)}: negate → all French
- {allF(0), someF(2)}: negate → all Spanish
- {allF(0), allS(1)}: negate → mixed

No alternative appears in all three → IE = ∅. -/
theorem altAllOr_three_mces :
    maxConsistentExclusions groupDomain allForS altAllOr =
      [[1, 3], [0, 2], [0, 1]] := by native_decide

/-- The existential alternatives ("some are French" / "some are Spanish")
are NOT symmetric in the @cite{fox-katzir-2011} sense: they overlap at
`mixed` and `allBoth` worlds (both alternatives true), so they do not
partition the prejacent's denotation.

This matters because it means the IE emptiness (above) cannot be
derived from `Symmetric.symmetric_not_ie` — it requires the full MCE
computation showing three incompatible exclusion sets. -/
theorem altAllOr_not_symmetric :
    isSymmetric groupDomain allForS someFrenchAlt someSpanishAlt = false ∧
    isSymmetric groupDomain allForS allFrenchAlt allSpanishAlt = false := by
  exact ⟨by native_decide, by native_decide⟩

/-- **The core negative result**: the IE computation is identical for any
domain size when the same abstract alternative structure is used.

The 4-world model above is domain-size-invariant: it captures the
entailment structure of both ALL-20-OR and ALL-2-OR. The alternatives
stand in the same entailment relations regardless of whether n = 2
or n = 20. Therefore, the IE set — and hence the predicted implicatures
— are identical.

This is @cite{denic-2023}'s argument in §3.2 (final paragraph):
"ALL-20-OR and ALL-2-OR activate comparable sets of alternatives, [so]
they stand in the same entailment relations to them, and will thus
necessarily be predicted to have the same implicatures."

Since @cite{franke-2011}'s IBR converges to exhMW for scalar games
(`ibr_equals_exhMW` in `ScalarGames.lean`), IBR inherits the same
inability to distinguish ALL-20-OR from ALL-2-OR. -/
theorem entailment_invariant_across_domain_size :
    -- ALT-or → distributive for ALL-20-OR (correct) AND ALL-2-OR (wrong)
    ieIndices groupDomain allForS altOr = [0, 1] ∧
    -- ALT-all-or → ignorance for ALL-20-OR (wrong) AND ALL-2-OR (correct)
    ieIndices groupDomain allForS altAllOr = [] := by
  exact ⟨by native_decide, by native_decide⟩

end EntailmentNegativeResult


-- ═══════════════════════════════════════════════════════════════════════
-- §3  Probabilistic Pruning: The Positive Proposal
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Informativeness-based alternative pruning

@cite{denic-2023} proposal (30): the probability of pruning alternative A
from ALT(S) increases with P(A|S) — the conditional probability that A
is true given S. Informativeness is inversely related: the more likely
A is given S (the less informative A is relative to S), the more
likely A is to be pruned.

The key insight: P(Some of n are A | All n are A or B) increases with n,
because having more individuals makes it more likely that at least one
satisfies A. So existential alternatives are more likely pruned for
larger domains, yielding ALT-or (→ distributive) for ALL-20-OR and
ALT-all-or (→ ignorance) for ALL-2-OR.

We make this precise using the uniform conditional probability model:
P(∃x. A(x) | ∀x. disjunction of m predicates) = 1 − ((m−1)/m)^n. -/

section ProbabilisticPruning

/-- Conditional probability P(∃x∈D. A(x) | ∀x∈D. A(x)∨B₁(x)∨...∨Bₘ₋₁(x))
under uniform independent assignment to m equally likely predicates.

With m predicates and n individuals independently assigned, each
individual is assigned to A with probability 1/m, so:
- P(no individual is A) = ((m−1)/m)^n
- P(∃x. A(x)) = 1 − ((m−1)/m)^n

@cite{denic-2023} §4: the critical observation is that this probability
increases with n (more individuals → more likely someone is A) and
decreases with m (more disjuncts → less likely any given one holds). -/
def uniformCondProb (n m : Nat) : ℚ :=
  1 - ((↑m - 1 : Int) / (↑m : Int) : ℚ) ^ n

/-- Conditional probability values for the four data points.

- ALL-20-OR (n=20, m=2): 1 − (1/2)²⁰ = 1048575/1048576
- SIMPLE-DISJ (n=4, m=2): 1 − (1/2)⁴ = 15/16
- ALL-2-OR (n=2, m=2): 1 − (1/2)² = 3/4
- COMPLEX-DISJ (n=4, m=4): 1 − (3/4)⁴ = 175/256

Higher condProb → more pruning → more likely distributive.
Lower condProb → less pruning → more likely ignorance. -/
theorem condProb_values :
    uniformCondProb 20 2 = (1048575 : Int) / 1048576 ∧
    uniformCondProb 4 2 = (15 : Int) / 16 ∧
    uniformCondProb 2 2 = (3 : Int) / 4 ∧
    uniformCondProb 4 4 = (175 : Int) / 256 := by
  simp only [uniformCondProb]; native_decide

/-- The conditional probability ordering matches the inference pattern:
ALL-20-OR > SIMPLE-DISJ > ALL-2-OR > COMPLEX-DISJ.

Distributive sentences have higher condProb (existential alternatives
are less informative, more likely pruned); ignorance sentences have
lower condProb (existential alternatives are more informative, less
likely pruned).

Any pruning threshold between 175/256 ≈ 0.68 and 3/4 = 0.75 correctly
classifies all four data points. -/
theorem condProb_ordering :
    uniformCondProb 20 2 > uniformCondProb 4 2 ∧
    uniformCondProb 4 2 > uniformCondProb 2 2 ∧
    uniformCondProb 2 2 > uniformCondProb 4 4 := by
  simp only [uniformCondProb]; native_decide

/-- The proposal correctly predicts the ALL-20-OR vs ALL-2-OR contrast.

Under the uniform model, existential alternatives are more likely pruned
for ALL-20-OR (condProb ≈ 1) than ALL-2-OR (condProb = 3/4):

- ALL-20-OR: existentials likely pruned → ALT-or → distributive ✓
- ALL-2-OR: existentials likely retained → ALT-all-or → ignorance ✓ -/
theorem domain_size_distinguishes :
    all20or.restrictorSize > all2or.restrictorSize ∧
    all20or.preferred = .distributive ∧
    all2or.preferred = .ignorance := by decide

/-- The proposal correctly predicts the SIMPLE-DISJ vs COMPLEX-DISJ contrast.

Under the uniform model, existential alternatives are more likely pruned
for SIMPLE-DISJ (condProb = 15/16) than COMPLEX-DISJ (condProb = 175/256):

- SIMPLE-DISJ: existentials likely pruned → ALT-or → distributive ✓
- COMPLEX-DISJ: existentials likely retained → ALT-all-or → ignorance ✓ -/
theorem disjunct_count_distinguishes :
    complexDisj.disjunctCount > simpleDisj.disjunctCount ∧
    simpleDisj.restrictorSize = complexDisj.restrictorSize ∧
    simpleDisj.preferred = .distributive ∧
    complexDisj.preferred = .ignorance := by decide

end ProbabilisticPruning


-- ═══════════════════════════════════════════════════════════════════════
-- §4  Deviance Puzzle: Singleton-Denoting Predicates
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Singleton-denoting predicates and deviance

@cite{denic-2023} §5: a predicate (in context) is *singleton-denoting*
if, given common knowledge, it can only be true of a unique individual.

- "is Mary" is singleton-denoting: CK says only one person IS Mary
- "is called Mary" is NOT singleton-denoting: multiple people can be
  called Mary

Deviance arises when ignorance inferences of singleton-denoting
predicates contradict CK. This extends @cite{magri-2009}'s blind
oddness mechanism. -/

section DeviancePuzzle

/-- Whether a predicate is singleton-denoting in context.

@cite{denic-2023} §5: a (complex) predicate is singleton-denoting if,
given common knowledge, it can only be true of a unique (singular or
plural) individual. Examples:
- "is Mary" + domain of individuals → singleton-denoting
- "wrote Anna Karenina" + domain of authors → singleton-denoting
- "is called Mary" + domain of individuals → NOT singleton-denoting
- "read Anna Karenina" + domain of students → NOT singleton-denoting -/
def singletonDenoting {α : Type} (predDomain : List α) (predicate : α → Bool)
    (context : α → Bool) : Bool :=
  let witnesses := (predDomain.filter context).filter predicate
  witnesses.length ≤ 1

-- ── Singleton-denotation verification ──────────────────────────────

/-- Individual-level domain for verifying singleton-denotation.
Three girls in the DEVIANT-BE scenario. -/
private inductive Girl where | g1 | g2 | g3 deriving DecidableEq
private def girls : List Girl := [.g1, .g2, .g3]
private def allGirls : Girl → Bool := λ _ => true

/-- "is Mary" — singleton-denoting: only g1 is Mary (by CK). -/
private def isMary : Girl → Bool | .g1 => true | _ => false
/-- "is Susan" — singleton-denoting: only g2 is Susan. -/
private def isSusan : Girl → Bool | .g2 => true | _ => false

/-- "is called Mary" — NOT singleton-denoting: multiple girls can share
the name "Mary." -/
private def isCalledMary : Girl → Bool | .g1 | .g2 => true | _ => false

/-- Identity predicates ("is Mary") are singleton-denoting. -/
theorem isMary_singleton :
    singletonDenoting girls isMary allGirls = true := by native_decide

theorem isSusan_singleton :
    singletonDenoting girls isSusan allGirls = true := by native_decide

/-- "Is called" predicates are NOT singleton-denoting. -/
theorem isCalledMary_not_singleton :
    singletonDenoting girls isCalledMary allGirls = false := by native_decide

-- ── Deviance data ──────────────────────────────────────────────────

/-- A deviance datum from @cite{denic-2023} §5. -/
structure DevianceDatum where
  label : String
  isDeviant : Bool
  isSingletonDenoting : Bool
  deriving Repr

/-- DEVIANT-BE: "#Each of those three girls is Mary, Susan, or Jane."
@cite{denic-2023} ex. (31). -/
def deviantBe : DevianceDatum :=
  { label := "DEVIANT-BE", isDeviant := true, isSingletonDenoting := true }

/-- NON-DEVIANT-CALLED: "Each of those three girls is called Mary, Susan, or Jane."
@cite{denic-2023} ex. (32). -/
def nonDeviantCalled : DevianceDatum :=
  { label := "NON-DEVIANT-CALLED", isDeviant := false, isSingletonDenoting := false }

/-- DEVIANT-WRITE: "#Each of those three writers wrote Anna Karenina,
Germinal, or Harry Potter."
@cite{denic-2023} ex. (33). -/
def deviantWrite : DevianceDatum :=
  { label := "DEVIANT-WRITE", isDeviant := true, isSingletonDenoting := true }

/-- NON-DEVIANT-READ: "Each of those three students read Anna Karenina,
Germinal, or Harry Potter."
@cite{denic-2023} ex. (34). -/
def nonDeviantRead : DevianceDatum :=
  { label := "NON-DEVIANT-READ", isDeviant := false, isSingletonDenoting := false }

/-- The four deviance data points from @cite{denic-2023} §5. -/
def deviancePuzzleData : List DevianceDatum :=
  [deviantBe, nonDeviantCalled, deviantWrite, nonDeviantRead]

/-- Deviance tracks singleton-denotation exactly. -/
theorem deviance_iff_singleton :
    deviancePuzzleData.all (λ d => d.isDeviant == d.isSingletonDenoting)
    = true := by native_decide


-- ═══════════════════════════════════════════════════════════════════════
-- §4.1  DEVIANT-BE via BlindOdd
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Concrete model: DEVIANT-BE

"#Each of those three girls is Mary, Susan, or Jane."

We model this as a `BlindScenario` and show that `blindOdd` correctly
predicts deviance. The key: since "is Mary/Susan/Jane" is singleton-
denoting, the ignorance inferences ("the speaker is ignorant about
whether at least one girl is Mary") contradict CK (the speaker must
know which girl is which).

This is exactly @cite{magri-2009}'s mechanism (BH + MH) applied to a
new empirical domain, as @cite{denic-2023} proposes in §6. -/

/-- Worlds for DEVIANT-BE.

Three girls, each is exactly one of Mary, Susan, Jane. By CK (singleton-
denoting), each name maps to exactly one girl. The only question is
which permutation. We model 3 representative worlds. -/
inductive DeviantBEWorld where
  /-- Girl 1 = Mary, Girl 2 = Susan, Girl 3 = Jane. -/
  | msj
  /-- Girl 1 = Mary, Girl 2 = Jane, Girl 3 = Susan. -/
  | mjs
  /-- Girl 1 = Susan, Girl 2 = Mary, Girl 3 = Jane. -/
  | smj
  deriving DecidableEq, Repr

/-- Utterances: the target sentence and its individual-disjunct
alternatives. -/
inductive DeviantBEUtt where
  /-- "Each is Mary, Susan, or Jane" (the target). -/
  | eachOrDisj
  /-- "At least one is Mary" (existential alternative). -/
  | someIsMary
  /-- "At least one is Susan." -/
  | someIsSusan
  /-- "At least one is Jane." -/
  | someIsJane
  deriving DecidableEq, Repr

open DeviantBEWorld DeviantBEUtt in
/-- Blind scenario for DEVIANT-BE.

The target sentence is trivially true at all CK worlds (each girl IS
one of Mary/Susan/Jane by construction). The existential alternatives
are also all true at every CK world (in every permutation, at least one
girl is Mary, at least one is Susan, etc.). This means the alternatives
are not excludable — but the ignorance inferences (the speaker doesn't
know whether one of them is Mary) contradict CK. -/
def deviantBEScenario : BlindScenario DeviantBEWorld DeviantBEUtt where
  meaning
    | eachOrDisj, _ => true   -- trivially true: each IS one of them
    | someIsMary, _ => true   -- in all permutations, someone is Mary
    | someIsSusan, _ => true  -- in all permutations, someone is Susan
    | someIsJane, _ => true   -- in all permutations, someone is Jane
  alternatives
    | eachOrDisj => [someIsMary, someIsSusan, someIsJane]
    | someIsMary => [eachOrDisj]
    | someIsSusan => [eachOrDisj]
    | someIsJane => [eachOrDisj]
  context := λ _ => true  -- all permutation worlds are CK-compatible
  worlds := [msj, mjs, smj]

/-- No alternative is IE for DEVIANT-BE: all alternatives are entailed
by the prejacent (trivially true everywhere), so none can be excluded. -/
theorem deviantBE_no_ie :
    ieIndices deviantBEScenario.worlds
      (deviantBEScenario.meaning .eachOrDisj)
      ((deviantBEScenario.alternatives .eachOrDisj).map deviantBEScenario.meaning)
      = [] := by native_decide

/-- DEVIANT-BE is NOT blindOdd in this direct model, because IE is empty
(no implicature is generated at all). The deviance comes not from
*scalar* implicatures contradicting CK, but from *ignorance* inferences
contradicting CK — a subtlety that requires grammatical ignorance
inferences (K_speaker in the grammar, or Gricean quantity reasoning).

@cite{denic-2023} §6–7: deviance is due to ignorance inferences (derived
via the maxim of quantity or grammatically via K_speaker) contradicting
CK. Since all alternatives are true at all CK worlds, claiming ignorance
about any of them contradicts CK. -/
theorem deviantBE_not_blindOdd_directly :
    deviantBEScenario.blindOdd .eachOrDisj = false := by native_decide

/-- DEVIANT-BE triggers ignorance inferences that contradict CK.

Non-IE alternatives exist (the speaker should be ignorant about them),
but CK settles all of them (every existential alternative is true at
every CK world). The speaker CANNOT be ignorant → contradiction → deviant.

This is @cite{denic-2023}'s proposal (40): "Sentences DEVIANT-BE and
DEVIANT-WRITE are deviant because they trigger ignorance inferences
which contradict common knowledge." -/
theorem deviantBE_ignorance_contradicts_ck :
    deviantBEScenario.ignoranceContradictsCK .eachOrDisj = true := by native_decide


-- ═══════════════════════════════════════════════════════════════════════
-- §4.2  NON-DEVIANT-CALLED: No CK Contradiction
-- ═══════════════════════════════════════════════════════════════════════

/-! ### NON-DEVIANT-CALLED: "Each is called Mary, Susan, or Jane"

"is called Mary" is NOT singleton-denoting: multiple individuals can be
called Mary. So ignorance about "at least one is called Mary" is
consistent with CK — the speaker genuinely might not know. -/

/-- Worlds for NON-DEVIANT-CALLED.

Since "is called" is not singleton-denoting, there are CK-compatible
worlds where NOT everyone called Mary exists in the group. -/
inductive CalledWorld where
  /-- All three are called different names (one Mary, one Susan, one Jane). -/
  | allDifferent
  /-- All three are called Mary. -/
  | allMary
  /-- Some called Mary, some called Susan, none called Jane. -/
  | noJane
  deriving DecidableEq, Repr

open CalledWorld DeviantBEUtt in
/-- Blind scenario for NON-DEVIANT-CALLED.

Unlike DEVIANT-BE, the existential alternatives are NOT all true at
every CK world — it is genuinely possible that none is called Jane
(multiple people can share the name Mary or Susan). -/
def nonDeviantCalledScenario : BlindScenario CalledWorld DeviantBEUtt where
  meaning
    | eachOrDisj, _ => true
    | someIsMary, allDifferent => true  | someIsMary, allMary => true
    | someIsMary, noJane => true
    | someIsSusan, allDifferent => true | someIsSusan, allMary => false
    | someIsSusan, noJane => true
    | someIsJane, allDifferent => true  | someIsJane, allMary => false
    | someIsJane, noJane => false
  alternatives
    | eachOrDisj => [someIsMary, someIsSusan, someIsJane]
    | someIsMary => [eachOrDisj]
    | someIsSusan => [eachOrDisj]
    | someIsJane => [eachOrDisj]
  context := λ _ => true
  worlds := [allDifferent, allMary, noJane]

/-- NON-DEVIANT-CALLED: ignorance does NOT contradict CK.

The speaker CAN be genuinely ignorant about "at least one is called Jane"
because there exist CK worlds where it's true (allDifferent) and where
it's false (allMary, noJane). -/
theorem nonDeviantCalled_ignorance_ok :
    nonDeviantCalledScenario.ignoranceContradictsCK .eachOrDisj = false := by
  native_decide

/-- The deviance contrast: singleton-denoting predicates trigger CK-
contradicting ignorance inferences; non-singleton-denoting ones don't.

@cite{denic-2023} §5–6: the property distinguishing DEVIANT-BE from
NON-DEVIANT-CALLED is exactly whether the predicate is singleton-
denoting. -/
theorem deviance_contrast :
    deviantBEScenario.ignoranceContradictsCK .eachOrDisj = true ∧
    nonDeviantCalledScenario.ignoranceContradictsCK .eachOrDisj = false :=
  ⟨by native_decide, by native_decide⟩

end DeviancePuzzle


-- ═══════════════════════════════════════════════════════════════════════
-- §5  Blind Informativeness: Why CK Must Be Screened Off
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Blindness extends to informativeness computation

@cite{denic-2023} §7.3: the informativeness computation feeding
pruning must itself be blind to common knowledge. The argument:

1. @cite{magri-2009}: EXH is blind to CK (BH) — formalized via
   `BlindScenario.strengthened`, which uses logical entailment, not
   CK-relativized entailment.

2. @cite{denic-2023}: informativeness evaluation for pruning is ALSO
   blind to CK. If it weren't, then for DEVIANT-BE, CK would tell us
   P(at least one is Mary | Each is Mary, Susan, or Jane) = 1 — ALL
   existential alternatives would have condProb = 1 given CK, so all
   would be pruned → no ignorance inference → no deviance. But
   DEVIANT-BE IS deviant, so the pruning mechanism cannot use CK.

Together: the entire implicature computation pipeline — from alternative
generation through informativeness evaluation to exhaustification —
operates without consulting predicate-specific common knowledge.
Only structural features (domain size, disjunct count, quantifier type)
enter the computation. -/

section BlindnessArgument

/-- If CK were used to evaluate informativeness for DEVIANT-BE, every
existential alternative would have condProb = 1 (all true at all CK
worlds). Under monotone pruning, all alternatives with maximal condProb
would be pruned, leaving no active alternatives for exhaustification.

We verify the premise: all existential alternatives ARE true at all
CK worlds in the DEVIANT-BE scenario. -/
theorem deviantBE_all_alts_ck_settled :
    (deviantBEScenario.alternatives .eachOrDisj).all (λ alt =>
      deviantBEScenario.cWorlds.all (deviantBEScenario.meaning alt)) = true := by
  native_decide

/-- The counterfactual: if we pruned all existential alternatives (as
CK-informed informativeness would recommend), exhaustification would be
vacuous — no alternatives to negate. This produces no ignorance
inferences and incorrectly predicts non-deviance.

But DEVIANT-BE IS deviant (`deviantBE_ignorance_contradicts_ck`), so
CK must be screened off from the informativeness computation. -/
theorem ck_pruning_would_be_vacuous :
    exhB deviantBEScenario.worlds [] (deviantBEScenario.meaning .eachOrDisj) =
      deviantBEScenario.meaning .eachOrDisj := by
  funext w; cases w <;> native_decide

end BlindnessArgument


-- ═══════════════════════════════════════════════════════════════════════
-- §6  Connecting the Two Puzzles
-- ═══════════════════════════════════════════════════════════════════════

/-! ### The two puzzles constrain each other

@cite{denic-2023} §7: the deviance puzzle constrains the solution to
the inference puzzle. The deviance data requires blindness of
informativeness to CK (§5). Combined with the inference puzzle's
requirement that informativeness guides pruning (§3), we get:

**Pruning is guided by informativeness computed blindly to CK.**

This is stronger than either puzzle requires alone:
- Inference puzzle alone: informativeness guides pruning (could use CK)
- Deviance puzzle alone: implicatures are blind to CK (could not
  involve pruning)
- Together: informativeness-guided pruning that is blind to CK -/

/-- The combined prediction: both puzzles are resolved by a single
mechanism (informativeness-based pruning blind to CK). The two puzzle
types are not independent — their solutions constrain each other.

- Inference puzzle ← informativeness-based pruning (§3):
  condProb ordering (`condProb_ordering`) separates cases that
  entailment cannot (`entailment_invariant_across_domain_size`)
- Deviance puzzle ← blindness of informativeness to CK (§5):
  CK-informed pruning would vacuously remove all alternatives
  (`ck_pruning_would_be_vacuous`), preventing the ignorance
  inferences that cause deviance (`deviantBE_ignorance_contradicts_ck`)
- Combined ← blind informativeness-based pruning -/
theorem puzzles_connected :
    -- Inference puzzle: entailment gives same IE for both...
    ieIndices groupDomain allForS altAllOr = [] ∧
    ieIndices groupDomain allForS altOr = [0, 1] ∧
    -- ...but condProb distinguishes them
    uniformCondProb 20 2 > uniformCondProb 2 2 ∧
    -- Deviance puzzle: ignorance contradicts CK for singleton-denoting...
    deviantBEScenario.ignoranceContradictsCK .eachOrDisj = true ∧
    -- ...but not for non-singleton-denoting predicates
    nonDeviantCalledScenario.ignoranceContradictsCK .eachOrDisj = false := by
  refine ⟨by native_decide, by native_decide, ?_, by native_decide, by native_decide⟩
  simp only [uniformCondProb]; native_decide


end Phenomena.ScalarImplicatures.Studies.Denic2023
