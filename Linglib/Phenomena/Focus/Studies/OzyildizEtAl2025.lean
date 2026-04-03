import Linglib.Theories.Semantics.Focus.Sensitivity

/-!
# Özyıldız, Qing, Roelofsen, Uegaki & Romero (2025)
@cite{ozyildiz-etal-2025}

Operationalizing focus-sensitivity in a cross-linguistic context.
Natural Language Semantics 34:47–83.

## Core Contributions

1. **Definition of focus-sensitivity** for clause-embedding predicates (def 2/58)
2. **Structural Rooth–Villalta bridge**: `liftDegreeFS` — degree predicates are
   focus-sensitive because focus alternatives determine the comparison class;
   `liftNonFS` — doxastic predicates are not (§2b)
3. **Two-step diagnostic**: inference-based + truth-based test (§3)
4. **Substrate/conflicting attitude framework**: why UE predicates can't support
   the contexts needed for Villalta-style tests (`ue_recipe_inconsistent`, §4)
5. **Conjectured semantic universals** T and I (§7)
6. **Counterexample predicates**: B'/B'' (evading truth/inference tests), D'/D''
   (false positives/negatives for non-UE predicates), P (T–I independence)

## Architecture

Focus-sensitivity for clause-embedding predicates structurally connects two
existing linglib modules:

- `Theories/Semantics/Focus/Interpretation.lean`: Rooth 1992 focus alternatives
  (`PropFocusValue W`)
- `Theories/Semantics/Attitudes/Preferential.lean`: Villalta 2008 degree
  semantics (`PreferenceFunction`, `ThresholdFunction`, `QuestionDen`)

The connection is made structural by `liftDegreeFS`, which lifts a degree
predicate μ(x,p) > θ(C) to a `ClauseEmbedPred` by setting C = altsToC(⟦α⟧f).
This makes the key insight — **focus alternatives = comparison class** —
true by construction, not just documented.

## Focus-Sensitivity: The Missing Property

Linglib's `PreferentialPredicate` tracks veridical/valence/C-distributivity
but not focus-sensitivity. This study adds it as a classifiable property,
connecting @cite{dretske-1972}'s original observation to the formal apparatus
of @cite{rooth-1992} and @cite{villalta-2008}.

## Cross-References

- @cite{qing-uegaki-2025}: Same author team; NVP question-embedding (C-distributivity + TSP)
- @cite{uegaki-sudo-2019}: The hope-wh puzzle
- @cite{romero-2015-salt}: Surprise-predicates and exhaustivity
- @cite{harner-2016}: Semantic focus-sensitivity for attitude predicates
- @cite{wehbe-flor-2022}: Focus-sensitivity and homogeneity
- @cite{tonhauser-matthewson-2016}: Desiderata for semantic data collection
-/

namespace Phenomena.Focus.Studies.OzyildizEtAl2025

open Semantics.FocusInterpretation (PropFocusValue ClauseEmbedPred IsFocusSensitive
  IsNotFocusSensitive not_fs_iff_ignores_focus liftNonFS liftNonFS_not_fs)
open Semantics.Focus.Sensitivity (liftDegreeFS liftDegreeFS_is_fs)
open Semantics.Attitudes.Preferential (PreferenceFunction ThresholdFunction QuestionDen)

-- ============================================================================
-- §1. Focus-Sensitive Clause-Embedding Predicates (Definition 2/58)
-- ============================================================================

/-!
## Definition of Focus-Sensitivity

@cite{ozyildiz-etal-2025} def 2: A clause-embedding predicate V is
focus-sensitive iff there exist a context C and two clauses S, S' that
are only different in terms of the placement of focus such that:
(i) ⌜x Vs S⌝ and ⌜x Vs S'⌝ have different truth values in C, and
(ii) the difference in truth values cannot be attributed to factors
independent from the use of V.

Condition (ii) rules out confounds from embedded focus-sensitive operators
like *only* or *even*.

### Formalization

Following @cite{rooth-1992}, two clauses "differing only in focus" have the
same ordinary semantic value but different focus semantic values. A
focus-sensitive predicate is one whose truth conditions depend on the
focus alternatives (⟦α⟧f), not just the ordinary value (⟦α⟧o).

This connects directly to @cite{villalta-2008}: the comparison class C
in the degree semantics μ(x,p) > θ(C) IS (derived from) the focus
alternatives. Focus-sensitivity = sensitivity to C.
-/

-- ============================================================================
-- §2. Concrete Predicates: Classification
-- ============================================================================

/-!
## Focus-Sensitivity Classification

@cite{ozyildiz-etal-2025} classifies predicates through their two-step test.
Results for English predicates discussed in the paper:

| Predicate | Focus-sensitive? | Evidence (paper examples) |
|-----------|-----------------|--------------------------|
| want | ✓ | (7)–(10): conflicting preferences |
| be glad | ✓ | (15): factive + conflicting attitudes |
| know | ✗ | (16): no truth-value difference |
| believe | ✗ | (53)–(54): both inferences are entailments |
| be surprised | ✓ | (20)–(24): conflicting likelihood judgments |
| guess | ✓ | (21): speech act focus-sensitivity |
-/

/-- Focus-sensitivity classification from @cite{ozyildiz-etal-2025}. -/
structure Classification where
  /-- Predicate form -/
  predicate : String
  /-- Is it focus-sensitive? -/
  focusSensitive : Bool
  /-- Is it veridical (factive)? -/
  veridical : Bool
  /-- Is it upward-entailing in complement position? -/
  upwardEntailing : Bool
  /-- Evidence summary -/
  evidence : String
  deriving Repr, BEq

def wantClass : Classification :=
  ⟨"want", true, false, false,
   "Conflicting preferences make focus-shifted sentences differ in truth value"⟩

def beGladClass : Classification :=
  ⟨"be glad", true, true, false,
   "Factive presupposition + conflicting attitudes; like want but veridical"⟩

def knowClass : Classification :=
  ⟨"know", false, true, true,
   "No truth-conditional difference: both focus variants entail each other"⟩

def believeClass : Classification :=
  ⟨"believe", false, false, true,
   "Both inference pairs are entailments; no invalidating context exists"⟩

def beSurprisedClass : Classification :=
  ⟨"be surprised", true, true, false,
   "Conflicting likelihood judgments; substrate attitude = belief presupposition"⟩

def guessClass : Classification :=
  ⟨"guess", true, false, false,
   "Speech act predicate; conflicting and substrate attitudes differ from want"⟩

def allClassifications : List Classification :=
  [wantClass, beGladClass, knowClass, believeClass, beSurprisedClass, guessClass]

-- Focus-sensitive predicates are non-UE in complement position
-- (This is the empirical pattern underlying Universal I)
theorem fs_predicates_are_nonUE :
    (allClassifications.filter (·.focusSensitive)).all (!·.upwardEntailing) = true := by
  native_decide

-- Non-focus-sensitive predicates are UE in complement position
theorem nonfs_predicates_are_UE :
    (allClassifications.filter (!·.focusSensitive)).all (·.upwardEntailing) = true := by
  native_decide

-- ============================================================================
-- §3b. Substrate and Conflicting Attitudes (@cite{ozyildiz-etal-2025} §4)
-- ============================================================================

/-!
## The General Recipe for Villalta-Style Contexts

@cite{ozyildiz-etal-2025} §4, ex. (22): Given predicate V and target sentences
⌜x Vs that ... A... B_F ...⌝ and ⌜x Vs that ... A_F ... B ...⌝, construct a
context C that makes all of the following true:

1. **Substrate attitude**: The presuppositions of ⌜x Vs that ... A... B_F ...⌝
2. **Conflicting attitudes**:
   - (i) x Vs that ... B ... (V applied to B-content only)
   - (ii) ¬[x Vs that ... A ...] (negation of V applied to A-content)

### Why It Works for Preferential Predicates

For *want*: substrate = DOXASTIC (belief that John will teach), conflicting =
PREFERENTIAL (Lisa prefers Thursdays, disprefers John). Different modalities
→ consistent.

For *be glad*: substrate = DOXASTIC (factive + belief), conflicting =
PREFERENTIAL. Different modalities → consistent.

For *be surprised*: substrate = DOXASTIC (belief), conflicting = LIKELIHOOD
expectations. Different modalities → consistent.

### Why It Fails for Believe (@cite{ozyildiz-etal-2025} ex. (28))

For *believe*: substrate = DOXASTIC (belief), conflicting = DOXASTIC (belief).
SAME modality → the conflicting attitude (ii) ¬[x believes A] contradicts
the substrate, because the substrate entails x believes A (by UE).

This structural impossibility explains the empirical correlation captured
by `nonfs_predicates_are_UE`: UE predicates can't support the conflicting
attitudes needed to demonstrate focus-sensitivity.
-/

/-- For a UE predicate, the substrate attitude V(x, A∧B) entails the content
    that the conflicting attitude (ii) negates: V(x, A).

    Proof: A∧B ⊆ A (pointwise), so V(x, A∧B) → V(x, A) by UE.

    @cite{ozyildiz-etal-2025} §4, ex. (28): the believe impossibility. -/
theorem ue_substrate_entails_conflicting {W E : Type*}
    (V : E → (W → Bool) → W → Bool)
    (x : E) (A B : W → Bool) (w : W)
    (h_ue : ∀ (p q : W → Bool),
              (∀ w', p w' = true → q w' = true) →
              V x p w = true → V x q w = true)
    (h_substrate : V x (fun w' => A w' && B w') w = true) :
    V x A w = true := by
  apply h_ue _ A _ h_substrate
  intro w' h; revert h; cases A w' <;> simp

/-- Corollary: no consistent Villalta-style context exists for UE predicates.

    The recipe (22) requires both V(x, A∧B) = true (substrate) and
    V(x, A) = false (conflicting attitude (ii)). But UE gives
    V(x, A∧B) → V(x, A), so these are contradictory.

    This is WHY believe, know, and other UE predicates are never
    focus-sensitive: the recipe for demonstrating focus-sensitivity
    is structurally impossible for them. -/
theorem ue_recipe_inconsistent {W E : Type*}
    (V : E → (W → Bool) → W → Bool)
    (x : E) (A B : W → Bool) (w : W)
    (h_ue : ∀ (p q : W → Bool),
              (∀ w', p w' = true → q w' = true) →
              V x p w = true → V x q w = true)
    (h_substrate : V x (fun w' => A w' && B w') w = true)
    (h_conflicting : V x A w = false) :
    False := by
  have h := ue_substrate_entails_conflicting V x A B w h_ue h_substrate
  simp [h_conflicting] at h

-- ============================================================================
-- §4. Conjectured Semantic Universals
-- ============================================================================

/-!
## Conjectured Universal T (@cite{ozyildiz-etal-2025} (62))

For any predicate V attested in natural languages, if V is focus-sensitive
then ⌜x Vs S⌝ and ⌜x Vs S'⌝ have different truth conditions, for **any**
S and S' that differ only in focus placement. In particular, if V is
compatible with finite clauses, (59a) and (59b) have different truth
conditions.

### Consequence
Universal T ensures the truth-based test (comparing truth values of two
specific focus-shifted sentences) is sufficient to detect focus-sensitivity.
Without T, a predicate like B' (§5) could be focus-sensitive only for
*particular* clause pairs, evading the test.

## Conjectured Universal I (@cite{ozyildiz-etal-2025} (68))

For any predicate V attested in natural languages, if V is focus-sensitive
then ⌜x Vs A B_F⌝ does **not** entail ⌜x Vs A⌝, for any A and B. In
particular, (63) is invalidated.

### Consequence
Universal I ensures the inference-based test (checking whether the
focused sentence entails the defocused one) correctly detects
focus-sensitivity. Without I, a predicate like B'' (§5) could be
focus-sensitive yet pass the entailment test.
-/

/-- **Conjectured Universal T** (@cite{ozyildiz-etal-2025} (62)):
    Focus-sensitive predicates exhibit sensitivity **uniformly** across
    all clause pairs differing in focus.

    If V is focus-sensitive at all, then for EVERY pair of distinct
    focus-alternative sets, there exist conditions under which V
    yields different truth values. -/
def UniversalT {W E : Type*} (V : ClauseEmbedPred W E) : Prop :=
  IsFocusSensitive V →
    ∀ (f₁ f₂ : PropFocusValue W), f₁ ≠ f₂ →
      ∃ (x : E) (p : W → Bool) (w : W), V x p f₁ w ≠ V x p f₂ w

/-- **Conjectured Universal I** (@cite{ozyildiz-etal-2025} (68)):
    If V is focus-sensitive, then ⌜x Vs A B_F⌝ does not entail ⌜x Vs A⌝,
    for any A and B.

    The inference pattern (63) involves BOTH a proposition weakening
    (A∧B → A) AND a change in focus alternatives (determined by the
    different focus structures). Universal I says this inference always
    fails for focus-sensitive predicates.

    This is independently needed from Universal T: Predicate P (69)
    satisfies T but violates I (see `predicateP_violates_I`). -/
def UniversalI {W E : Type*} (V : ClauseEmbedPred W E) : Prop :=
  IsFocusSensitive V →
    ∀ (pNarrow pBroad : W → Bool) (fNarrow fBroad : PropFocusValue W),
      (∀ w, pNarrow w = true → pBroad w = true) →  -- A∧B entails A
      pNarrow ≠ pBroad →
      ∃ (x : E) (w : W),
        V x pNarrow fNarrow w = true ∧ V x pBroad fBroad w = false

-- ============================================================================
-- §5. Counterexample Predicates B' and B''
-- ============================================================================

/-!
## Pathological Predicates

@cite{ozyildiz-etal-2025} §7 constructs predicates B' and B'' that are
focus-sensitive but evade the diagnostic test, showing it is not logically
complete (only empirically sound given Universals T and I).

### B' (@cite{ozyildiz-etal-2025} (60))

B' is exactly like *believe* except it returns FALSE when the focus
alternatives happen to match a specific "bad" set. B' is focus-sensitive
(its truth depends on focus alternatives) but the truth-based test on
the standard sentence pair (59a/b) can't detect it, because neither
test sentence triggers the special condition.

### B'' (@cite{ozyildiz-etal-2025} (64))

B'' is like *believe* except it returns FALSE when the focus alternatives
match a different specific set — one that IS triggered by the test
sentences. This makes the premise of the inference test always false,
so the entailment holds trivially, and the inference test yields a
false negative.

Both are ruled out by Universals T and I respectively, under the
assumption that such pathological predicates are not attested in
natural languages.
-/

/-- **Predicate B'** (@cite{ozyildiz-etal-2025} (60)):
    Identical to believe except returns FALSE for one specific set of
    focus alternatives.

    Focus-sensitive (depends on focus alts) but undetectable by the
    truth-based test on (59a/b) because those sentences don't trigger
    the special condition. Ruled out by Universal T. -/
def predicateB' {W E : Type*}
    (believe : E → (W → Bool) → W → Bool)
    (badAlts : PropFocusValue W)
    [DecidableEq (PropFocusValue W)] : ClauseEmbedPred W E :=
  λ x p f w => if f = badAlts then false else believe x p w

/-- B' is focus-sensitive: it gives different results for badAlts vs other alts. -/
theorem predicateB'_is_fs {W E : Type*}
    (believe : E → (W → Bool) → W → Bool)
    (badAlts otherAlts : PropFocusValue W)
    [DecidableEq (PropFocusValue W)]
    (h_ne : otherAlts ≠ badAlts)
    (x : E) (p : W → Bool) (w : W)
    (h_bel : believe x p w = true) :
    predicateB' believe badAlts x p otherAlts w ≠
    predicateB' believe badAlts x p badAlts w := by
  simp only [predicateB', h_ne, ↓reduceIte]
  rw [h_bel]
  decide

/-- B' violates Universal T: it is sensitive to only ONE pair of focus
    alternatives (the bad set vs anything else), not uniformly to all pairs. -/
theorem predicateB'_violates_T {W E : Type*}
    (believe : E → (W → Bool) → W → Bool)
    (badAlts f₁ f₂ : PropFocusValue W)
    [DecidableEq (PropFocusValue W)]
    (h1 : f₁ ≠ badAlts) (h2 : f₂ ≠ badAlts) :
    -- For any two non-bad focus alt sets, B' gives the same result
    ∀ (x : E) (p : W → Bool) (w : W),
      predicateB' believe badAlts x p f₁ w =
      predicateB' believe badAlts x p f₂ w := by
  intro x p w
  simp only [predicateB', h1, h2, ↓reduceIte]

/-- **Predicate B''** (@cite{ozyildiz-etal-2025} (64)):
    Like believe but returns FALSE for a specific set of focus alternatives
    that IS triggered by the test sentences' focus structure.

    The inference test fails because the premise (with the triggering focus)
    is always FALSE, making the entailment trivially true. Ruled out by
    Universal I. -/
def predicateB'' {W E : Type*}
    (believe : E → (W → Bool) → W → Bool)
    (triggerAlts : PropFocusValue W)
    [DecidableEq (PropFocusValue W)] : ClauseEmbedPred W E :=
  λ x p f w => if f = triggerAlts then false else believe x p w

/-- B'' makes the inference-test premise trivially false:
    when the test sentence has the triggering focus, B'' is always false,
    so the inference (false → anything) is trivially valid. -/
theorem predicateB''_trivializes_inference {W E : Type*}
    (believe : E → (W → Bool) → W → Bool)
    (triggerAlts : PropFocusValue W)
    [DecidableEq (PropFocusValue W)]
    (x : E) (p : W → Bool) (w : W) :
    predicateB'' believe triggerAlts x p triggerAlts w = false := by
  simp only [predicateB'']
  rfl

-- ============================================================================
-- §5a. Predicate P: Independence of T and I (@cite{ozyildiz-etal-2025} (69))
-- ============================================================================

/-!
## Predicate P: T and I Are Independent

@cite{ozyildiz-etal-2025} (69) constructs Predicate P to show that
Universals T and I are independently needed — neither subsumes the other.

### Definition

⌜x Ps φ⌝ is true iff:
(a) x says φ, AND
(b) x believes that one of the propositions in φ's focus alternatives is true.

### Properties

- P IS focus-sensitive: condition (b) depends on the focus alternatives.
- P satisfies Universal T: its focus-sensitivity is uniform — the definition
  makes no reference to particular sets of focus alternatives or particular
  positions of focus (unlike B' and B'').
- P VIOLATES Universal I: the inference (63) holds for P, because
  (70a) → (71a) by UE of *say*, and (70b) → (71b) as long as the embedded
  clause is a member of the focus alternatives (footnote 16).

Therefore, T cannot rule out P, but I can. This shows T and I are
logically independent: both are needed for the two-step diagnostic
to be empirically sound.
-/

/-- **Predicate P** (@cite{ozyildiz-etal-2025} (69)):
    ⌜x Ps φ⌝ = x says φ ∧ x believes some focus alternative of φ.

    Focus-sensitive (condition (b) depends on focus alternatives), satisfies
    Universal T (uniform sensitivity), but violates Universal I (inference (63)
    holds). This shows T and I are independently needed.

    `believesSomeAlt` abstracts condition (b): whether x believes at least one
    proposition in the focus alternative set. -/
def predicateP {W E : Type*}
    (say : E → (W → Bool) → W → Bool)
    (believesSomeAlt : E → PropFocusValue W → W → Bool) : ClauseEmbedPred W E :=
  λ x p f w => say x p w && believesSomeAlt x f w

/-- P is focus-sensitive when believesSomeAlt distinguishes some focus sets. -/
theorem predicateP_is_fs {W E : Type*}
    (say : E → (W → Bool) → W → Bool)
    (believesSomeAlt : E → PropFocusValue W → W → Bool)
    (x : E) (p : W → Bool) (w : W)
    (f₁ f₂ : PropFocusValue W)
    (h_say : say x p w = true)
    (h_yes : believesSomeAlt x f₁ w = true)
    (h_no : believesSomeAlt x f₂ w = false) :
    IsFocusSensitive (predicateP say believesSomeAlt) := by
  refine ⟨x, p, f₁, f₂, w, ?_⟩
  simp [predicateP, h_say, h_yes, h_no]

/-- P violates Universal I: the inference (63) CAN hold.

    When *say* is UE (saying A∧B entails saying A) and belief in a
    focus alternative extends monotonically (believing some alt in fNarrow
    entails believing some alt in fBroad — e.g., because the embedded clause
    itself is in fBroad, per footnote 16), then the full entailment
    V(x, A∧B, fNarrow) → V(x, A, fBroad) goes through.

    This contradicts Universal I, which requires this entailment to FAIL
    for all focus-sensitive predicates. Hence P is ruled out by I but not T. -/
theorem predicateP_violates_I {W E : Type*}
    (say : E → (W → Bool) → W → Bool)
    (believesSomeAlt : E → PropFocusValue W → W → Bool)
    (pNarrow pBroad : W → Bool) (fNarrow fBroad : PropFocusValue W)
    (h_say_ue : ∀ (x : E) (w : W),
      say x pNarrow w = true → say x pBroad w = true)
    (h_belief_mono : ∀ (x : E) (w : W),
      believesSomeAlt x fNarrow w = true → believesSomeAlt x fBroad w = true) :
    ∀ (x : E) (w : W),
      predicateP say believesSomeAlt x pNarrow fNarrow w = true →
      predicateP say believesSomeAlt x pBroad fBroad w = true := by
  intro x w h
  simp only [predicateP, Bool.and_eq_true] at h ⊢
  exact ⟨h_say_ue x w h.1, h_belief_mono x w h.2⟩

-- ============================================================================
-- §5b. Non-UE Counterexamples D' and D'' (@cite{ozyildiz-etal-2025} §6.1)
-- ============================================================================

/-!
## Inference-Test Counterexamples for Non-UE Predicates

B' and B'' (§5 above) are pathological predicates that evade the
truth-based and inference-based tests respectively. D' and D'' are
DIFFERENT counterexamples from §6.1 that show the inference-based test
alone yields incorrect results for non-UE predicates.

### D' (@cite{ozyildiz-etal-2025} (38)): 1-inference FALSE POSITIVE

D' resembles *deny*: ⌜x D's φ⌝ = x commits to ¬φ. D' is NOT
focus-sensitive (truth depends on ¬φ, not on focus alternatives) but
IS non-UE (strengthening φ weakens ¬φ). The 1-inference test detects
non-entailment (D'(x, A∧B) ⊬ D'(x, A) since ¬(A∧B) ⊬ ¬A) and
wrongly concludes focus-sensitivity.

### D'' (@cite{ozyildiz-etal-2025} (42)): 2-inference FALSE NEGATIVE

D'' is like D' but additionally requires the speech act to respond to
a QUD matching the focus alternatives. D'' IS focus-sensitive (QUD
matching depends on focus alternatives) but both inferences yield the
same result (non-entailment), so the 2-inference variant sees no
asymmetry → wrongly concludes no evidence.

Both errors are caught by the truth-based follow-up step in the
proposed two-step method.
-/

/-- **Predicate D'** (@cite{ozyildiz-etal-2025} (38)):
    ⌜x D's φ⌝ = x commits to ¬φ.
    NOT focus-sensitive. Defined as `liftNonFS` since D' ignores
    focus alternatives entirely. -/
def predicateD' {W E : Type*}
    (commits_to_neg : E → (W → Bool) → W → Bool) : ClauseEmbedPred W E :=
  liftNonFS commits_to_neg

/-- D' is not focus-sensitive (ignores focus alternatives). -/
theorem predicateD'_not_fs {W E : Type*}
    (commits_to_neg : E → (W → Bool) → W → Bool) :
    IsNotFocusSensitive (predicateD' commits_to_neg) :=
  liftNonFS_not_fs commits_to_neg

/-- **Predicate D''** (@cite{ozyildiz-etal-2025} (42)):
    Like D' but additionally requires QUD-matching with focus alternatives.
    IS focus-sensitive: truth depends on whether focus alternatives match
    the QUD of the speech act. -/
def predicateD'' {W E : Type*}
    (commits_to_neg : E → (W → Bool) → W → Bool)
    (qudMatches : PropFocusValue W → Bool) : ClauseEmbedPred W E :=
  λ x p f w => commits_to_neg x p w && qudMatches f

/-- D'' is focus-sensitive when the QUD matcher distinguishes some focus sets. -/
theorem predicateD''_is_fs {W E : Type*}
    (commits_to_neg : E → (W → Bool) → W → Bool)
    (qudMatches : PropFocusValue W → Bool)
    (x : E) (p : W → Bool) (w : W)
    (f₁ f₂ : PropFocusValue W)
    (h_base : commits_to_neg x p w = true)
    (h_match : qudMatches f₁ = true)
    (h_nomatch : qudMatches f₂ = false) :
    IsFocusSensitive (predicateD'' commits_to_neg qudMatches) := by
  refine ⟨x, p, f₁, f₂, w, ?_⟩
  simp [predicateD'', h_base, h_match, h_nomatch]

-- ============================================================================
-- §6. The Two-Step Diagnostic
-- ============================================================================

/-!
## The Proposed Test (@cite{ozyildiz-etal-2025} §3)

### Step 1: Inference-based elicitation of invalidating contexts

Given predicate V and two sentences:
- Premise: ⌜x Vs that [A...B_F]⌝ (narrow focus on B)
- Conclusion: ⌜x Vs that [A...]⌝ (B dropped)

Ask: Does the premise entail the conclusion?
- If YES for all consultants → no evidence for focus-sensitivity
- If NO for at least one → elicit the invalidating context, proceed to Step 2

### Step 2: Truth-based test

In the invalidating context(s) from Step 1, compare:
- S₁: ⌜x Vs that [A...B_F]⌝
- S₂: ⌜x Vs that [A_F...B]⌝ (focus shifted)

If truth values differ → V is focus-sensitive for this consultant.

### Key insight: why both steps are needed

- Truth-based alone fails **item generalizability**: no general recipe for
  constructing contexts (@cite{villalta-2008}'s contexts require
  predicate-specific substrate/conflicting attitudes)
- Inference-based alone fails **stability**: non-UE predicates cause false
  positives/negatives (§6.1)
- Combined: inference step elicits contexts; truth step validates
-/

/-- Result of the two-step focus-sensitivity diagnostic. -/
inductive DiagnosticResult where
  | noEvidence       -- All inferences are entailments; no invalidating context found
  | focusSensitive   -- Invalidating context found AND truth values differ
  | inconclusive     -- Invalidating context found but truth values are the same
  deriving DecidableEq, Repr

/-- The diagnostic applied to a predicate with known properties.

    The inference test detects non-entailment (= non-UE complement position).
    The truth test then confirms focus-sensitivity in the invalidating context. -/
def diagnose (isEntailment : Bool) (truthValuesDiffer : Bool) : DiagnosticResult :=
  if isEntailment then .noEvidence
  else if truthValuesDiffer then .focusSensitive
  else .inconclusive

-- Verification: diagnostic agrees with classification for known predicates

theorem want_diagnosed_fs : diagnose false true = .focusSensitive := rfl
theorem know_diagnosed_no : diagnose true false = .noEvidence := rfl
theorem believe_diagnosed_no : diagnose true false = .noEvidence := rfl

-- ============================================================================
-- §7. Desiderata for Semantic Elicitation Methods
-- ============================================================================

/-!
## Evaluation Criteria (@cite{tonhauser-matthewson-2016})

The paper evaluates methods against five desiderata:

| Desideratum | Proposed | Truth-only | Coherence | Inference-only |
|-------------|----------|------------|-----------|----------------|
| Stability | ✓ | ✓ | ✗ (min.) | ✗ |
| Replicability | ✓ | ✓ | ✓ | ✓ |
| Transparency | ~✓ | ✓ | ✗ | ✗ |
| Cross-ling. uniformity | ✓ | ✓ | ✗ | ✓ |
| Item generalizability | ✓ | ✗ | ✗ | ✓ |

The proposed two-step method is the only one satisfying all five.
-/

/-- Desiderata from @cite{tonhauser-matthewson-2016} for semantic data collection. -/
inductive Desideratum where
  | stability              -- Context controls variation in judgments
  | replicability           -- Can be replicated across researchers/languages
  | transparency            -- Clear how data supports the conclusion
  | crossLingUniformity     -- Minimal language-specific elements
  | itemGeneralizability    -- Clear recipe for any item in the class
  deriving DecidableEq, Repr

/-- A method's rating on each desideratum. -/
structure MethodEvaluation where
  name : String
  ratings : List (Desideratum × Bool)
  deriving Repr

def proposedMethod : MethodEvaluation :=
  ⟨"inference + truth (proposed)",
   [(.stability, true), (.replicability, true), (.transparency, true),
    (.crossLingUniformity, true), (.itemGeneralizability, true)]⟩

def truthOnly : MethodEvaluation :=
  ⟨"truth-based only",
   [(.stability, true), (.replicability, true), (.transparency, true),
    (.crossLingUniformity, true), (.itemGeneralizability, false)]⟩

def coherenceTest : MethodEvaluation :=
  ⟨"coherence-based",
   [(.stability, false), (.replicability, true), (.transparency, false),
    (.crossLingUniformity, false), (.itemGeneralizability, false)]⟩

def inferenceOnly : MethodEvaluation :=
  ⟨"inference-based only",
   [(.stability, false), (.replicability, true), (.transparency, false),
    (.crossLingUniformity, true), (.itemGeneralizability, true)]⟩

-- The proposed method is the only one satisfying all desiderata
theorem proposed_satisfies_all :
    proposedMethod.ratings.all (·.2) = true := by native_decide

theorem truthOnly_fails_generalizability :
    (truthOnly.ratings.filter (!·.2)).map (·.1) = [.itemGeneralizability] := by native_decide

-- ============================================================================
-- §8. Non-UE Predicates and the Inference Test (§6.1)
-- ============================================================================

/-!
## Problems with Non-Upward-Entailing Predicates

@cite{ozyildiz-etal-2025} §6.1 shows that the inference-based test can
yield incorrect results for non-upward-entailing (non-UE) predicates.

The inference test checks: does ⌜x Vs that P on THURSDAYS⌝ entail
⌜x Vs that P⌝? For UE predicates (believe, know), dropping "on Thursdays"
weakens the proposition, so entailment holds — correctly indicating
non-focus-sensitivity.

For non-UE predicates:
- **1-inference false positive**: A non-focus-sensitive non-UE predicate D'
  (like deny) can fail the entailment test (false → true flip) even though
  it's not focus-sensitive, because non-UE predicates don't preserve
  entailment under weakening.
- **2-inference false negative**: A focus-sensitive non-UE predicate D''
  can pass the entailment test (both inferences fail symmetrically) even
  though it IS focus-sensitive.

Both errors are caught by the truth-based follow-up step.
-/

/-- The complement position's monotonicity is relevant to the inference test.

    This connects to `Theories/Semantics/Entailment/Polarity.lean`:
    - UE predicates: dropping focus material preserves truth → entailment holds
    - Non-UE predicates: dropping material may flip truth → false non-entailment -/
inductive ComplementMonotonicity where
  | upwardEntailing     -- believe, know: weakening preserves truth
  | nonUpwardEntailing  -- want, deny, be surprised: weakening may not preserve truth
  deriving DecidableEq, Repr

/-- For UE predicates, the inference test is reliable:
    non-entailment genuinely indicates focus-sensitivity. -/
def inferenceTestReliable : ComplementMonotonicity → Bool
  | .upwardEntailing => true
  | .nonUpwardEntailing => false

end Phenomena.Focus.Studies.OzyildizEtAl2025
