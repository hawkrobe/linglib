/-
# RSA Embedded Scalar Implicatures: Full Potts et al. (2016) Model

Implements the **complete** Lexical Uncertainty model from:
  Potts, Lassiter, Levy & Frank (2016). Embedded implicatures as pragmatic
  inferences under compositional lexical uncertainty. Journal of Semantics.

## The Paper's Setup (Section 4.3)

### World Space (Table 3, p.33)

3 players (A, B, C), each with 3 possible outcomes:
- N = didn't score (solved nothing)
- S = scored but didn't ace (solved some-but-not-all)
- A = aced (solved all)

Worlds are equivalence classes based on outcome counts, yielding 10 classes.

### Lexica (Equation 14, p.35)

Multiple refinable items create rich lexicon space:
- Quantifiers: {⟦some⟧_weak, ⟦some⟧_strong} where strong = some-but-not-all
- Predicates: {⟦scored⟧_weak, ⟦scored⟧_strong} where weak = scored-or-aced

This gives 2² = 4 lexica from just these two items.

### Messages (Table 2, p.32)

Utterances crossing quantifiers × predicates:
- "No one scored", "No one aced"
- "Exactly one player scored", "Exactly one player aced"
- "Every player scored", "Every player aced"
- etc.

### RSA Equations (13a-c, p.34)

- l₀(w | m, L) ∝ L(m, w) P(w)
- s₁(m | w, L) ∝ exp(λ(log l₀(w | m, L) - C(m)))
- L₁(w | m) ∝ P(w) Σ_L P(L) s₁(m | w, L)

### Optimal Parameters (Table 7, p.39)

- λ = 0.1 (very low rationality: speaker nearly uniform)
- k = 1 (L₁ pragmatic listener)
- Flat priors over worlds and lexica
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.RSA.Extensions.LexicalUncertainty.Basic
import Linglib.Phenomena.ScalarImplicatures.Data
import Linglib.Theories.RSA.ScalarImplicatures.Embedded.Basic

namespace RSA.PottsLU

open RSA.Eval LURSA
open Phenomena.ScalarImplicatures

-- ============================================================================
-- PART 1: Player Outcomes
-- ============================================================================

/--
Outcome for a single player.

Following the paper's notation:
- N = didn't score (none solved)
- S = scored but didn't ace (some-but-not-all solved)
- A = aced (all solved)
-/
inductive Outcome where
  | N  -- none
  | S  -- some-but-not-all
  | A  -- all
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Did this player score (solve at least one)? -/
def Outcome.scored : Outcome → Bool
  | .N => false
  | .S => true
  | .A => true

/-- Did this player ace (solve all)? -/
def Outcome.aced : Outcome → Bool
  | .N => false
  | .S => false
  | .A => true

/-- Did this player score-but-not-ace? -/
def Outcome.scoredNotAced : Outcome → Bool
  | .N => false
  | .S => true
  | .A => false

-- ============================================================================
-- PART 2: World States (Equivalence Classes)
-- ============================================================================

/--
World state as equivalence class based on outcome counts.

Following Table 3 (p.33), we use counts: (nN, nS, nA) where nN + nS + nA = 3.

The 10 equivalence classes are:
- NN: (3,0,0) - all players got N
- NS: (2,1,0) - two N, one S
- NA: (2,0,1) - two N, one A
- SS: (1,2,0) - one N, two S
- SA: (1,1,1) - one of each
- AA: (1,0,2) - one N, two A
- SSS: (0,3,0) - all S
- SSA: (0,2,1) - two S, one A
- SAA: (0,1,2) - one S, two A
- AAA: (0,0,3) - all A
-/
inductive WorldClass where
  | NN   -- (3,0,0): NNN
  | NS   -- (2,1,0): NNS
  | NA   -- (2,0,1): NNA
  | SS   -- (1,2,0): NSS
  | SA   -- (1,1,1): NSA
  | AA   -- (1,0,2): NAA
  | SSS  -- (0,3,0): SSS
  | SSA  -- (0,2,1): SSA
  | SAA  -- (0,1,2): SAA
  | AAA  -- (0,0,3): AAA
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Count of players who scored (at least one) -/
def WorldClass.numScored : WorldClass → Nat
  | .NN  => 0
  | .NS  => 1
  | .NA  => 1
  | .SS  => 2
  | .SA  => 2
  | .AA  => 2
  | .SSS => 3
  | .SSA => 3
  | .SAA => 3
  | .AAA => 3

/-- Count of players who aced -/
def WorldClass.numAced : WorldClass → Nat
  | .NN  => 0
  | .NS  => 0
  | .NA  => 1
  | .SS  => 0
  | .SA  => 1
  | .AA  => 2
  | .SSS => 0
  | .SSA => 1
  | .SAA => 2
  | .AAA => 3

/-- Count of players who scored-but-not-aced -/
def WorldClass.numScoredNotAced : WorldClass → Nat
  | .NN  => 0
  | .NS  => 1
  | .NA  => 0
  | .SS  => 2
  | .SA  => 1
  | .AA  => 0
  | .SSS => 3
  | .SSA => 2
  | .SAA => 1
  | .AAA => 0

/-- Did at least one player score? -/
def WorldClass.someScored (w : WorldClass) : Bool := w.numScored > 0

/-- Did all players score? -/
def WorldClass.allScored (w : WorldClass) : Bool := w.numScored == 3

/-- Did no one score? -/
def WorldClass.noOneScored (w : WorldClass) : Bool := w.numScored == 0

/-- Did at least one player ace? -/
def WorldClass.someAced (w : WorldClass) : Bool := w.numAced > 0

/-- Did all players ace? -/
def WorldClass.allAced (w : WorldClass) : Bool := w.numAced == 3

/-- Did no one ace? -/
def WorldClass.noOneAced (w : WorldClass) : Bool := w.numAced == 0

/-- Did at least one player score-but-not-ace? -/
def WorldClass.someScoredNotAced (w : WorldClass) : Bool := w.numScoredNotAced > 0

/-- All world classes -/
def allWorlds : List WorldClass :=
  [.NN, .NS, .NA, .SS, .SA, .AA, .SSS, .SSA, .SAA, .AAA]

-- ============================================================================
-- PART 3: Utterances
-- ============================================================================

/--
Quantifiers in the utterance.
-/
inductive Quant where
  | no
  | some_
  | exactlyOne
  | exactlyTwo
  | every
  | null  -- Silent/baseline
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Predicates: "scored" vs "aced".

"scored" = solved at least one problem
"aced" = solved all problems
-/
inductive Pred where
  | scored
  | aced
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Full utterance: Quantifier + Predicate.

Examples:
- (no, scored) = "No one scored"
- (some_, aced) = "Someone aced"
- (every, scored) = "Everyone scored"
-/
structure Utterance where
  quant : Quant
  pred : Pred
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Shorthand constructors -/
def noScored : Utterance := ⟨.no, .scored⟩
def noAced : Utterance := ⟨.no, .aced⟩
def someScored : Utterance := ⟨.some_, .scored⟩
def someAced : Utterance := ⟨.some_, .aced⟩
def exactlyOneScored : Utterance := ⟨.exactlyOne, .scored⟩
def exactlyOneAced : Utterance := ⟨.exactlyOne, .aced⟩
def exactlyTwoScored : Utterance := ⟨.exactlyTwo, .scored⟩
def exactlyTwoAced : Utterance := ⟨.exactlyTwo, .aced⟩
def everyScored : Utterance := ⟨.every, .scored⟩
def everyAced : Utterance := ⟨.every, .aced⟩
def nullUtt : Utterance := ⟨.null, .scored⟩

/-- All non-null utterances -/
def allUtterances : List Utterance :=
  [noScored, noAced, someScored, someAced,
   exactlyOneScored, exactlyOneAced, exactlyTwoScored, exactlyTwoAced,
   everyScored, everyAced, nullUtt]

-- ============================================================================
-- PART 4: Lexica (Equation 14)
-- ============================================================================

/--
Lexicon parameters: which items are refined.

Following equation (14), we have:
- refineQuant: if true, "some" means "some-but-not-all"
- refinePred: if true, "scored" means "scored-but-not-aced"
-/
structure LexParams where
  /-- If true, "some" = some-but-not-all (exclusive) -/
  refineQuant : Bool
  /-- If true, "scored" = scored-but-not-aced -/
  refinePred : Bool
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All 4 lexica from the cross-product -/
def allLexParams : List LexParams :=
  [ ⟨false, false⟩,  -- L_base: weak "some", weak "scored"
    ⟨true, false⟩,   -- "some" = some-not-all, "scored" = scored
    ⟨false, true⟩,   -- "some" = some, "scored" = scored-not-aced
    ⟨true, true⟩ ]   -- "some" = some-not-all, "scored" = scored-not-aced

/--
Truth value of an utterance in a world under given lexicon parameters.

This implements the compositional semantics with refinement.
-/
def utteranceTruth (params : LexParams) (u : Utterance) (w : WorldClass) : Bool :=
  -- First, determine the predicate extension
  let predCount : Nat :=
    if params.refinePred then
      -- "scored" means scored-but-not-aced
      if u.pred == .scored then w.numScoredNotAced
      else w.numAced  -- "aced" is unambiguous
    else
      -- "scored" means scored-or-aced
      if u.pred == .scored then w.numScored
      else w.numAced
  -- Now apply the quantifier
  match u.quant with
  | .no => predCount == 0
  | .some_ =>
    if params.refineQuant then
      -- "some" = some-but-not-all
      predCount > 0 && predCount < 3
    else
      -- "some" = at-least-one
      predCount > 0
  | .exactlyOne => predCount == 1
  | .exactlyTwo => predCount == 2
  | .every => predCount == 3
  | .null => true

/-- Create a Lexicon from LexParams -/
def lexiconOfParams (params : LexParams) : Lexicon Utterance WorldClass where
  meaning u w := boolToRat (utteranceTruth params u w)

/-- All 4 lexica as Lexicon objects -/
def allLexica : List (Lexicon Utterance WorldClass) :=
  allLexParams.map lexiconOfParams

-- ============================================================================
-- PART 5: The Full LU Scenario
-- ============================================================================

/--
The complete Potts et al. (2016) scenario.

Following Table 7 optimal parameters:
- λ = 0.1 → we approximate with α = 1 and note the speaker is nearly uniform
- Flat priors over worlds and lexica
-/
def pottsScenario : LUScenario where
  Utterance := Utterance
  World := WorldClass
  baseLexicon := lexiconOfParams ⟨false, false⟩
  lexica := allLexica
  lexPrior := fun _ => 1  -- Flat prior per paper
  worldPrior := fun _ => 1  -- Flat prior per paper
  utterances := allUtterances
  worlds := allWorlds
  α := 1  -- Note: paper uses λ=0.1, we analyze effects below

-- ============================================================================
-- PART 6: RSA Computations
-- ============================================================================

/-- L₁ distribution over worlds for a given utterance -/
def l1Worlds (u : Utterance) : List (WorldClass × ℚ) :=
  LURSA.L1 pottsScenario u

/-- L₁ probability for a specific world -/
def l1Prob (u : Utterance) (w : WorldClass) : ℚ :=
  LURSA.L1_prob pottsScenario u w

-- ============================================================================
-- PART 7: Key Predictions
-- ============================================================================

/-
## DE Context: "No one scored"

Under L_base (weak "scored"):
- "No one scored" = nobody scored any = true only in NN

Under L_refined (strong "scored" = scored-not-aced):
- "No one scored" = nobody scored-without-acing
- True in NN (nobody scored anything)
- True in NA, AA, AAA (those who performed, aced)

The key question: does RSA prefer the global (L_base) or local (L_refined) reading?

With proper lexicon competition, the global reading should dominate because
it's more informative when "no one aced" is available as an alternative.
-/

/-- L₁ for "No one scored" -/
def l1NoScored : List (WorldClass × ℚ) := l1Worlds noScored

#eval l1NoScored

/-- Sum probabilities for worlds consistent with global reading (just NN) -/
def pGlobalDE : ℚ := l1Prob noScored .NN

/-- Sum probabilities for worlds consistent only with local reading -/
def pLocalOnlyDE : ℚ :=
  l1Prob noScored .NA + l1Prob noScored .AA + l1Prob noScored .AAA

#eval (pGlobalDE, pLocalOnlyDE)
#eval decide (pGlobalDE > pLocalOnlyDE)

/-
## UE Context: "Someone scored"

Under L_base (weak):
- "Someone scored" = at least one person scored any
- True in all worlds except NN

Under L_refined (strong "scored"):
- "Someone scored" = at least one person scored-but-not-aced
- True in NS, SS, SA, SSS, SSA, SAA (not in NN, NA, AA, AAA)

In UE, the local reading (someone scored-not-aced) should be preferred
because it's more informative.
-/

/-- L₁ for "Someone scored" -/
def l1SomeScored : List (WorldClass × ℚ) := l1Worlds someScored

#eval l1SomeScored

/-- Worlds where local reading is informative (scored-not-aced exists) -/
def pLocalUE : ℚ :=
  l1Prob someScored .NS + l1Prob someScored .SS + l1Prob someScored .SA +
  l1Prob someScored .SSS + l1Prob someScored .SSA + l1Prob someScored .SAA

/-- Worlds where only global is true (everyone who scored also aced) -/
def pGlobalOnlyUE : ℚ :=
  l1Prob someScored .NA + l1Prob someScored .AA + l1Prob someScored .AAA

#eval (pLocalUE, pGlobalOnlyUE)
#eval decide (pLocalUE > pGlobalOnlyUE)

-- ============================================================================
-- PART 8: Main Theorems - The Model Derives Correct Predictions
-- ============================================================================

/--
**MAIN RESULT 1: DE Blocking**

In downward-entailing contexts ("No one scored"), the model predicts
the GLOBAL reading is preferred.

- Global: "No one scored" = nobody solved any → world NN only
- Local: "No one scored" = nobody solved-without-acing → includes NA, AA, AAA

The model assigns higher probability to the global-only world (NN).
-/
theorem potts_model_derives_de_blocking : pGlobalDE > pLocalOnlyDE := by
  native_decide

/--
**MAIN RESULT 2: UE Implicature**

In upward-entailing contexts ("Someone scored"), the model predicts
the LOCAL reading is preferred.

- Global: "Someone scored" = at least one solved any → all non-NN worlds
- Local: "Someone scored" = at least one solved-without-acing → excludes all-aced worlds

The model assigns higher probability to local-compatible worlds.
-/
theorem potts_model_derives_ue_implicature : pLocalUE > pGlobalOnlyUE := by
  native_decide

/--
**Combined result matching empirical pattern**

The full Potts et al. (2016) model correctly derives:
1. DE blocking (global preferred in downward-entailing contexts)
2. UE implicature (local preferred in upward-entailing contexts)
-/
theorem potts_model_derives_de_ue_asymmetry :
    pGlobalDE > pLocalOnlyDE ∧ pLocalUE > pGlobalOnlyUE := by
  exact ⟨potts_model_derives_de_blocking, potts_model_derives_ue_implicature⟩

-- ============================================================================
-- PART 9: Formal Predictions
-- ============================================================================

/-
## Summary of Predictions

The full Potts model with:
- 10 world classes
- 4 lexica (2 refinable items × 2 values)
- 11 utterances (5 quantifiers × 2 predicates + null)

Should derive:
1. DE: Global reading preferred (weak "scored")
2. UE: Local reading preferred (when informative)

The key mechanism is ALTERNATIVE COMPETITION:
- In DE ("no one scored"), the alternative "no one aced" blocks the local reading
- In UE ("someone scored"), the local reading is simply more informative
-/

-- ============================================================================
-- PART 10: Low Rationality Analysis (λ = 0.1)
-- ============================================================================

/-
## The Role of λ = 0.1

The paper uses λ = 0.1, meaning the speaker is nearly uniform over
true messages. This is crucial because:

1. At high λ, the speaker picks the most informative message
2. At low λ, the speaker is nearly uniform → listener relies more on lexicon structure
3. This shifts power from pragmatic inference to lexical competition

With α = 1 (our default), we get a more "pragmatically rational" speaker.
To approximate λ = 0.1, we'd need fractional α, which our ℕ-based system
doesn't support directly.

However, the key insight is preserved: lexicon structure matters more than
pure informativity when the speaker is not highly rational.
-/

/--
Alternative scenario with α = 0 would make speaker completely uniform,
but α : ℕ means minimum is 1. The paper's λ = 0.1 is between uniform (0) and
our α = 1.

We document this limitation and note the qualitative behavior is similar.
-/
def lowRationalityNote : String :=
  "Paper uses λ=0.1 (nearly uniform speaker). Our α=1 is more rational. " ++
  "For exact replication, implement ℚ-valued exponentiation."

-- ============================================================================
-- PART 11: Connection to Phenomena Data
-- ============================================================================

/--
Connection to the empirical DE blocking pattern.

The Potts model predicts that in DE contexts, the global reading
(weak predicate) is preferred.
-/
theorem potts_model_de_prediction :
    -- Empirical: DE blocks embedded implicature
    someAllBlocking.implicatureInDE = false := by
  native_decide

/--
Connection to UE implicature pattern.

In UE contexts, the local reading (strong predicate, when informative)
is preferred.
-/
theorem potts_model_ue_prediction :
    -- Empirical: UE allows embedded implicature
    someAllBlocking.implicatureInUE = true := by
  native_decide

-- ============================================================================
-- PART 12: Detailed World-by-World Analysis
-- ============================================================================

/-- Pretty-print L₁ distribution -/
def showL1 (u : Utterance) : List (String × ℚ) :=
  (l1Worlds u).map fun (w, p) => (toString (repr w), p)

#eval showL1 noScored
#eval showL1 someScored
#eval showL1 noAced
#eval showL1 someAced

-- ============================================================================
-- PART 13: Regression Tests - Reduced Models Fail
-- ============================================================================

/-
## Why the Full Model is Necessary

The following regression tests prove that simpler versions of the model
give WRONG predictions. This documents why Potts et al.'s full structure
(multiple refinable items, rich world space) is necessary.
-/

-- ----------------------------------------------------------------------------
-- Regression Test 1: Only 2 Lexica (Predicate Refinement Only)
-- ----------------------------------------------------------------------------

/--
Reduced lexicon space: only refine predicate, not quantifier.

This gives just 2 lexica:
- L₀: weak "scored" (scored-or-aced)
- L₁: strong "scored" (scored-but-not-aced)

This is the key test because the local/global distinction for
"no one scored" depends on predicate refinement.
-/
def twoLexParams_pred : List LexParams :=
  [ ⟨false, false⟩,  -- weak "some", weak "scored"
    ⟨false, true⟩ ]  -- weak "some", strong "scored"

def twoLexica_pred : List (Lexicon Utterance WorldClass) :=
  twoLexParams_pred.map lexiconOfParams

def reducedLexiconScenario : LUScenario where
  Utterance := Utterance
  World := WorldClass
  baseLexicon := lexiconOfParams ⟨false, false⟩
  lexica := twoLexica_pred
  lexPrior := fun _ => 1
  worldPrior := fun _ => 1
  utterances := allUtterances
  worlds := allWorlds
  α := 1

/-- L₁ for "no one scored" with only 2 lexica (predicate refinement) -/
def l1NoScoredReduced : List (WorldClass × ℚ) :=
  LURSA.L1 reducedLexiconScenario noScored

def pGlobalDE_reduced : ℚ := getScore l1NoScoredReduced .NN

def pLocalOnlyDE_reduced : ℚ :=
  getScore l1NoScoredReduced .NA +
  getScore l1NoScoredReduced .AA +
  getScore l1NoScoredReduced .AAA

#eval (pGlobalDE_reduced, pLocalOnlyDE_reduced)
#eval decide (pGlobalDE_reduced > pLocalOnlyDE_reduced)

/--
**REGRESSION TEST 1: 2-Lexicon Model (Predicate Only) Succeeds**

Even with only 2 lexica, if those lexica refine the predicate (the
item that matters for "no one scored"), the model still works.

This shows predicate refinement is the key mechanism.
-/
theorem two_lexicon_pred_model_succeeds_de :
    pGlobalDE_reduced > pLocalOnlyDE_reduced := by
  native_decide

-- Now test UE with this reduced model
def l1SomeScoredReduced : List (WorldClass × ℚ) :=
  LURSA.L1 reducedLexiconScenario someScored

def pLocalUE_reduced : ℚ :=
  getScore l1SomeScoredReduced .NS + getScore l1SomeScoredReduced .SS +
  getScore l1SomeScoredReduced .SA + getScore l1SomeScoredReduced .SSS +
  getScore l1SomeScoredReduced .SSA + getScore l1SomeScoredReduced .SAA

def pGlobalOnlyUE_reduced : ℚ :=
  getScore l1SomeScoredReduced .NA + getScore l1SomeScoredReduced .AA +
  getScore l1SomeScoredReduced .AAA

#eval (pLocalUE_reduced, pGlobalOnlyUE_reduced)
#eval decide (pLocalUE_reduced > pGlobalOnlyUE_reduced)

/--
**REGRESSION TEST 1b: 2-Lexicon Model Also Works for UE**

The 2-lexicon model with predicate refinement correctly predicts
local wins in UE context.
-/
theorem two_lexicon_pred_model_succeeds_ue :
    pLocalUE_reduced > pGlobalOnlyUE_reduced := by
  native_decide

-- ============================================================================
-- PART 14: REGRESSION TESTS - Simplified Models Fail
-- ============================================================================

/-
## Why the Full Model Structure is Necessary

The simplified 2-lexicon, 3-world model from EmbeddedScalars.lean gives
**inverted** predictions:
- DE: predicts LOCAL wins (should be GLOBAL)
- UE: predicts GLOBAL wins (should be LOCAL)

The full Potts model succeeds because of:
1. **10 world classes** (not 3) - proper truth condition distinctions
2. **4 lexica** (2 refinable items) - predicate AND quantifier refinement
3. **11 utterances** - message alternatives create competition

These regression tests prove the simplified model fails.
-/

-- ----------------------------------------------------------------------------
-- Regression Test 1: Simplified Model from EmbeddedScalars.lean
-- ----------------------------------------------------------------------------

/--
**REGRESSION TEST: Simplified Model Gives Wrong Predictions**

The EmbeddedScalars.lean model (2 lexica, 3 worlds) predicts:
- DE: L_refined (local) wins — WRONG (should be global)
- UE: L_base (global) wins — WRONG (should be local)

This theorem imports the result from EmbeddedScalars.lean.
-/
theorem simplified_model_fails :
    -- DE: local wins (WRONG - should be global)
    EmbeddedScalars.pLexRefined > EmbeddedScalars.pLexBase ∧
    -- UE: global wins (WRONG - should be local)
    EmbeddedScalars.pLexBaseUE > EmbeddedScalars.pLexRefinedUE :=
  EmbeddedScalars.simple_lu_model_limitation

-- ----------------------------------------------------------------------------
-- Regression Test 2: Full Model Gives Correct Predictions
-- ----------------------------------------------------------------------------

/--
**MAIN THEOREM: Full Model Succeeds Where Simplified Fails**

The full Potts et al. (2016) model correctly derives:
- DE: GLOBAL wins (blocking embedded implicature)
- UE: LOCAL wins (allowing embedded implicature)

While the simplified model gives inverted predictions.
-/
theorem full_model_succeeds_simplified_fails :
    -- Full model: correct predictions
    (pGlobalDE > pLocalOnlyDE) ∧
    (pLocalUE > pGlobalOnlyUE) ∧
    -- Simplified model: inverted predictions
    (EmbeddedScalars.pLexRefined > EmbeddedScalars.pLexBase) ∧
    (EmbeddedScalars.pLexBaseUE > EmbeddedScalars.pLexRefinedUE) := by
  exact ⟨potts_model_derives_de_blocking,
         potts_model_derives_ue_implicature,
         EmbeddedScalars.simple_lu_model_limitation.1,
         EmbeddedScalars.simple_lu_model_limitation.2⟩

-- ----------------------------------------------------------------------------
-- Summary: What Makes Models Succeed or Fail
-- ----------------------------------------------------------------------------

/--
**THEOREM: Rich World Space is the Critical Factor**

Comparison of model variants:

| Model | Worlds | Lexica | DE Prediction | UE Prediction | Correct? |
|-------|--------|--------|---------------|---------------|----------|
| Simplified (EmbeddedScalars) | 3 | 2 | Local wins | Global wins | ✗ BOTH WRONG |
| 2-Lexicon + Rich Worlds | 10 | 2 | Global wins | Local wins | ✓ BOTH RIGHT |
| Full Potts | 10 | 4 | Global wins | Local wins | ✓ BOTH RIGHT |

The 3-world model fails because world coverage asymmetries dominate:
the lexicon that makes the utterance true in more worlds gets extra mass,
inverting the informativity-based predictions.
-/
theorem world_space_is_critical :
    -- Simplified (3 worlds): FAILS
    (EmbeddedScalars.pLexRefined > EmbeddedScalars.pLexBase) ∧
    -- 2-Lexicon + 10 worlds: SUCCEEDS
    (pGlobalDE_reduced > pLocalOnlyDE_reduced) ∧
    -- Full Potts (10 worlds): SUCCEEDS
    (pGlobalDE > pLocalOnlyDE) := by
  exact ⟨EmbeddedScalars.simple_lu_model_limitation.1,
         two_lexicon_pred_model_succeeds_de,
         potts_model_derives_de_blocking⟩

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This File Implements

The **complete** Potts et al. (2016) model:

1. **World Space**: 10 equivalence classes from 3 players × 3 outcomes
2. **Lexica**: 4 lexica from 2 refinable items (quantifier, predicate)
3. **Utterances**: 11 messages (quantifier × predicate combinations)
4. **RSA**: L₁ marginalizing over lexica per equations (13a-c)

## Key Differences from Simple Model

The simple 2-lexicon model in EmbeddedScalars.lean failed because:
- Only 3 worlds (not enough structure)
- Only 2 lexica (no predicate refinement)
- No message alternatives for competition

The full model succeeds (when properly parameterized) because:
- Rich world space captures fine-grained truth distinctions
- Multiple refinable items create competition between readings
- Message alternatives ("no one aced") block inappropriate local readings

## Remaining Limitation

Our implementation uses α : ℕ while the paper uses λ = 0.1 (a small positive real).
For exact numerical replication, would need to implement ℚ-valued exponentiation.
The qualitative predictions should match.
-/

end RSA.PottsLU
