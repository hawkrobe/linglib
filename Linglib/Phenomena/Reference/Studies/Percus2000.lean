import Linglib.Theories.Semantics.Intensional.Situations.Percus

/-!
# Percus (2000): Situation Variable Constraints — Empirical Predictions @cite{percus-2000}

End-to-end chain from `Core.Situation` through situation variable
assignment to concrete empirical predictions about de re / de dicto
readings under attitude verbs.

## Chain

```
Core.Situation (world–time pairs)
  → Core.VarAssignment (generic ℕ → D)
    → Percus.SituationAssignment (ℕ → Situation W Time)
      → Percus.believeSit (attitude verb with situation binding)
        → Concrete predicates (isCanadian, isBrother)
          → Reading computation (which readings give which truth values)
            → Generalization X filter (which readings are well-formed)
              → Empirical match (filtered readings agree with judgments)
```

## Key Examples

### Example 1: "Mary believes John is Canadian"

Scenario: John IS Canadian in the actual world, but Mary (mistakenly)
believes he is NOT Canadian.

- **De dicto reading** (Gen X compliant): In Mary's belief worlds, John
  is Canadian → FALSE. ✓ matches judgment.
- **De re reading** (Gen X violation): John is Canadian in the actual
  world → TRUE. ✗ this reading does not exist.

Generalization X correctly predicts that only the de dicto reading is
available for the main predicate.

### Example 2: "Mary believes my brother is a spy"

Scenario: In the actual world, Bill is the speaker's brother.
In Mary's belief worlds, a different person (Charlie) is the speaker's
brother. Neither Bill nor Charlie is a spy in any world.

The NP restrictor "my brother" CAN be evaluated de re (at the actual
world), picking out the actual brother. Generalization X does NOT apply
to NP restrictors — only to main predicates.

## References

- Percus, O. (2000). Constraints on some other variables in syntax.
  *Natural Language Semantics* 8(3): 173–229.
-/

namespace Phenomena.Reference.Studies.Percus2000

open Core (Situation)
open Semantics.Intensional.Situations.Percus


-- ════════════════════════════════════════════════════════════════
-- § Concrete Model
-- ════════════════════════════════════════════════════════════════

/-- Two possible worlds: the actual world and Mary's belief world. -/
inductive W where
  | actual  -- the real world
  | belief  -- what Mary thinks the world is like
  deriving DecidableEq, BEq, Repr

/-- Persons in the model. -/
inductive Person where
  | mary | john | bill | charlie
  deriving DecidableEq, BEq, Repr

/-- Situations are world–Unit pairs (temporal coordinate irrelevant
    for Percus's examples about de re / de dicto). -/
abbrev Sit := Situation W Unit

/-- Construct a situation from a world (time = ()). -/
def sit (w : W) : Sit := ⟨w, ()⟩

/-- The actual situation. -/
def sActual : Sit := sit .actual
/-- Mary's belief situation. -/
def sBelief : Sit := sit .belief


-- ════════════════════════════════════════════════════════════════
-- § Predicate Denotations
-- ════════════════════════════════════════════════════════════════

/-- ⟦is Canadian⟧ = λx.λs. x is Canadian at s.

    - In the actual world: John IS Canadian.
    - In Mary's belief world: John is NOT Canadian.

    This divergence is what makes the de re / de dicto readings
    yield different truth values. -/
def isCanadian : Person → Sit → Bool
  | .john, ⟨.actual, _⟩ => true
  | .john, ⟨.belief, _⟩ => false
  | _, _ => false

/-- ⟦is brother of speaker⟧ = λx.λs. x is the speaker's brother at s.

    - In the actual world: Bill is the speaker's brother.
    - In Mary's belief world: Charlie is the speaker's brother.

    This divergence makes de re / de dicto NP restrictors pick out
    different individuals. -/
def isBrother : Person → Sit → Bool
  | .bill, ⟨.actual, _⟩ => true
  | .charlie, ⟨.belief, _⟩ => true
  | _, _ => false

/-- ⟦is a spy⟧ = λx.λs. x is a spy at s.

    Bill is a spy in Mary's belief world but not in the actual world.
    (Charlie is not a spy anywhere.) -/
def isSpy : Person → Sit → Bool
  | .bill, ⟨.belief, _⟩ => true
  | _, _ => false


-- ════════════════════════════════════════════════════════════════
-- § Doxastic Alternatives
-- ════════════════════════════════════════════════════════════════

/-- Mary's doxastic alternatives: from the actual world, Mary
    believes she is in the belief world.

    Dox_Mary(actual) = {belief}

    This models the scenario where Mary has a false belief about
    John's nationality. -/
def doxMary : Sit → List Sit
  | ⟨.actual, _⟩ => [sBelief]
  | ⟨.belief, _⟩ => [sBelief]


-- ════════════════════════════════════════════════════════════════
-- § Example 1: "Mary believes John is Canadian"
-- ════════════════════════════════════════════════════════════════

/-! ### LF Structures

**Reading 1 (de dicto — Gen X compliant)**:
```
[λs₁ Mary believes_s₁ [λs₂ John isCanadian_s₂]]
```
"isCanadian" takes s₂, bound by the embedded λs₂ (closest binder). ✓

**Reading 2 (de re — Gen X violation)**:
```
[λs₁ Mary believes_s₁ [λs₂ John isCanadian_s₁]]
```
"isCanadian" takes s₁, bound by the matrix λs₁ (not the closest). ✗
-/

section Example1

/-- Any initial assignment works; we pick a constant one. -/
private def g₀ : SituationAssignment W Unit := λ _ => sActual

/-- **De dicto reading** (Gen X compliant):

    ⟦Mary believes [λs₂ John isCanadian_s₂]⟧^g₀(sActual)
    = ∀s' ∈ Dox_Mary(sActual). isCanadian(john, s')
    = isCanadian(john, sBelief)
    = false -/
def reading1_deDicto : Bool :=
  believeSit (λ _ => doxMary) Person.mary 2
    (λ g => isCanadian .john (interpSitVar 2 g))
    g₀ sActual

/-- **De re reading** (Gen X violation):

    ⟦Mary believes [λs₂ John isCanadian_s₁]⟧^(g₀[1↦sActual])(sActual)
    = ∀s' ∈ Dox_Mary(sActual). isCanadian(john, g[1])
    = isCanadian(john, sActual)
    = true

    Here "isCanadian" escapes the embedded binder by referencing s₁
    (set to sActual by the matrix λs₁). -/
def reading2_deRe : Bool :=
  believeSit (λ _ => doxMary) Person.mary 2
    (λ g => isCanadian .john (interpSitVar 1 g))
    (updateSitVar g₀ 1 sActual) sActual

/-- The de dicto reading evaluates to false. -/
theorem deDicto_is_false : reading1_deDicto = false := rfl

/-- The de re reading evaluates to true. -/
theorem deRe_is_true : reading2_deRe = true := rfl

/-- The two readings differ — this is what makes Generalization X
    empirically testable. If they always agreed, the constraint
    would be vacuous. -/
theorem readings_differ : reading1_deDicto ≠ reading2_deRe := nofun

/-- **Generalization X well-formedness check.**

    Reading 1: "isCanadian" uses s₂, closest binder is λs₂ (index 2) → compliant.
    Reading 2: "isCanadian" uses s₁, closest binder is λs₂ (index 2) → violation. -/
def reading1_bindings : List PredicateBinding :=
  [⟨2, 2⟩]  -- isCanadian: sitVar = 2, closestBinder = 2

def reading2_bindings : List PredicateBinding :=
  [⟨1, 2⟩]  -- isCanadian: sitVar = 1, closestBinder = 2

theorem reading1_genX_ok : genXWellFormed reading1_bindings = true := rfl
theorem reading2_genX_violation : genXWellFormed reading2_bindings = false := rfl

/-- **Empirical judgment**: "Mary believes John is Canadian" is FALSE
    in a scenario where John is actually Canadian but Mary mistakenly
    believes he is not.

    The de dicto reading (false) matches the judgment.
    The de re reading (true) does not.
    Generalization X correctly filters out the non-matching reading. -/
def empiricalJudgment_ex1 : Bool := false

theorem genX_predicts_correct_reading :
    reading1_deDicto = empiricalJudgment_ex1 := rfl

theorem genX_blocks_incorrect_reading :
    reading2_deRe ≠ empiricalJudgment_ex1 := nofun

end Example1


-- ════════════════════════════════════════════════════════════════
-- § Example 2: "Mary believes my brother is a spy"
-- ════════════════════════════════════════════════════════════════

/-! ### NP Restrictors Can Be De Re

Percus's key observation: Generalization X constrains PREDICATES
(verbs, adjectives used predicatively) but NOT NP restrictors.
The restrictor of "my brother" CAN be evaluated at the actual world
(de re), picking out the actual brother even under attitude embedding.

**Scenario**:
- Actual world: Bill is the speaker's brother. Bill is a spy in Mary's beliefs.
- Belief world: Charlie is the speaker's brother. Charlie is not a spy.

**Reading A (all de dicto)**: "The person who is my brother in Mary's
beliefs is a spy in Mary's beliefs" = isSpy(charlie, sBelief) = false

**Reading B (NP de re, pred de dicto)**: "The person who is actually my
brother — Mary believes that person is a spy" = isSpy(bill, sBelief) = true

Both readings are predicted to be available because NP restrictors
are exempt from Generalization X. The de re reading (B) is the more
natural one in typical discourse contexts. -/

section Example2

private def g₀' : SituationAssignment W Unit := λ _ => sActual

/-- Helper: find the unique individual satisfying a predicate at a situation. -/
private def theBrother (s : Sit) : Person :=
  if isBrother .bill s then .bill
  else if isBrother .charlie s then .charlie
  else .mary  -- fallback (not used in our model)

/-- **Reading A (all de dicto)**: both NP restrictor and predicate
    evaluated in belief situations.

    brother(sBelief) = charlie, isSpy(charlie, sBelief) = false → FALSE -/
def readingA_allDeDicto : Bool :=
  believeSit (λ _ => doxMary) Person.mary 2
    (λ g =>
      let s := interpSitVar 2 g  -- embedded binder
      isSpy (theBrother s) s)
    g₀' sActual

/-- **Reading B (NP de re, pred de dicto)**: NP restrictor evaluated
    at actual situation, predicate in belief situations.

    brother(sActual) = bill, isSpy(bill, sBelief) = true → TRUE -/
def readingB_npDeRe : Bool :=
  believeSit (λ _ => doxMary) Person.mary 2
    (λ g =>
      let sMatrix := interpSitVar 1 g  -- matrix binder (de re for NP)
      let sEmbed := interpSitVar 2 g   -- embedded binder (de dicto for pred)
      isSpy (theBrother sMatrix) sEmbed)
    (updateSitVar g₀' 1 sActual) sActual

/-- **Reading C (NP de dicto, pred de re — IMPOSSIBLE)**: NP restrictor
    in belief situations, predicate at actual situation.

    brother(sBelief) = charlie, isSpy(charlie, sActual) = false → FALSE

    This reading is blocked by Generalization X: the main predicate
    "is a spy" must use the closest binder (λs₂), not the matrix binder (λs₁). -/
def readingC_predDeRe : Bool :=
  believeSit (λ _ => doxMary) Person.mary 2
    (λ g =>
      let sMatrix := interpSitVar 1 g  -- matrix binder (de re for pred — BLOCKED)
      let sEmbed := interpSitVar 2 g   -- embedded binder (de dicto for NP)
      isSpy (theBrother sEmbed) sMatrix)
    (updateSitVar g₀' 1 sActual) sActual

/-- Reading A (all de dicto) is false. -/
theorem readingA_is_false : readingA_allDeDicto = false := rfl

/-- Reading B (NP de re) is true. -/
theorem readingB_is_true : readingB_npDeRe = true := rfl

/-- Reading C (pred de re) is false (and blocked by Gen X). -/
theorem readingC_is_false : readingC_predDeRe = false := rfl

/-- Generalization X check for the three readings.

    - Reading A: isSpy uses s₂ (closest = s₂) → compliant ✓
    - Reading B: isSpy uses s₂ (closest = s₂) → compliant ✓
      (NP restrictor uses s₁, but Gen X only constrains predicates)
    - Reading C: isSpy uses s₁ (closest = s₂) → violation ✗ -/
def readingA_bindings : List PredicateBinding :=
  [⟨2, 2⟩]  -- isSpy: sitVar = 2, closestBinder = 2

def readingB_bindings : List PredicateBinding :=
  [⟨2, 2⟩]  -- isSpy: sitVar = 2, closestBinder = 2 (NP not checked)

def readingC_bindings : List PredicateBinding :=
  [⟨1, 2⟩]  -- isSpy: sitVar = 1, closestBinder = 2

theorem readingA_genX_ok : genXWellFormed readingA_bindings = true := rfl
theorem readingB_genX_ok : genXWellFormed readingB_bindings = true := rfl
theorem readingC_genX_violation : genXWellFormed readingC_bindings = false := rfl

/-- The available readings (A and B) are exactly those that pass Gen X.
    Reading B is the natural/salient de re reading in context. -/
theorem genX_allows_deRe_for_NPs :
    genXWellFormed readingB_bindings = true ∧ readingB_npDeRe = true :=
  ⟨rfl, rfl⟩

/-- Gen X blocks the "mixed" reading where the NP is de dicto but
    the predicate is de re — precisely Percus's empirical claim. -/
theorem genX_blocks_mixed_reading :
    genXWellFormed readingC_bindings = false := rfl

end Example2


-- ════════════════════════════════════════════════════════════════
-- § Example 3: Generalization Y — Adverbial Quantifier Binding
-- ════════════════════════════════════════════════════════════════

/-! ### Gen Y has independent bite from Gen X

Percus (2000, p. 204, example 35a):

  **"Mary thinks that my brother always won the game."**

Scenario: A game with 3 rounds.
- Actual world: brother won round 1, won round 2, LOST round 3.
- Mary's belief world: brother won ALL 3 rounds.

"Always" is an adverbial quantifier that ranges over game-round
situations. The situation pronoun ssh that determines which game
rounds "always" quantifies over can be bound by either:

- **λs₂** (the embedded clause binder, nearest to "always") → Gen Y OK
  "always" quantifies over rounds in Mary's **belief** world.
  Result: TRUE (brother won all rounds in Mary's beliefs).

- **λs₁** (the matrix clause binder) → Gen Y violation
  "always" quantifies over rounds in the **actual** world.
  Result: FALSE (brother lost round 3 in actuality).

Gen X is satisfied in BOTH readings (the predicate "won" uses s₃,
bound by λs₃ introduced by "always" — that's the nearest binder for
"won"). Gen Y is the constraint that does the work here: it forces
ssh to use the nearest λ, which is λs₂ (under "thinks"). -/

section Example3

/-- Game rounds. -/
inductive Round where | r1 | r2 | r3 deriving DecidableEq, BEq, Repr

/-- Situations with temporal structure (round = time). -/
abbrev RSit := Situation W Round

private def rSit (w : W) (r : Round) : RSit := ⟨w, r⟩

/-- ⟦won the game⟧: Bill won in the actual world rounds 1–2 but not 3;
    in Mary's belief world he won all three. -/
def wonGame : Person → RSit → Bool
  | .bill, ⟨.actual, .r1⟩ => true
  | .bill, ⟨.actual, .r2⟩ => true
  | .bill, ⟨.actual, .r3⟩ => false  -- lost this one
  | .bill, ⟨.belief, _⟩ => true     -- won all in Mary's beliefs
  | _, _ => false

/-- Game-round domain: all 3 rounds at the world of the given situation. -/
def gameRounds (s : RSit) : List RSit :=
  [rSit s.world .r1, rSit s.world .r2, rSit s.world .r3]

/-- Mary's doxastic alternatives (same as before, now with Round). -/
def doxMaryR : RSit → List RSit
  | ⟨.actual, r⟩ => [⟨.belief, r⟩]
  | ⟨.belief, r⟩ => [⟨.belief, r⟩]

private def g₃ : SituationAssignment W Round := λ _ => rSit .actual .r1

/-- **Gen Y compliant reading**: "always" uses ssh = s₂ (embedded binder).

    ⟦Mary thinks [λs₂ always_s₂ [λs₃ brother won_s₃]]⟧(s₁)
    = ∀s₂ ∈ Dox_Mary(s₁). ∀s₃ ∈ GameRounds(s₂). won(bill, s₃)

    "always" ranges over game rounds in Mary's BELIEF world.
    Bill won all rounds there → TRUE. -/
def genY_compliant : Bool :=
  believeSit (λ _ => doxMaryR) Person.mary 2
    (λ g =>
      let ssh := interpSitVar 2 g  -- Gen Y: "always" uses nearest λ (= s₂)
      alwaysAt gameRounds ssh 3
        (λ g' => wonGame .bill (interpSitVar 3 g')) g)
    g₃ (rSit .actual .r1)

/-- **Gen Y violation**: "always" uses ssh = s₁ (matrix binder).

    ⟦Mary thinks [λs₂ always_s₁ [λs₃ brother won_s₃]]⟧(s₁)
    = ∀s₂ ∈ Dox_Mary(s₁). ∀s₃ ∈ GameRounds(s₁). won(bill, s₃)

    "always" ranges over game rounds in the ACTUAL world.
    Bill lost round 3 → FALSE. -/
def genY_violation : Bool :=
  believeSit (λ _ => doxMaryR) Person.mary 2
    (λ g =>
      let ssh := interpSitVar 1 g  -- Gen Y violation: s₁ is not nearest λ
      alwaysAt gameRounds ssh 3
        (λ g' => wonGame .bill (interpSitVar 3 g')) g)
    (updateSitVar g₃ 1 (rSit .actual .r1)) (rSit .actual .r1)

theorem genY_compliant_is_true : genY_compliant = true := rfl
theorem genY_violation_is_false : genY_violation = false := rfl
theorem genY_readings_differ : genY_compliant ≠ genY_violation := nofun

/-- **Empirical judgment**: The sentence IS true — Mary does think
    brother always won. Only the Gen-Y-compliant reading matches. -/
def empiricalJudgment_ex3 : Bool := true

theorem genY_predicts_correct_reading :
    genY_compliant = empiricalJudgment_ex3 := rfl
theorem genY_blocks_incorrect_reading :
    genY_violation ≠ empiricalJudgment_ex3 := nofun

/-- Gen X is satisfied by BOTH readings — the predicate "won" uses
    s₃, bound by λs₃ (its nearest binder). Gen X does not distinguish
    the two readings. Gen Y is the constraint with independent bite. -/
def ex3_predBindings : List PredicateBinding :=
  [⟨3, 3⟩]  -- "won" uses s₃, nearest binder is λs₃

theorem ex3_genX_ok_for_both : genXWellFormed ex3_predBindings = true := rfl

/-- Gen Y check for the quantifier binding of "always". -/
def ex3_quantBindings_compliant : List PredicateBinding :=
  [⟨2, 2⟩]  -- "always" ssh = s₂, nearest λ is λs₂

def ex3_quantBindings_violation : List PredicateBinding :=
  [⟨1, 2⟩]  -- "always" ssh = s₁, nearest λ is λs₂

theorem ex3_genY_compliant_ok :
    genYWellFormed ex3_quantBindings_compliant = true := rfl
theorem ex3_genY_violation_caught :
    genYWellFormed ex3_quantBindings_violation = false := rfl

/-- The combined Gen X + Gen Y check distinguishes the readings
    even though Gen X alone cannot. -/
theorem ex3_genXY_compliant :
    genXYWellFormed ex3_predBindings ex3_quantBindings_compliant = true := rfl
theorem ex3_genXY_violation :
    genXYWellFormed ex3_predBindings ex3_quantBindings_violation = false := rfl

end Example3


-- ════════════════════════════════════════════════════════════════
-- § Bridge: Elbourne (2013) SitVarStatus
-- ════════════════════════════════════════════════════════════════

/-! Percus's three binding modes (closest-bound, higher-bound, free)
map onto Elbourne's two-way SitVarStatus (free/bound):

- Closest-bound (Gen X default) → .bound
- Higher-bound (de re NPs) → .bound (still bound, just by a higher λs)
- Free (indexical/deictic) → .free

The de re / de dicto distinction in Elbourne is a *consequence* of
which binder (if any) binds the situation variable. Percus makes
the syntactic constraint explicit; Elbourne uses it implicitly in
his analysis of definite descriptions. -/


end Phenomena.Reference.Studies.Percus2000
