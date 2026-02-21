import Linglib.Theories.Semantics.Intensional.Situations.Percus
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.FunctionWords

/-!
# Percus (2000): Situation Variable Constraints — Empirical Predictions @cite{percus-2000}

End-to-end derivation chain from Fragment lexical entries through
Percus's situation variable theory to concrete de re / de dicto
predictions.

## Chain

```
Fragments/English/Predicates/Verbal.lean
  "believe": opaqueContext = true, attitudeBuilder = .doxastic .nonVeridical
  "think":   opaqueContext = true, attitudeBuilder = .doxastic .nonVeridical
    ↓  (opaqueContext = true → introduces situation binder λs)
    ↓  (doxastic .nonVeridical → universal quantification, no veridicality)
Theories/Semantics/Intensional/Situations/Percus.lean
  believeSit: ∀s' ∈ Dox(s). complement(g[n ↦ s'])
  alwaysAt:   ∀s' ∈ domain(ssh). scope(g[n ↦ s'])
  genXWellFormed / genYWellFormed: filter readings
    ↓  (concrete model + predicate denotations)
Phenomena/Reference/Studies/Percus2000.lean  (this file)
  reading computations → truth values → match empirical judgments
```

## References

- Percus, O. (2000). Constraints on some other variables in syntax.
  *Natural Language Semantics* 8(3): 173–229.
-/

namespace Phenomena.Reference.Studies.Percus2000

open Core (Situation)
open Semantics.Intensional.Situations.Percus
open Core.Verbs (AttitudeBuilder)


-- ════════════════════════════════════════════════════════════════
-- § Fragment Bridge: Lexical Entries → Percus Situation Binding
-- ════════════════════════════════════════════════════════════════

/-! ### Bridge 1: VerbEntry → Situation Binding

A verb's `opaqueContext` field determines whether it introduces a
situation binder (Percus's λs) in its complement. An opaque-context
verb evaluates its complement relative to a NEW set of situations
(doxastic alternatives, desire alternatives, etc.), not the matrix
evaluation situation.

A verb's `attitudeBuilder` field determines the quantificational
semantics: doxastic attitudes use universal quantification over
doxastic alternatives (`believeSit`). -/

/-- An opaque-context verb introduces a situation binder in Percus's
    framework: the complement is evaluated at alternative situations,
    not the matrix situation. -/
def introducesSitBinder (v : Fragments.English.Predicates.Verbal.VerbEntry) : Bool :=
  v.opaqueContext

/-- A doxastic attitude builder triggers universal quantification
    over doxastic alternatives. -/
def isDoxasticUniversal (v : Fragments.English.Predicates.Verbal.VerbEntry) : Bool :=
  match v.attitudeBuilder with
  | some (.doxastic _) => true
  | _ => false

-- Per-verb verification: Fragment fields match Percus requirements
theorem believe_introduces_sit_binder :
    introducesSitBinder Fragments.English.Predicates.Verbal.believe = true := rfl
theorem think_introduces_sit_binder :
    introducesSitBinder Fragments.English.Predicates.Verbal.think = true := rfl

theorem believe_is_doxastic :
    isDoxasticUniversal Fragments.English.Predicates.Verbal.believe = true := rfl
theorem think_is_doxastic :
    isDoxasticUniversal Fragments.English.Predicates.Verbal.think = true := rfl

theorem believe_is_nonveridical :
    Fragments.English.Predicates.Verbal.believe.attitudeBuilder =
    some (.doxastic .nonVeridical) := rfl

/-! ### Bridge 2: AdvQuantEntry → Situation Quantification

The `force` field of an adverbial quantifier entry determines which
Percus operator to use: `alwaysAt` for universal force. -/

theorem always_is_universal :
    Fragments.English.FunctionWords.always.force = .universal := rfl

/-! ### Bridge 3: NounEntry → Model Entities

Proper noun Fragment entries identify individuals in the model.
Common noun entries identify situation-dependent predicates (restrictors). -/

theorem mary_is_proper :
    Fragments.English.Nouns.mary.proper = true := rfl
theorem john_is_proper :
    Fragments.English.Nouns.john.proper = true := rfl
theorem bill_is_proper :
    Fragments.English.Nouns.bill.proper = true := rfl
theorem brother_is_common :
    Fragments.English.Nouns.brother.proper = false := rfl
theorem spy_is_common :
    Fragments.English.Nouns.spy.proper = false := rfl


-- ════════════════════════════════════════════════════════════════
-- § Concrete Model
-- ════════════════════════════════════════════════════════════════

/-- Two possible worlds: the actual world and Mary's belief world. -/
inductive W where
  | actual  -- the real world
  | belief  -- what Mary thinks the world is like
  deriving DecidableEq, BEq, Repr

/-- Persons in the model, corresponding to Fragment proper nouns. -/
inductive Person where
  | mary | john | bill | charlie
  deriving DecidableEq, BEq, Repr

/-- Situations are world–Unit pairs (temporal coordinate irrelevant
    for Percus's de re / de dicto examples). -/
abbrev Sit := Situation W Unit

def sit (w : W) : Sit := ⟨w, ()⟩
def sActual : Sit := sit .actual
def sBelief : Sit := sit .belief


-- ════════════════════════════════════════════════════════════════
-- § Lexicon: Fragment Entries → Model Denotations
-- ════════════════════════════════════════════════════════════════

/-- Map Fragment proper noun forms to model entities. -/
def entityOf (n : Fragments.English.Nouns.NounEntry) : Person :=
  if n.formSg == "Mary" then .mary
  else if n.formSg == "John" then .john
  else if n.formSg == "Bill" then .bill
  else .charlie

-- Verify the mapping
theorem entityOf_mary :
    entityOf Fragments.English.Nouns.mary = .mary := rfl
theorem entityOf_john :
    entityOf Fragments.English.Nouns.john = .john := rfl
theorem entityOf_bill :
    entityOf Fragments.English.Nouns.bill = .bill := rfl


-- ════════════════════════════════════════════════════════════════
-- § Predicate Denotations (Situation-Dependent)
-- ════════════════════════════════════════════════════════════════

/-- ⟦is Canadian⟧ = λx.λs. x is Canadian at s.

    Crucially varies across worlds — this is what makes de re / de
    dicto readings yield different truth values:
    - Actual: John IS Canadian
    - Belief: John is NOT Canadian -/
def isCanadian : Person → Sit → Bool
  | .john, ⟨.actual, _⟩ => true
  | .john, ⟨.belief, _⟩ => false
  | _, _ => false

/-- ⟦is brother of speaker⟧ — the denotation of Fragment noun "brother"
    as a situation-dependent predicate (relational, 1-place after
    saturating the possessor).

    - Actual: Bill is the speaker's brother
    - Belief: Charlie is the speaker's brother -/
def isBrotherOf : Person → Sit → Bool
  | .bill, ⟨.actual, _⟩ => true
  | .charlie, ⟨.belief, _⟩ => true
  | _, _ => false

/-- ⟦is a spy⟧ — the denotation of Fragment noun "spy" as a
    situation-dependent predicate.

    Bill is a spy in Mary's belief world but not in actuality. -/
def isSpyAt : Person → Sit → Bool
  | .bill, ⟨.belief, _⟩ => true
  | _, _ => false

-- Verify: noun forms match their denotation names
theorem brother_form :
    Fragments.English.Nouns.brother.formSg = "brother" := rfl
theorem spy_form :
    Fragments.English.Nouns.spy.formSg = "spy" := rfl


-- ════════════════════════════════════════════════════════════════
-- § Doxastic Alternatives
-- ════════════════════════════════════════════════════════════════

/-- Mary's doxastic alternatives: Dox_Mary(actual) = {belief}.
    Mary mistakenly believes she is in the belief world. -/
def doxMary : Sit → List Sit
  | ⟨.actual, _⟩ => [sBelief]
  | ⟨.belief, _⟩ => [sBelief]


-- ════════════════════════════════════════════════════════════════
-- § Example 1: "Mary believes John is Canadian"
-- ════════════════════════════════════════════════════════════════

/-! ### Derivation from Fragment entries

1. **"believes"** = Fragment `Verbal.believe`
   - `opaqueContext = true` → introduces situation binder λs₂
   - `attitudeBuilder = .doxastic .nonVeridical` → uses `believeSit`
2. **"Mary"** = Fragment `Nouns.mary` → `entityOf mary = .mary`
3. **"John"** = Fragment `Nouns.john` → `entityOf john = .john`
4. **"is Canadian"** = `isCanadian` (situation-dependent predicate)
5. **Gen X**: "isCanadian" must use s₂ (closest binder = λs₂)

LF (Gen X compliant): `[λs₁ Mary believes_s₁ [λs₂ John isCanadian_s₂]]`
LF (Gen X violation):  `[λs₁ Mary believes_s₁ [λs₂ John isCanadian_s₁]]` -/

section Example1

private def g₀ : SituationAssignment W Unit := λ _ => sActual

/-- De dicto reading (Gen X compliant). Uses `believeSit` because
    `believe.attitudeBuilder = .doxastic .nonVeridical`.
    Predicate uses s₂ (embedded binder) per Gen X. -/
def reading1_deDicto : Bool :=
  believeSit (λ _ => doxMary)
    (entityOf Fragments.English.Nouns.mary) 2
    (λ g => isCanadian (entityOf Fragments.English.Nouns.john) (interpSitVar 2 g))
    g₀ sActual

/-- De re reading (Gen X violation). Predicate uses s₁ (matrix binder),
    violating Gen X (closest binder is λs₂). -/
def reading2_deRe : Bool :=
  believeSit (λ _ => doxMary)
    (entityOf Fragments.English.Nouns.mary) 2
    (λ g => isCanadian (entityOf Fragments.English.Nouns.john) (interpSitVar 1 g))
    (updateSitVar g₀ 1 sActual) sActual

theorem deDicto_is_false : reading1_deDicto = false := rfl
theorem deRe_is_true : reading2_deRe = true := rfl
theorem readings_differ : reading1_deDicto ≠ reading2_deRe := nofun

-- Gen X well-formedness
def reading1_bindings : List PredicateBinding := [⟨2, 2⟩]
def reading2_bindings : List PredicateBinding := [⟨1, 2⟩]

theorem reading1_genX_ok : genXWellFormed reading1_bindings = true := rfl
theorem reading2_genX_violation : genXWellFormed reading2_bindings = false := rfl

-- Empirical match
def empiricalJudgment_ex1 : Bool := false

theorem genX_predicts_correct_reading :
    reading1_deDicto = empiricalJudgment_ex1 := rfl
theorem genX_blocks_incorrect_reading :
    reading2_deRe ≠ empiricalJudgment_ex1 := nofun

end Example1


-- ════════════════════════════════════════════════════════════════
-- § Example 2: "Mary believes my brother is a spy"
-- ════════════════════════════════════════════════════════════════

/-! ### Derivation from Fragment entries

1. **"believes"** = Fragment `Verbal.believe` → `believeSit` (as above)
2. **"my brother"** = Fragment `Nouns.brother` → `isBrotherOf` (common noun,
   situation-dependent restrictor — Gen X does NOT constrain NP restrictors)
3. **"is a spy"** = Fragment `Nouns.spy` → `isSpyAt` (situation-dependent
   predicate — Gen X DOES constrain this)
4. **"Mary"** = Fragment `Nouns.mary` → `.mary`

Three readings: A (all de dicto), B (NP de re), C (pred de re — blocked). -/

section Example2

private def g₀' : SituationAssignment W Unit := λ _ => sActual

private def theBrother (s : Sit) : Person :=
  if isBrotherOf .bill s then .bill
  else if isBrotherOf .charlie s then .charlie
  else .mary

/-- Reading A (all de dicto): both NP restrictor and predicate in belief situations. -/
def readingA_allDeDicto : Bool :=
  believeSit (λ _ => doxMary) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let s := interpSitVar 2 g
      isSpyAt (theBrother s) s)
    g₀' sActual

/-- Reading B (NP de re, pred de dicto): NP restrictor at actual situation,
    predicate in belief situations. Gen X allows this — it only constrains
    predicates, not NP restrictors. -/
def readingB_npDeRe : Bool :=
  believeSit (λ _ => doxMary) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let sMatrix := interpSitVar 1 g
      let sEmbed := interpSitVar 2 g
      isSpyAt (theBrother sMatrix) sEmbed)
    (updateSitVar g₀' 1 sActual) sActual

/-- Reading C (pred de re — BLOCKED by Gen X): predicate at actual
    situation, NP restrictor in belief situations. -/
def readingC_predDeRe : Bool :=
  believeSit (λ _ => doxMary) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let sMatrix := interpSitVar 1 g
      let sEmbed := interpSitVar 2 g
      isSpyAt (theBrother sEmbed) sMatrix)
    (updateSitVar g₀' 1 sActual) sActual

theorem readingA_is_false : readingA_allDeDicto = false := rfl
theorem readingB_is_true : readingB_npDeRe = true := rfl
theorem readingC_is_false : readingC_predDeRe = false := rfl

-- Gen X: predicate bindings only (NP restrictors exempt)
def readingA_bindings : List PredicateBinding := [⟨2, 2⟩]
def readingB_bindings : List PredicateBinding := [⟨2, 2⟩]
def readingC_bindings : List PredicateBinding := [⟨1, 2⟩]

theorem readingA_genX_ok : genXWellFormed readingA_bindings = true := rfl
theorem readingB_genX_ok : genXWellFormed readingB_bindings = true := rfl
theorem readingC_genX_violation : genXWellFormed readingC_bindings = false := rfl

end Example2


-- ════════════════════════════════════════════════════════════════
-- § Example 3: "Mary thinks my brother always won the game"
-- ════════════════════════════════════════════════════════════════

/-! ### Derivation from Fragment entries

1. **"thinks"** = Fragment `Verbal.think`
   - `opaqueContext = true` → introduces λs₂
   - `attitudeBuilder = .doxastic .nonVeridical` → `believeSit`
2. **"always"** = Fragment `FunctionWords.always`
   - `force = .universal` → `alwaysAt` (universal situation quantification)
   - Gen Y: ssh must use nearest λ (= λs₂ under "thinks")
3. **"won"** = `wonGame` (situation-dependent predicate)
   - Gen X: must use s₃ (nearest binder = λs₃ from "always")

Gen Y has independent bite: Gen X is satisfied in BOTH readings (the
predicate "won" uses s₃, bound by λs₃ either way). Gen Y is the
constraint that forces "always" to quantify over belief-world rounds. -/

section Example3

inductive Round where | r1 | r2 | r3 deriving DecidableEq, BEq, Repr

abbrev RSit := Situation W Round
private def rSit (w : W) (r : Round) : RSit := ⟨w, r⟩

/-- ⟦won the game⟧: Bill won rounds 1–2 in actuality but lost round 3;
    in Mary's belief world he won all three. -/
def wonGame : Person → RSit → Bool
  | .bill, ⟨.actual, .r1⟩ => true
  | .bill, ⟨.actual, .r2⟩ => true
  | .bill, ⟨.actual, .r3⟩ => false
  | .bill, ⟨.belief, _⟩ => true
  | _, _ => false

/-- Game-round domain: all 3 rounds at the world of the given situation. -/
def gameRounds (s : RSit) : List RSit :=
  [rSit s.world .r1, rSit s.world .r2, rSit s.world .r3]

def doxMaryR : RSit → List RSit
  | ⟨.actual, r⟩ => [⟨.belief, r⟩]
  | ⟨.belief, r⟩ => [⟨.belief, r⟩]

private def g₃ : SituationAssignment W Round := λ _ => rSit .actual .r1

/-- Gen Y compliant: "always" (from Fragment, force = .universal) uses
    ssh = s₂ (embedded binder, nearest λ per Gen Y).
    Uses `alwaysAt` because `FunctionWords.always.force = .universal`. -/
def genY_compliant : Bool :=
  believeSit (λ _ => doxMaryR) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let ssh := interpSitVar 2 g
      alwaysAt gameRounds ssh 3
        (λ g' => wonGame (entityOf Fragments.English.Nouns.bill) (interpSitVar 3 g')) g)
    g₃ (rSit .actual .r1)

/-- Gen Y violation: "always" uses ssh = s₁ (matrix binder). -/
def genY_violation : Bool :=
  believeSit (λ _ => doxMaryR) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let ssh := interpSitVar 1 g
      alwaysAt gameRounds ssh 3
        (λ g' => wonGame (entityOf Fragments.English.Nouns.bill) (interpSitVar 3 g')) g)
    (updateSitVar g₃ 1 (rSit .actual .r1)) (rSit .actual .r1)

theorem genY_compliant_is_true : genY_compliant = true := rfl
theorem genY_violation_is_false : genY_violation = false := rfl
theorem genY_readings_differ : genY_compliant ≠ genY_violation := nofun

-- Empirical match
def empiricalJudgment_ex3 : Bool := true

theorem genY_predicts_correct_reading :
    genY_compliant = empiricalJudgment_ex3 := rfl
theorem genY_blocks_incorrect_reading :
    genY_violation ≠ empiricalJudgment_ex3 := nofun

-- Gen X satisfied by both readings; Gen Y distinguishes them
def ex3_predBindings : List PredicateBinding := [⟨3, 3⟩]
def ex3_quantBindings_compliant : List PredicateBinding := [⟨2, 2⟩]
def ex3_quantBindings_violation : List PredicateBinding := [⟨1, 2⟩]

theorem ex3_genX_ok_for_both : genXWellFormed ex3_predBindings = true := rfl
theorem ex3_genY_compliant_ok :
    genYWellFormed ex3_quantBindings_compliant = true := rfl
theorem ex3_genY_violation_caught :
    genYWellFormed ex3_quantBindings_violation = false := rfl

theorem ex3_genXY_compliant :
    genXYWellFormed ex3_predBindings ex3_quantBindings_compliant = true := rfl
theorem ex3_genXY_violation :
    genXYWellFormed ex3_predBindings ex3_quantBindings_violation = false := rfl

end Example3


end Phenomena.Reference.Studies.Percus2000
