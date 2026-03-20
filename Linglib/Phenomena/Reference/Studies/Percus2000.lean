import Linglib.Core.Semantics.Intension
import Linglib.Core.Temporal.Tense
import Linglib.Core.Context.Tower
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.FunctionWords

/-!
# @cite{percus-2000}: Constraints on Situation Variables in Syntax @cite{percus-2000}
@cite{heim-kratzer-1998} @cite{kratzer-1998} @cite{partee-1973}

Formalizes Percus's theory of situation pronouns in LF and derives
concrete de re / de dicto predictions from Fragment lexical entries.

Every predicate takes a situation argument, every clause introduces a
lambda-s binder, and **Generalization X** constrains which binder can
bind which variable.

## Generalization X

> The situation pronoun that a predicate is associated with must be
> bound by the minimal c-commanding situation binder.

## Situation Assignment Infrastructure

Situation assignments specialize `Core.VarAssignment` from `D = Time`
(Partee's temporal variables) to `D = Situation W Time` (Percus's
situation variables).

## Empirical Chain

```
Fragments/English/Predicates/Verbal.lean
  "believe": opaqueContext = true, attitudeBuilder =.doxastic.nonVeridical
  "think": opaqueContext = true, attitudeBuilder =.doxastic.nonVeridical
    ↓ (opaqueContext = true → introduces situation binder λs)
(this file: theory + empirical predictions)
  believeSit: ∀s' ∈ Dox(s). complement(g[n ↦ s'])
  genXWellFormed / genYWellFormed: filter readings
    ↓ (concrete model + predicate denotations)
  reading computations → truth values → match empirical judgments
```

-/

namespace Phenomena.Reference.Studies.Percus2000

open Core (Situation)
open Core.VarAssignment (VarAssignment updateVar lookupVar varLambdaAbs
  update_lookup_same update_lookup_other)
open Core.Context
open Core.Verbs (AttitudeBuilder)


-- ════════════════════════════════════════════════════════════════
-- § Situation Assignment
-- ════════════════════════════════════════════════════════════════

/-- Situation assignment function: maps variable indices to situations. -/
abbrev SituationAssignment (W Time : Type*) := VarAssignment (Situation W Time)

/-- Situation variable denotation: s_n^g = g(n). -/
abbrev interpSitVar {W Time : Type*} (n : ℕ) (g : SituationAssignment W Time) :
    Situation W Time :=
  lookupVar n g

/-- Modified situation assignment g[n -> s]. -/
abbrev updateSitVar {W Time : Type*} (g : SituationAssignment W Time)
    (n : ℕ) (s : Situation W Time) : SituationAssignment W Time :=
  updateVar g n s

/-- Situation lambda abstraction: bind a situation variable. -/
abbrev sitLambdaAbs {W Time α : Type*} (n : ℕ)
    (body : SituationAssignment W Time → α) :
    SituationAssignment W Time → Situation W Time → α :=
  varLambdaAbs n body


-- ════════════════════════════════════════════════════════════════
-- § Generalization X
-- ════════════════════════════════════════════════════════════════

structure PredicateBinding where
  sitVarIndex : ℕ
  closestBinderIndex : ℕ

def PredicateBinding.genXCompliant (b : PredicateBinding) : Bool :=
  b.sitVarIndex == b.closestBinderIndex

def genXWellFormed (bindings : List PredicateBinding) : Bool :=
  bindings.all PredicateBinding.genXCompliant

/-- Generalization Y: adverbial quantifiers must use nearest binder. -/
def genYWellFormed (quantifierBindings : List PredicateBinding) : Bool :=
  quantifierBindings.all PredicateBinding.genXCompliant

def genXYWellFormed (predicateBindings quantifierBindings : List PredicateBinding) : Bool :=
  genXWellFormed predicateBindings && genYWellFormed quantifierBindings


-- ════════════════════════════════════════════════════════════════
-- § Tower Bridge: Generalization X as Depth Constraint
-- ════════════════════════════════════════════════════════════════

def GenXAsTowerDepth {C R : Type*} (ap : AccessPattern C R) : Prop :=
  ap.depth = .local

def RestrictorUnconstrained {C R : Type*} (_ap : AccessPattern C R) : Prop :=
  True

def genXTowerWellFormed {C : Type*}
    (predicatePatterns : List (Σ R, AccessPattern C R))
    (_restrictorPatterns : List (Σ R, AccessPattern C R)) : Prop :=
  ∀ p, p ∈ predicatePatterns → GenXAsTowerDepth p.2

theorem genX_bridge_compliant :
    ∀ (b : PredicateBinding), b.genXCompliant = true ↔
      b.sitVarIndex = b.closestBinderIndex := by
  intro b
  simp only [PredicateBinding.genXCompliant, beq_iff_eq]


-- ════════════════════════════════════════════════════════════════
-- § Attitude Semantics with Situation Binding
-- ════════════════════════════════════════════════════════════════

abbrev DoxSit (W Time E : Type*) := E → Situation W Time → List (Situation W Time)

def believeSit {W Time E : Type*}
    (dox : DoxSit W Time E) (agent : E) (n : ℕ)
    (complement : SituationAssignment W Time → Bool)
    (g : SituationAssignment W Time) (s : Situation W Time) : Bool :=
  (dox agent s).all λ s' => complement (updateSitVar g n s')

def alwaysAt {W Time : Type*}
    (domain : Situation W Time → List (Situation W Time))
    (ssh : Situation W Time) (n : ℕ)
    (scope : SituationAssignment W Time → Bool)
    (g : SituationAssignment W Time) : Bool :=
  (domain ssh).all λ s' => scope (updateSitVar g n s')


-- ════════════════════════════════════════════════════════════════
-- § Key Properties
-- ════════════════════════════════════════════════════════════════

theorem sitVar_receives_binder_value {W Time : Type*}
    (g : SituationAssignment W Time) (n : ℕ) (s : Situation W Time) :
    interpSitVar n (updateSitVar g n s) = s :=
  update_lookup_same g n s

theorem sitVar_other_unaffected {W Time : Type*}
    (g : SituationAssignment W Time) (n i : ℕ) (s : Situation W Time)
    (h : i ≠ n) :
    interpSitVar i (updateSitVar g n s) = interpSitVar i g :=
  update_lookup_other g n i s h


-- ════════════════════════════════════════════════════════════════
-- § Bridge: Temporal <-> Situational
-- ════════════════════════════════════════════════════════════════

def toTemporalAssignment {W Time : Type*}
    (g : SituationAssignment W Time) : Core.Tense.TemporalAssignment Time :=
  λ n => (g n).time

theorem temporal_projection_commutes {W Time : Type*}
    (g : SituationAssignment W Time) (n : ℕ) :
    Core.Tense.interpTense n (toTemporalAssignment g) = (interpSitVar n g).time :=
  rfl


-- ════════════════════════════════════════════════════════════════
-- § Fragment Bridge: Lexical Entries → Percus Situation Binding
-- ════════════════════════════════════════════════════════════════

def introducesSitBinder (v : Fragments.English.Predicates.Verbal.VerbEntry) : Bool :=
  v.opaqueContext

def isDoxasticUniversal (v : Fragments.English.Predicates.Verbal.VerbEntry) : Bool :=
  match v.attitudeBuilder with
  | some (.doxastic _) => true
  | _ => false

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

theorem always_is_universal :
    Fragments.English.FunctionWords.always.force = .universal := rfl

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

inductive W where
  | actual | belief
  deriving DecidableEq, BEq, Repr

inductive Person where
  | mary | john | bill | charlie
  deriving DecidableEq, BEq, Repr

abbrev Sit := Situation W Unit

def sit (w : W) : Sit := ⟨w, ()⟩
def sActual : Sit := sit .actual
def sBelief : Sit := sit .belief

def entityOf (n : Fragments.English.Nouns.NounEntry) : Person :=
  if n.formSg == "Mary" then .mary
  else if n.formSg == "John" then .john
  else if n.formSg == "Bill" then .bill
  else .charlie

theorem entityOf_mary :
    entityOf Fragments.English.Nouns.mary = .mary := rfl
theorem entityOf_john :
    entityOf Fragments.English.Nouns.john = .john := rfl
theorem entityOf_bill :
    entityOf Fragments.English.Nouns.bill = .bill := rfl


-- ════════════════════════════════════════════════════════════════
-- § Predicate Denotations (Situation-Dependent)
-- ════════════════════════════════════════════════════════════════

def isCanadian : Person → Sit → Bool
  | .john, ⟨.actual, _⟩ => true
  | .john, ⟨.belief, _⟩ => false
  | _, _ => false

def isBrotherOf : Person → Sit → Bool
  | .bill, ⟨.actual, _⟩ => true
  | .charlie, ⟨.belief, _⟩ => true
  | _, _ => false

def isSpyAt : Person → Sit → Bool
  | .bill, ⟨.belief, _⟩ => true
  | _, _ => false

theorem brother_form :
    Fragments.English.Nouns.brother.formSg = "brother" := rfl
theorem spy_form :
    Fragments.English.Nouns.spy.formSg = "spy" := rfl


-- ════════════════════════════════════════════════════════════════
-- § Doxastic Alternatives
-- ════════════════════════════════════════════════════════════════

def doxMary : Sit → List Sit
  | ⟨.actual, _⟩ => [sBelief]
  | ⟨.belief, _⟩ => [sBelief]


-- ════════════════════════════════════════════════════════════════
-- § Example 1: "Mary believes John is Canadian"
-- ════════════════════════════════════════════════════════════════

section Example1

private def g₀ : SituationAssignment W Unit := λ _ => sActual

def reading1_deDicto : Bool :=
  believeSit (λ _ => doxMary)
    (entityOf Fragments.English.Nouns.mary) 2
    (λ g => isCanadian (entityOf Fragments.English.Nouns.john) (interpSitVar 2 g))
    g₀ sActual

def reading2_deRe : Bool :=
  believeSit (λ _ => doxMary)
    (entityOf Fragments.English.Nouns.mary) 2
    (λ g => isCanadian (entityOf Fragments.English.Nouns.john) (interpSitVar 1 g))
    (updateSitVar g₀ 1 sActual) sActual

theorem deDicto_is_false : reading1_deDicto = false := rfl
theorem deRe_is_true : reading2_deRe = true := rfl
theorem readings_differ : reading1_deDicto ≠ reading2_deRe := nofun

def reading1_bindings : List PredicateBinding := [⟨2, 2⟩]
def reading2_bindings : List PredicateBinding := [⟨1, 2⟩]

theorem reading1_genX_ok : genXWellFormed reading1_bindings = true := rfl
theorem reading2_genX_violation : genXWellFormed reading2_bindings = false := rfl

def empiricalJudgment_ex1 : Bool := false

theorem genX_predicts_correct_reading :
    reading1_deDicto = empiricalJudgment_ex1 := rfl
theorem genX_blocks_incorrect_reading :
    reading2_deRe ≠ empiricalJudgment_ex1 := nofun

end Example1


-- ════════════════════════════════════════════════════════════════
-- § Example 2: "Mary believes my brother is a spy"
-- ════════════════════════════════════════════════════════════════

section Example2

private def g₀' : SituationAssignment W Unit := λ _ => sActual

private def theBrother (s : Sit) : Person :=
  if isBrotherOf .bill s then .bill
  else if isBrotherOf .charlie s then .charlie
  else .mary

def readingA_allDeDicto : Bool :=
  believeSit (λ _ => doxMary) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let s := interpSitVar 2 g
      isSpyAt (theBrother s) s)
    g₀' sActual

def readingB_npDeRe : Bool :=
  believeSit (λ _ => doxMary) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let sMatrix := interpSitVar 1 g
      let sEmbed := interpSitVar 2 g
      isSpyAt (theBrother sMatrix) sEmbed)
    (updateSitVar g₀' 1 sActual) sActual

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

section Example3

inductive Round where | r1 | r2 | r3 deriving DecidableEq, BEq, Repr

abbrev RSit := Situation W Round
private def rSit (w : W) (r : Round) : RSit := ⟨w, r⟩

def wonGame : Person → RSit → Bool
  | .bill, ⟨.actual, .r1⟩ => true
  | .bill, ⟨.actual, .r2⟩ => true
  | .bill, ⟨.actual, .r3⟩ => false
  | .bill, ⟨.belief, _⟩ => true
  | _, _ => false

def gameRounds (s : RSit) : List RSit :=
  [rSit s.world .r1, rSit s.world .r2, rSit s.world .r3]

def doxMaryR : RSit → List RSit
  | ⟨.actual, r⟩ => [⟨.belief, r⟩]
  | ⟨.belief, r⟩ => [⟨.belief, r⟩]

private def g₃ : SituationAssignment W Round := λ _ => rSit .actual .r1

def genY_compliant : Bool :=
  believeSit (λ _ => doxMaryR) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let ssh := interpSitVar 2 g
      alwaysAt gameRounds ssh 3
        (λ g' => wonGame (entityOf Fragments.English.Nouns.bill) (interpSitVar 3 g')) g)
    g₃ (rSit .actual .r1)

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

def empiricalJudgment_ex3 : Bool := true

theorem genY_predicts_correct_reading :
    genY_compliant = empiricalJudgment_ex3 := rfl
theorem genY_blocks_incorrect_reading :
    genY_violation ≠ empiricalJudgment_ex3 := nofun

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
