import Linglib.Core.IntensionalLogic.Rigidity
import Linglib.Core.Assignment
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
  "believe": opaqueContext = true, attitude =.doxastic.nonVeridical
  "think": opaqueContext = true, attitude =.doxastic.nonVeridical
    ↓ (opaqueContext = true → introduces situation binder λs)
(this file: theory + empirical predictions)
  believeSit: ∀s' ∈ Dox(s). complement(g[n ↦ s'])
  genXWellFormed / genYWellFormed: filter readings
    ↓ (concrete model + predicate denotations)
  reading computations → truth values → match empirical judgments
```

-/

namespace Percus2000

open Core (Situation)
open Core.VarAssignment (VarAssignment updateVar lookupVar varLambdaAbs
  update_lookup_same update_lookup_other)
open Core.Context
open Core.Verbs (Attitude)


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
    (complement : SituationAssignment W Time → Prop)
    (g : SituationAssignment W Time) (s : Situation W Time) : Prop :=
  ∀ s' ∈ dox agent s, complement (updateSitVar g n s')

instance {W Time E : Type*}
    (dox : DoxSit W Time E) (agent : E) (n : ℕ)
    (complement : SituationAssignment W Time → Prop) [DecidablePred complement]
    (g : SituationAssignment W Time) (s : Situation W Time) :
    Decidable (believeSit dox agent n complement g s) := by
  unfold believeSit; infer_instance

def alwaysAt {W Time : Type*}
    (domain : Situation W Time → List (Situation W Time))
    (ssh : Situation W Time) (n : ℕ)
    (scope : SituationAssignment W Time → Prop)
    (g : SituationAssignment W Time) : Prop :=
  ∀ s' ∈ domain ssh, scope (updateSitVar g n s')

instance {W Time : Type*}
    (domain : Situation W Time → List (Situation W Time))
    (ssh : Situation W Time) (n : ℕ)
    (scope : SituationAssignment W Time → Prop) [DecidablePred scope]
    (g : SituationAssignment W Time) :
    Decidable (alwaysAt domain ssh n scope g) := by
  unfold alwaysAt; infer_instance


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
  match v.attitude with
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
    Fragments.English.Predicates.Verbal.believe.attitude =
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
  deriving DecidableEq, Repr

inductive Person where
  | mary | john | bill | charlie
  deriving DecidableEq, Repr

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

def isCanadian (p : Person) (s : Sit) : Prop :=
  match p, s.world with
  | .john, .actual => True
  | _, _ => False

instance instDecidableIsCanadian (p : Person) (s : Sit) : Decidable (isCanadian p s) := by
  unfold isCanadian; cases p <;> cases s.world <;> infer_instance

def isBrotherOf (p : Person) (s : Sit) : Prop :=
  match p, s.world with
  | .bill, .actual => True
  | .charlie, .belief => True
  | _, _ => False

instance instDecidableIsBrotherOf (p : Person) (s : Sit) : Decidable (isBrotherOf p s) := by
  unfold isBrotherOf; cases p <;> cases s.world <;> infer_instance

def isSpyAt (p : Person) (s : Sit) : Prop :=
  match p, s.world with
  | .bill, .belief => True
  | _, _ => False

instance instDecidableIsSpyAt (p : Person) (s : Sit) : Decidable (isSpyAt p s) := by
  unfold isSpyAt; cases p <;> cases s.world <;> infer_instance

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

def reading1_deDicto : Prop :=
  believeSit (λ _ => doxMary)
    (entityOf Fragments.English.Nouns.mary) 2
    (λ g => isCanadian (entityOf Fragments.English.Nouns.john) (interpSitVar 2 g))
    g₀ sActual

instance : Decidable reading1_deDicto := by
  unfold reading1_deDicto believeSit; infer_instance

def reading2_deRe : Prop :=
  believeSit (λ _ => doxMary)
    (entityOf Fragments.English.Nouns.mary) 2
    (λ g => isCanadian (entityOf Fragments.English.Nouns.john) (interpSitVar 1 g))
    (updateSitVar g₀ 1 sActual) sActual

instance : Decidable reading2_deRe := by
  unfold reading2_deRe believeSit; infer_instance

theorem deDicto_is_false : ¬ reading1_deDicto := by decide
theorem deRe_is_true : reading2_deRe := by decide
theorem readings_differ : ¬ (reading1_deDicto ↔ reading2_deRe) := by
  intro h; exact deDicto_is_false (h.mpr deRe_is_true)

def reading1_bindings : List PredicateBinding := [⟨2, 2⟩]
def reading2_bindings : List PredicateBinding := [⟨1, 2⟩]

theorem reading1_genX_ok : genXWellFormed reading1_bindings = true := rfl
theorem reading2_genX_violation : genXWellFormed reading2_bindings = false := rfl

def empiricalJudgment_ex1 : Prop := False

theorem genX_predicts_correct_reading :
    reading1_deDicto ↔ empiricalJudgment_ex1 := by
  unfold empiricalJudgment_ex1; exact iff_false_intro deDicto_is_false
theorem genX_blocks_incorrect_reading :
    ¬ (reading2_deRe ↔ empiricalJudgment_ex1) := by
  intro h; exact h.mp deRe_is_true

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

def readingA_allDeDicto : Prop :=
  believeSit (λ _ => doxMary) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let s := interpSitVar 2 g
      isSpyAt (theBrother s) s)
    g₀' sActual

instance : Decidable readingA_allDeDicto := by
  unfold readingA_allDeDicto believeSit; infer_instance

def readingB_npDeRe : Prop :=
  believeSit (λ _ => doxMary) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let sMatrix := interpSitVar 1 g
      let sEmbed := interpSitVar 2 g
      isSpyAt (theBrother sMatrix) sEmbed)
    (updateSitVar g₀' 1 sActual) sActual

instance : Decidable readingB_npDeRe := by
  unfold readingB_npDeRe believeSit; infer_instance

def readingC_predDeRe : Prop :=
  believeSit (λ _ => doxMary) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let sMatrix := interpSitVar 1 g
      let sEmbed := interpSitVar 2 g
      isSpyAt (theBrother sEmbed) sMatrix)
    (updateSitVar g₀' 1 sActual) sActual

instance : Decidable readingC_predDeRe := by
  unfold readingC_predDeRe believeSit; infer_instance

theorem readingA_is_false : ¬ readingA_allDeDicto := by decide
theorem readingB_is_true : readingB_npDeRe := by decide
theorem readingC_is_false : ¬ readingC_predDeRe := by decide

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

inductive Round where | r1 | r2 | r3 deriving DecidableEq, Repr

abbrev RSit := Situation W Round
private def rSit (w : W) (r : Round) : RSit := ⟨w, r⟩

def wonGame (p : Person) (s : RSit) : Prop :=
  match p, s.world, s.time with
  | .bill, .actual, .r1 => True
  | .bill, .actual, .r2 => True
  | .bill, .actual, .r3 => False
  | .bill, .belief, _ => True
  | _, _, _ => False

instance instDecidableWonGame (p : Person) (s : RSit) : Decidable (wonGame p s) := by
  unfold wonGame; cases p <;> cases s.world <;> cases s.time <;> infer_instance

def gameRounds (s : RSit) : List RSit :=
  [rSit s.world .r1, rSit s.world .r2, rSit s.world .r3]

def doxMaryR : RSit → List RSit
  | ⟨.actual, r⟩ => [⟨.belief, r⟩]
  | ⟨.belief, r⟩ => [⟨.belief, r⟩]

private def g₃ : SituationAssignment W Round := λ _ => rSit .actual .r1

def genY_compliant : Prop :=
  believeSit (λ _ => doxMaryR) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let ssh := interpSitVar 2 g
      alwaysAt gameRounds ssh 3
        (λ g' => wonGame (entityOf Fragments.English.Nouns.bill) (interpSitVar 3 g')) g)
    g₃ (rSit .actual .r1)

instance : Decidable genY_compliant := by
  unfold genY_compliant believeSit alwaysAt; infer_instance

def genY_violation : Prop :=
  believeSit (λ _ => doxMaryR) (entityOf Fragments.English.Nouns.mary) 2
    (λ g =>
      let ssh := interpSitVar 1 g
      alwaysAt gameRounds ssh 3
        (λ g' => wonGame (entityOf Fragments.English.Nouns.bill) (interpSitVar 3 g')) g)
    (updateSitVar g₃ 1 (rSit .actual .r1)) (rSit .actual .r1)

instance : Decidable genY_violation := by
  unfold genY_violation believeSit alwaysAt; infer_instance

theorem genY_compliant_is_true : genY_compliant := by decide
theorem genY_violation_is_false : ¬ genY_violation := by decide
theorem genY_readings_differ : ¬ (genY_compliant ↔ genY_violation) := by
  intro h; exact genY_violation_is_false (h.mp genY_compliant_is_true)

def empiricalJudgment_ex3 : Prop := True

theorem genY_predicts_correct_reading :
    genY_compliant ↔ empiricalJudgment_ex3 := by
  unfold empiricalJudgment_ex3; exact iff_true_intro genY_compliant_is_true
theorem genY_blocks_incorrect_reading :
    ¬ (genY_violation ↔ empiricalJudgment_ex3) := by
  intro h; exact genY_violation_is_false (h.mpr (by unfold empiricalJudgment_ex3; trivial))

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


end Percus2000
