import Linglib.Semantics.ArgumentStructure.LevinClass
import Linglib.Data.Examples.LevinRappaportHovav1995

/-!
# Levin and Rappaport Hovav (1995): Unaccusativity

This file formalizes the linking rules of [levin-hovav-1995] and the classification of
[levin-1993]'s intransitive verb classes they yield. The Immediate Cause Linking Rule (1), the
Directed Change Linking Rule (24), the Existence Linking Rule (47) and the Default Linking Rule
(49) of chapter 4 assign an argument to the external or the direct internal argument position
from what the verb's meaning says of it (`Characterization`), the Directed Change and Existence
rules taking precedence over the Immediate Cause rule and that over the Default rule (§4.2,
`link`); a monadic verb is unaccusative when its sole argument is a direct internal argument.
Appendix A assigns Levin's classes to the book's semantic classes (`characterizations`), whence
chapter 4's verdicts: verbs of emission are unergative, verbs of change of state, of inherently
directed motion and of existence and appearance unaccusative whatever their agentivity, the
run verbs unergative and the roll verbs unaccusative when nonagentive. The book's diagnostics
in `Data/Examples/LevinRappaportHovav1995.json` sort the verbs the same way
(`diagnostics_agree`).

## Implementation notes

* A class the book discusses under several construals, such as the verbs of spatial
  configuration in their simple, maintain and assume position senses, lists one
  characterization per construal, and a data row records whether its verb is used agentively.
* The relative order of the Directed Change and Existence rules, which the book leaves open
  (§4.2.4), does not affect the position either assigns.

## References

* [levin-hovav-1995]
* [levin-1993]
-/

namespace LevinRappaportHovav1995

open ArgumentStructure Data.Examples

/-- What a verb's meaning says of an argument, as the linking rules read it: whether it is the
immediate cause of the eventuality, so that the verb is internally caused (§3.2.1), whether it
undergoes a directed change (§4.1.2), and whether its existence is asserted or denied
(§4.1.3). -/
structure Characterization where
  immediateCause : Bool
  directedChange : Bool
  existence : Bool
  deriving DecidableEq, Repr

/-- The argument-structure positions the rules assign. -/
inductive Position
  | external | directInternal
  deriving DecidableEq, Repr

/-- The four linking rules of chapter 4. -/
inductive LinkingRule
  /-- (1): the argument denoting the immediate cause is the external argument. -/
  | immediateCause
  /-- (24): the argument undergoing the directed change is the direct internal argument. -/
  | directedChange
  /-- (47): the argument whose existence is asserted or denied is the direct internal
  argument. -/
  | existence
  /-- (49): an argument under the scope of no other rule is the direct internal argument. -/
  | default
  deriving DecidableEq, Repr

namespace LinkingRule

/-- The rule's scope. -/
def Applies : LinkingRule → Characterization → Prop
  | .immediateCause, c => c.immediateCause = true
  | .directedChange, c => c.directedChange = true
  | .existence, c => c.existence = true
  | .default, c => c.immediateCause = false ∧ c.directedChange = false ∧ c.existence = false

instance (r : LinkingRule) (c : Characterization) : Decidable (r.Applies c) := by
  cases r <;> unfold Applies <;> infer_instance

/-- The position the rule assigns. -/
def position : LinkingRule → Position
  | .immediateCause => .external
  | _ => .directInternal

/-- Precedence (§4.2.4), lower first: the Directed Change and Existence rules over the
Immediate Cause rule over the Default rule. -/
def rank : LinkingRule → ℕ
  | .directedChange | .existence => 0
  | .immediateCause => 1
  | .default => 2

end LinkingRule

/-- The rule that links the argument: the applicable rule of highest precedence. -/
def link (c : Characterization) : LinkingRule :=
  if c.directedChange then .directedChange else if c.existence then .existence
  else if c.immediateCause then .immediateCause else .default

theorem link_applies (c : Characterization) : (link c).Applies c := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> decide

theorem link_rank_le (c : Characterization) (r : LinkingRule) (h : r.Applies c) :
    (link c).rank ≤ r.rank := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> cases r <;> revert h <;> decide

/-- The verb is unaccusative: its sole argument is a direct internal argument. -/
def Unaccusative (c : Characterization) : Prop := (link c).position = .directInternal

/-- The verb is unergative: its sole argument is the external argument. -/
def Unergative (c : Characterization) : Prop := (link c).position = .external

instance (c : Characterization) : Decidable (Unaccusative c) := inferInstanceAs (Decidable (_ = _))
instance (c : Characterization) : Decidable (Unergative c) := inferInstanceAs (Decidable (_ = _))

/-- Unaccusativity in one line: the argument undergoes a directed change, has its existence at
issue, or is not the immediate cause. -/
theorem unaccusative_iff (c : Characterization) : Unaccusative c ↔
    c.directedChange = true ∨ c.existence = true ∨ c.immediateCause = false := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> decide

/-! ### The verdicts of chapter 4 -/

/-- An internally caused verb whose argument neither undergoes a directed change nor has its
existence at issue is unergative (§4.1.1): the agentive monadic verbs, verbs such as *cough*
and *tremble*, the verbs of emission (§4.1.1.1) and the verbs of spatial configuration in their
maintain position sense (§4.1.1.2). -/
theorem internallyCaused_unergative : Unergative ⟨true, false, false⟩ := by decide

/-- A verb of directed change is unaccusative whatever its causation: the externally caused
verbs of change of state (§4.1.2), the internally caused ones (§4.2.1), the verbs of inherently
directed motion (§4.2.2) and the assume position sense (§4.2.3). -/
theorem directedChange_unaccusative (ic ex : Bool) : Unaccusative ⟨ic, true, ex⟩ := by
  cases ic <;> cases ex <;> decide

/-- A verb whose argument's existence is at issue is unaccusative whatever its causation
(§4.1.3, §4.2.4): verbs of existence, appearance and disappearance. -/
theorem existence_unaccusative (ic dc : Bool) : Unaccusative ⟨ic, dc, true⟩ := by
  cases ic <;> cases dc <;> decide

/-- The roll verbs used nonagentively fall under the Default rule alone and are unaccusative
(§4.1.4). -/
theorem default_unaccusative : Unaccusative ⟨false, false, false⟩ := by decide

/-! ### Appendix A: the classes of Levin 1993 -/

/-- Appendix A's assignment of [levin-1993]'s intransitive classes to the book's semantic
classes, one characterization per construal the book discusses: the verbs of emission are
internally caused (§4.1.1.1); the verbs of inherently directed motion undergo a directed
change, agentively or not (§4.2.2); the roll verbs are externally caused with no directed
change, and internally caused when agentive (§4.1.4, §4.2.2); the run verbs are internally
caused (§4.1.4); the verbs of existence, appearance, occurrence and disappearance have their
argument's existence at issue, agentively or not (§4.1.3, §4.2.4); the verbs of spatial
configuration assert existence in their simple position sense, are internally caused in their
maintain position sense and add a directed change in their assume position sense (§4.1.1.2,
§4.2.3); the verbs of change of state undergo a directed change, externally caused for the
break, bend, cooking and other alternating verbs and internally caused for the entity-specific
ones (§4.1.2, §4.2.1). -/
def characterizations : LevinClass → List Characterization
  | .lightEmission | .soundEmission | .smellEmission | .substanceEmission => [⟨true, false, false⟩]
  | .inherentlyDirectedMotion => [⟨true, true, false⟩, ⟨false, true, false⟩]
  | .roll => [⟨false, false, false⟩, ⟨true, false, false⟩]
  | .run => [⟨true, false, false⟩]
  | .exist | .appear | .occurrence | .disappearance => [⟨true, false, true⟩, ⟨false, false, true⟩]
  | .spatialConfiguration => [⟨false, false, true⟩, ⟨true, false, false⟩, ⟨true, true, false⟩]
  | .break_ | .bend | .cooking | .otherChangeOfState => [⟨false, true, false⟩]
  | .entitySpecificChangeOfState => [⟨true, true, false⟩]
  | _ => []

/-- Verbs of emission are unergative (§4.1.1.1). -/
theorem emission_unergative :
    ∀ c ∈ [LevinClass.lightEmission, .soundEmission, .smellEmission, .substanceEmission],
      ∀ ch ∈ characterizations c, Unergative ch := by
  decide +kernel

/-- Verbs of change of state are unaccusative, externally or internally caused (§4.1.2,
§4.2.1). -/
theorem changeOfState_unaccusative :
    ∀ c ∈ [LevinClass.break_, .bend, .cooking, .otherChangeOfState,
      .entitySpecificChangeOfState], ∀ ch ∈ characterizations c, Unaccusative ch := by
  decide +kernel

/-- Verbs of inherently directed motion are unaccusative whether used agentively or not
(§4.2.2). -/
theorem directedMotion_unaccusative :
    ∀ ch ∈ characterizations .inherentlyDirectedMotion, Unaccusative ch := by
  decide

/-- Verbs of existence, appearance, occurrence and disappearance are unaccusative whether
used agentively or not (§4.1.3, §4.2.4). -/
theorem existence_classes_unaccusative :
    ∀ c ∈ [LevinClass.exist, .appear, .occurrence, .disappearance],
      ∀ ch ∈ characterizations c, Unaccusative ch := by
  decide +kernel

/-- The run verbs are unergative (§4.1.4). -/
theorem run_unergative : ∀ ch ∈ characterizations .run, Unergative ch := by decide

/-- The roll verbs are unaccusative when nonagentive and unergative when agentive (§4.1.4,
§4.2.2). -/
theorem roll_variable :
    (∃ ch ∈ characterizations .roll, ch.immediateCause = false ∧ Unaccusative ch) ∧
      ∃ ch ∈ characterizations .roll, ch.immediateCause = true ∧ Unergative ch := by
  decide

/-- Verbs of spatial configuration are unaccusative in their simple and assume position senses
and unergative in their maintain position sense (§4.1.1.2, §4.2.3). -/
theorem spatialConfiguration_variable :
    (∃ ch ∈ characterizations .spatialConfiguration, ch.existence = true ∧ Unaccusative ch) ∧
      (∃ ch ∈ characterizations .spatialConfiguration, ch.directedChange = true ∧
        Unaccusative ch) ∧
      ∃ ch ∈ characterizations .spatialConfiguration, ch.immediateCause = true ∧
        ch.directedChange = false ∧ Unergative ch := by
  decide

/-! ### The diagnostics -/

/-- The unaccusative diagnostics the data rows apply, by what acceptability indicates: the
unergative resultative pattern, the X's way construction and a cognate object indicate an
unergative verb, the unaccusative resultative pattern an unaccusative one (§4.1.1, §4.1.2,
§4.1.4). Locative inversion and there-insertion rows are data, not diagnostics: chapter 6
finds unergative verbs in locative inversion too. -/
def diagnosticOf (ex : LinguisticExample) : Option Bool :=
  ex.parse? "diagnostic" [("resultativeUnergativePattern", true), ("wayConstruction", true),
    ("cognateObject", true), ("resultativeUnaccusativePattern", false)]

/-- The class of a row's verb, by the book's section number. -/
def classOf (ex : LinguisticExample) : Option LevinClass :=
  (ex.feature? "class").bind LevinClass.ofNumberString?

/-- The construal of a row's verb: its characterization in the class with the row's
agentivity. -/
def construalOf (ex : LinguisticExample) : List Characterization :=
  match classOf ex, ex.parse? "agentive" [("yes", true), ("no", false)] with
  | some c, some a => (characterizations c).filter (·.immediateCause = a)
  | _, _ => []

/-- Every diagnostic row is acceptable exactly when the verb's construal has the status the
diagnostic indicates. -/
theorem diagnostics_agree :
    ∀ ex ∈ Examples.all, ∀ unerg ∈ diagnosticOf ex, ∀ ch ∈ construalOf ex,
      (ex.judgment = .acceptable ↔ if unerg then Unergative ch else Unaccusative ch) := by
  decide

end LevinRappaportHovav1995
