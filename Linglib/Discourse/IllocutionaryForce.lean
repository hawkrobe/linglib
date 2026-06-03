import Linglib.Semantics.Context.Tower
import Linglib.Discourse.Roles
import Linglib.Semantics.Mood.IllocutionaryMood
/-!
# Illocutionary Force: F in F(p)
[searle-1969] [searle-1979] [searle-1983]
[francik-clark-1985]
The pragmatic-act side of the Searlean F(p) parallel: `DirectionOfFit`,
`SearleClass` taxonomy, and `PreparatoryCondition`. The S(r) side
(psychological mode, sincerity, Intentional state) lives in
`Discourse/Intentionality.lean`.
-/
namespace Discourse
open Semantics.Context
open Semantics.Mood (IllocutionaryMood moodAuthority)
/-! ### Direction of Fit ([searle-1983]) -/
/-- Direction of fit: how responsibility for matching the state and
    the world is distributed ([searle-1983]). -/
inductive DirectionOfFit where
  /-- State must match reality (beliefs, assertions). -/
  | mindToWorld
  /-- World must change to match the state (desires, orders). -/
  | worldToMind
  /-- Presupposed truth, no fit responsibility (expressives). -/
  | null
  /-- Both directions simultaneously (declarations). -/
  | double
  deriving DecidableEq, Repr, Inhabited
/-! ### Illocutionary Taxonomy ([searle-1979]) -/
/-- [searle-1979]'s five basic categories of illocutionary acts;
    exhaustive and mutually exclusive. -/
inductive SearleClass where
  /-- Assertions, statements, descriptions. -/
  | assertive
  /-- Orders, commands, requests. -/
  | directive
  /-- Promises, vows, pledges. -/
  | commissive
  /-- Verdicts, appointments (bring about by declaring). -/
  | declaration
  /-- Apologies, congratulations (express feelings about presupposed states). -/
  | expressive
  deriving DecidableEq, Repr, Inhabited
/-- Direction of fit for each illocutionary class. -/
def SearleClass.directionOfFit : SearleClass → DirectionOfFit
  | .assertive   => .mindToWorld
  | .directive    => .worldToMind
  | .commissive   => .worldToMind
  | .declaration  => .double
  | .expressive   => .null
end Discourse
namespace Semantics.Mood.IllocutionaryMood
open Discourse (SearleClass DirectionOfFit)
/-- Map `IllocutionaryMood` to Searle class. -/
def searleClass : IllocutionaryMood → SearleClass
  | .declarative   => .assertive
  | .interrogative  => .directive
  | .imperative     => .directive
  | .promissive     => .commissive
  | .exclamative    => .expressive
/-- Direction of fit for an illocutionary mood, derived via Searle class. -/
def directionOfFit (m : IllocutionaryMood) : DirectionOfFit :=
  m.searleClass.directionOfFit
end Semantics.Mood.IllocutionaryMood
namespace Discourse
open Semantics.Mood (IllocutionaryMood moodAuthority)
/-! ### Preparatory Conditions ([searle-1969] [francik-clark-1985]) -/
/-- Preparatory conditions for directive speech acts. [searle-1969]
    introduces the notion; the ability/knowledge/memory/perception/permission/
    willingness inventory and the specificity subsumption used below are
    consolidated in the analysis of [francik-clark-1985] on indirect
    requests. -- UNVERIFIED: the precise subsumption ordering attribution. -/
inductive PreparatoryCondition where
  | ability
  | knowledge
  | memory
  | perception
  | permission
  | willingness
  deriving DecidableEq, Repr
/-- `c₁.subsumes c₂` iff satisfying c₂ entails satisfying c₁. -/
def PreparatoryCondition.subsumes : PreparatoryCondition → PreparatoryCondition → Prop
  -- reflexive
  | .ability, .ability | .knowledge, .knowledge | .memory, .memory
  | .perception, .perception | .permission, .permission
  | .willingness, .willingness => True
  -- ability subsumes its subtypes
  | .ability, .knowledge | .ability, .memory
  | .ability, .perception | .ability, .permission => True
  -- knowledge subsumes its subtypes
  | .knowledge, .memory | .knowledge, .perception => True
  | _, _ => False
instance : DecidableRel PreparatoryCondition.subsumes := fun c₁ c₂ => by
  cases c₁ <;> cases c₂ <;> unfold PreparatoryCondition.subsumes <;> infer_instance
theorem PreparatoryCondition.subsumes_refl (c : PreparatoryCondition) :
    c.subsumes c := by cases c <;> trivial
/-- The specificity chain: memory/perception → knowledge → ability. -/
theorem PreparatoryCondition.specificity_chain :
    PreparatoryCondition.ability.subsumes .knowledge ∧
    PreparatoryCondition.knowledge.subsumes .memory ∧
    PreparatoryCondition.knowledge.subsumes .perception ∧
    PreparatoryCondition.ability.subsumes .permission := ⟨trivial, trivial, trivial, trivial⟩
/-- Willingness is independent of ability: neither subsumes the other. -/
theorem PreparatoryCondition.willingness_independent :
    ¬ PreparatoryCondition.ability.subsumes .willingness ∧
    ¬ PreparatoryCondition.willingness.subsumes .ability := ⟨id, id⟩
/-- Directives are the speech act class that has preparatory conditions
    on the hearer's ability and willingness. -/
theorem directive_has_preparatory_conditions :
    SearleClass.directive.directionOfFit = .worldToMind := rfl
/-! ### Verification -/
-- Epistemic authority (theorems about moodAuthority — moved here so that
-- `.declarative`/`.interrogative` are visible from the IllocutionaryMood namespace)
theorem epistemic_authority_declarative :
    moodAuthority .declarative = .speaker := rfl
theorem epistemic_authority_interrogative :
    moodAuthority .interrogative = .addressee := rfl
-- Direction of fit per Searle class
theorem assertive_mind_to_world :
    SearleClass.assertive.directionOfFit = .mindToWorld := rfl
theorem directive_world_to_mind :
    SearleClass.directive.directionOfFit = .worldToMind := rfl
theorem commissive_world_to_mind :
    SearleClass.commissive.directionOfFit = .worldToMind := rfl
theorem declaration_double :
    SearleClass.declaration.directionOfFit = .double := rfl
theorem expressive_null :
    SearleClass.expressive.directionOfFit = .null := rfl
end Discourse
