import Linglib.Semantics.Mood.Defs

/-!
# Searlean Speech Acts: F(p) and S(r)

[searle-1969]'s speech-act theory as elaborated in [searle-1979] and
[searle-1983]: an illocutionary act `F(p)` performed sincerely expresses the
corresponding Intentional state `S(r)` — the sincerity-condition law — and
conditions of satisfaction transfer between them. Also the preparatory
conditions for directives, in the inventory of [francik-clark-1985].

## Main declarations

* `DirectionOfFit` — how responsibility for matching state and world is distributed.
* `SearleClass` — [searle-1979]'s five illocutionary classes.
* `PsychMode` — the psychological modes (the `S` in `S(r)`).
* `Illocutionary.searleClass`, `Illocutionary.sincerityCondition` — the
  per-mood illocutionary class and the `F → S` bridge.
* `CausalSelfRef`, `PsychMode.causalSelfRef` — whether a mode must figure in the
  causal chain producing its own conditions of satisfaction.
* `PreparatoryCondition` — felicity preconditions for directives, ordered by the
  `subsumes` specificity relation.
* `Illocutionary.sincerityCondition_directionOfFit` — the sincerity
  condition's direction of fit matches the speech act's.
* `PsychMode.causalSelfRef_not_determined_by_directionOfFit` — causal
  self-referentiality is not a function of direction of fit.

## Implementation notes

`PsychMode.expressive` collapses [searle-1969]'s heterogeneous expressive
sincerity states (gratitude, pleasure, regret, ...) into a single mode; its null
direction of fit is [searle-1979]'s claim about the expressive class.
Commitment-based accounts (`CommitmentForce.doxastic` "act-as-if-believe", per
[condoravdi-lauer-2012] and [lauer-2013]; Brandom's commitment-without-entitlement)
deliberately weaken `Illocutionary.sincerityCondition .declarative = .belief`
from sincere belief to public commitment.

## References

* [searle-1969], [searle-1979], [searle-1983], [francik-clark-1985]
-/

open Mood (Illocutionary)

/-! ### Direction of fit -/

/-- Direction of fit: how responsibility for matching the state and the world is
distributed ([searle-1983]). -/
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

/-! ### Illocutionary taxonomy — `F(p)` -/

/-- [searle-1979]'s five basic categories of illocutionary acts; exhaustive and
mutually exclusive. -/
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
  | .directive   => .worldToMind
  | .commissive  => .worldToMind
  | .declaration => .double
  | .expressive  => .null

/-! ### Psychological mode — `S(r)` -/

/-- Psychological modes: the "S" in [searle-1983]'s `S(r)`. -/
inductive PsychMode where
  /-- `Bel(p)`: satisfied iff `p` obtains. -/
  | belief
  /-- `Des(p)`: satisfied iff `p` comes about. -/
  | desire
  /-- `Int(p)`: satisfied iff `p` is brought about by carrying out the intention. -/
  | intention
  /-- `Per(p)`: satisfied iff the object causes this experience. -/
  | perception
  /-- Stand-in for [searle-1969]'s heterogeneous expressive states (gratitude,
  pleasure, regret, ...); truth presupposed, no fit responsibility ([searle-1979]). -/
  | expressive
  deriving DecidableEq, Repr, Inhabited

/-- Direction of fit for each psychological mode. -/
def PsychMode.directionOfFit : PsychMode → DirectionOfFit
  | .belief     => .mindToWorld
  | .desire     => .worldToMind
  | .intention  => .worldToMind
  | .perception => .mindToWorld
  | .expressive => .null

/-! ### Mood bridges — class and sincerity condition -/

namespace Mood.Illocutionary

/-- The [searle-1979] illocutionary class of each mood. -/
def searleClass : Illocutionary → SearleClass
  | .declarative   => .assertive
  | .interrogative => .directive
  | .imperative    => .directive
  | .promissive    => .commissive
  | .exclamative   => .expressive

/-- Direction of fit for an illocutionary mood, derived via Searle class. -/
def directionOfFit (m : Illocutionary) : DirectionOfFit :=
  m.searleClass.directionOfFit

/-- Sincerity condition ([searle-1969]): performing a speech act with mood `F`
expresses the corresponding Intentional state `S`. -/
def sincerityCondition : Illocutionary → PsychMode
  | .declarative   => .belief      -- asserting `p` expresses `Bel(p)`
  | .interrogative => .desire      -- asking expresses `Des(addressee answers)`
  | .imperative    => .desire      -- ordering expresses `Des(hearer does A)`
  | .promissive    => .intention   -- promising expresses `Int(speaker does A)`
  | .exclamative   => .expressive  -- exclaiming expresses feeling

/-- The sincerity condition's direction of fit matches the speech act's:
[searle-1983]'s central `F(p)` / `S(r)` parallel. -/
theorem sincerityCondition_directionOfFit (m : Illocutionary) :
    m.sincerityCondition.directionOfFit = m.directionOfFit := by
  cases m <;> rfl

end Mood.Illocutionary

/-! ### Causal self-referentiality -/

/-- Whether an Intentional state must figure in the causal chain producing its
own conditions of satisfaction ([searle-1983]). -/
inductive CausalSelfRef where
  /-- Not self-referential (beliefs, desires). -/
  | none
  /-- The state must cause its conditions of satisfaction (intentions). -/
  | stateToWorld
  /-- The conditions of satisfaction must cause the state (perceptions). -/
  | worldToState
  deriving DecidableEq, Repr, Inhabited

/-- Causal self-referentiality for each psychological mode. Perception's direction
of *causation* (world-to-state) runs opposite its direction of *fit* (mind-to-world):
the two axes are independent. -/
def PsychMode.causalSelfRef : PsychMode → CausalSelfRef
  | .belief     => .none
  | .desire     => .none
  | .intention  => .stateToWorld
  | .perception => .worldToState
  | .expressive => .none

/-- Causal self-referentiality is not determined by direction of fit: belief and
perception share mind-to-world fit but differ in self-referentiality. -/
theorem PsychMode.causalSelfRef_not_determined_by_directionOfFit :
    ∃ a b : PsychMode, a.directionOfFit = b.directionOfFit ∧
      a.causalSelfRef ≠ b.causalSelfRef :=
  ⟨.belief, .perception, rfl, nofun⟩

/-! ### Preparatory conditions -/

/-- Preparatory conditions for directive speech acts. [searle-1969] introduces
the notion; the ability/knowledge/memory/perception/permission/willingness
inventory and the specificity subsumption used below are consolidated in the
analysis of [francik-clark-1985] on indirect requests.
-- UNVERIFIED: the precise subsumption ordering attribution. -/
inductive PreparatoryCondition where
  /-- The hearer is able to perform the act. -/
  | ability
  /-- The hearer knows the relevant information. -/
  | knowledge
  /-- The hearer remembers the relevant information. -/
  | memory
  /-- The hearer can perceive the relevant object. -/
  | perception
  /-- The relevant permission obtains. -/
  | permission
  /-- The hearer is willing to perform the act. -/
  | willingness
  deriving DecidableEq, Repr, Inhabited

/-- `c₁.subsumes c₂` iff satisfying `c₂` entails satisfying `c₁`. -/
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
      PreparatoryCondition.ability.subsumes .permission :=
  ⟨trivial, trivial, trivial, trivial⟩

/-- Willingness is independent of ability: neither subsumes the other. -/
theorem PreparatoryCondition.willingness_independent :
    ¬ PreparatoryCondition.ability.subsumes .willingness ∧
      ¬ PreparatoryCondition.willingness.subsumes .ability :=
  ⟨id, id⟩
