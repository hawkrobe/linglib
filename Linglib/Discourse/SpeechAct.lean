import Linglib.Semantics.Mood.Defs
import Mathlib.Order.Max

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
* `PreparatoryCondition` — felicity preconditions on a request for information, partially
  ordered by specificity.
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

/-- Preparatory conditions on a request for information, in the inventory of
[francik-clark-1985]: the hearer's ability to supply it, with knowing it, remembering it, having
come across it and being allowed to tell it as ways of being able; the hearer's willingness; and
[searle-1969]'s condition on questions that the speaker does not already have it. -/
inductive PreparatoryCondition where
  /-- The hearer is able to supply the information. -/
  | ability
  /-- The hearer knows the information. -/
  | knowledge
  /-- The hearer remembers the information. -/
  | memory
  /-- The hearer has come across the information. -/
  | perception
  /-- The hearer is allowed to give the information. -/
  | permission
  /-- The hearer is willing to give the information. -/
  | willingness
  /-- The speaker does not already have the information. -/
  | speakerIgnorance
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace PreparatoryCondition

/-- Satisfying the first condition is a way of satisfying the second: [francik-clark-1985]'s
gradient of specificity, on which knowing, remembering, having come across and being allowed to
tell are ways of being able to supply the information, and remembering or having come across it
are ways of knowing it. Willingness and the speaker's own condition stand alone. -/
protected def le : PreparatoryCondition → PreparatoryCondition → Prop
  | .knowledge, .ability | .memory, .ability | .perception, .ability | .permission, .ability
  | .memory, .knowledge | .perception, .knowledge => True
  | c, d => c = d

instance : DecidableRel PreparatoryCondition.le := λ c d => by
  cases c <;> cases d <;> unfold PreparatoryCondition.le <;> infer_instance

instance : LE PreparatoryCondition := ⟨PreparatoryCondition.le⟩

instance : DecidableLE PreparatoryCondition :=
  inferInstanceAs (DecidableRel PreparatoryCondition.le)

instance : PartialOrder PreparatoryCondition where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : NoTopOrder PreparatoryCondition := ⟨by decide⟩

instance : NoBotOrder PreparatoryCondition := ⟨by decide⟩

end PreparatoryCondition
