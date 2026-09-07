import Mathlib.Tactic.DeriveFintype

/-!
# The energy source of a force bearer

A participant that exerts force draws the energy from its own source, as living things,
machines and natural agents do, from energy imparted to it or held in its position or motion,
as a projectile or a load-bearing column, or from another participant that uses it, as an
instrument. Cruse's agentive and effective features are the first two and his instrumental
the third; Van Valin and Wilkins's self-energetic effector is either of the first two, and
Rappaport Hovav and Levin's projectile the second.

## Main definitions

* `EnergySource` — internal, imparted, or instrumental.
* `EnergySource.IsSelfEnergetic` — not instrumental: Van Valin and Wilkins's effector and
  Cruse's *do*-relationship among force bearers.

## References

* [D. A. Cruse, *Some thoughts on agentivity* (1973)][cruse-1973]
* [R. D. Van Valin, D. P. Wilkins, *The case for "effector": case roles, agents, and agency
  revisited* (1996)][van-valin-wilkins-1996]
* [M. Rappaport Hovav, B. Levin, *Variable agentivity: polysemy or underspecification?*
  (2024)][rappaport-hovav-levin-2024]
-/

namespace ArgumentStructure

/-- The source of the energy with which a participant exerts force. -/
inductive EnergySource where
  /-- The participant's own energy: living things, self-propelled machines, natural agents
  (Cruse's agentive feature). -/
  | internal
  /-- Energy imparted to the participant or held in its position or motion: a projectile, a
  load-bearing column (Cruse's effective feature). -/
  | imparted
  /-- The energy of a participant that uses it: an instrument or a body part (Cruse's and
  Fillmore's instrumental). -/
  | instrumental
  deriving DecidableEq, Fintype

namespace EnergySource

/-- A self-energetic force bearer, Van Valin and Wilkins's effector: one whose energy is not
supplied by a user, and so one of which *did something* holds. -/
def IsSelfEnergetic (s : EnergySource) : Prop := s ≠ .instrumental

instance : DecidablePred IsSelfEnergetic := λ _ => inferInstanceAs (Decidable (_ ≠ _))

@[simp] theorem isSelfEnergetic_internal : IsSelfEnergetic .internal := by decide

@[simp] theorem isSelfEnergetic_imparted : IsSelfEnergetic .imparted := by decide

@[simp] theorem not_isSelfEnergetic_instrumental : ¬ IsSelfEnergetic .instrumental := by
  decide

end EnergySource

end ArgumentStructure
