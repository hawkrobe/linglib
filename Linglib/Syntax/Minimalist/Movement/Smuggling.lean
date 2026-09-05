import Linglib.Syntax.Minimalist.Movement.Reconstruction

/-!
# Smuggling

A constituent YP containing XP moves past W, which blocked XP: after the move YP c-commands W and
W no longer c-commands XP, so a probe above W that W would have intervened for now reaches XP.
On a derivation this is the step predicate `SyntacticObject.Derivation.IsSmugglingStep`, read
off the replayed stages through `Derivation.CCommandsAt`: the mover of the step contains `xp`,
`w` c-commands `xp` before the step, and after it the mover c-commands `w` and `w` no longer
c-commands `xp`. The blocking is rendered as `w`'s c-command of `xp`; the probe it matters for
is the consumer's to supply, as the passive study does when Infl finds the object closest once
PartP has carried it past the external argument in Spec-vP. Which heads let a constituent out
of their complement is a question each account answers for itself, and none is fixed here.

## References

* [C. Collins, *A Smuggling Approach to the Passive in English* (2005)][collins-2005]
-/

namespace Minimalist.SyntacticObject.Derivation

variable {d : Derivation} {steps : List Step} {i : Nat} {xp w : SyntacticObject}

/-- Step `i` of `d` smuggles `xp` past `w`: its mover contains `xp`, which `w` c-commands before
the step, and after it the mover c-commands `w` and `w` no longer c-commands `xp`. -/
def IsSmugglingStep (d : Derivation) (i : Nat) (xp w : SyntacticObject) : Prop :=
  ∃ m ∈ d.steps[i]? >>= Step.mover?,
    contains m xp ∧ d.CCommandsAt i w xp ∧ d.CCommandsAt (i + 1) m w ∧
      ¬ d.CCommandsAt (i + 1) w xp

instance (d : Derivation) (i : Nat) (xp w : SyntacticObject) :
    Decidable (d.IsSmugglingStep i xp w) := by
  unfold IsSmugglingStep; infer_instance

/-- A smuggling step of a derivation is one of every extension. -/
theorem IsSmugglingStep.append (h : d.IsSmugglingStep i xp w) :
    (d.append steps).IsSmugglingStep i xp w := by
  obtain ⟨m, hm, hc, h₁, h₂, h₃⟩ := h
  have hi := lt_length_of_mem_mover? hm
  refine ⟨m, by rwa [Derivation.append, List.getElem?_append_left hi], hc,
    (cCommandsAt_append_of_le hi.le).2 h₁, (cCommandsAt_append_of_le hi).2 h₂,
    λ h => h₃ ((cCommandsAt_append_of_le hi).1 h)⟩

end Minimalist.SyntacticObject.Derivation
