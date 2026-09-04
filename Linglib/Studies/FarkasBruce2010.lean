import Linglib.Discourse.Commitment.Table

/-!
# Farkas and Bruce 2010: On reacting to assertions and polar questions

The Table model of [farkas-bruce-2010] is `Commitment.Table`; this file records the claim the
model is built to make: an assertion proposes rather than updates. It commits its author and
places its sentence on the Table, projecting confirmation, but leaves the common ground as it
was — against [stalnaker-1978], where assertion narrows the context set directly — so that
confirmation and denial can react to it, and a denial leaves the conversation in crisis.

## Main results

* `assert_cg` — assertion does not change the common ground.
* `assert_not_narrowing` — the Stalnakerian narrowing law fails: `Commitment.Table` is not a
  `HasAssertion` instance under its own `assert`.
* `inCrisis_assert_compl` — a denied assertion is a crisis.

## References

* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
* [R. Stalnaker, *Assertion* (1978)][stalnaker-1978]
-/

namespace FarkasBruce2010

open Commitment

variable {W : Type*} (K : Table DiscourseRole W) (p : Set W)

/-- Assertion proposes: the common ground is exactly as before (9). -/
theorem assert_cg : (K.assert .speaker p).cg = K.cg := rfl

/-- A world can survive the assertion of `p` without satisfying `p`, since only the projected set
moves; `Commitment.Table` is not a `HasAssertion` instance under its own `assert`. -/
theorem assert_not_narrowing :
    ∃ (K : Table DiscourseRole Bool) (p : Set Bool) (w : Bool),
      w ∈ (K.assert .speaker p).contextSet ∧ w ∉ p :=
  ⟨.empty, {true}, false, by simp [Table.contextSet, Table.assert, Table.push, Table.commit],
    Bool.false_ne_true⟩

/-- The addressee's denial leaves the conversation in crisis (21). -/
theorem inCrisis_assert_compl : ((K.assert .speaker p).assert .addressee pᶜ).InCrisis :=
  K.inCrisis_assert_compl .speaker p .addressee

end FarkasBruce2010
