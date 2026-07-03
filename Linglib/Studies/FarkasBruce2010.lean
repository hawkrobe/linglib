import Linglib.Discourse.Commitment.Table

/-!
# Farkas & Bruce 2010
[farkas-bruce-2010]

The F&B table-model *dynamics* — `assert` / `polarQuestion` / `acceptTop`
and the plain `dcS` / `dcL` commitment views — live in the substrate
`Discourse/Commitment/Table.lean`, which is itself the [farkas-bruce-2010]
table model. This study file records the paper's load-bearing claim about the
assertion/acceptance split.
-/

namespace FarkasBruce2010

open Discourse.Commitment.Table

variable {W : Type*}

/-- F&B's assertion does **not** narrow the common ground, in contrast to
    [stalnaker-1978] where assertion is a direct common-ground update.
    The pre-assertion `cg` is preserved exactly; acceptance is a separate move
    (`acceptTop`). -/
theorem assert_preserves_cg (ds : State W) (p : W → Prop) :
    (assert ds p).cg = ds.cg :=
  assert_cg ds p

/-- F&B's `assert` violates the Stalnakerian narrowing law: a world can
    survive the assertion of `p` without satisfying `p`, because assertion
    only proposes (`dcS` + table) and the context set moves at acceptance.
    This is the formal witness for the non-instance advertised at
    `CommonGround.HasAssertion` — `State W` does not instantiate it via
    F&B's own `assert`. -/
theorem assert_not_narrowing :
    ∃ (ds : State Bool) (p : Bool → Prop) (w : Bool),
      w ∈ (assert ds p).contextSet ∧ ¬ p w :=
  ⟨.empty, (· = true), false, trivial, Bool.false_ne_true⟩

end FarkasBruce2010
