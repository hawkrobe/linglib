import Linglib.Discourse.Commitment.Table

/-!
# Farkas & Bruce 2010
@cite{farkas-bruce-2010}

The F&B table-model *dynamics* — `assert` / `polarQuestion` / `acceptTop`
and the plain `dcS` / `dcL` commitment views — live in the substrate
`Discourse/Commitment/Table.lean`, which is itself the @cite{farkas-bruce-2010}
table model. This study file records the paper's load-bearing claim about the
assertion/acceptance split.
-/

namespace FarkasBruce2010

open Discourse.Commitment.Table

variable {W : Type*}

/-- F&B's assertion does **not** narrow the common ground, in contrast to
    @cite{stalnaker-1978} where assertion is a direct common-ground update.
    The pre-assertion `cg` is preserved exactly; acceptance is a separate move
    (`acceptTop`). -/
theorem assert_preserves_cg (ds : State W) (p : W → Prop) :
    (assert ds p).cg = ds.cg :=
  assert_cg ds p

end FarkasBruce2010
