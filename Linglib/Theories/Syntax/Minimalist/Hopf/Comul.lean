import Linglib.Theories.Syntax.Minimalist.Hopf.AdmissibleCut
import Linglib.Theories.Syntax.Minimalist.Hopf.Defs
import Linglib.Core.Algebra.ConnesKreimer.Coproduct

/-!
# Connes-Kreimer Coproducts (Δ^c, Δ^d) — Re-export shim

The `[UPSTREAM]` content of this file (entire) was hoisted to
`Linglib/Core/Algebra/ConnesKreimer/Coproduct.lean` per Stage 0.5
(see `scratch/mcb_stage1_plan.md`). This file remains as a re-export
so existing `import Linglib.Theories.Syntax.Minimalist.Hopf.Comul`
import lines continue to work, and so the `Minimalist.Hopf.X` qualified
names (`forestToHc`, `comulTree`, `comulForest`, `comulAlgHom`,
`counit`, `comulTreeDel`, `comulForestDel`, `comulDelAlgHom`) still
resolve.

If you're importing this file directly, prefer importing
`Linglib.Core.Algebra.ConnesKreimer.Coproduct` going forward.
-/
