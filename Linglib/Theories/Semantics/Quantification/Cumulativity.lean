import Linglib.Theories.Semantics.Plurality.Cumulativity
import Linglib.Theories.Semantics.Aspect.Cumulativity
import Linglib.Phenomena.Plurals.Studies.Charlow2021.HigherOrder

/-!
# Cross-framework synthesis: cumulative readings of modified numerals

@cite{charlow-2021} @cite{beck-sauerland-2000} @cite{champollion-2017}
@cite{schein-1993}

## Why this file exists

Three rival accounts of cumulative readings live in three different directories
and (until this file) never spoke to each other:

| Account | Mechanism | Location |
|---|---|---|
| Tower continuations | Higher-order dynamic GQ via `Cont` monad | `Phenomena/Plurals/Studies/Charlow2021/HigherOrder.lean` |
| Beck-Sauerland `**` | Pluralization operator on relations between Finsets | `Theories/Semantics/Plurality/Cumulativity.lean` |
| Champollion `*` | Cumulative-closure on event predicates | `Theories/Semantics/Events/Aspect/Cumulativity.lean` |

Linglib's stated thesis: theoretical incompatibilities should be made visible.
Three accounts of the same phenomenon, formalized side-by-side without bridge
theorems, fails that test. The 4-agent Quantification/ audit (2026-04-28)
flagged this as the directory's loudest silent divergence.

## Status

**Stub.** This file collects the three accounts in one import graph but the
substantive cross-framework theorems are deferred to a follow-up session.
The bridge questions:

- Tower-continuation `cumulativeTower v u boys movies saw' = ?` Beck-Sauerland's
  `Cumulative (fun b m => saw b m) (boys.toFinset) (movies.toFinset)`?
  Both purport to express "every boy saw at least one movie AND every movie
  was seen by at least one boy"; equivalence holds on the obvious shared
  scenario but the type-level packaging differs (DRS-state-threading vs
  Bool-valued Finset relation).
- Beck-Sauerland `**` ↔ Champollion `*`: B&S pluralizes the *relation*; CHP
  pluralizes each *predicate* and propagates via `IsCumThetaVerb`. The
  scenarios where they diverge involve dependent indefinites and incremental
  themes — exactly the cases where Charlow's tower system claims advantage.

## TODO

1. Pick a shared concrete scenario (e.g., 3 boys × 5 movies × `saw`).
2. State `tower_eq_BeckSauerland_on_scenario` and `BS_eq_Champollion_on_scenario`
   as decidable equalities. Each likely needs a `decide`-friendly
   reformulation of the tower output.
3. Identify a scenario where they diverge (dependent indefinite or
   per-event reading) — this is the substantive contribution.

For now the file just guarantees the three accounts compile in the same
import-graph, which is the precondition for stating bridge theorems.
-/

namespace Phenomena.Plurality.Cumulativity.CrossFramework

-- Stub: bridge theorems pending; see TODO in module docstring.
-- TODO: prove `tower_eq_BeckSauerland_on_scenario`
-- TODO: prove `BS_eq_Champollion_on_scenario`
-- TODO: identify divergence scenario

end Phenomena.Plurality.Cumulativity.CrossFramework
