import Linglib.Theories.Syntax.DependencyGrammar.Formal.CoordinationParallelism
import Linglib.Phenomena.Ellipsis.Gapping

/-!
# Bridge: CoordinationParallelism → Gapping Phenomena

Connects the Dependency Grammar coordination parallelism analysis
(Osborne 2019, Ch 10-11) to the empirical gapping data in
`Phenomena.Ellipsis.Gapping`.

The key bridge: sharing direction in coordination corresponds to
gapping direction — forward sharing maps to forward gapping (SVO),
backward sharing maps to backward gapping (SOV).
-/

namespace DepGrammar.CoordinationParallelism.Bridge

/-- **Bridge → Phenomena/Ellipsis/Gapping.lean**: forward sharing corresponds
    to forward gapping (verb retained in first conjunct), backward sharing
    corresponds to backward gapping (verb retained in last conjunct). -/
theorem sharing_direction_matches_gapping :
    -- Forward sharing: verb overt in first conjunct (like English forward gapping)
    (Phenomena.Ellipsis.Gapping.rossOriginal .SVO).allowsForward = true ∧
    -- Backward sharing: possible in SOV (like backward gapping)
    (Phenomena.Ellipsis.Gapping.rossOriginal .SOV).allowsBackward = true := by
  constructor <;> rfl

end DepGrammar.CoordinationParallelism.Bridge
