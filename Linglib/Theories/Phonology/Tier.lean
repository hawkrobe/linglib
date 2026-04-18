import Linglib.Core.StringHom
import Linglib.Theories.Phonology.Autosegmental.GrammaticalTone

/-!
# Phonological Tiers

@cite{goldsmith-1976}

Phonology-specific tier constructors built on `Core.Tier`. The generic
operations (`apply`, `id`, `byClass`, `total`, monoid-hom laws) live in
`Core/StringHom.lean`; this module only adds the canonical phonological
projections that downstream phonology files need.
-/

namespace Phonology.Tier

/-- The canonical tonal tier (@cite{goldsmith-1976}): every TBU projects
    to its tone. Length-preserving (no erasure) — built via `Tier.total`. -/
def tonal {S : Type} :
    Core.Tier (Phonology.Autosegmental.GrammaticalTone.TBU S)
              Phonology.Autosegmental.RegisterTier.ToneFeature :=
  Core.Tier.total Phonology.Autosegmental.GrammaticalTone.TBU.tone

/-- The tonal-tier projection equals the historical `List.map TBU.tone`
    formulation. Used to ground `BasemapCorrespondence.tonalTier`. -/
theorem apply_tonal {S : Type}
    (tbus : List (Phonology.Autosegmental.GrammaticalTone.TBU S)) :
    Core.Tier.apply tonal tbus = tbus.map Phonology.Autosegmental.GrammaticalTone.TBU.tone :=
  Core.Tier.apply_total _ _

end Phonology.Tier
