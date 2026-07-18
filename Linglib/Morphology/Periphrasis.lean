import Linglib.Morphology.RelevanceHierarchy

/-!
# Inflectional distribution in periphrasis
[anderson-2006] [bybee-1985]

The split of inflectional categories between the two elements of a
periphrastic construction.
-/

namespace Morphology

/-- Distribution of inflectional categories between two elements of a
    periphrastic construction (e.g., auxiliary and lexical verb in an AVC).
    [anderson-2006] [bybee-1985]

    In an aux-headed AVC, `onLex` is minimal (stem only or empty).
    In a lex-headed AVC, `onAux` is empty.
    In a split AVC, `onAux` and `onLex` host different category types.
    In a doubled AVC, `onAux` and `onLex` overlap. -/
structure InflDistribution where
  onAux : List MorphCategory
  onLex : List MorphCategory
  deriving Repr, DecidableEq

end Morphology
