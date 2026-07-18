import Linglib.Morphology.RelevanceHierarchy

/-!
# Inflectional distribution in auxiliary verb constructions
[anderson-2006] [spencer-popova-2015]

The split of inflectional categories between the two elements of an
auxiliary verb construction. Possessing such a distribution is neutral on
periphrasis-hood: serial-verb and light-verb constructions distribute
inflection too, and periphrasis proper requires paradigm-cell integration
([spencer-popova-2015] pp. 200, 204). The distribution data is the raw
material for the distributed-exponence criterion the periphrasis
literature states over it.
-/

namespace Morphology

/-- Distribution of inflectional categories between the two elements of an
    auxiliary verb construction. The category vocabulary is
    `MorphCategory` ([bybee-1985]'s relevance hierarchy); the pattern
    taxonomy is [anderson-2006]'s AVC classification:

    - aux-headed: `onLex` minimal (stem only or empty).
    - lex-headed: `onAux` empty or minimal (e.g. tonal subject person,
      Doyayo — [anderson-2006] p. 120).
    - split: `onAux` and `onLex` host different category types.
    - doubled: `onAux` and `onLex` coincide.
    - split/doubled: some category doubled on both, others split. -/
structure InflDistribution where
  onAux : List MorphCategory
  onLex : List MorphCategory
  deriving Repr, DecidableEq

end Morphology
