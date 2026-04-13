import Linglib.Phenomena.Morphology.Studies.HahnDegenFutrell2021
import Linglib.Phenomena.Causation.Typology

/-!
# Bridge: Memory-Surprisal MorphemeOrder → Causation Typology
@cite{song-1996}

Connects the Japanese causative -(s)ase morpheme order analysis from
`Phenomena.Morphology.Studies.HahnDegenFutrell2021` to @cite{song-1996}'s causative typology
in `Phenomena.Causation.Typology`.

The key bridge: Japanese -(s)ase occupies the valence slot (innermost
functional suffix), consistent with its classification as a COMPACT
morphological causative.
-/

namespace Phenomena.Causation.Studies.Song1996

/-! ### Bridge: Japanese -(s)ase = Song's COMPACT morphological causative

Japanese -(s)ase is classified as a morphological COMPACT causative in
@cite{song-1996}. The `ik_ase` entry in `Fragments/Japanese/Predicates` confirms
this: `causative = some.make`. -/

/-- The Japanese -(s)ase causative entry is causative (derived from causative). -/
theorem ik_ase_is_causative :
    Fragments.Japanese.Predicates.ik_ase.causative.isSome = true := rfl

/-- Japanese -(s)ase uses the.make causative builder (direct causation). -/
theorem ik_ase_is_make :
    Fragments.Japanese.Predicates.ik_ase.causative = some .make := rfl

/-- @cite{song-1996} classifies Japanese -(s)ase as COMPACT.

The COMPACT type subsumes morphological causatives like Japanese -(s)ase,
Turkish -dür, and also lexical causatives like English *kill*.
This is consistent with the slot being valence (innermost). -/
theorem japanese_causative_is_compact :
    Phenomena.Causation.Typology.japaneseAse.constructionType = .compact := by native_decide

end Phenomena.Causation.Studies.Song1996
