import Linglib.Theories.Syntax.DependencyGrammar.Formal.MemorySurprisal.MorphemeOrder
import Linglib.Phenomena.Causatives.Typology

/-!
# Bridge: Memory-Surprisal MorphemeOrder → Causatives Typology

Connects the Japanese causative -(s)ase morpheme order analysis from
`MemorySurprisal.MorphemeOrder` to Song (1996)'s causative typology
in `Phenomena.Causatives.Typology`.

The key bridge: Japanese -(s)ase occupies the valence slot (innermost
functional suffix), consistent with its classification as a COMPACT
morphological causative.
-/

namespace DepGrammar.MemorySurprisal.MorphemeOrder.Bridge

/-! ### Bridge: Japanese -(s)ase = Song's COMPACT morphological causative

Japanese -(s)ase is classified as a morphological COMPACT causative in
Song (1996). The `ik_ase` entry in `Fragments/Japanese/Predicates` confirms
this: `causativeBuilder = some .make`. -/

/-- The Japanese -(s)ase causative entry is causative (derived from causativeBuilder). -/
theorem ik_ase_is_causative :
    Fragments.Japanese.Predicates.ik_ase.causativeBuilder.isSome = true := rfl

/-- Japanese -(s)ase uses the .make causative builder (direct causation). -/
theorem ik_ase_is_make :
    Fragments.Japanese.Predicates.ik_ase.causativeBuilder = some .make := rfl

/-- Song (1996) classifies Japanese -(s)ase as COMPACT.

The COMPACT type subsumes morphological causatives like Japanese -(s)ase,
Turkish -dür, and also lexical causatives like English *kill*.
This is consistent with the slot being valence (innermost). -/
theorem japanese_causative_is_compact :
    Phenomena.Causatives.Typology.japaneseAse.constructionType = .compact := by native_decide

end DepGrammar.MemorySurprisal.MorphemeOrder.Bridge
