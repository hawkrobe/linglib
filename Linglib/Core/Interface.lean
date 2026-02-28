import Linglib.Core.Interfaces.SemanticStructure
import Linglib.Core.Interfaces.CombinationSchemata
import Linglib.Core.Interfaces.BindingSemantics
import Linglib.Core.Interfaces.ScopeTheory
import Linglib.Core.Interfaces.ImplicatureTheory
import Linglib.Core.Interfaces.Felicity
import Linglib.Core.Interfaces.CoreferenceTheory
import Linglib.Core.Interfaces.ExtractionMorphology
import Linglib.Core.Interfaces.VoiceSystem
import Linglib.Core.Interfaces.AssertionTheory

/-!
# Theory Comparison Interfaces

Re-exports all interface modules. Import this file to get all interfaces,
or import individual files from `Core/Interfaces/` for finer-grained control.

- `SemanticStructure`: Syntax–semantics composition (HasTerminals, SemanticStructure)
- `CombinationSchemata`: Müller's three universal schemata (CombinationKind)
- `BindingSemantics`: H&K binding (BindingConfig, HasBindingConfig)
- `ScopeTheory`: Scope readings (AvailableScopes, HasBinaryScope)
- `ImplicatureTheory`: Scalar implicature predictions (ImplicatureTheory)
- `FelicityCondition`: Felicity/oddness predictions (FelicityCondition)
- `CoreferenceTheory`: Coreference predictions (CoreferenceTheory)
- `ExtractionMorphology`: Cross-linguistic extraction marking (ExtractionProfile)
- `VoiceSystem`: Voice system typology (VoiceSystemProfile)
-/
