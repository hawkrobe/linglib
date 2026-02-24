import Linglib.Theories.Syntax.DependencyGrammar.Core.Nominal
import Linglib.Phenomena.Anaphora.Coreference

/-!
# Bridge: DG Nominal → Anaphora Coreference

Connects the DG nominal classification (reflexive, pronoun, r-expression) to
empirical coreference minimal pairs from `Phenomena.Anaphora.Coreference`.

Imports both `DepGrammar.Nominal` (which provides `capturesMinimalPair` and
`capturesPhenomenonData`) and the Phenomena coreference data so that
downstream files (e.g., `Coreference.lean`, `CRDC.lean`) can verify their
grammaticality predicates against empirical minimal pairs.

## Bridges

- `DepGrammar.Nominal.capturesPhenomenonData` + `reflexiveCoreferenceData` etc.
-/
