/-
# Linglib.Core.SemanticBackend

**DEPRECATED**: This module is replaced by `Core/RSA.lean`.

The semantic interface is now unified under `SimpleRSAScenario`.

- For Boolean semantics: use `SimpleRSAScenario.ofBool`
- For graded semantics: use `SimpleRSAScenario` directly with custom φ

See `Core/RSA.lean` for the new interface.
-/

import Linglib.Theories.RSA.Core

-- Re-export new types for backward compatibility during migration
-- Users should migrate to RSAScenario directly

namespace SemanticBackend

/-- Deprecated: use SimpleRSAScenario.ofBool instead -/
abbrev LiteralBackend (U W : Type) [BEq U] [BEq W] := SimpleRSAScenario U W

/-- Deprecated: use RSAScenario directly -/
abbrev GradedBackend (U W : Type) [BEq U] [BEq W] := SimpleRSAScenario U W

end SemanticBackend
