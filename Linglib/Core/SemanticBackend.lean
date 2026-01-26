/-
# Linglib.Core.SemanticBackend

**DEPRECATED**: This module is replaced by `Core/RSA.lean`.

The semantic interface is now unified under `RSAScenario Score`.

- For Boolean semantics: use `RSAScenario.ofBool`
- For graded semantics: use `RSAScenario Score` directly with custom φ

See `Core/RSA.lean` for the new interface.
-/

import Linglib.Core.RSA

-- Re-export new types for backward compatibility during migration
-- Users should migrate to RSAScenario directly

namespace SemanticBackend

/-- Deprecated: use RSAScenario.ofBool instead -/
abbrev LiteralBackend (U W : Type) [BEq U] [BEq W] := RSAScenario U W

/-- Deprecated: use RSAScenario directly -/
abbrev GradedBackend (U W : Type) [BEq U] [BEq W] := RSAScenario U W

end SemanticBackend
