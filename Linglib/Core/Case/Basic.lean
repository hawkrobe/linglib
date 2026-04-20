import Mathlib.Data.Finset.Card
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Lexical.UD

/-!
# Case — Basic Definitions
@cite{de-marneffe-zeman-2021} @cite{blake-1994} @cite{stassen-1985}

The `Core.Case` type itself (a definitional alias for `UD.Case`), the
lowercase constructor abbrevs that mirror the UD PascalCase ones, and the
small enums for alignment family and case assignment.

Both naming conventions are valid: `.Nom`/`.Acc` (UD PascalCase) and
`.nom`/`.acc` (theoretical lowercase) refer to the same constructors,
via `@[match_pattern]` abbrevs in `Core/Lexical/UD.lean` and here.
-/

namespace Core

/-- The two major morphosyntactic alignment families. -/
inductive AlignmentFamily where
  | accusative
  | ergative
  deriving DecidableEq, Repr

/-- Cross-linguistic case inventory. **Definitional alias for `UD.Case`** —
    the Universal Dependencies treebank tagset (28 constructors). All
    theoretical machinery (Blake hierarchy, Anderson features, Caha
    containment, Heine grammaticalization) operates over this same type,
    ensuring there is a single source of truth shared between UD-annotated
    lexical data and theoretical analyses. -/
abbrev Case := UD.Case

-- Fintype Case follows from Fintype UD.Case (derived in Core/Lexical/UD.lean).
deriving instance Fintype for Case

/-! Lowercase `match_pattern` constructor aliases (`.nom`, `.acc`, …) live
    in the canonical `UD.Case` namespace (`Core/Lexical/UD.lean`). Since
    `Core.Case = UD.Case`, dot-notation `(.nom : Core.Case)` resolves
    through that single source of truth — no separate `Core.Case.*` aliases
    are needed. -/

/-- The 28 UD case constructors are exhaustive. -/
theorem Case.card_univ : (Finset.univ : Finset Case).card = 28 := by decide

/-- How case is assigned to an NP in a given construction
    (@cite{stassen-1985}, §2.2.1). -/
inductive CaseAssignment where
  | derived
  | fixed
  deriving DecidableEq, Repr

/-- For fixed-case NPs, what syntactic role the NP occupies. -/
inductive FixedCaseEncoding where
  | directObject
  | adverbial
  deriving DecidableEq, Repr

end Core
