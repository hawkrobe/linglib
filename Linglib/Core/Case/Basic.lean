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

/-! Lowercase abbrevs in the `Core.Case` namespace, mirroring the UD ones.
    Lets `Core.Case.nom` (qualified access) resolve, in addition to the
    `UD.Case.nom`-namespace abbrevs already exposed via the abbrev type. -/
namespace Case
@[match_pattern] abbrev nom    : Case := UD.Case.Nom
@[match_pattern] abbrev acc    : Case := UD.Case.Acc
@[match_pattern] abbrev erg    : Case := UD.Case.Erg
@[match_pattern] abbrev abs    : Case := UD.Case.Abs
@[match_pattern] abbrev gen    : Case := UD.Case.Gen
@[match_pattern] abbrev dat    : Case := UD.Case.Dat
@[match_pattern] abbrev loc    : Case := UD.Case.Loc
@[match_pattern] abbrev abl    : Case := UD.Case.Abl
@[match_pattern] abbrev all    : Case := UD.Case.All
@[match_pattern] abbrev inst   : Case := UD.Case.Ins
@[match_pattern] abbrev com    : Case := UD.Case.Com
@[match_pattern] abbrev voc    : Case := UD.Case.Voc
@[match_pattern] abbrev part   : Case := UD.Case.Par
@[match_pattern] abbrev perl   : Case := UD.Case.Per
@[match_pattern] abbrev ben    : Case := UD.Case.Ben
@[match_pattern] abbrev caus   : Case := UD.Case.Cau
@[match_pattern] abbrev ess    : Case := UD.Case.Ess
@[match_pattern] abbrev transl : Case := UD.Case.Tra
@[match_pattern] abbrev abess  : Case := UD.Case.Abe
end Case

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
