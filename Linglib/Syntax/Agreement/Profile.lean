import Linglib.Syntax.Agreement.Bundle
import Linglib.Syntax.Agreement.Target
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Agreement profiles — the descriptive fact layer
[corbett-1998] [corbett-2006] [norris-2019]

Agreement in the wide, descriptive sense of reference grammars ("the
adjective agrees in number, gender, and case"): systematic covariance of a
target's form with properties of another element ([corbett-1998] §1's
definition). A grammar records, per target category, the feature dimensions
in which forms covary; [norris-2019]'s 174-language concord survey ranges
over exactly the dimensions below (number concord most common, case concord
rare and almost never alone).

Which covariances count as agreement in the NARROW, theoretical sense is the
contested analytical layer, kept out of this file: [corbett-1998] §2.4
excludes case and definiteness by the asymmetry criterion
(`Studies/Corbett1998.lean`), while [alexeyenko-zeijlstra-2025] carry κ
through the nominal projection alongside φ
(`Studies/AlexeyenkoZeijlstra2025.lean`). Both analyses consume these facts;
neither is baked into them.

## Main declarations

- `Agreement.Profile`: one language's per-target agreement dimensions, over the
  `Agreement.Dimension` of `Syntax/Agreement/Bundle.lean`
-/

namespace Agreement

/-- A language's agreement profile (wide sense): for each target category,
    the dimensions in which that target's form covaries. `∅` = invariant
    (bare) forms. Conditioned splits (e.g. Russian verbs: person/number in
    nonpast, gender/number in past) are unioned, not modeled. -/
abbrev Profile := Target → Finset Dimension

end Agreement
