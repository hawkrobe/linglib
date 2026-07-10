import Linglib.Syntax.Agreement.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Covariance profiles — the descriptive fact layer of agreement
[corbett-1998] [corbett-2006] [norris-2019]

The pretheoretic agreement datum is *systematic covariance*: a target's form
varies with properties of another element ([corbett-1998] §1). Reference
grammars record, per target category, the feature dimensions in which forms
covary; [norris-2019]'s 174-language concord survey ranges over exactly the
dimensions below (number concord most common, case concord rare and almost
never alone).

Which covariances count as AGREEMENT is the contested analytical layer, kept
out of this file: [corbett-1998] §2.4 excludes case and definiteness by the
asymmetry criterion (`Studies/Corbett1998.lean`), while
[alexeyenko-zeijlstra-2025] carry κ through the nominal projection alongside
φ (`Studies/AlexeyenkoZeijlstra2025.lean`). Both analyses consume these
facts; neither is baked into them.

## Main declarations

- `Agreement.Dimension`: a feature dimension in which forms may covary
- `Agreement.CovarianceProfile`: one language's per-target covariant
  dimensions
-/

namespace Agreement

/-- A feature dimension in which a target's form may covary with another
    element: [corbett-1998] §2's indisputable three plus §2.4's contested
    pair ([corbett-2006] "less clear" features), the space [norris-2019]'s
    concord survey ranges over. Whether a given dimension's covariance is
    agreement, government, or feature percolation is an analysis, not a fact
    of this type. -/
inductive Dimension where
  | person | number | gender | case | definiteness
  deriving DecidableEq, Repr, Fintype

/-- A language's covariance profile: for each target category, the dimensions
    in which that target's form covaries. `∅` = invariant (bare) forms.
    Conditioned splits (e.g. Russian verbs: person/number in nonpast,
    gender/number in past) are unioned, not modeled. -/
abbrev CovarianceProfile := AgreementTarget → Finset Dimension

end Agreement
