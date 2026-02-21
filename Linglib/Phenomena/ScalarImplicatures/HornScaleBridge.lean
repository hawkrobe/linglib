import Linglib.Phenomena.ScalarImplicatures.Basic
import Linglib.Core.HornScale

/-!
# Horn Scale Bridge

Connects the string-based `HornScaleDatumPair` records in
`Phenomena/ScalarImplicatures/Basic.lean` to the typed Horn scale algebra
in `Core/HornScale.lean` (`Quantifiers.entails`, `Connectives.entails`,
`Modals.entails`, `strongerAlternatives`).

## Bridge Structure

For each string-level scale datum (someAllDatum, orAndDatum,
possibleNecessaryDatum), we prove:

1. **Entailment agreement**: the typed `entails` function matches the
   string-level stronger/weaker ordering.

2. **Alternative agreement**: `strongerAlternatives` on the typed scale
   produces the expected set.

3. **Scale membership**: the datum's `strongerTerm` is indeed stronger
   in the typed scale.

## References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
-/

namespace Phenomena.ScalarImplicatures.HornScaleBridge

open Core.Scale
open Phenomena.ScalarImplicatures

-- ════════════════════════════════════════════════════
-- § 1. Quantifier Scale: some/all
-- ════════════════════════════════════════════════════

/-- "all" entails "some" in the typed algebra. -/
theorem all_entails_some :
    Quantifiers.entails .all .some_ = true := by native_decide

/-- "most" entails "some" in the typed algebra. -/
theorem most_entails_some :
    Quantifiers.entails .most .some_ = true := by native_decide

/-- someAllDatum's strongerTerm is "all", and all entails some. -/
theorem someAll_ordering_match :
    someAllDatum.strongerTerm = "all" ∧
    Quantifiers.entails .all .some_ = true :=
  ⟨rfl, by native_decide⟩

/-- "some" has stronger alternatives [most, all] in the typed scale. -/
theorem some_stronger_alts :
    strongerAlternatives Quantifiers.quantScale .some_ = [.most, .all] := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 2. Connective Scale: or/and
-- ════════════════════════════════════════════════════

/-- "and" entails "or" in the typed algebra. -/
theorem and_entails_or :
    Connectives.entails .and_ .or_ = true := by native_decide

/-- orAndDatum's strongerTerm is "and", and and entails or. -/
theorem orAnd_ordering_match :
    orAndDatum.strongerTerm = "and" ∧
    Connectives.entails .and_ .or_ = true :=
  ⟨rfl, by native_decide⟩

/-- "or" has stronger alternatives [and] in the typed scale. -/
theorem or_stronger_alts :
    strongerAlternatives Connectives.connScale .or_ = [.and_] := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 3. Modal Scale: possible/necessary
-- ════════════════════════════════════════════════════

/-- "necessary" entails "possible" in the typed algebra. -/
theorem necessary_entails_possible :
    Modals.entails .necessary .possible = true := by native_decide

/-- possibleNecessaryDatum's strongerTerm is "necessary", and
    necessary entails possible. -/
theorem possibleNecessary_ordering_match :
    possibleNecessaryDatum.strongerTerm = "necessary" ∧
    Modals.entails .necessary .possible = true :=
  ⟨rfl, by native_decide⟩

/-- "possible" has stronger alternatives [necessary] in the typed scale. -/
theorem possible_stronger_alts :
    strongerAlternatives Modals.modalScale .possible = [.necessary] := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. Cross-Scale Agreement
-- ════════════════════════════════════════════════════

/-- All three string-level datum pairs agree with the typed algebra:
    each datum's strongerTerm is the stronger element in its typed scale. -/
theorem all_scales_agree :
    (someAllDatum.strongerTerm = "all" ∧
     Quantifiers.entails .all .some_ = true) ∧
    (orAndDatum.strongerTerm = "and" ∧
     Connectives.entails .and_ .or_ = true) ∧
    (possibleNecessaryDatum.strongerTerm = "necessary" ∧
     Modals.entails .necessary .possible = true) :=
  ⟨⟨rfl, by native_decide⟩, ⟨rfl, by native_decide⟩, ⟨rfl, by native_decide⟩⟩

/-- Entailment is reflexive on all three scales. -/
theorem entailment_reflexive :
    Quantifiers.entails .some_ .some_ = true ∧
    Connectives.entails .or_ .or_ = true ∧
    Modals.entails .possible .possible = true := by native_decide

end Phenomena.ScalarImplicatures.HornScaleBridge
