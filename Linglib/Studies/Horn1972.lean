import Linglib.Semantics.Alternatives.Lexical

/-!
# Horn Scales
[horn-1972]

Entailment orderings on the three classic Horn scales — ⟨some, most, all⟩,
⟨or, and⟩, ⟨possible, necessary⟩ — verified in the typed Horn scale algebra
of `Semantics/Alternatives/HornScale.lean` (`Quantifiers.entails`,
`Connectives.entails`, `Modals.entails`, `strongerAlternatives`).
-/

namespace Horn1972

open Alternatives

-- ════════════════════════════════════════════════════
-- § 1. Quantifier Scale: some/all
-- ════════════════════════════════════════════════════

/-- "all" entails "some" in the typed algebra. -/
theorem all_entails_some :
    Quantifiers.entails .all .some_ = true := by native_decide

/-- "most" entails "some" in the typed algebra. -/
theorem most_entails_some :
    Quantifiers.entails .most .some_ = true := by native_decide

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

/-- "possible" has stronger alternatives [necessary] in the typed scale. -/
theorem possible_stronger_alts :
    strongerAlternatives Modals.modalScale .possible = [.necessary] := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. Cross-Scale Properties
-- ════════════════════════════════════════════════════

/-- Entailment is reflexive on all three scales. -/
theorem entailment_reflexive :
    Quantifiers.entails .some_ .some_ = true ∧
    Connectives.entails .or_ .or_ = true ∧
    Modals.entails .possible .possible = true := by native_decide

end Horn1972
