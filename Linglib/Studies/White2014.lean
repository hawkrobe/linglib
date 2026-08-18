import Linglib.Studies.Williams2026
import Linglib.Fragments.English.Predicates.Verbal

/-!
# White 2014: The Modalized Complement Analysis of *forget*
[white-2014]

White 2014 maintains a uniformly factive denotation for *forget* by
positing a covert root modal in non-finite complements (the Modalized
Complement Analysis, MCA). This file verifies the MCA's coverage on its
own terms — the finite-CP / plain-infinitive asymmetry it was designed
for — and confirms Fragment-level consistency: the English Fragment's
split of *forget* into `forget` (negative implicative, infinitival) and
`forget_rog` (factive, finite) aligns with the frames the MCA
classifies correctly.

The MCA's structural prediction is formalized as
`Williams2026.MCAPredictsModal` (the reconstruction in the later
paper's §3.1.1, whose study file also prosecutes the gerund
refutation, `Williams2026.mca_overpredicts_gerund` — per the
chronological-dependency rule that comparison lives there, not here).
The pre-existence classifier used in the fragment-consistency section
is the post-2014 project-canonical apparatus
(`Williams2026.SatisfiesPreExistence`); its use here is the sanctioned
canonical-successor deviation.
-/

namespace White2014

open Williams2026
open English.Predicates.Verbal

/-! ### MCA coverage of the canonical contrast -/

/-- Finite CP: the MCA correctly predicts no modal insertion. -/
theorem mca_correct_finiteCP :
    ¬ MCAPredictsModal forget_finiteCP.frame := by decide

/-- Plain infinitive: the MCA correctly predicts modal insertion. -/
theorem mca_correct_infinitival :
    MCAPredictsModal forget_infinitival.frame := by decide

/-! ### Fragment consistency -/

theorem forget_takes_infinitival :
    forget.complementType = .infinitival := by decide

theorem forget_rog_takes_finite :
    forget_rog.complementType = .finiteClause := by decide

theorem forget_rog_is_factive :
    forget_rog.factivePresup = true := by decide

theorem forget_rog_satisfies_preExistence :
    SatisfiesPreExistence forget_rog.complementType := by decide

theorem forget_inf_violates_preExistence :
    ¬ SatisfiesPreExistence forget.complementType := by decide

end White2014
