import Linglib.Features.WordOrder
import Linglib.Studies.BrueningAlKhalaf2020
import Linglib.Data.Examples.Schwarzer2026

/-!
# Schwarzer (2026): The law and order of selection-violating coordination

This file formalizes the squib's test of the three analyses of selection-violating coordination,
a clause coordinated with a noun phrase in a position where only the noun phrase is selected. The
bottom-up analyses of [sag-etal-1985] and [munn-1993] give the coordination an asymmetric
structure in which the first conjunct alone is prominent for the selector, so the selected noun
phrase comes first whatever the position of the verb; the linear closeness analysis of
[bruening-alkhalaf-2020] and [bruening-2025] derives left to right and lets the conjunct linearly
adjacent to the selector satisfy selection; and the temporal closeness analysis of [kim-lu-2024]
treats the mismatch as a grammaticality illusion in which the parser checks the conjunct closest in
time to the selector, which yields the linear prediction again (`temporalOrder`). In German the two
predictions come apart: complements precede the verb in an embedded finite clause and follow it in
a root clause with verb-second (`embeddedPosition`, `rootPosition`), so the closeness accounts
predict a clause-first order in the embedded case, where [bruening-alkhalaf-2020]'s
`predictOrder` gives the two accounts opposite verdicts (`accounts_diverge_embedded`).

Experiment 1 confirms that German allows the construction with verbs that reject a bare
*dass*-clause (`Data/Examples/Schwarzer2026`, (11) and (12)); Experiment 2's forced choice finds
the noun phrase first in twenty-three of thirty choices in both positions. A noun-phrase-first
preference in the embedded position refutes the closeness prediction (`closeness_refuted`), while
the structural prediction is position-invariant (`structural_position_invariant`); the squib
notes that the latter is thereby supported only indirectly.

## Implementation notes

* The verb positions are read off the German verb-second profile, with the finite verb in the
  clause-final position of an embedded clause and in second position of a root declarative.
  The predicates of the experiments are recorded with their clausal frames in
  `Fragments/German/Predicates`.
* The experiments' scores are recorded in the example rows' comments; the mixed model and the
  logistic regression are not formalized.

## References

* [schwarzer-2026]
* [bruening-alkhalaf-2020]
* [kim-lu-2024]
* [sag-etal-1985]
-/

namespace Schwarzer2026

open Features WordOrder BrueningAlKhalaf2020

/-- The position of a coordinated complement relative to the finite verb in a German root
declarative: the verb in second position precedes its complements, the configuration of (17). -/
abbrev rootPosition : VerbPosition := .postverbal

/-- The position in an embedded finite clause: the verb is clause-final, so the coordination
precedes it, the configuration of (16). -/
abbrev embeddedPosition : VerbPosition := .preverbal

/-- The temporal closeness analysis predicts the order the linear one does: in either position
the conjunct closest in time to the selector is the linearly adjacent one, the first when the
verb precedes and the last, whose features are still in memory, when it follows. -/
abbrev temporalOrder : VerbPosition → ConjunctOrder := predictOrder .linear

/-- The bottom-up prediction does not depend on the verb's position: the selected noun phrase
is first, (10b). -/
theorem structural_position_invariant (pos : VerbPosition) :
    predictOrder .structural pos = .dpFirst := rfl

/-- The closeness accounts predict the clause first in the embedded position, (10a). -/
theorem closeness_embedded : predictOrder .linear embeddedPosition = .cpFirst := rfl

/-- The accounts diverge in the embedded position only, which is what makes German the test
case: in the root position both predict the noun phrase first. -/
theorem accounts_diverge_embedded :
    predictOrder .structural embeddedPosition ≠ predictOrder .linear embeddedPosition ∧
      predictOrder .structural rootPosition = predictOrder .linear rootPosition :=
  ⟨by decide, (agree_iff_head_precedes rootPosition).2 rfl⟩

/-- A preferred order in the embedded position that puts the noun phrase first refutes the
linear and temporal closeness accounts, whatever the reason for the preference. -/
theorem closeness_refuted {observed : VerbPosition → ConjunctOrder}
    (h : observed embeddedPosition = .dpFirst) :
    predictOrder .linear embeddedPosition ≠ observed embeddedPosition ∧
      temporalOrder embeddedPosition ≠ observed embeddedPosition := by
  rw [h]
  exact ⟨by decide, by decide⟩

end Schwarzer2026
