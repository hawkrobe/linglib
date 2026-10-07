/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Chain
public import Linglib.Syntax.Minimalist.SyntacticObject.Phase

/-!
# Locality on chains

Locality constrains the links of a chain. Chomsky's Phase Impenetrability Condition bars a link
from the interior of a phase, the positions its head c-commands, to a position outside the head's
maximal projection, so that the edge is the escape hatch (`Crosses`); an island is a domain no
link may leave (`Escapes`). A token with one copy has no link, so binding in situ is subject to
neither (`not_crosses_of_length_le_one`, `not_escapes_of_length_le_one`), and movement, covert
movement included, is subject to both, as Sato and Ngui find. The positional interior carries
the terms within the complement of the unordered phase (`withinComplement_iff_exists_mem_interior`).

## Main definitions

* `Minimalist.interior`: the interior of a phase on positions, the positions its head c-commands.
* `Minimalist.Crosses`, `Minimalist.Escapes`: a link leaving a phase from its interior, and a
  link leaving a domain.

## Main statements

* `Minimalist.withinComplement_iff_exists_mem_interior`: the positions in `interior` carry the
  terms within the complement of a phase head occurring once.

## Implementation notes

* Positions, not terms, individuate copies, so the phase interior of the unordered object
  (`SyntacticObject.phaseInterior`) cannot tell the links of a successive-cyclic chain apart, and
  the locality of links is stated on positions.

## References

* [chomsky-2000]
* [sato-ngui-2017]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order PhraseStructure

variable (t : PlanarSyntacticObject) (tok : LIToken)

/-- The interior of the phase headed at `h` is the set of positions the head c-commands. -/
def interior (h : TreePath) : Set TreePath := {q | CCommands t.val h q}

instance (h q : TreePath) : Decidable (q ∈ interior t h) :=
  inferInstanceAs (Decidable (CCommands _ _ _))

/-- The interior positions of a phase head occurring only at `a` carry the terms within its
complement. -/
theorem withinComplement_iff_exists_mem_interior {t : PlanarSyntacticObject} {ℓ : LIToken}
    {a : t.val.Positions} {x : SyntacticObject}
    (hu : ∀ q, t.termAt q = SyntacticObject.leaf ℓ ↔ q = a)
    (hph : (t : SyntacticObject).IsPhaseHead ℓ) :
    (t : SyntacticObject).WithinComplement ℓ x ↔ ∃ q : t.val.Positions, ↑q ∈ interior t a ∧
      t.termAt q = x := by
  have ha : t.termAt a = SyntacticObject.leaf ℓ := (hu a).2 rfl
  have hu' : ∀ q, t.termAt q = t.termAt a → q = a := fun q hq ↦ (hu q).1 (hq.trans ha)
  obtain ⟨m₀, hm₀, hℓ, hm₀ℓ⟩ := hph
  rw [← mem_phaseInterior, phaseInterior_eq_domainIn fun m hm hmℓ ↦ ?_, mem_domainIn, ← ha]
  · exact PlanarSyntacticObject.cCommandsIn_termAt_iff hu'
  · rw [PlanarSyntacticObject.eq_termAt_pred_of_immediatelyContains hu' hm (by rwa [ha]),
      ← PlanarSyntacticObject.eq_termAt_pred_of_immediatelyContains hu' hm₀ (by rwa [ha])]
    exact hℓ

/-- A link of the chain of `tok` leaves the phase headed at `h` when it runs from the interior to
a position outside the head's maximal projection; the Phase Impenetrability Condition forbids it,
and a link to the edge does not leave. -/
def Crosses (h : TreePath) : Prop :=
  ∃ x ∈ links t tok, x.2 ∈ interior t h ∧ ¬ projectionAt t h ≤ x.1

instance (h : TreePath) : Decidable (Crosses t tok h) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A link of the chain of `tok` leaves the domain at `D` when it runs from inside `D` to outside,
as movement out of an island does. -/
def Escapes (D : TreePath) : Prop := ∃ x ∈ links t tok, D ≤ x.2 ∧ ¬ D ≤ x.1

instance (D : TreePath) : Decidable (Escapes t tok D) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem not_crosses_of_length_le_one (h : (chain t tok).length ≤ 1) (hd : TreePath) :
    ¬ Crosses t tok hd := by
  simp [Crosses, links_eq_nil_of_length_le_one t tok h]

theorem not_escapes_of_length_le_one (h : (chain t tok).length ≤ 1) (D : TreePath) :
    ¬ Escapes t tok D := by
  simp [Escapes, links_eq_nil_of_length_le_one t tok h]

end Minimalist
