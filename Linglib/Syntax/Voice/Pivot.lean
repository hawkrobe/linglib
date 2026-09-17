import Linglib.Syntax.Voice.Alternation

/-!
# Symmetrical voices and the pivot

A voice alternation of the valency axis (`Alternation.lean`) nucleativizes or
denucleativizes a participant. The symmetrical voices of Western Austronesian
and of a few languages elsewhere do neither: verb morphology codes which
participant is the pivot, the syntactically privileged term, without affecting
the transitivity of the construction ([creissels-2024] §8.1.7). A voice of such
a system is an alternation together with the slot of the derived frame it
selects as pivot (`Voice.PivotSelection`), and the transitivity-related role of
the pivot (`PivotSelection.pivotRole`) is read off the frame. A system is a
family of voices indexed by a language's voice inventory: it is symmetrical
when no voice changes which participants are core terms, and multiple rather
than binary when some voice selects an oblique as pivot (§8.5.1, §8.5.2).

Of the four characteristics of an Austronesian-type voice system in
[erlewine-levin-van-urk-2017], the privileged argument realized in one form or
position whatever its function (4a) is `pivot`, and verb morphology varying
with its choice, obliques included (4b), is `marking` and `Multiple`; the
extraction restriction to the pivot (4c) and the marking of non-pivot subjects
(4d) are recorded where a fragment states them.

## Main definitions

* `Voice.PivotSelection` — an alternation with the derived slot it selects as pivot
* `PivotSelection.pivotRole`, `PivotSelection.SelectsOblique` — the pivot's
  transitivity-related role, and its being an oblique
* `Voice.Symmetrical`, `Voice.Multiple`, `Voice.Equipollent` — properties of a
  family of voices

## Main results

* `Voice.Symmetrical.not_isValencyIncreasing`, `Symmetrical.not_isValencyDecreasing`
  — no voice of a symmetrical system changes valency

## Implementation notes

* The initial construction of a system is the voice whose alternation is
  `ValencyAlternation.refl`, uncoded; every other voice is an alternation from
  it. Which voice is initial is the morphologically simpler or semantically
  unmarked one, as in the valency axis, so a system whose two voices are both
  marked has an equipollent alternation between them.
* [creissels-2024] §8.1.7 reports two rival criteria for symmetry: equipollent
  marking (Himmelmann) and equal transitivity of all voices (Riesberg), and
  adopts the second. `Symmetrical` is the book's criterion and `Equipollent` the
  first; Balinese separates them (`Studies/Creissels2024.lean`).
* The semantic role of an oblique pivot, locative, instrumental or conveyance,
  names the voice in the fragment; the substrate records only whether the pivot
  is an oblique.

## References

* [creissels-2024]
* [erlewine-levin-van-urk-2017]
-/

namespace Voice

/-- A voice of a pivot-prominent system: what the voice does to the construction,
and the slot of the derived frame it selects as pivot. -/
structure PivotSelection extends ValencyAlternation where
  /-- The derived slot selected as pivot. -/
  pivot : ArgumentFrame.Slot
  deriving DecidableEq, Repr

namespace PivotSelection

variable (v : PivotSelection)

/-- The transitivity-related role of the pivot: A, P or S for a core term, X for an
oblique. -/
def pivotRole : Option TermRole := v.targetRole v.pivot

/-- The pivot is an oblique, the selection a binary system does not allow
([creissels-2024] §8.5.2). -/
def SelectsOblique : Prop := v.pivotRole = some .X

instance : Decidable v.SelectsOblique := inferInstanceAs (Decidable (_ = _))

end PivotSelection

/-! ### Voice systems -/

variable {V : Type*} (S : V → PivotSelection)

/-- Every voice selects a pivot without affecting transitivity: the book's criterion for a
symmetrical voice system ([creissels-2024] §8.1.7). -/
def Symmetrical : Prop := ∀ v, (S v).IsSymmetrical

/-- Some voice selects an oblique as pivot: a multiple system, as against a binary one whose
pivot is always a nuclear participant ([creissels-2024] §8.5.1, §8.5.2). -/
def Multiple : Prop := ∃ v, (S v).SelectsOblique

/-- Every coded voice is equipollently coded, no voice being derived from the initial
construction by adding marking: the criterion for symmetry [creissels-2024] §8.1.7
attributes to Himmelmann and does not adopt. -/
def Equipollent : Prop := ∀ v, (S v).marking.IsVoice → (S v).marking = .equipollent

section
variable [Fintype V]

instance : Decidable (Symmetrical S) := inferInstanceAs (Decidable (∀ _, _))
instance : Decidable (Multiple S) := inferInstanceAs (Decidable (∃ _, _))
instance : Decidable (Equipollent S) := inferInstanceAs (Decidable (∀ _, _ → _))

end

variable {S}

theorem Symmetrical.not_isValencyIncreasing (h : Symmetrical S) (v : V) :
    ¬ (S v).IsValencyIncreasing := fun h' ↦ (h v).1 h'.1

theorem Symmetrical.not_isValencyDecreasing (h : Symmetrical S) (v : V) :
    ¬ (S v).IsValencyDecreasing := fun h' ↦ (h v).2 h'.1

end Voice
