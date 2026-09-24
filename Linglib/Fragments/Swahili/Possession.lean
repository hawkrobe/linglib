module

public import Linglib.Fragments.Swahili.Basic
public import Linglib.Data.WALS.Features.F117A
public import Linglib.Data.WALS.Features.F24A

/-!
# Swahili possession

This file defines the Swahili have-construction as Heine and Stassen describe it. The
possessor is the subject and the possessee follows the comitative *na* 'with', an instance of
Heine's companion schema, "X is with Y", and of Stassen's with-possessive. In the present
tense the copula is absent and the subject prefix attaches to *na*, *ni-na saa* 'I have a
watch'; in the other tenses the copula *kuwa* 'be' is kept, *a-li-ku-wa na wake wawili* 'he had
two wives'. With a locative class as subject the same construction is the existential, *ku-na
chakula* 'there is food', and the progressive *wa-na-ku-la* 'they are eating' has the same
source. The belong-construction is the equational *saa ni y-angu* 'the watch is mine', and the
attributive possessive marks the possessor phrase with the connective *-a* agreeing with the
possessum, *nyumba y-a Habiba* 'Habiba's house'.

## Main definitions

* `Swahili.Possession.na`, `present`, `past`: the comitative and the present and past
  have-constructions on a subject prefix

## Main results

* `Swahili.Possession.present_first_singular`, `past_third_singular`: the forms of the
  examples from the subject-prefix paradigm
* `Swahili.Possession.existential`: the existential is the present construction on a locative
  subject prefix
* `Swahili.Possession.wals_117A`, `wals_24A`: the atlas codes the predicative possessive as
  conjunctional and the attributive possessive as dependent-marking

## References

* [B. Heine, *Possession: Cognitive Sources, Forces, and Grammaticalization*
  (1997)][heine-1997]
* [L. Stassen, *Predicative Possession* (2009)][stassen-2009]
-/

@[expose] public section

namespace Swahili.Possession

open Swahili Agreement Morphology Data.WALS

/-- The comitative *na* 'with', the predicate of the have-construction. -/
def na : Morph := .free "na"

/-- The present tense have-construction puts the subject prefix on *na*, with no copula. -/
def present (s : Morph) : List Morph := [s, na]

/-- The past tense have-construction keeps the copula, the subject prefix, the past *-li-*
and *ku-wa* before *na*. -/
def past (s : Morph) : List Morph := [s, .pref "li", .pref "ku", .root "wa", na]

/-- *ni-na saa* 'I have a watch'. -/
theorem present_first_singular :
    (subjectPrefix.realize (.pn .first .singular)).map present = some [.pref "ni", na] := rfl

/-- *a-li-ku-wa na wake wawili* 'he had two wives'. -/
theorem past_third_singular :
    (subjectPrefix.realize (.pn .third .singular)).map past =
      some [.pref "a", .pref "li", .pref "ku", .root "wa", na] := rfl

/-- The existential is the present construction on a locative subject prefix, *ku-na chakula*
'there is food' and *pa-na watu wengi* 'there are many people'. -/
theorem existential :
    present NounClass.cl17.subjPrefix = [.pref "ku", na] ∧
      present NounClass.cl16.subjPrefix = [.pref "pa", na] :=
  ⟨rfl, rfl⟩

/-- The atlas codes the predicative possessive as conjunctional, Stassen's with-possessive. -/
theorem wals_117A :
    (Datapoint.lookupISO F117A.allData "swh").map (·.value) = some .conjunctional := by
  decide

/-- The atlas codes the attributive possessive as dependent-marking. -/
theorem wals_24A :
    (Datapoint.lookupISO F24A.allData "swh").map (·.value) = some .dependentMarking := by
  decide

end Swahili.Possession
