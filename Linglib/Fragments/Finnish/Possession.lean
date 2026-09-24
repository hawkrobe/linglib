module

public import Linglib.Fragments.Finnish.Declension
public import Linglib.Syntax.Agreement.Paradigm

/-!
# Finnish possessive endings

A possessed Finnish noun takes a possessive ending that agrees in person and number with the
possessor, as in *talo-ni* 'my house', and the genitive of a personal pronoun may accompany
it, as in *minu-n talo-ni*. The endings are -ni, -si and -nsA in the singular and -mme, -nne
and -nsA in the plural, so that the third person alone does not distinguish number.

A possessive ending follows the case ending. The final consonant of a case ending is dropped
before it, so that the nominative and the genitive coincide, as in *ove-mme* 'our door, of
our door', and the illative loses its -n, as in *auto-o-ni* 'into my car'. The translative is
-kse before it. After a case ending in a short vowel the third person is usually -Vn, as in
*talo-ssa-an* 'in his house', beside the older -nsA.

## Main definitions

* `Finnish.Possession.endings`: the possessive endings, an agreement paradigm.
* `Finnish.Possession.caseEnding`: the form of a case ending before a possessive ending.
* `Finnish.Possession.inflection`: the endings of a possessed noun in a case.

## Main results

* `Finnish.Possession.realize_eq_realize_iff`: two cells share an ending exactly when they are
  the same cell or both are third person.
* `Finnish.Possession.inflection_third`: the third person is -Vn after the inessive and -nsA
  after the illative.
* `Finnish.Possession.inflection_gen`: a possessed noun has the same endings in the genitive
  as in the nominative.

## Implementation notes

The third person is also -nsA after a partitive -A that follows a stem-final A, as in *kala-a-nsa*
'his fish', a condition on the stem that is not represented.

## References

* [karlsson-2017]
-/

@[expose] public section

namespace Finnish.Possession

open Phonology Agreement

/-- The possessive endings. -/
def endings : Paradigm (List Segment) :=
  [(.pn .first .singular, [n, i]), (.pn .second .singular, [s, i]),
    (.pn .third .singular, [n, s, A]), (.pn .first .plural, [m, m, e]),
    (.pn .second .plural, [n, n, e]), (.pn .third .plural, [n, s, A])]

/-- Two cells share an ending exactly when they are the same cell or both are third
person. -/
theorem realize_eq_realize_iff :
    ∀ p ∈ Bundle.pnCells, ∀ q ∈ Bundle.pnCells, endings.realize p = endings.realize q ↔
      p = q ∨ p.person = .third ∧ q.person = .third := by
  decide

/-- The form of the ending of the case `c` before a possessive ending: the translative is
-kse, and a final consonant is dropped. -/
def caseEnding (c : Case) : Option (List Segment) :=
  if c = .transl then some [k, s, e]
  else (Declension.ending c).map fun w ↦ if ∀ x ∈ w.getLast?, x.IsVowel then w else w.dropLast

/-- The endings of a noun in the case `c` possessed by the cell `p`. After a case ending in a
short vowel the third person is -Vn. -/
def inflection (c : Case) (p : Bundle) : Option (List Segment) :=
  (caseEnding c).bind fun w ↦
    if p.person = .third ∧ ∃ x ∈ (Declension.ending c).bind List.getLast?, x.IsVowel then
      some (w ++ [V, n])
    else (endings.realize p).map (w ++ ·)

/-- The third person is -Vn after the inessive, as in *talo-ssa-an* 'in his house', and -nsA
after the illative, whose ending ends in a consonant, as in *talo-o-nsa* 'into his house'. -/
theorem inflection_third :
    inflection .ine (.pn .third .singular) = some [s, s, A, V, n] ∧
      inflection .ill (.pn .third .singular) = some [V, n, s, A] := by
  decide

/-- A possessed noun has the same endings in the genitive as in the nominative. -/
theorem inflection_gen (p : Bundle) : inflection .gen p = inflection .nom p := by
  have : ¬ n.IsVowel := by decide
  simp [inflection, caseEnding, Declension.ending, Declension.endings, this]

end Finnish.Possession
