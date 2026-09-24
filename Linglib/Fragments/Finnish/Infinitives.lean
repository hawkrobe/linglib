module

public import Linglib.Fragments.Finnish.Case
public import Linglib.Fragments.Finnish.Phonology

/-!
# Finnish infinitives

Karlsson names the Finnish infinitives after their function endings, as the *Iso suomen
kielioppi* does. There are the A infinitive, which is the dictionary form, the E infinitive,
the MA infinitive and the rare MINEN infinitive, traditionally the first to the fourth.
Infinitives take case endings as nouns do, but few of them. The A infinitive has its basic
form, a nominative, and a translative that takes a possessive ending, as in *sano-a-kse-ni*
'in order for me to say'. The E infinitive has an inessive of time, as in *sano-e-ssa* 'while
saying', and an instructive of manner, as in *itki-e-n* 'crying'. The MA infinitive has the
inessive, elative, illative, adessive and abessive, as in *luke-ma-ssa* 'reading', and a rare
instructive of necessity, as in *tule-ma-n*. The MINEN infinitive has only a nominative and a
partitive, both of obligation.

The A and E infinitives are built on the infinitive stem, and the MA and MINEN infinitives on
the inflectional stem, the stem of the present, as *ole-ma-* against *ol-la* 'be'. The ending
of the A infinitive depends on how its stem ends. It is -dA after a long vowel or a diphthong,
as in *saa-da* 'get', and -tA after `s`, as in *juos-ta* 'run'. After `l`, `n` or `r` it
repeats that consonant, as in *tul-la* 'come', and after a short vowel or a `t` it is -A, as
in *sano-a* 'say' and *huomat-a* 'notice'. The E infinitive changes the -A to -e, as in
*sano-e-* and *juos-te-*.

## Main definitions

* `Finnish.Infinitive`: the four infinitives.
* `Finnish.Infinitive.cases`: the cases an infinitive takes.
* `Finnish.Infinitive.aEnding`: the ending of the A infinitive after its stem.
* `Finnish.Infinitive.base`: a stem with an infinitive's function ending, before a case
  ending.

## Main results

* `Finnish.Infinitive.cases_subset_inventory`: an infinitive takes cases of the noun.
* `Finnish.Infinitive.toCase_mem_cases_ma_iff`: of the local cases the MA infinitive takes the
  interior series and, of the exterior series, the adessive alone.

## Implementation notes

The stems *teh-* 'do' and *näh-* 'see' take -dA, which Karlsson lists among the exceptions, and
the E infinitive of a stem in -e changes it to -i, as in *luki-e-ssa* 'while reading'; neither
is represented. The partitive of the MINEN infinitive is built on -mis-, as in *mene-mis-tä*,
and a case ending after it is not derived.

## References

* [karlsson-2017]
-/

@[expose] public section

namespace Finnish

open Phonology

/-- The Finnish infinitives, named by their function endings. -/
inductive Infinitive where
  /-- The A infinitive, the first, which is the dictionary form: *sano-a* 'say'. -/
  | a
  /-- The E infinitive, the second: *sano-e-ssa* 'while saying'. -/
  | e
  /-- The MA infinitive, the third: *sano-ma-an* 'to say'. -/
  | ma
  /-- The MINEN infinitive, the fourth: *tietä-minen* 'knowing'. -/
  | minen
  deriving DecidableEq, Repr, Fintype

namespace Infinitive

/-- The cases an infinitive takes. -/
def cases : Infinitive → Finset Case
  | .a => {.nom, .transl}
  | .e => {.ine, .inst}
  | .ma => {.ine, .ela, .ill, .ade, .abess, .inst}
  | .minen => {.nom, .part}

/-- An infinitive takes cases of the noun. -/
theorem cases_subset_inventory (i : Infinitive) : i.cases ⊆ Case.inventory := by
  cases i <;> decide

/-- Of the local cases the MA infinitive takes the interior series and, of the exterior
series, the adessive alone. -/
theorem toCase_mem_cases_ma_iff {r : Case.Region} {d : Case.PathDir} {c : Case}
    (h : Case.toCase r d = some c) : c ∈ ma.cases ↔ r = .interior ∨ r = .exterior ∧ d = .place := by
  cases r <;> cases d <;> cases h <;> decide

/-- The ending of the A infinitive after its stem: -dA after a long vowel or a diphthong, -tA
after `s`, the stem's final consonant with -A after `l`, `n` or `r`, and -A otherwise. -/
def aEnding (w : List Segment) : List Segment :=
  match w.reverse with
  | x :: y :: _ =>
    if x.IsVowel ∧ y.IsVowel then [d, A]
    else if x = s then [t, A]
    else if x = l ∨ x = n ∨ x = r then [x, A]
    else [A]
  | _ => [A]

/-- The stem `w` with the function ending of an infinitive, before a case ending. -/
def base : Infinitive → List Segment → List Segment
  | .a, w => w ++ aEnding w
  | .e, w => w ++ (aEnding w).dropLast ++ [Finnish.e]
  | .ma, w => w ++ [m, A]
  | .minen, w => w ++ [m, i, n, Finnish.e, n]

end Infinitive

end Finnish
