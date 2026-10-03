module

public import Linglib.Syntax.Negation
public import Linglib.Fragments.Arabic.ModernStandard.Case
public import Linglib.Fragments.Arabic.ModernStandard.Verbs

/-!
# Modern Standard Arabic negation

Modern Standard Arabic negates a verb with a particle chosen by tense: *laa* for the present, *lam*
for the past with the verb in the jussive, and *lan* for the future with the verb in the
subjunctive. The particle *maa* negates a verb that keeps its own tense. The verb *lays-a* 'not
be' takes the person markers of the past tense but negates the present, and gives a verbless
clause a finite verb whose predicate is in the accusative.

## Main definitions

* `laa`, `lam`, `lan`, `maa`: the negative particles.
* `laysa`, `laysaForms`: the negative verb *lays-a* and its forms by person, number and
  gender.
* `verbal`, `equational`: affirmative clauses with their negatives.

## Implementation notes

The verbal pairs are Benmamoun's, in his transliteration and hyphenation, except that the subject
*ṭ-ṭullaab-u* 'the students' is left out and the future *sa-ya-ðhab-uun* is cut *-uu-n* like the
present *ya-drus-uu-n*. The equational pairs are Ryding's; the article, pronounced *l-* after
*lays-a*, is cited as *al-* in both members.

Ryding gives *maa* only with a past-tense verb and finds it rare in writing. Benmamoun also gives
it with a present-tense verb, and gives *lays-a* negating a present-tense verbal clause in free
variation with *laa*.

## TODO

Benmamoun derives the distribution of the negatives from a single negative head: *lam* and *lan*
are *laa* carrying past and future tense, and *lays-a* is *laa* carrying agreement. That analysis
belongs in a study. An imperfective paradigm with its moods would let the moods the particles
govern be read off the verb forms.

## References

* [benmamoun-2000]
* [ryding-2005]
-/

@[expose] public section

open Morphology Negation

namespace Arabic.ModernStandard.Negation

/-- The particle *laa* negates a present-tense verb, which stays in the indicative
([ryding-2005] p. 644). It also negates the second person of the jussive in a prohibition
(p. 645) and a noun in categorical negation (pp. 645–646). -/
def laa : Marker := { pieces := [[.free "laa"]] }

/-- The particle *lam* negates the past, with the verb in the jussive ([ryding-2005] p. 647). -/
def lam : Marker := { pieces := [[.free "lam"]] }

/-- The particle *lan* negates the future, with the verb in the subjunctive ([ryding-2005]
p. 648). -/
def lan : Marker := { pieces := [[.free "lan"]] }

/-- The particle *maa* negates a verb that keeps its tense, a past ([ryding-2005] p. 647) or a
present ([benmamoun-2000] (41), pp. 107–108). -/
def maa : Marker := { pieces := [[.free "maa"]] }

/-- The negative verb *lays-a* 'not be', cited by its long stem ([ryding-2005] p. 641). -/
def laysa : Marker := { pieces := [[.root "lays"]] }

/-- The stem *lays-a* takes before a person marker is *las-* when the marker starts with a
consonant and *lays-* when it starts with a vowel ([ryding-2005] p. 641). -/
def laysaStem (s : Morph) : Morph :=
  if s.form.front ∈ ['a', 'i', 'u'] then .root "lays" else .root "las"

/-- The forms of *lays-a* are its stem with the person markers of the past tense
([ryding-2005] p. 641). -/
def laysaForms : Agreement.Paradigm (List Morph) :=
  pastSuffix.map fun (c, s) ↦ (c, [laysaStem s, s])

/-- *lays-a* has a form in exactly the cells of the past tense. -/
theorem cells_laysaForms : laysaForms.cells = pastSuffix.cells := by
  simp [laysaForms, Agreement.Paradigm.cells]

/-- *lays-a* conjugates as in Ryding's chart (p. 642) and in [benmamoun-2000]'s (25) (p. 102),
which misprints *las-ti* as *lasti-ti*. It has no first person dual. -/
example :
    laysaForms.map (·.2) =
      [[.root "las", .suff "tu"], [.root "las", .suff "ta"], [.root "las", .suff "ti"],
       [.root "lays", .suff "a"], [.root "lays", .suff "at"], [.root "las", .suff "tumaa"],
       [.root "lays", .suff "aa"], [.root "lays", .suff "ataa"], [.root "las", .suff "naa"],
       [.root "las", .suff "tum"], [.root "las", .suff "tunna"], [.root "lays", .suff "uu"],
       [.root "las", .suff "na"]] ∧
    laysaForms.realize (.pn .first .dual) = none := by
  decide

/-- The pairs are the third person masculine plural of 'study' in the present and of 'go' in the
past and the future, with their negatives ([benmamoun-2000] (1)–(3), pp. 94–95). -/
def verbal : List Pair :=
  [⟨laa, [.pref "ya", .root "drus", .suff "uu", .suff "n"],
    laa.morphs ++ [.pref "ya", .root "drus", .suff "uu", .suff "n"]⟩,
   ⟨lam, [.root "ðahab", .suff "uu"], lam.morphs ++ [.pref "ya", .root "ðhab", .suff "uu"]⟩,
   ⟨lan, [.pref "sa", .pref "ya", .root "ðhab", .suff "uu", .suff "n"],
    lan.morphs ++ [.pref "ya", .root "ðhab", .suff "uu"]⟩]

/-- The verbless clauses *al-ʾustaadh-u muʾarrix-un* 'the professor is a historian' and *ʾanaa
lubnaaniyyat-un* 'I am Lebanese (f.)' pair with negatives whose predicate is in the accusative
([ryding-2005] pp. 642–643). -/
def equational : List Pair :=
  [⟨laysa, [.pref "al", .root "ʾustaadh", .suff (Declension.triptote .definite .nom),
      .root "muʾarrix", .suff (Declension.triptote .indefinite .nom)],
    [.root "lays", .suff "a",
      .pref "al", .root "ʾustaadh", .suff (Declension.triptote .definite .nom),
      .root "muʾarrix", .suff (Declension.triptote .indefinite .acc)]⟩,
   ⟨laysa, [.free "ʾanaa", .root "lubnaaniyyat", .suff (Declension.triptote .indefinite .nom)],
    [.root "las", .suff "tu", .root "lubnaaniyyat", .suff (Declension.triptote .indefinite .acc)]⟩]

/-- Each negative of an equational pair begins with a form of *lays-a*. -/
example : ∀ q ∈ equational, ∃ f ∈ laysaForms, q.negative.take 2 = f.2 := by
  decide

end Arabic.ModernStandard.Negation
