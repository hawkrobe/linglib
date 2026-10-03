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
* `laysa`, `laysaForm`: the negative verb *lays-a* and its forms in each person, number and
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
def lam : Marker := { pieces := [[.free "lam"]], gloss := "NEG.PST" }

/-- The particle *lan* negates the future, with the verb in the subjunctive ([ryding-2005]
p. 648). -/
def lan : Marker := { pieces := [[.free "lan"]], gloss := "NEG.FUT" }

/-- The particle *maa* negates a verb that keeps its tense, a past ([ryding-2005] p. 647) or a
present ([benmamoun-2000] (41), pp. 107–108). -/
def maa : Marker := { pieces := [[.free "maa"]] }

/-- The negative verb *lays-a* 'not be', cited by its long stem ([ryding-2005] p. 641). -/
def laysa : Marker := { pieces := [[.root "lays"]] }

/-- The stem *lays-a* takes before a person marker is *las-* when the marker starts with a
consonant and *lays-* when it starts with a vowel ([ryding-2005] p. 641). -/
def laysaStem (s : Morph) : Morph :=
  if s.form.front ∈ ['a', 'i', 'u'] then .root "lays" else .root "las"

/-- The form of *lays-a* in a person, number and gender is the stem with the person marker of the
past tense ([ryding-2005] p. 641). -/
def laysaForm (p : Person) (n : Number) (g : Gender) : Option (List Morph) :=
  (pastSuffix p n g).map fun s ↦ [laysaStem s, s]

/-- *lays-a* has a form exactly where the past tense has a person marker. -/
theorem laysaForm_isSome_iff (p : Person) (n : Number) (g : Gender) :
    (laysaForm p n g).isSome ↔ (pastSuffix p n g).isSome := by
  simp [laysaForm]

/-- *lays-a* conjugates as in Ryding's chart (p. 642) and in [benmamoun-2000]'s (25) (p. 102),
which misprints *las-ti* as *lasti-ti*. -/
example :
    laysaForm .first .singular .masculine = some [.root "las", .suff "tu"] ∧
    laysaForm .first .plural .masculine = some [.root "las", .suff "naa"] ∧
    laysaForm .second .singular .masculine = some [.root "las", .suff "ta"] ∧
    laysaForm .second .singular .feminine = some [.root "las", .suff "ti"] ∧
    laysaForm .second .dual .masculine = some [.root "las", .suff "tumaa"] ∧
    laysaForm .second .dual .feminine = some [.root "las", .suff "tumaa"] ∧
    laysaForm .second .plural .masculine = some [.root "las", .suff "tum"] ∧
    laysaForm .second .plural .feminine = some [.root "las", .suff "tunna"] ∧
    laysaForm .third .singular .masculine = some [.root "lays", .suff "a"] ∧
    laysaForm .third .singular .feminine = some [.root "lays", .suff "at"] ∧
    laysaForm .third .dual .masculine = some [.root "lays", .suff "aa"] ∧
    laysaForm .third .dual .feminine = some [.root "lays", .suff "ataa"] ∧
    laysaForm .third .plural .masculine = some [.root "lays", .suff "uu"] ∧
    laysaForm .third .plural .feminine = some [.root "las", .suff "na"] ∧
    laysaForm .first .dual .masculine = none := by
  decide

/-- The pairs are the third person masculine plural of 'study' in the present and of 'go' in the
past and the future, with their negatives ([benmamoun-2000] (1)–(3), pp. 94–95). -/
def verbal : List Pair :=
  [⟨[.pref "ya", .root "drus", .suff "uu", .suff "n"],
    laa.morphs ++ [.pref "ya", .root "drus", .suff "uu", .suff "n"]⟩,
   ⟨[.root "ðahab", .suff "uu"], lam.morphs ++ [.pref "ya", .root "ðhab", .suff "uu"]⟩,
   ⟨[.pref "sa", .pref "ya", .root "ðhab", .suff "uu", .suff "n"],
    lan.morphs ++ [.pref "ya", .root "ðhab", .suff "uu"]⟩]

/-- The verbless clauses *al-ʾustaadh-u muʾarrix-un* 'the professor is a historian' and *ʾanaa
lubnaaniyyat-un* 'I am Lebanese (f.)' pair with negatives whose predicate is in the accusative
([ryding-2005] pp. 642–643). -/
def equational : List Pair :=
  [⟨[.pref "al", .root "ʾustaadh", .suff (Declension.triptote .definite .nom),
      .root "muʾarrix", .suff (Declension.triptote .indefinite .nom)],
    [.root "lays", .suff "a",
      .pref "al", .root "ʾustaadh", .suff (Declension.triptote .definite .nom),
      .root "muʾarrix", .suff (Declension.triptote .indefinite .acc)]⟩,
   ⟨[.free "ʾanaa", .root "lubnaaniyyat", .suff (Declension.triptote .indefinite .nom)],
    [.root "las", .suff "tu", .root "lubnaaniyyat", .suff (Declension.triptote .indefinite .acc)]⟩]

/-- Each negative of an equational pair begins with a form of *lays-a*. -/
example : ∀ q ∈ equational, ∃ p n g, ∃ f, laysaForm p n g = some f ∧ q.negative.take 2 = f := by
  decide

end Arabic.ModernStandard.Negation
