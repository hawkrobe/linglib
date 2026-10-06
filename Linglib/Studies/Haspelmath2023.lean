/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph
public import Linglib.Morphology.Root.Basic
public import Linglib.Morphology.Word.Comparative

/-!
# Haspelmath (2023): Defining the word

Haspelmath defines a word as a free morph, a clitic, or a root or compound possibly augmented
by nonrequired affixes and augmented by required affixes if there are any. A clitic is a bound
morph that is neither a root nor an affix, and a required affix is one that must be present in
a free form unless another affix replaces it. This file checks the definitions,
`Morphology.Comparative.IsWordIn` and its parts, against the paper's examples, and compares the
definition with Bloomfield's minimum free form, which it is meant to correct.

## Main results

* `to_clitic_zu_prefix`: English infinitival *to* is a clitic and German *zu-* a prefix.
* `genitive_clitic_suffix`: English genitive *'s* is a clitic and German *-s* a suffix.
* `alber_required`, `geb_required`: Italian *alber* needs the suffix *-o* or *-i* and German
  *geb* the suffix *-en* or *-t*, so the bare roots are not words.
* `tree_word`: English *tree* has no required affix, so it is a word, though not a free form.
* `bloomfield_too_narrow`, `bloomfield_too_broad`: *tree* and the clitic *to* are words but not
  minimum free forms, and *a tree* is a minimum free form but not a word.
* `wordsAt_affix_words`: the words at `.affix` of the English and Italian forms are words, while
  *a=tree*, one word at `.clitic`, is not.

## Implementation notes

Each example is an inventory of the paper's free forms, each a list of morphs with textbook
attachment labels, with the classes of its roots. The definition of an affix refers to the roots
of Definition 6, which needs a free form with the root as its only contentful morph; on the free
forms the paper cites for Definition 2 these are exactly the contentful morphs
(`roots_contentful`), and the other inventories take the contentful morphs as roots. The English
article's distribution comes from the 2021 paper's *a house*, *a big house*. Compounds are not
formalized.

## References

* [bloomfield-1933]
* [haspelmath-2021c]
* [haspelmath-2023]
-/

@[expose] public section

namespace Haspelmath2023

open Morphology Morphology.Comparative

/-! ### Roots -/

/-- The English possessive *my*. -/
def my : Morph := .procl "my"
/-- The English object root *husband*. -/
def husband : Morph := .root "husband"
/-- The English article *a*. -/
def a : Morph := .procl "a"
/-- The English object root *café*. -/
def cafe : Morph := .root "café"
/-- The English pronoun *he*. -/
def he : Morph := .procl "he"
/-- The English auxiliary *is*. -/
def is : Morph := .free "is"
/-- The English action root *work*. -/
def work : Morph := .root "work"
/-- The English progressive suffix *-ing*. -/
def ing : Morph := .suff "ing"
/-- The English property root *nice*. -/
def nice : Morph := .root "nice"
/-- The English adverb *now*. -/
def now : Morph := .free "now"
/-- The English interjection *ouch*. -/
def ouch : Morph := .free "ouch"

/-- The English free forms cited for Definitions 1 and 2 are *nice*, *work*, *now*, *ouch*,
*my husband*, *a café* and *he is working*. -/
def freeForms : List (List Morph) :=
  [[nice], [work], [now], [ouch], [my, husband], [a, cafe], [he, is, work, ing]]

/-- The classes of the English roots. -/
def freeFormsClass (m : Morph) : Option RootClass :=
  if m = husband ∨ m = cafe then some .object
  else if m = work then some .action else if m = nice then some .property else none

/-- On these free forms the roots of Definition 6 are the contentful morphs. -/
theorem roots_contentful :
    ∀ m ∈ freeForms.flatten,
      IsRootIn freeForms freeFormsClass m ↔ IsContentful freeFormsClass m := by
  decide

/-! ### Clitics and affixes -/

/-- The English infinitival *to*. -/
def «to» : Morph := .procl "to"
/-- The English action root *destroy*. -/
def destroy : Morph := .root "destroy"
/-- The English property root *thorough*. -/
def thorough : Morph := .root "thorough"
/-- The English adverbial suffix *-ly*. -/
def ly : Morph := .suff "ly"

/-- The English infinitives *to destroy* and *to thoroughly destroy*. -/
def infinitives : List (List Morph) := [[«to», destroy], [«to», thorough, ly, destroy]]

/-- The classes of the English roots. -/
def infinitivesClass (m : Morph) : Option RootClass :=
  if m = destroy then some .action else if m = thorough then some .property else none

/-- The German particle *aus* 'out'. -/
def aus : Morph := .pref "aus"
/-- The German infinitival *zu-*. -/
def zu : Morph := .pref "zu"
/-- The German action root *geh* 'go'. -/
def geh : Morph := .root "geh"
/-- The German infinitive suffix *-en*. -/
def en : Morph := .suff "en"

/-- The German infinitive *aus-zu-gehen* 'to go out'. -/
def ausZuGehen : List (List Morph) := [[aus, zu, geh, en]]

/-- The class of the German root. -/
def ausZuGehenClass (m : Morph) : Option RootClass := if m = geh then some .action else none

/-- English *to* precedes an adverb as well as a verb, so it is a clitic, while German *zu-*
always occurs on a verb root and is a prefix. -/
theorem to_clitic_zu_prefix :
    IsCliticIn infinitives infinitivesClass (IsContentful infinitivesClass) «to» ∧
      IsAffixIn ausZuGehen ausZuGehenClass (IsContentful ausZuGehenClass) zu := by
  decide

/-- The English and German object root *Kim*. -/
def kim : Morph := .root "Kim"
/-- The English genitive *'s*. -/
def s_gen : Morph := .encl "s"
/-- The English object root *umbrella*. -/
def umbrella : Morph := .root "umbrella"
/-- The English article *the*. -/
def the : Morph := .procl "the"
/-- The English object root *dog*. -/
def dog : Morph := .root "dog"
/-- The English object root *bone*. -/
def bone : Morph := .root "bone"
/-- The English object root *boy*. -/
def boy : Morph := .root "boy"
/-- The English pronoun *I*. -/
def i : Morph := .procl "I"
/-- The English action root *love*. -/
def love : Morph := .root "love"

/-- The English genitives *Kim's umbrella*, *the dog's bone* and *the boy I love's umbrella*. -/
def genitives : List (List Morph) :=
  [[kim, s_gen, umbrella], [the, dog, s_gen, bone], [the, boy, i, love, s_gen, umbrella]]

/-- The classes of the English roots. -/
def genitivesClass (m : Morph) : Option RootClass :=
  if m = love then some .action
  else if m = kim ∨ m = umbrella ∨ m = dog ∨ m = bone ∨ m = boy then some .object else none

/-- The German genitive *-s*. -/
def s_genDe : Morph := .suff "s"
/-- The German object root *Ring* 'ring'. -/
def ring : Morph := .root "Ring"

/-- The German genitive *Kim-s Ring* 'Kim's ring'. -/
def genitivesDe : List (List Morph) := [[kim, s_genDe, ring]]

/-- The classes of the German roots. -/
def genitivesDeClass (m : Morph) : Option RootClass :=
  if m = kim ∨ m = ring then some .object else none

/-- English *'s* also follows a verb, so it is a clitic, while German *-s* always follows a noun
and is a suffix. -/
theorem genitive_clitic_suffix :
    IsCliticIn genitives genitivesClass (IsContentful genitivesClass) s_gen ∧
      IsAffixIn genitivesDe genitivesDeClass (IsContentful genitivesDeClass) s_genDe := by
  decide

/-! ### Required affixes -/

/-- The Italian object root *alber* 'tree'. -/
def alber : Morph := .root "alber"
/-- The Italian singular suffix *-o*. -/
def o : Morph := .suff "o"
/-- The Italian plural suffix *-i*. -/
def i_pl : Morph := .suff "i"

/-- The Italian free forms *alber-o* 'tree' and *alber-i* 'trees'. -/
def italian : List (List Morph) := [[alber, o], [alber, i_pl]]

/-- The class of the Italian root. -/
def italianClass (m : Morph) : Option RootClass := if m = alber then some .object else none

/-- *alber* needs *-o* unless *-i* replaces it, so *-o* is a required affix, *alber* is not a
word and *alber-o* is. -/
theorem alber_required :
    IsRequiredAffixIn italian italianClass (IsContentful italianClass) o alber ∧
      ¬ IsWordIn italian italianClass (IsContentful italianClass) [alber] ∧
      IsWordIn italian italianClass (IsContentful italianClass) [alber, o] := by
  decide

/-- The German action root *geb* 'give'. -/
def geb : Morph := .root "geb"
/-- The German imperative plural suffix *-t*. -/
def t : Morph := .suff "t"

/-- The German free forms *geb-en* '(to) give' and *geb-t* 'give (pl.)'. -/
def german : List (List Morph) := [[geb, en], [geb, t]]

/-- The class of the German root. -/
def germanClass (m : Morph) : Option RootClass := if m = geb then some .action else none

/-- *geb* takes *-en* or the alternative required suffix *-t*, so the bare root is not a
word. -/
theorem geb_required :
    IsRequiredAffixIn german germanClass (IsContentful germanClass) en geb ∧
      ¬ IsWordIn german germanClass (IsContentful germanClass) [geb] := by
  decide

/-- The English object root *tree*. -/
def tree : Morph := .root "tree"
/-- The English plural suffix *-s*. -/
def s_pl : Morph := .suff "s"
/-- The English object root *house*. -/
def house : Morph := .root "house"
/-- The English property root *big*. -/
def big : Morph := .root "big"

/-- The English free forms *a tree* and *trees*, with *a house* and *a big house* for the
article. -/
def trees : List (List Morph) := [[a, tree], [tree, s_pl], [a, house], [a, big, house]]

/-- The classes of the English roots. -/
def treesClass (m : Morph) : Option RootClass :=
  if m = tree ∨ m = house then some .object else if m = big then some .property else none

/-- *-s* can be absent from a free form, as in *a tree*, without another affix replacing it, so
it is not required, and *tree* is a word although it is not a free form. -/
theorem tree_word :
    ¬ IsRequiredAffixIn trees treesClass (IsContentful treesClass) s_pl tree ∧
      IsWordIn trees treesClass (IsContentful treesClass) [tree] ∧ [tree] ∉ trees := by
  decide

/-! ### Bloomfield's minimum free form (§3.1) -/

/-- Bloomfield's definition is too narrow: *tree* and the clitic *to* are words but not free
forms, so not minimum free forms. -/
theorem bloomfield_too_narrow :
    (IsWordIn trees treesClass (IsContentful treesClass) [tree] ∧
        ¬ IsMinimalFreeForm trees [tree]) ∧
      IsWordIn infinitives infinitivesClass (IsContentful infinitivesClass) [«to»] ∧
        ¬ IsMinimalFreeForm infinitives [«to»] :=
  ⟨⟨by decide, fun h ↦ by simpa [trees] using h.1⟩, by decide,
    fun h ↦ by simpa [infinitives] using h.1⟩

/-- Bloomfield's definition is too broad: *a tree* cannot be broken up into free forms, so it
is a minimum free form, but it is a clitic and a root, not a word. -/
theorem bloomfield_too_broad :
    IsMinimalFreeForm trees [a, tree] ∧
      ¬ IsWordIn trees treesClass (IsContentful treesClass) [a, tree] :=
  ⟨isMinimalFreeForm_of_take (by decide) (by decide), by decide⟩

/-! ### Words at an attachment -/

/-- The words at `.affix` of the English forms with *tree* and of the Italian forms are words,
while *a=tree*, one word at `.clitic`, is not. -/
theorem wordsAt_affix_words :
    (∀ f ∈ trees, ∀ w ∈ Morph.wordsAt .affix f,
        IsWordIn trees treesClass (IsContentful treesClass) w) ∧
      (∀ f ∈ italian, ∀ w ∈ Morph.wordsAt .affix f,
        IsWordIn italian italianClass (IsContentful italianClass) w) ∧
      Morph.wordsAt .clitic [a, tree] = [[a, tree]] ∧
      ¬ IsWordIn trees treesClass (IsContentful treesClass) [a, tree] := by
  decide

end Haspelmath2023
