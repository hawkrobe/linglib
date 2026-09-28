module

public import Linglib.Syntax.Case.Alignment
public import Linglib.Semantics.Aspect.Defs

/-!
# Hindi case

Hindi nominals carry three layers of case-like marking ([masica-1991] §8.4, pp. 231–233). The
first is inflection: a noun has a direct, an oblique and a vocative form in each number, and a
declined adjective agrees with it in the direct–oblique contrast ([spencer-2005] (1)–(2);
[mohanan-1994] p. 62). The second is the postpositions *ne*, *ko*, *se*, *kaa*, *mẽ* and *par*,
which follow the oblique form and have one shape in both numbers ([masica-1991] p. 233;
[mohanan-1994] pp. 60–63). The third is the complex postpositions, which follow a genitive, as
*bacce-ke liye* 'for the child'.

Which of these are the cases is disputed. [masica-1991] treats the postpositions as formal cases
under the traditional labels, and finds no accusative among them (pp. 238–239); [mohanan-1994]
takes them to mark universal case features, *ko* both the accusative of objects and the dative of
goals (p. 67); [spencer-2005] takes the three inflected forms to be the only cases, the
postpositions being words that select the oblique. This file records the forms on which the three
agree: the inflected forms as `Hindi.Case`, and the postpositions with the functions they express.

The alignment is split by aspect: in the perfective the transitive subject takes *ne* and the
object the direct form, while elsewhere the subject is direct and the object takes *ko* when it is
marked at all ([blake-1994]).

## Main definitions

* `Hindi.Case`, `Hindi.Case.label`: the direct, oblique and vocative forms, and the comparative
  value each is named for.
* `Hindi.Noun`, `Hindi.nouns`: Spencer's two nouns with a vocative, by the form of each case in each
  number.
* `Hindi.Postposition`: the six postpositions, with their forms and the functions they express.
* `Hindi.alignment`: the alignment of case marking by aspect.

## Main results

* `Hindi.plural_larkaa_injective`: the plural of *laRkaa* 'boy' keeps the three cases apart, the
  vocative *laRko* against the oblique *laRkõ*.
* `Hindi.singular_oblique_eq_vocative`: the singular has one form for the oblique and the vocative.

## Implementation notes

The forms are [spencer-2005]'s transcription, `R` a retroflex rhotic, doubled vowels long and a
tilde marking nasalization. His table gives the inanimates *makaan* 'house' and *mez* 'table' no
vocative, and they are left out.

## References

* [masica-1991]
* [mohanan-1994]
* [spencer-2005]
* [blake-1994]
-/

@[expose] public section

namespace Hindi

/-! ### The inflected forms -/

/-- The three inflected forms of a noun. -/
inductive Case where
  /-- The direct form, the citation form and the form of an unmarked subject or object. -/
  | direct
  /-- The oblique form, which the postpositions follow. -/
  | oblique
  /-- The vocative. -/
  | vocative
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for, the nominative for the direct form. -/
def label : Case → _root_.Case
  | direct => .nom
  | oblique => .obl
  | vocative => .voc

/-- `forms direct oblique vocative` assigns each case its form. -/
def forms (direct oblique vocative : String) : Case → String
  | .direct => direct
  | .oblique => oblique
  | .vocative => vocative

end Case

/-- A noun by the form of each case in each number. -/
structure Noun where
  /-- The gloss. -/
  gloss : String
  /-- The singular form in each case. -/
  singular : Case → String
  /-- The plural form in each case. -/
  plural : Case → String

/-- *laRkaa* 'boy', masculine ([spencer-2005] (1)). -/
def larkaa : Noun where
  gloss := "boy"
  singular := Case.forms "laRkaa" "laRke" "laRke"
  plural := Case.forms "laRke" "laRkõ" "laRko"

/-- *laRkii* 'girl', feminine ([spencer-2005] (1)). -/
def larkii : Noun where
  gloss := "girl"
  singular := Case.forms "laRkii" "laRkii" "laRkii"
  plural := Case.forms "laRkiyãã" "laRkiyõ" "laRkiyo"

/-- The nouns. -/
def nouns : List Noun := [larkaa, larkii]

/-- The plural of *laRkaa* keeps the three cases apart, the vocative plural *-o* against the
oblique plural *-õ* ([masica-1991] p. 239). -/
theorem plural_larkaa_injective : Function.Injective larkaa.plural := by
  decide

/-- The singular has one form for the oblique and the vocative. -/
theorem singular_oblique_eq_vocative : ∀ n ∈ nouns, n.singular .oblique = n.singular .vocative := by
  decide

/-- The feminine singular has one form for all three cases. -/
theorem singular_larkii_eq (c : Case) : larkii.singular c = "laRkii" := by
  cases c <;> rfl

/-! ### The postpositions -/

/-- The postpositions that follow the oblique form, [mohanan-1994]'s case clitics and
[masica-1991]'s Layer II. -/
inductive Postposition where
  /-- *ne*, of the agent. -/
  | ne
  /-- *ko*, of the goal and the object. -/
  | ko
  /-- *se*, of the instrument and the source. -/
  | se
  /-- *kaa*, of the possessor, which agrees with the possessed noun. -/
  | kaa
  /-- *mẽ* 'in'. -/
  | me
  /-- *par* 'on, at'. -/
  | par
  deriving DecidableEq, Fintype, Repr

namespace Postposition

/-- The form of a postposition, *kaa* in its masculine singular direct form. -/
def form : Postposition → String
  | ne => "ne"
  | ko => "ko"
  | se => "se"
  | kaa => "kaa"
  | me => "mẽ"
  | par => "par"

/-- The comparative values a postposition expresses ([mohanan-1994] p. 67; [masica-1991]
p. 238): *ne* the agent of a perfective verb, *ko* the goal and the object, *se* the instrument,
the source and the companion, *kaa* the possessor, and *mẽ* and *par* location. -/
def functions : Postposition → Finset _root_.Case
  | ne => {.erg}
  | ko => {.dat, .acc}
  | se => {.inst, .abl, .com}
  | kaa => {.gen}
  | me => {.loc}
  | par => {.loc}

end Postposition

/-! ### Alignment -/

/-- The alignment by aspect: ergative in the perfective, where the transitive subject takes
*ne*, and accusative otherwise. -/
def alignment : Aspect.Perfectivity → Alignment.AlignmentType
  | .perfective => .ergative
  | .imperfective => .accusative

end Hindi
