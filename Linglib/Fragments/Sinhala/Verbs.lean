module

/-!
# Colloquial Sinhala verb fragment

[beavers-zubair-2013] [gair-paolillo-1997] [inman-1993]

The verb roots whose anticausatives [beavers-zubair-2013] analyze, with their volitive and
involitive stems.

## Volitive/involitive stem alternation

Every Sinhala verb root has a volitive stem and most have an involitive stem. The stems are
distinguished by a thematic-vowel alternation: front vowel + *-e-* in the present for
involitive, *-a-* or *-i-* otherwise. The volitive defaults to a volitional / intentional
reading and the involitive to a non-volitional / accidental one, but the contrast is not
truth-conditional. *minimarann* 'murder' and *kapann* 'cut' have no involitive stem.

The causer sorts [beavers-zubair-2013] assign these roots, and the analysis that derives the
missing involitives and anticausatives from them, are in `Studies/BeaversZubair2013.lean`.
-/

@[expose] public section

namespace Sinhala.Verbs

/-- A Colloquial Sinhala verb root, with its volitive stem and its involitive stem, if any. -/
structure SinhalaVerb where
  gloss : String
  volitiveForm : String
  involitiveForm : Option String
  deriving Repr, BEq

/-- *kadann* (vol) / *kædenn* (invol) 'break'. -/
def kadann : SinhalaVerb :=
  { gloss := "break",
    volitiveForm := "kadann",
    involitiveForm := some "kædenn" }

/-- *gilann* (vol) / *gilenn* (invol) 'drown'. Volitive with a nominative subject is
    intentional drowning, involitive with the postposition *atiŋ* accidental drowning, and
    intransitive *gilenn* the anticausative 'drown' ([beavers-zubair-2013] exx. (2)–(3)). -/
def gilann : SinhalaVerb :=
  { gloss := "drown",
    volitiveForm := "gilann",
    involitiveForm := some "gilenn" }

/-- *marann* (vol) / *mærenn* (invol) 'kill/die', one of the detransitivizing roots of
    [beavers-zubair-2013] §3.2, exx. (14) and (17). -/
def marann : SinhalaVerb :=
  { gloss := "kill",
    volitiveForm := "marann",
    involitiveForm := some "mærenn" }

/-- *minimarann* 'murder', with no involitive form. -/
def minimarann : SinhalaVerb :=
  { gloss := "murder",
    volitiveForm := "minimarann",
    involitiveForm := none }

/-- *kapann* 'cut', with no involitive form. -/
def kapann : SinhalaVerb :=
  { gloss := "cut",
    volitiveForm := "kapann",
    involitiveForm := none }

/-- *vinaash-karann* (vol) / *vinaash-kerenn* (invol) 'destroy'. Unlike English and German
    *destroy*, it alternates ([beavers-zubair-2013] §7.4). -/
def vinaashKarann : SinhalaVerb :=
  { gloss := "destroy",
    volitiveForm := "vinaash-karann",
    involitiveForm := some "vinaash-kerenn" }

/-- The canonical inventory used in B&Z 2013's empirical arguments. -/
def allVerbs : List SinhalaVerb :=
  [kadann, gilann, marann, minimarann, kapann, vinaashKarann]

/-- Whether a verb has an involitive stem form. -/
def hasInvolitive (v : SinhalaVerb) : Bool := v.involitiveForm.isSome

end Sinhala.Verbs
