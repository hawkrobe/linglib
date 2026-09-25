module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# San Martín Peras Mixtec complement-taking verbs

San Martín Peras Mixtec has no non-finite verb forms: every clause is completive, continuous or
irrealis, marked mostly by the tone of the first vowel, and every clause has an overt subject.
Complement-taking verbs take one of two kinds of clause. A finite complement is free in aspect
and in its subject. The other kind is always irrealis. Under verbs of wanting, hoping and
fearing, its subject may differ from the matrix subject, which *ná* can mark, and it may have a
time adverb of its own. Under verbs of trying, beginning, remembering and needing, its subject
is a clitic pronoun that refers to the matrix subject, and its time is the matrix time.

## Implementation notes

A finite complement is `ArgumentFrame.finiteClause`. An irrealis complement is
`subjunctiveFrame`, in [noonan-2007]'s subjunctive coding with an overt subject. A verb whose
irrealis complement has a coreferent subject carries `controlReading`, subject control; the
other irrealis-taking verbs carry no reading. The forms are the citation forms of the source's
predicate lists, with its tone marks, and each entry is named by its English gloss.

## References

* [ostrove-2026]
* [noonan-2007]
-/

@[expose] public section

namespace Mixtec.SMPM

/-- The irrealis complement is a declarative clause in the subjunctive coding with an overt
subject. -/
def subjunctiveFrame : ArgumentFrame :=
  ⟨some .nominal, [.clausal (some .subjunctive) (.only .declarative) (some (.overt none))]⟩

/-- The reading of an irrealis complement whose subject refers to the matrix subject. -/
def controlReading : Verb.Reading :=
  { frame := subjunctiveFrame, control := some .subjectControl }

/-! ### Verbs taking a finite complement ((27a)) -/

/-- *ka'án* 'think' takes a finite complement. -/
def think : Verb where
  form := "ka'án"
  frames := [.finiteClause]

/-- *nakanini* 'believe' takes a finite complement. -/
def believe : Verb where
  form := "nakanini"
  frames := [.finiteClause]

/-- *kuntàà ini* 'wonder' takes a finite complement. -/
def wonder : Verb where
  form := "kuntàà ini"
  frames := [.finiteClause]

/-- *kònì* 'know' takes a finite complement, and as 'know how to', optionally with *xá kasa*,
an irrealis complement with a coreferent subject ((27c)). -/
def know : Verb where
  form := "kònì"
  frames := [.finiteClause, subjunctiveFrame]
  readings := [controlReading]

/-- *kà'àn* 'say' takes a finite complement. -/
def say : Verb where
  form := "kà'àn"
  frames := [.finiteClause]
  speechActVerb := true

/-- *ntatǔ'un* 'chat' takes a finite complement. -/
def chat : Verb where
  form := "ntatǔ'un"
  frames := [.finiteClause]

/-- *káchi* 'said' takes a finite complement; it is defective, with only a completive form
(fn. 5). -/
def said : Verb where
  form := "káchi"
  frames := [.finiteClause]
  speechActVerb := true

/-- *kusijǐ ini* 'be happy' takes a finite complement. -/
def beHappy : Verb where
  form := "kusijǐ ini"
  frames := [.finiteClause]

/-- *ntsi'i ini* 'be sad' takes a finite complement. -/
def beSad : Verb where
  form := "ntsi'i ini"
  frames := [.finiteClause]

/-- *ntsiko ini* 'regret' takes a finite complement. -/
def regret : Verb where
  form := "ntsiko ini"
  frames := [.finiteClause]

/-! ### Verbs taking an irrealis complement with a free subject ((27b)) -/

/-- *kòni* 'want' takes an irrealis complement with a free subject. It is the one such verb out
of whose complement a quantifier can front (fn. 8). -/
def want : Verb where
  form := "kòni"
  frames := [subjunctiveFrame]

/-- *síso ini* 'hate' (lit. 'boil inside') takes an irrealis complement with a free subject. -/
def hate : Verb where
  form := "síso ini"
  frames := [subjunctiveFrame]

/-- *iyǐ'bi* 'fear, be afraid' takes an irrealis complement with a free subject. -/
def fear : Verb where
  form := "iyǐ'bi"
  frames := [subjunctiveFrame]

/-- *kuntasí* 'be scared' takes an irrealis complement with a free subject. -/
def beScared : Verb where
  form := "kuntasí"
  frames := [subjunctiveFrame]

/-- *nakwatu* 'pray' takes an irrealis complement with a free subject. -/
def pray : Verb where
  form := "nakwatu"
  frames := [subjunctiveFrame]

/-- *ntatu* 'hope' takes an irrealis complement with a free subject. -/
def hope : Verb where
  form := "ntatu"
  frames := [subjunctiveFrame]

/-- *xiinka* 'agree' takes an irrealis complement with a free subject. -/
def agree : Verb where
  form := "xiinka"
  frames := [subjunctiveFrame]

/-- *xǐinka* 'refuse' (lit. 'not agree') takes an irrealis complement with a free subject. -/
def refuse : Verb where
  form := "xǐinka"
  frames := [subjunctiveFrame]

/-- *chikàà ini* 'get the idea to' (lit. 'put inside') takes an irrealis complement with a free
subject. -/
def getIdea : Verb where
  form := "chikàà ini"
  frames := [subjunctiveFrame]

/-! ### Verbs taking an irrealis complement with a coreferent subject ((27c)) -/

/-- *ntukú* 'try' (lit. 'look for') takes an irrealis complement with a coreferent subject. -/
def try_ : Verb where
  form := "ntukú"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *nakú'ún ini* 'remember' takes an irrealis complement with a coreferent subject. -/
def remember : Verb where
  form := "nakú'ún ini"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *nantǒso* 'forget' takes an irrealis complement with a coreferent subject. -/
def forget : Verb where
  form := "nantǒso"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *kutô* 'like to' takes an irrealis complement with a coreferent subject. -/
def likeTo : Verb where
  form := "kutô"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *kixǎ* 'start, begin' takes an irrealis complement with a coreferent subject. -/
def start : Verb where
  form := "kixǎ"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *ntsi'i* 'finish' takes an irrealis complement with a coreferent subject. -/
def finish : Verb where
  form := "ntsi'i"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *xikwîn* 'stop' takes an irrealis complement with a coreferent subject. -/
def stop : Verb where
  form := "xikwîn"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *kò xikwîn* 'continue' (lit. 'not stop') takes an irrealis complement with a coreferent
subject. -/
def continue_ : Verb where
  form := "kò xikwîn"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *xiniñu'u* 'need' takes an irrealis complement with a coreferent subject. -/
def need : Verb where
  form := "xiniñu'u"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *sakwǎ'a* 'learn how to' takes an irrealis complement with a coreferent subject. -/
def learn : Verb where
  form := "sakwǎ'a"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- *kò ntaa* 'not bother' (lit. 'not climb') takes an irrealis complement with a coreferent
subject. -/
def notBother : Verb where
  form := "kò ntaa"
  frames := [subjunctiveFrame]
  readings := [controlReading]

/-- The complement-taking verbs of the source's lists. -/
def verbs : List Verb :=
  [think, believe, wonder, know, say, chat, said, beHappy, beSad, regret,
   want, hate, fear, beScared, pray, hope, agree, refuse, getIdea,
   try_, remember, forget, likeTo, start, finish, stop, continue_, need, learn, notBother]

end Mixtec.SMPM
