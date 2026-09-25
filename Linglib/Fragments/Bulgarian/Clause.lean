module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Bulgarian clausal embedding

Bulgarian (Slavic, ISO 639-3 `bul`) introduces a finite complement clause with the default
complementizer *če* 'that'. With a class of emotive factive predicates such as *săžaljavam*
'regret', *radvam se* 'be happy' and *sram me e* 'feel ashamed', the invariant relativizer
*deto* introduces the complement as well, alternating freely with *če* apart from register, and
also in the form *zadeto*. These predicates all take a *za* 'for' prepositional phrase beside
the clause. The transitive factives *razbiram* 'comprehend', *vzemam predvid* 'take into
account', *imam predvid* 'bear in mind', *prenebregvam* 'ignore' and *griža se* 'take care',
the emotive *văzmuštavam se* 'resent', which takes no *za* phrase, and the semi-factives
*znaja* 'know', *pomnja* 'remember', *otkrivam* 'find out', *viždam* 'see', *čuvam* 'hear' and
*zabeljazvam* 'notice' take *če* only.

Forms follow Krapova's scientific transliteration, *ă* for ъ; several citation forms are
multiword impersonals with an experiencer clitic, as *jad me e*. The predicate lists are the
ones Krapova names and are open-ended in the paper. The data are Krapova's; the hidden-relative
analysis of *deto* and the double requirement behind its distribution are stated in
`Studies/Deal2026.lean`.

## References

* [krapova-2010]
* [kiparsky-kiparsky-1970]
* [karttunen-1971b]
* [noonan-2007]
-/

@[expose] public section

namespace Bulgarian

/-! ### Clause-typers -/

/-- The default complementizer *če* 'that', available in every complement clause (fn. 46). -/
def che : Complementizer where
  morphs := [.free "če"]
  coding := some .indicative
  types := .only .declarative

/-- The invariant relativizer *deto*, which also introduces the complements of the emotive
factives that take a *za* phrase, alternating with *če* (§5). -/
def deto : Complementizer where
  morphs := [.free "deto"]
  coding := some .indicative
  types := .only .declarative

/-- The form *zadeto* of the same complementizer (fn. 45). -/
def zadeto : Complementizer where
  morphs := [.free "zadeto"]
  coding := some .indicative
  types := .only .declarative

/-! ### Predicates -/

/-- A Bulgarian complement-taking predicate is a verb entry with its [noonan-2007] class. -/
structure Verb extends _root_.Verb where
  /-- The [noonan-2007] class, `none` where the data give no clear assignment. -/
  predicateClass : Option Complement.PredicateClass

/-- The frames of an emotive factive, a finite clause or a *za* phrase (59). -/
def emotiveFrames : List ArgumentFrame := [ArgumentFrame.finiteClause, ArgumentFrame.pp]

/-- *săžaljavam* 'regret', the predicate of the projection trials (57). -/
def sazhaljavam : Verb where
  form := "săžaljavam"
  frames := emotiveFrames
  predicateClass := some .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full

/-- *vinoven săm* 'be one's fault' ((57b)). -/
def vinovenSam : Verb where
  form := "vinoven săm"
  frames := emotiveFrames
  predicateClass := some .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full

/-- *jad me e* 'be sorry, regret' ((56b)). -/
def jadMeE : Verb where
  form := "jad me e"
  frames := emotiveFrames
  predicateClass := some .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full

/-- *radvam se* 'be happy'. -/
def radvamSe : Verb where
  form := "radvam se"
  frames := emotiveFrames
  predicateClass := some .commentative
  attitude := some (.preferential (.degreeComparison .positive))
  factivity := some .full

/-- *nedovolstvam* 'be dissatisfied'. -/
def nedovolstvam : Verb where
  form := "nedovolstvam"
  frames := emotiveFrames
  predicateClass := some .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full

/-- *pritesnjavam se* 'worry'. -/
def pritesnjavamSe : Verb where
  form := "pritesnjavam se"
  frames := emotiveFrames
  predicateClass := some .commentative
  attitude := some (.preferential .uncertaintyBased)
  factivity := some .full

/-- *žal mi e* 'be sorry'. -/
def zhalMiE : Verb where
  form := "žal mi e"
  frames := emotiveFrames
  predicateClass := some .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full

/-- *măčno mi e* 'be sad'. -/
def machnoMiE : Verb where
  form := "măčno mi e"
  frames := emotiveFrames
  predicateClass := some .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full

/-- *sram me e* 'feel ashamed'. -/
def sramMeE : Verb where
  form := "sram me e"
  frames := emotiveFrames
  predicateClass := some .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full

/-- *văzmuštavam se* 'resent', emotive and factive but without a *za* phrase ((58a)). -/
def vazmushtavamSe : Verb where
  form := "văzmuštavam se"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := some .commentative
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full

/-- *razbiram* 'comprehend', a transitive factive on Kiparsky and Kiparsky's list. -/
def razbiram : Verb where
  form := "razbiram"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := some .knowledge
  attitude := some (.doxastic .veridical)
  factivity := some .full

/-- *vzemam predvid* 'take into account', printed *previd* in the paper. -/
def vzemamPredvid : Verb where
  form := "vzemam predvid"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := none
  attitude := some (.doxastic .veridical)
  factivity := some .full

/-- *imam predvid* 'bear in mind'. -/
def imamPredvid : Verb where
  form := "imam predvid"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := none
  attitude := some (.doxastic .veridical)
  factivity := some .full

/-- *prenebregvam* 'ignore'. -/
def prenebregvam : Verb where
  form := "prenebregvam"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := none
  attitude := some (.doxastic .veridical)
  factivity := some .full

/-- *griža se* 'take care'. -/
def grizhaSe : Verb where
  form := "griža se"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := none
  attitude := some (.doxastic .veridical)
  factivity := some .full

/-- *znaja* 'know', a semi-factive. -/
def znaja : Verb where
  form := "znaja"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := some .knowledge
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- *pomnja* 'remember'. -/
def pomnja : Verb where
  form := "pomnja"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := some .knowledge
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- *otkrivam* 'find out'. -/
def otkrivam : Verb where
  form := "otkrivam"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := some .knowledge
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- *viždam* 'see', on the propositional reading. -/
def vizhdam : Verb where
  form := "viždam"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := some .perception
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- *čuvam* 'hear', on the propositional reading. -/
def chuvam : Verb where
  form := "čuvam"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := some .perception
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- *zabeljazvam* 'notice'. -/
def zabeljazvam : Verb where
  form := "zabeljazvam"
  frames := [ArgumentFrame.finiteClause]
  predicateClass := none
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- The predicates Krapova names. -/
def verbs : List Verb :=
  [sazhaljavam, vinovenSam, jadMeE, radvamSe, nedovolstvam, pritesnjavamSe, zhalMiE, machnoMiE,
    sramMeE, vazmushtavamSe, razbiram, vzemamPredvid, imamPredvid, prenebregvam, grizhaSe,
    znaja, pomnja, otkrivam, vizhdam, chuvam, zabeljazvam]

/-- The predicates whose complement *deto* may introduce (§5). -/
def detoTakers : List Verb :=
  [sazhaljavam, vinovenSam, jadMeE, radvamSe, nedovolstvam, pritesnjavamSe, zhalMiE, machnoMiE,
    sramMeE]

end Bulgarian
