import Linglib.Features.Complementation

/-!
# Bulgarian Clausal Embedding Inventory

[krapova-2010]

Bulgarian (Slavic, ISO 639-3 `bul`) inventory of complement-taking
predicates around the invariant complementizer *deto*. [krapova-2010]
§5: *deto*-complements are available exactly to emotive factives that
also select a *za*-PP — factivity is necessary but not sufficient
(*văzmuštavam se* 'resent' is factive yet *deto*-excluded, her (58a)) —
and where available, *deto* "seems to freely alternate" with default
*če*, partly conditioned by register (colloquial; her fn. 45). The
*za*-PP selection biconditional and the hidden-relative analysis are
paper-specific and live study-side; this file carries the two directly
observed axes. Both predicate lists are open-ended in the paper ("such
as …", "e.g. …") — the inventories below are the predicates Krapova
names, not the full classes.

Forms follow the paper's scientific transliteration (*ă* for ъ; several
citation forms are multiword impersonals with an experiencer clitic,
e.g. *jad me e*).
-/

namespace Bulgarian.Clause

/-! ### Predicate schema -/

/-- Whether a predicate's notional complement may be introduced by the
    invariant complementizer *deto* ([krapova-2010] §5). Two values
    because only two are attested: *deto* is never obligatory — where
    possible it alternates with default *če* (which her fn. 46 says
    "may show up in all complement clauses") — and the alternation is
    partly register-conditioned (colloquial, fn. 45). -/
inductive DetoAvailability where
  /-- *deto* possible, alternating with *če* ((56)–(57)). -/
  | alternating
  /-- *če* only ((58)). -/
  | excluded
  deriving DecidableEq, Repr

/-- [krapova-2010] §5's two-way factivity split: "true" factives
    including the emotives ([kiparsky-kiparsky-1970]; Krapova cites the
    1971 reprint) vs semi-factives ([karttunen-1971]'s term). Class-
    level assertions — her projection trials ((57)) run on *săžaljavam*
    and *vinoven săm* only. -/
inductive Factivity where
  | trueFactive
  | semiFactive
  deriving DecidableEq, Repr

/-- A Bulgarian complement-taking predicate.

    - `ctpClass`: [noonan-2007] category; `none` where unclear.
    - `factivity`, `deto`: the two observed axes ([krapova-2010] §5). -/
structure BulgarianEmbedder where
  form : String
  gloss : String
  ctpClass : Option CTPClass
  factivity : Factivity
  deto : DetoAvailability
  deriving DecidableEq, Repr

/-! ### The *deto*-takers — emotive factives ([krapova-2010] §5)

"Predicates of emotive reaction or emotive appraisal"; all
[noonan-2007]-commentative, all "true" factive. -/

/-- *săžaljavam* 'regret' — the projection-trial predicate ((57a), (57c));
    the *zadeto* variant is exhibited at [deal-2026] (49). -/
def sazhaljavam : BulgarianEmbedder where
  form := "săžaljavam"; gloss := "regret"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .alternating

/-- *vinoven săm* 'be one's fault' ((57b), under matrix question). -/
def vinovenSam : BulgarianEmbedder where
  form := "vinoven săm"; gloss := "be one's fault"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .alternating

/-- *jad me e* 'be sorry; regret' ((56b)). -/
def jadMeE : BulgarianEmbedder where
  form := "jad me e"; gloss := "be sorry; regret"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .alternating

/-- *radvam se* 'be happy'. -/
def radvamSe : BulgarianEmbedder where
  form := "radvam se"; gloss := "be happy"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .alternating

/-- *nedovolstvam* 'be dissatisfied'. -/
def nedovolstvam : BulgarianEmbedder where
  form := "nedovolstvam"; gloss := "be dissatisfied"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .alternating

/-- *pritesnjavam se* 'worry'. -/
def pritesnjavamSe : BulgarianEmbedder where
  form := "pritesnjavam se"; gloss := "worry"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .alternating

/-- *žal mi e* 'be sorry'. -/
def zhalMiE : BulgarianEmbedder where
  form := "žal mi e"; gloss := "be sorry"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .alternating

/-- *măčno mi e* 'be sad'. -/
def machnoMiE : BulgarianEmbedder where
  form := "măčno mi e"; gloss := "be sad"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .alternating

/-- *sram me e* 'feel ashamed'. -/
def sramMeE : BulgarianEmbedder where
  form := "sram me e"; gloss := "feel ashamed"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .alternating

/-! ### The *deto*-excluded factives

"True" factives on [kiparsky-kiparsky-1970]'s list that nonetheless
reject *deto* ([krapova-2010] pp. 1265–1266) — her evidence that
factivity does not suffice. -/

/-- *văzmuštavam se* 'resent' ((58a)) — the named dissociation witness:
    emotive and factive, but takes no *za*-PP and no *deto*. -/
def vazmushtavamSe : BulgarianEmbedder where
  form := "văzmuštavam se"; gloss := "resent"
  ctpClass := some .commentative
  factivity := .trueFactive
  deto := .excluded

/-- *razbiram* 'comprehend'. -/
def razbiram : BulgarianEmbedder where
  form := "razbiram"; gloss := "comprehend"
  ctpClass := some .knowledge
  factivity := .trueFactive
  deto := .excluded

/-- *vzemam previd* 'take into account' (printed *previd*, beside
    *imam predvid* — transcribed verbatim). -/
def vzemamPrevid : BulgarianEmbedder where
  form := "vzemam previd"; gloss := "take into account"
  ctpClass := none
  factivity := .trueFactive
  deto := .excluded

/-- *imam predvid* 'bear in mind'. -/
def imamPredvid : BulgarianEmbedder where
  form := "imam predvid"; gloss := "bear in mind"
  ctpClass := none
  factivity := .trueFactive
  deto := .excluded

/-- *prenebregvam* 'ignore'. -/
def prenebregvam : BulgarianEmbedder where
  form := "prenebregvam"; gloss := "ignore"
  ctpClass := none
  factivity := .trueFactive
  deto := .excluded

/-- *griža se* 'take care' (on [krapova-2010]'s reading of the
    [kiparsky-kiparsky-1970] factive list). -/
def grizhaSe : BulgarianEmbedder where
  form := "griža se"; gloss := "take care"
  ctpClass := none
  factivity := .trueFactive
  deto := .excluded

/-! ### The *deto*-excluded semi-factives ([krapova-2010] p. 1266) -/

/-- *znaja* 'know'. -/
def znaja : BulgarianEmbedder where
  form := "znaja"; gloss := "know"
  ctpClass := some .knowledge
  factivity := .semiFactive
  deto := .excluded

/-- *pomnja* 'remember'. -/
def pomnja : BulgarianEmbedder where
  form := "pomnja"; gloss := "remember"
  ctpClass := some .knowledge
  factivity := .semiFactive
  deto := .excluded

/-- *otkrivam* 'find out'. -/
def otkrivam : BulgarianEmbedder where
  form := "otkrivam"; gloss := "find out"
  ctpClass := some .knowledge
  factivity := .semiFactive
  deto := .excluded

/-- *viždam* 'see' (the propositional reading). -/
def vizhdam : BulgarianEmbedder where
  form := "viždam"; gloss := "see"
  ctpClass := some .perception
  factivity := .semiFactive
  deto := .excluded

/-- *čuvam* 'hear' (the propositional reading). -/
def chuvam : BulgarianEmbedder where
  form := "čuvam"; gloss := "hear"
  ctpClass := some .perception
  factivity := .semiFactive
  deto := .excluded

/-- *zabeljazvam* 'notice' (perception/knowledge borderline). -/
def zabeljazvam : BulgarianEmbedder where
  form := "zabeljazvam"; gloss := "notice"
  ctpClass := none
  factivity := .semiFactive
  deto := .excluded

/-! ### Inventories -/

/-- The predicates [krapova-2010] names (open-ended lists — see module
    docstring). -/
def allEmbedders : List BulgarianEmbedder :=
  [sazhaljavam, vinovenSam, jadMeE, radvamSe, nedovolstvam,
   pritesnjavamSe, zhalMiE, machnoMiE, sramMeE,
   vazmushtavamSe, razbiram, vzemamPrevid, imamPredvid, prenebregvam,
   grizhaSe, znaja, pomnja, otkrivam, vizhdam, chuvam, zabeljazvam]

/-- The *deto*-takers. -/
def detoTakers : List BulgarianEmbedder :=
  allEmbedders.filter (·.deto == .alternating)

/-- Drift sentry: the *deto*-takers are exactly the nine emotive
    factives Krapova names. -/
theorem detoTakers_membership :
    detoTakers = [sazhaljavam, vinovenSam, jadMeE, radvamSe,
                  nedovolstvam, pritesnjavamSe, zhalMiE, machnoMiE,
                  sramMeE] := by decide

/-- Every *deto*-taker is a "true" (emotive) factive. -/
theorem detoTakers_all_trueFactive :
    detoTakers.all (·.factivity == .trueFactive) = true := by decide

/-- Factivity does not suffice for *deto*: "true" factives with *deto*
    excluded exist (*văzmuštavam se* and the transitive class) —
    [krapova-2010]'s dissociation. -/
theorem factivity_not_sufficient_for_deto :
    ∃ v ∈ allEmbedders,
      v.factivity = .trueFactive ∧ v.deto = .excluded := by decide

end Bulgarian.Clause
