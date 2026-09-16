import Linglib.Syntax.Reciprocal
import Linglib.Studies.Siloni2012
import Linglib.Semantics.Plurality.Reciprocal
import Linglib.Fragments.English.Reciprocals
import Linglib.Fragments.Chichewa.Reciprocals
import Linglib.Fragments.Romance.French.Reciprocals
import Linglib.Fragments.German.Reciprocals
import Linglib.Fragments.Greek.StandardModern.Reciprocals
import Linglib.Fragments.Hungarian.Reciprocals
import Linglib.Fragments.Icelandic.Reciprocals
import Linglib.Fragments.Mandarin.Reciprocals
import Linglib.Fragments.Slavic.Czech.Reciprocals
import Linglib.Fragments.Slavic.Russian.Reciprocals
import Linglib.Fragments.Swahili.Reciprocals
import Linglib.Fragments.Wambaya.Reciprocals

/-!
# Nordlinger (2023): The Typology of Reciprocal Constructions

This file formalizes the generalizations of the review of reciprocal constructions in
[nordlinger-2023], which organizes the classificatory work of [nedjalkov-2007a],
[maslova-2008], [evans-2008], and [siloni-2012] around two correlations. Nominal and
argument strategies tend to preserve the valency of the base verb while verb-marking
strategies tend to reduce it: across the sampled profiles every valency indicator the review
reports agrees with the strategy's default, derived in the substrate from the coding-frame
effect of reciprocalization (`valency_follows_default`), so no nominal primary strategy reads
monovalent and every monovalent reading is verb-marked (`nominal_strategy_bivalent`,
`monovalent_implies_verbal`). The tendency is not absolute: Tonga's verb-marked reciprocal
keeps both argument NPs (`tonga_counterexample`), and in the Australian cases of
[evans-et-al-2007] the indicators disagree, an ergative subject beside an obligatorily
absent object in Kuuk Thaayorre and intransitive agreement beside an incorporated patient in
Dalabon (`kuukThaayorre_mixed`, `dalabon_mixed`).
Discontinuous reciprocals, with the reciprocants split across the subject and a comitative
phrase, are licensed exactly for lexically formed reciprocal verbs on the typology of
[siloni-2012], which the review's Greek, Swahili, Hungarian, French, and Czech judgments
confirm (`siloni_discontinuity_prediction`). The review's semantic typology after
[evans-et-al-2011b] and [dalrymple-et-al-1998], six shapes of mutual relation from strong
reciprocity to the ring, is realized as the relation shapes of `Semantics/Plurality/Reciprocal`
(`ReciprocityType.Realizes`), and the polysemies of the reciprocal marker beyond the
reflexive are exhibited by the Yakut collective and the East Futunan iterative readings.

## Implementation notes

Each profile records a marker inventory drawn from the language's fragment, what each valency
indicator the review reports says, and, where the review discusses them, the formation locus
and the discontinuity judgment; the primary strategy is the inventory's first marker. The
mixed-effect languages have no fragment, so their markers are the review's examples. Malagasy,
bivalent at f-structure and monovalent at c-structure on [hurst-2012]'s analysis, splits
levels rather than indicators and is not profiled.

## References

* [nordlinger-2023]
* [nedjalkov-2007a]
* [nedjalkov-2007b]
* [maslova-2008]
* [evans-2008]
* [siloni-2008]
* [siloni-2012]
* [dalrymple-et-al-1998]
* [evans-et-al-2011b]
* [evans-et-al-2007]
* [dimitriadis-2008]
* [hurst-2012]
* [majid-et-al-2011]
-/

namespace Nordlinger2023

open Reciprocal

/-! ### Reciprocal profiles -/

/-- Per-language reciprocal profile: the marker inventory (primary strategy
    first) plus the observed valency, formation locus, and discontinuity
    judgments from the review; the primary strategy is derived from the inventory. -/
structure RecipProfile where
  /-- Marker inventory (primary strategy first), sourced from the
      language's `Fragments/{Lang}/Reciprocals.lean`. -/
  markers : List Marker
  /-- What each valency indicator the review reports says of the primary construction. -/
  valency : ValencyProfile
  /-- Formation locus of verb-marked reciprocals ([siloni-2012]) -/
  formation : Option Formation := none
  /-- Attested availability of the discontinuous reciprocal construction
      ([nordlinger-2023] §3.3 judgments), independent of `formation` so
      Siloni's prediction can be checked rather than stipulated -/
  discontinuousAttested : Option Bool := none
  deriving DecidableEq

/-- Primary strategy: the strategy of the inventory's first marker. -/
def RecipProfile.primaryStrategy (p : RecipProfile) : Option Strategy :=
  p.markers.head?.map (·.strategy)

-- Language data: 12 reciprocal profiles from [nordlinger-2023]

/-- English: bipartite NP *each other* (bivalent, distinct from reflexive;
    [nordlinger-2023] ex. 1b) plus lexical reciprocals (*quarrel*, *meet*,
    ex. 7). Per [siloni-2012] the lexical class is lexicon-formed, but
    *kiss*/*hug* resist the discontinuous construction (fn. 32), so no
    formation-level discontinuity value is recorded. Expresses all six
    reciprocity types (ex. 44). -/
def rpEnglish : RecipProfile :=
  { markers := English.Reciprocals.markers
  , valency := .single .objectSlot .bivalent }

/-- Russian: bipartite NP *drug druga* 'other other-ACC'
    ([nordlinger-2023] ex. 9, grouped with English *each other* as the
    bipartite strategy) plus reflexive-identical verbal postfix *-sja*
    (monovalent; ex. 31). Unlike French *se* (a separable clitic),
    *-sja* is a bound suffix. -/
def rpRussian : RecipProfile :=
  { markers := Russian.Reciprocals.markers
  , valency := .single .objectSlot .bivalent }

/-- Swahili: verbal affix *-an-* (monovalent, distinct from reflexive
    *-ji-*; [nordlinger-2023] ex. 12). Forms discontinuous reciprocals
    with comitative *na* (ex. 37 from [hurst-2012], ex. 40 from
    [dimitriadis-2004]), hence lexicon-formed under Siloni's typology as
    presented in §3.3 ([siloni-2012] itself does not discuss Swahili).
    The morphological rule is `Swahili.Reciprocals.reciprocalAffix`. -/
def rpSwahili : RecipProfile :=
  { markers := Swahili.Reciprocals.markers
  , valency := .single .objectSlot .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true }

/-- Hungarian: verbal affix *-óz-* (monovalent; [nordlinger-2023]
    ex. 19, 30, citing [siloni-2008]). Lexicon-formed per [siloni-2012]'s
    own classification; forms discontinuous reciprocals with comitative
    *-val* (ex. 38, from [dimitriadis-2008]). -/
def rpHungarian : RecipProfile :=
  { markers := Hungarian.Reciprocals.markers
  , valency := .single .objectSlot .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true }

/-- French: reciprocal clitic *se* (monovalent, reflexive-identical;
    [nordlinger-2023] ex. 28, 47) plus distinct bipartite *l'un l'autre*.
    The review argues (after [siloni-2008], [siloni-2012]) that *se* is
    not a reciprocal object: embedded *se*-reciprocals lack the "I"
    reading (ex. 35). Syntax-formed, and discontinuous reciprocals are
    ungrammatical (ex. 39). -/
def rpFrench : RecipProfile :=
  { markers := French.Reciprocals.markers
  , valency := .single .objectSlot .monovalent
  , formation := some .syntactic
  , discontinuousAttested := some false }

/-- Greek (Modern): nonactive voice morphology (monovalent, reflexive-
    identical in form) plus a distinct periphrastic reciprocal (*o enas
    ton allon*, [maslova-nedjalkov-2013]). Forms discontinuous
    reciprocals with *me* 'with': "O Giannis filithike me ti Maria"
    ([nordlinger-2023] ex. 27b, 36, from [dimitriadis-2008]) — hence
    lexicon-formed under Siloni's typology as presented in §3.3
    ([siloni-2012] itself does not discuss Greek). -/
def rpGreek : RecipProfile :=
  { markers := Greek.StandardModern.Reciprocals.markers
  , valency := .single .objectSlot .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true }

/-- German: dedicated reciprocal pronoun *einander* alongside reflexive
    *sich* in reciprocal use. Both fill the object slot, preserving
    bivalent syntax. [siloni-2012] fn. 13 suggests German
    *sich*-reciprocals are syntactic reciprocal verbs; the review does
    not take this up, so no formation value is recorded. -/
def rpGerman : RecipProfile :=
  { markers := German.Reciprocals.markers
  , valency := .single .objectSlot .bivalent }

/-- Mandarin: compound verb strategy *dǎ-lái-dǎ-qù*
    (beat-come-beat-go = 'beat each other'), single subject NP.
    Distinct from reflexive. [nordlinger-2023] ex. 13 (citing
    [konig-kokutani-2006]); [evans-2008] treats verb compounding as a
    multiclausal strategy. -/
def rpMandarin : RecipProfile :=
  { markers := Mandarin.Reciprocals.markers
  , valency := .single .objectSlot .monovalent }

/-- Wambaya: bound reciprocal pronoun *-ngg-* (RR morpheme in the
    auxiliary's pronominal complex), identical to reflexive
    ([nordlinger-2023] ex. 11, citing [nordlinger-1998]); grouped with
    the NP strategies of ex. 9–10 by [konig-kokutani-2006] and
    [evans-2008]. The RR morpheme fills the object position of the
    pronominal complex, the bound-pronominal argument slot that defines
    the argument strategies (ex. 18b for Warlpiri), so that indicator
    reads bivalent. -/
def rpWambaya : RecipProfile :=
  { markers := Wambaya.Reciprocals.markers
  , valency := .single .objectSlot .bivalent }

/-- Icelandic: bipartite NP *hvort annað*, each part independently
    inflected for case (*annað* takes the argument-position case,
    *hvort* agrees with the antecedent). Bivalent — the accusative on
    *annað* shows the clause remains transitive.
    [nordlinger-2023] ex. 17 (citing [hurst-nordlinger-2021]). -/
def rpIcelandic : RecipProfile :=
  { markers := Icelandic.Reciprocals.markers
  , valency := .single .objectSlot .bivalent }

/-- Chicheŵa: verbal affix *-an-* (monovalent).
    [nordlinger-2023] ex. 20 (citing [dalrymple-et-al-1994]). -/
def rpChichewa : RecipProfile :=
  { markers := Chichewa.Reciprocals.markers
  , valency := .single .objectSlot .monovalent }

/-- Czech: reciprocal clitic *se* (monovalent, reflexive-identical;
    [nordlinger-2023] ex. 29, citing [siloni-2008]), alongside the
    periphrastic *jeden druhého* 'each other' attested in
    [siloni-2012]'s Czech examples. Syntax-formed;
    discontinuous reciprocals are unavailable ([nordlinger-2023] p. 86,
    with French). -/
def rpCzech : RecipProfile :=
  { markers := Czech.Reciprocals.markers
  , valency := .single .objectSlot .monovalent
  , formation := some .syntactic
  , discontinuousAttested := some false }

def allRecipProfiles : List RecipProfile :=
  [ rpEnglish, rpRussian, rpSwahili, rpHungarian, rpFrench
  , rpGreek, rpGerman, rpMandarin, rpWambaya, rpIcelandic
  , rpChichewa, rpCzech ]

/-! ### Strategy and valency -/

/-- Every valency indicator the review reports for a sampled construction agrees with its
strategy's default, derived in the substrate from the detransitivizing coding-frame effect of
reciprocalization. -/
theorem valency_follows_default :
    ∀ p ∈ allRecipProfiles, ∀ s ∈ p.primaryStrategy,
      p.valency.Unanimous s.defaultValency := by
  decide

variable {p : RecipProfile} {s : Strategy}

/-- Nominal and argument strategies preserve valency: no nominal primary strategy in the
sample reads monovalent on any indicator. -/
theorem nominal_strategy_bivalent (hp : p ∈ allRecipProfiles) (hs : s ∈ p.primaryStrategy)
    (h : s.IsNominal) : ¬ p.valency.Reads .monovalent := fun hr ↦
  (Strategy.defaultValency_eq_monovalent_iff s).1 (valency_follows_default p hp s hs _ hr).symm h

/-- Conversely, a monovalent reading in the sample comes only from a verb-marked strategy. -/
theorem monovalent_implies_verbal (hp : p ∈ allRecipProfiles) (hs : s ∈ p.primaryStrategy)
    (h : p.valency.Reads .monovalent) : ¬ s.IsNominal :=
  (Strategy.defaultValency_eq_monovalent_iff s).1 (valency_follows_default p hp s hs _ h).symm

/-! ### Mixed transitivity effects

The tendency is not absolute. Tonga's verb-marked reciprocal keeps both reciprocants as
argument NPs ([maslova-2008]), and in the Australian cases of [evans-et-al-2007] the
indicators of valency disagree with one another. -/

/-- Warlpiri *-nyanu*: the reflexive–reciprocal bound pronoun in the object slot of the
pronominal complex ([nordlinger-2023] ex. 18b, 48). -/
def warlpiriNyanu : Marker :=
  { form := "-nyanu", strategy := .boundPronoun, readings := {.reciprocal, .reflexive} }

/-- Warlpiri: the object bound pronoun and the ergative subject agree that the clause stays
transitive (ex. 18b). -/
def rpWarlpiri : RecipProfile :=
  { markers := [warlpiriNyanu]
  , valency := fun | .objectSlot | .subjectCase => some .bivalent | _ => none }

/-- Kuuk Thaayorre *-rr*: the reciprocal verbal suffix (ex. 25). -/
def kuukThaayorreRr : Marker := { form := "-rr", strategy := .verbalAffix }

/-- Kuuk Thaayorre: the object NP is obligatorily absent, yet the subject keeps ergative case
(ex. 25). -/
def rpKuukThaayorre : RecipProfile :=
  { markers := [kuukThaayorreRr]
  , valency := fun | .objectSlot => some .monovalent | .subjectCase => some .bivalent
                   | _ => none }

/-- Dalabon *-rr*: the reflexive–reciprocal verbal suffix (ex. 26b). -/
def dalabonRr : Marker :=
  { form := "-rr", strategy := .verbalAffix, readings := {.reciprocal, .reflexive} }

/-- Dalabon: the verb takes the intransitive subject pronominal series yet incorporates the
patient's body part, as in the transitive clause (ex. 26). -/
def rpDalabon : RecipProfile :=
  { markers := [dalabonRr]
  , valency := fun | .agreement => some .monovalent | .incorporation => some .bivalent
                   | _ => none }

/-- Tonga *-an*: the reciprocal verbal suffix (ex. 21, from [maslova-2008]). -/
def tongaAn : Marker := { form := "-an", strategy := .verbalAffix }

/-- Tonga: both reciprocants are argument NPs of the verb-marked reciprocal (ex. 21). -/
def rpTonga : RecipProfile :=
  { markers := [tongaAn], valency := .single .objectSlot .bivalent }

/-- Warlpiri's two indicators agree with the bound-pronoun default. -/
theorem warlpiri_follows_default :
    ∀ s ∈ rpWarlpiri.primaryStrategy, rpWarlpiri.valency.Unanimous s.defaultValency := by
  decide

/-- The Kuuk Thaayorre and Dalabon indicators disagree, so neither construction is unanimous
on any default. -/
theorem kuukThaayorre_mixed : rpKuukThaayorre.valency.Mixed := by decide

theorem dalabon_mixed : rpDalabon.valency.Mixed := by decide

/-- Tonga contradicts the tendency: a verb-marked reciprocal whose object slot stays filled. -/
theorem tonga_counterexample :
    ∀ s ∈ rpTonga.primaryStrategy, ¬ s.IsNominal ∧ rpTonga.valency.Reads .bivalent := by
  decide

/-! ### Discontinuous reciprocals -/

/-- Discontinuous reciprocals are possible exactly for lexically formed reciprocal verbs
([siloni-2008], [siloni-2012]): every profile carrying a formation locus and a discontinuity
judgment satisfies the value the locus predicts. -/
theorem siloni_discontinuity_prediction :
    ∀ p ∈ allRecipProfiles, ∀ f ∈ p.formation, ∀ d ∈ p.discontinuousAttested,
      (Siloni2012.Property.discontinuous.Holds f ↔ d = true) := by
  decide

/-! ### Semantic reciprocity types (§4) -/

/-- Semantic type of reciprocal relation.

    [nordlinger-2023] §4 presents the semantic typology of
    [evans-et-al-2011b], who take as their starting point the symmetric
    relations identified by [dalrymple-et-al-1998] and distinguish six
    types of mutual relation ([nordlinger-2023] ex. 44,
    [evans-et-al-2011b] p. 8):

    - `strong`: every participant reciprocates with every other
      ("The members of this family love one another.")
    - `pairwise`: participants are paired off
      ("The people at the dinner party were married to one another.")
    - `chain`: sequential, each with the next
      ("The graduating students followed one another up onto the stage.")
    - `radial`: one central participant acts on all others
      ("The teacher and her pupils intimidated one another.")
    - `melee`: widespread but not exhaustive reciprocation
      ("The drunks in the pub were punching one another.")
    - `ring`: circular chain, last links back to first
      ("The children chased each other round in a ring.") -/
inductive ReciprocityType where
  | strong
  | pairwise
  | chain
  | radial
  | melee
  | ring
  deriving DecidableEq, Repr

/-- The relation shape each configurational label denotes over a
    participant plurality — [majid-et-al-2011]'s extensional schemas as
    the exact-extension conditions of `Reciprocal`.
    Symmetry and participant-exhaustiveness are theorems there
    (`ChainConfig.not_pairSymmetricOn`,
    `RadialConfig.inclusiveAlternativeOrdering`, melee failing
    `InclusiveAlternativeOrdering` by definition, …), not stipulated
    features of the labels. -/
def ReciprocityType.Realizes {A : Type*} [DecidableEq A] :
    ReciprocityType → (A → A → Prop) → Finset A → Prop
  | .strong,   R, X => Reciprocal.StrongReciprocity R X
  | .pairwise, R, X => Reciprocal.PairwiseConfig R X
  | .chain,    R, X => Reciprocal.ChainConfig R X
  | .radial,   R, X => Reciprocal.RadialConfig R X
  | .melee,    R, X => Reciprocal.MeleeConfig R X
  | .ring,     R, X => Reciprocal.RingConfig R X

/-! ### Polysemous markers beyond the sample

Reflexive polysemy is carried by the profile inventories above (French
*se*, German *sich*, Wambaya *-ngg-*, Russian *-sja*). The review's further
polysemy types are attested by markers outside the 12-language sample. -/

/-- Yakut *-üs*: reciprocal + collective/sociative — *ölör-üs* 'kill
    each other' or 'kill somebody together' ([nordlinger-2023] ex. 49,
    citing [nedjalkov-2007b]). -/
def yakutUs : Marker :=
  { form := "-üs", strategy := .verbalAffix
  , readings := {.reciprocal, .collective, .sociative} }

/-- East Futunan *fe-...-ʼaki*: reciprocal + iterative — *fe-tapa-ʼaki*
    'sparkle again and again' ([nordlinger-2023] ex. 50, citing
    [nedjalkov-2007b]). -/
def eastFutunanFeAki : Marker :=
  { form := "fe-...-ʼaki", strategy := .verbalAffix
  , readings := {.reciprocal, .iterative} }

end Nordlinger2023
