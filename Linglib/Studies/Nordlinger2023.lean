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
strategies tend to reduce it, so across the sampled profiles every nominal primary
strategy is bivalent and every monovalent construction is verb-marked
(`nominal_strategy_bivalent`, `monovalent_implies_verbal`), and the observed valency
follows the strategy's default everywhere but Wambaya, whose ergative-retaining
reflexive–reciprocal clause stays bivalent (`valency_follows_default_except_wambaya`).
Discontinuous reciprocals, with the reciprocants split across the subject and a comitative
phrase, are licensed exactly for lexically formed reciprocal verbs on the typology of
[siloni-2012], which the review's Greek, Swahili, Hungarian, French, and Czech judgments
confirm (`siloni_discontinuity_prediction`). The review's semantic typology after
[evans-et-al-2011b] and [dalrymple-et-al-1998], six shapes of mutual relation from strong
reciprocity to the ring, is realized as the relation shapes of `Semantics/Plurality/Reciprocal`
(`ReciprocityType.Realizes`), and the polysemies of the reciprocal marker beyond the
reflexive are exhibited by the Yakut collective and the East Futunan iterative readings.

## Implementation notes

Each profile records a marker inventory drawn from the language's fragment, the observed
valency, and, where the review discusses them, the formation locus and the discontinuity
judgment; the primary strategy is the inventory's first marker. Tonga's bivalent verbal
reciprocal and Malagasy's valency retention at functional structure, the review's
counterexamples to the tendency, are outside the sample.

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
  language : String
  iso : String
  /-- Marker inventory (primary strategy first), sourced from the
      language's `Fragments/{Lang}/Reciprocals.lean`. -/
  markers : List Marker
  /-- Observed valency of the primary construction -/
  valency : Valency
  /-- Formation locus of verb-marked reciprocals ([siloni-2012]) -/
  formation : Option Formation := none
  /-- Attested availability of the discontinuous reciprocal construction
      ([nordlinger-2023] §3.3 judgments), independent of `formation` so
      Siloni's prediction can be checked rather than stipulated -/
  discontinuousAttested : Option Bool := none
  deriving Repr, DecidableEq

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
  { language := "English", iso := "eng"
  , markers := English.Reciprocals.markers
  , valency := .bivalent }

/-- Russian: bipartite NP *drug druga* 'other other-ACC'
    ([nordlinger-2023] ex. 9, grouped with English *each other* as the
    bipartite strategy) plus reflexive-identical verbal postfix *-sja*
    (monovalent; ex. 31). Unlike French *se* (a separable clitic),
    *-sja* is a bound suffix. -/
def rpRussian : RecipProfile :=
  { language := "Russian", iso := "rus"
  , markers := Russian.Reciprocals.markers
  , valency := .bivalent }

/-- Swahili: verbal affix *-an-* (monovalent, distinct from reflexive
    *-ji-*; [nordlinger-2023] ex. 12). Forms discontinuous reciprocals
    with comitative *na* (ex. 37 from [hurst-2012], ex. 40 from
    [dimitriadis-2004]), hence lexicon-formed under Siloni's typology as
    presented in §3.3 ([siloni-2012] itself does not discuss Swahili).
    The morphological rule is `Swahili.Reciprocals.reciprocalAffix`. -/
def rpSwahili : RecipProfile :=
  { language := "Swahili", iso := "swh"
  , markers := Swahili.Reciprocals.markers
  , valency := .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true }

/-- Hungarian: verbal affix *-óz-* (monovalent; [nordlinger-2023]
    ex. 19, 30, citing [siloni-2008]). Lexicon-formed per [siloni-2012]'s
    own classification; forms discontinuous reciprocals with comitative
    *-val* (ex. 38, from [dimitriadis-2008]). -/
def rpHungarian : RecipProfile :=
  { language := "Hungarian", iso := "hun"
  , markers := Hungarian.Reciprocals.markers
  , valency := .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true }

/-- French: reciprocal clitic *se* (monovalent, reflexive-identical;
    [nordlinger-2023] ex. 28, 47) plus distinct bipartite *l'un l'autre*.
    The review argues (after [siloni-2008], [siloni-2012]) that *se* is
    not a reciprocal object: embedded *se*-reciprocals lack the "I"
    reading (ex. 35). Syntax-formed, and discontinuous reciprocals are
    ungrammatical (ex. 39). -/
def rpFrench : RecipProfile :=
  { language := "French", iso := "fra"
  , markers := French.Reciprocals.markers
  , valency := .monovalent
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
  { language := "Modern Greek", iso := "ell"
  , markers := Greek.StandardModern.Reciprocals.markers
  , valency := .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true }

/-- German: dedicated reciprocal pronoun *einander* alongside reflexive
    *sich* in reciprocal use. Both fill the object slot, preserving
    bivalent syntax. [siloni-2012] fn. 13 suggests German
    *sich*-reciprocals are syntactic reciprocal verbs; the review does
    not take this up, so no formation value is recorded. -/
def rpGerman : RecipProfile :=
  { language := "German", iso := "deu"
  , markers := German.Reciprocals.markers
  , valency := .bivalent }

/-- Mandarin: compound verb strategy *dǎ-lái-dǎ-qù*
    (beat-come-beat-go = 'beat each other'), single subject NP.
    Distinct from reflexive. [nordlinger-2023] ex. 13 (citing
    [konig-kokutani-2006]); [evans-2008] treats verb compounding as a
    multiclausal strategy. -/
def rpMandarin : RecipProfile :=
  { language := "Mandarin", iso := "cmn"
  , markers := Mandarin.Reciprocals.markers
  , valency := .monovalent }

/-- Wambaya: reciprocal clitic *-ngg-* (RR morpheme in the auxiliary),
    identical to reflexive. [nordlinger-2023] ex. 11 (citing
    [nordlinger-1998], p. 142). Bivalent: nominal subjects retain
    ergative marking under reciprocalization ([evans-et-al-2007]:
    transitivity is compromised but argument structure undisturbed);
    the NOM subject in ex. 11 is a free pronoun, which declines
    nominative/accusative regardless of transitivity
    ([nordlinger-1998]). -/
def rpWambaya : RecipProfile :=
  { language := "Wambaya", iso := "wmb"
  , markers := Wambaya.Reciprocals.markers
  , valency := .bivalent }

/-- Icelandic: bipartite NP *hvort annað*, each part independently
    inflected for case (*annað* takes the argument-position case,
    *hvort* agrees with the antecedent). Bivalent — the accusative on
    *annað* shows the clause remains transitive.
    [nordlinger-2023] ex. 17 (citing [hurst-nordlinger-2021]). -/
def rpIcelandic : RecipProfile :=
  { language := "Icelandic", iso := "isl"
  , markers := Icelandic.Reciprocals.markers
  , valency := .bivalent }

/-- Chicheŵa: verbal affix *-an-* (monovalent).
    [nordlinger-2023] ex. 20 (citing [dalrymple-et-al-1994]). -/
def rpChichewa : RecipProfile :=
  { language := "Chicheŵa", iso := "nya"
  , markers := Chichewa.Reciprocals.markers
  , valency := .monovalent }

/-- Czech: reciprocal clitic *se* (monovalent, reflexive-identical;
    [nordlinger-2023] ex. 29, citing [siloni-2008]), alongside the
    periphrastic *jeden druhého* 'each other' attested in
    [siloni-2012]'s Czech examples. Syntax-formed;
    discontinuous reciprocals are unavailable ([nordlinger-2023] p. 86,
    with French). -/
def rpCzech : RecipProfile :=
  { language := "Czech", iso := "ces"
  , markers := Czech.Reciprocals.markers
  , valency := .monovalent
  , formation := some .syntactic
  , discontinuousAttested := some false }

def allRecipProfiles : List RecipProfile :=
  [ rpEnglish, rpRussian, rpSwahili, rpHungarian, rpFrench
  , rpGreek, rpGerman, rpMandarin, rpWambaya, rpIcelandic
  , rpChichewa, rpCzech ]

/-! ### Strategy and valency -/

/-- Nominal and argument strategies preserve valency: every nominal primary strategy in the
sample is bivalent. -/
theorem nominal_strategy_bivalent :
    ∀ p ∈ allRecipProfiles, ∀ s ∈ p.primaryStrategy, s.isNominal = true →
      p.valency = .bivalent := by
  decide

/-- Verbal affixes reduce valency: every verbal-affix primary strategy is monovalent. -/
theorem verbal_affix_monovalent :
    ∀ p ∈ allRecipProfiles, p.primaryStrategy = some .verbalAffix → p.valency = .monovalent := by
  decide

/-- Conversely, no monovalent reciprocal construction in the sample is nominal. -/
theorem monovalent_implies_verbal :
    ∀ p ∈ allRecipProfiles, p.valency = .monovalent →
      ∀ s ∈ p.primaryStrategy, s.isNominal = false := by
  decide

/-- The observed valency is the strategy's default, derived in the substrate from the
detransitivizing coding-frame effect of reciprocalization, throughout the sample except
Wambaya, whose ergative-retaining clause stays bivalent ([evans-et-al-2007]). -/
theorem valency_follows_default_except_wambaya :
    ∀ p ∈ allRecipProfiles, p.iso ≠ "wmb" →
      ∀ s ∈ p.primaryStrategy, p.valency = s.defaultValency := by
  decide

/-! ### Discontinuous reciprocals -/

/-- Discontinuous reciprocals are possible exactly for lexically formed reciprocal verbs
([siloni-2008], [siloni-2012]): every profile carrying a formation locus and a discontinuity
judgment satisfies the value the locus predicts. -/
theorem siloni_discontinuity_prediction :
    ∀ p ∈ allRecipProfiles, ∀ f ∈ p.formation, ∀ d ∈ p.discontinuousAttested,
      (Siloni2012.predictedProperties f).discontinuous = d := by
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
  , readings := [.reciprocal, .collective, .sociative] }

/-- East Futunan *fe-...-ʼaki*: reciprocal + iterative — *fe-tapa-ʼaki*
    'sparkle again and again' ([nordlinger-2023] ex. 50, citing
    [nedjalkov-2007b]). -/
def eastFutunanFeAki : Marker :=
  { form := "fe-...-ʼaki", strategy := .verbalAffix
  , readings := [.reciprocal, .iterative] }

end Nordlinger2023
