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
strategies tend to reduce it: wherever the review's valency indicators agree, they agree
with the strategy's default, derived in the substrate from the coding-frame effect of
reciprocalization (`valency_follows_default`), so no nominal strategy reads monovalent and
every monovalent reading is verb-marked (`nominal_strategy_bivalent`,
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

Each language's construction takes its marker from the language's fragment, or from the
review's example where no fragment exists (Warlpiri, Kuuk Thaayorre, Dalabon, Tonga), and
records the valency indicators the review reports. The formation locus is [siloni-2012]'s own
classification where it covers the language and the review's extension otherwise. Malagasy,
bivalent at f-structure and monovalent at c-structure on [hurst-2012]'s analysis, splits
levels rather than indicators and is not represented.

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

/-! ### The review's languages -/

/-- The languages whose reciprocal constructions the review describes. -/
inductive Language where
  | english | russian | swahili | hungarian | french | greek | german | mandarin
  | wambaya | icelandic | chichewa | czech | warlpiri | kuukThaayorre | dalabon | tonga
  deriving DecidableEq, Fintype

/-- Warlpiri *-nyanu*: the reflexive–reciprocal bound pronoun in the object slot of the
pronominal complex ([nordlinger-2023] ex. 18b, 48). -/
def warlpiriNyanu : Marker :=
  { form := "-nyanu", strategy := .boundPronoun, readings := {.reciprocal, .reflexive} }

/-- Kuuk Thaayorre *-rr*: the reciprocal verbal suffix ([nordlinger-2023] ex. 25). -/
def kuukThaayorreRr : Marker := { form := "-rr", strategy := .verbalAffix }

/-- Dalabon *-rr*: the reflexive–reciprocal verbal suffix ([nordlinger-2023] ex. 26b). -/
def dalabonRr : Marker :=
  { form := "-rr", strategy := .verbalAffix, readings := {.reciprocal, .reflexive} }

/-- Tonga *-an*: the reciprocal verbal suffix ([nordlinger-2023] ex. 21, from
[maslova-2008]). -/
def tongaAn : Marker := { form := "-an", strategy := .verbalAffix }

/-- A construction whose only reported indicator is the object slot. -/
private def objectSlot (v : Valency) : Indicator → Option Valency
  | .objectSlot => some v
  | _ => none

/-- The reciprocal construction the review describes for each language.

English: bipartite NP *each other* in the object position (ex. 1b), distinct from the
reflexive; the lexical reciprocals (*quarrel*, *meet*, ex. 7) are verb entries, not a marker.
Russian: bipartite *drug druga* 'other other-ACC' (ex. 9), the accusative showing the object
slot filled; the reflexive-identical postfix *-sja* (ex. 31) is the inventory's second marker.
Swahili: verbal affix *-an-* with a single subject NP (ex. 12). Hungarian: verbal affix
*-óz-* (ex. 19, 30). French: the clitic *se* is not a reciprocal object (ex. 28, 35), so the
slot is empty; bipartite *l'un l'autre* is the second marker. Greek: nonactive morphology
(ex. 27a). German: *einander* in the object position, beside reflexive *sich*. Mandarin:
compound *dǎ-lái-dǎ-qù* with a single subject NP (ex. 13). Wambaya: the RR morpheme in the
object position of the auxiliary's pronominal complex (ex. 11), the bound-pronominal slot
that defines the argument strategies (ex. 18b for Warlpiri). Icelandic: bipartite *hvort
annað*, the accusative on *annað* showing the clause transitive (ex. 17a). Chicheŵa: verbal
affix *-an-* (ex. 20). Czech: the clitic *se* (ex. 29), as in French. Warlpiri: the object
bound pronoun and the ergative subject both keep the clause transitive (ex. 18b). Kuuk
Thaayorre: the object NP is obligatorily absent yet the subject keeps ergative case (ex. 25).
Dalabon: the verb takes the intransitive subject pronominal series yet incorporates the
patient's body part as in the transitive clause (ex. 26). Tonga: both reciprocants are
argument NPs of the verb-marked reciprocal (ex. 21). -/
def Language.construction : Language → Construction
  | .english => { marker := English.Reciprocals.eachOther, valency := objectSlot .bivalent }
  | .russian => { marker := Russian.Reciprocals.drugDruga, valency := objectSlot .bivalent }
  | .swahili => { marker := Swahili.Reciprocals.anSuffix, valency := objectSlot .monovalent }
  | .hungarian =>
      { marker := Hungarian.Reciprocals.ozSuffix, valency := objectSlot .monovalent }
  | .french => { marker := French.Reciprocals.se, valency := objectSlot .monovalent }
  | .greek =>
      { marker := Greek.StandardModern.Reciprocals.nonactive
      , valency := objectSlot .monovalent }
  | .german => { marker := German.Reciprocals.einander, valency := objectSlot .bivalent }
  | .mandarin => { marker := Mandarin.Reciprocals.compound, valency := objectSlot .monovalent }
  | .wambaya => { marker := Wambaya.Reciprocals.rr, valency := objectSlot .bivalent }
  | .icelandic => { marker := Icelandic.Reciprocals.hvorAnnad, valency := objectSlot .bivalent }
  | .chichewa => { marker := Chichewa.Reciprocals.anSuffix, valency := objectSlot .monovalent }
  | .czech => { marker := Czech.Reciprocals.se, valency := objectSlot .monovalent }
  | .warlpiri =>
      { marker := warlpiriNyanu
      , valency := fun | .objectSlot | .subjectCase => some .bivalent | _ => none }
  | .kuukThaayorre =>
      { marker := kuukThaayorreRr
      , valency := fun | .objectSlot => some .monovalent | .subjectCase => some .bivalent
                       | _ => none }
  | .dalabon =>
      { marker := dalabonRr
      , valency := fun | .agreement => some .monovalent | .incorporation => some .bivalent
                       | _ => none }
  | .tonga => { marker := tongaAn, valency := objectSlot .bivalent }

/-- The formation locus of the verb-marked reciprocals the review discusses (§3.3):
[siloni-2012]'s own classification where it covers the language, and the review's
extension to Swahili and Greek, lexicon-formed because they form discontinuous
reciprocals with a comitative (ex. 36, 37). English's lexical reciprocals are set aside:
*kiss* and *hug* resist the discontinuous construction ([siloni-2012] fn. 32), and German
*sich*-reciprocals ([siloni-2012] fn. 13) are not taken up by the review. -/
def Language.formation : Language → Option Formation
  | .french => some Siloni2012.Language.french.formation
  | .czech => some Siloni2012.Language.czech.formation
  | .hungarian => some Siloni2012.Language.hungarian.formation
  | .swahili | .greek => some .lexical
  | _ => none

/-- Whether the review attests the discontinuous reciprocal construction (§3.3): Greek,
Swahili and Hungarian with a comitative (ex. 36–38), French and Czech ungrammatical (ex. 39,
p. 86). -/
def Language.discontinuous : Language → Option Bool
  | .swahili | .hungarian | .greek => some true
  | .french | .czech => some false
  | _ => none

/-! ### Strategy and valency -/

/-- Wherever the review's valency indicators agree, they agree with the strategy's default,
derived in the substrate from the detransitivizing coding-frame effect of reciprocalization;
Tonga is the review's counterexample. -/
theorem valency_follows_default :
    ∀ l : Language, ¬ l.construction.Mixed → l ≠ .tonga →
      l.construction.Unanimous l.construction.strategy.defaultValency := by
  decide

variable {l : Language}

/-- Nominal and argument strategies preserve valency: no nominal strategy reads monovalent
on any indicator. -/
theorem nominal_strategy_bivalent (hm : ¬ l.construction.Mixed) (ht : l ≠ .tonga)
    (h : l.construction.strategy.IsNominal) : ¬ l.construction.Reads .monovalent := fun hr ↦
  (Strategy.defaultValency_eq_monovalent_iff _).1
    (valency_follows_default l hm ht _ hr).symm h

/-- Conversely, a monovalent reading comes only from a verb-marked strategy. -/
theorem monovalent_implies_verbal (hm : ¬ l.construction.Mixed) (ht : l ≠ .tonga)
    (h : l.construction.Reads .monovalent) : ¬ l.construction.strategy.IsNominal :=
  (Strategy.defaultValency_eq_monovalent_iff _).1 (valency_follows_default l hm ht _ h).symm

/-! ### Mixed transitivity effects

The tendency is not absolute. Tonga's verb-marked reciprocal keeps both reciprocants as
argument NPs ([maslova-2008]), and in the Australian cases of [evans-et-al-2007] the
indicators of valency disagree with one another. -/

theorem kuukThaayorre_mixed : Language.kuukThaayorre.construction.Mixed := by decide

theorem dalabon_mixed : Language.dalabon.construction.Mixed := by decide

/-- Tonga contradicts the tendency: a verb-marked reciprocal whose object slot stays filled. -/
theorem tonga_counterexample :
    ¬ Language.tonga.construction.strategy.IsNominal ∧
      Language.tonga.construction.Reads .bivalent := by
  decide

/-! ### Discontinuous reciprocals -/

/-- Discontinuous reciprocals are possible exactly for lexically formed reciprocal verbs
([siloni-2008], [siloni-2012]): every language with a formation locus and a discontinuity
judgment satisfies the value the locus predicts. -/
theorem siloni_discontinuity_prediction :
    ∀ l : Language, ∀ f ∈ l.formation, ∀ d ∈ l.discontinuous,
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

Reflexive polysemy is carried by the markers above (French
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
