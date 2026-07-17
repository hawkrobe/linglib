import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Linglib.Features.Case.Capabilities
import Linglib.Features.Gender.Capabilities
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities
import Linglib.Morphology.Word
import Linglib.Syntax.Agreement.Basic

/-!
# Wechsler & Zlatić 2000: Agreement via the Declension–Concord–Index–Semantics chain
[wechsler-zlatic-2000] [corbett-1991] [corbett-1998] [pollard-sag-1994]
[dalrymple-kaplan-2000]

A noun carries two feature bundles — CONCORD (case, number, gender),
read by NP-internal targets, and the referential INDEX (person, number,
gender), read by pronouns and finite verbs — correlated with declension
class and semantics by a chain of binary constraints (their ex. 4):

    declension ⇔ concord ⇔ index ⇔ semantics

Regular nouns satisfy every link; hybrid nouns break one (or, *braća*,
two). The theory predicts exactly the three contiguous break patterns of
the seven a-priori possibilities, all attested (their §9, n. 3).

## Main declarations

* `Noun`, `DecCon`/`ConInd`/`IndSem` — the lexical entry and the three
  chain constraints (their exs. 15, 17, 18+22)
* `brokenLinks`, `seven_logical_patterns`/`three_contiguous_predicted` —
  the mismatch pattern of a noun, and the 7-logical/3-contiguous count
* `concordAgrees`/`indexAgrees` — target checking through the
  `HasX.Compatible` mixins, with the *deca* paradigm (exs. 41–42)
* `no_single_phi_bundle_for_deca` — the §3.3 single-bundle "illusion" as
  a refutation against `Word.Agree`
* `indexReaders_lowerSet` — the Agreement Hierarchy skeleton over
  `Agreement.Target`, robust to the open predicate position

Coordinate resolution (their fn. 18) is handled in
`Studies/DalrympleKaplan2000.lean`, to which the paper defers; the HPSG
spell-out function φ (Appendix) is out of scope.

## TODO

* Concord-ending syncretism (Table 2) and the participle indeterminacy
  it causes (§7.3, left open in the paper).
* The *sudija*/*mušterija* disjunctive sex specification (exs. 20,
  31–32), here flattened to resolved variants.
* Pragmatic agreement: masculine-plural pronouns for mixed groups
  (§3.1).

-/

set_option autoImplicit false

namespace WechslerZlatic2000

/-! ### Feature bundles (§3.3)

CONCORD comprises case, number, and gender; INDEX comprises person,
number, and gender. Case is contextual (valued in syntax), so the
lexical CONCORD carries number and gender; a *realized* NP-internal
target adds the case value. -/

/-- Serbo-Croatian declension classes (their Table 1). The singular
    citation-form classes are I/II/III; pluralia tantum sit outside this
    classification (their Table 3 lists their declension as a distinct
    value "pl", §6), so they get their own constructor rather than being
    forced into a numbered class. -/
inductive Declension where
  | I
  | II
  | III
  | pluralia
  deriving DecidableEq, Repr

/-- Lexical CONCORD features: number and gender (case is contextual). -/
structure ConcordF where
  number : Number
  gender : Gender
  deriving DecidableEq, Repr

/-- INDEX features: person, number, gender (their ex. 8). -/
structure IndexF where
  person : Person
  number : Number
  gender : Gender
  deriving DecidableEq, Repr

/-- Semantic sex restriction on the noun's referent (their exs. 18–20).
    *sudija* 'judge'-type nouns are treated via their resolved variants,
    following the paper's exs. 31–32. -/
inductive SexRestriction where
  | female
  | male
  | unrestricted
  deriving DecidableEq, Repr

/-- The COUNT feature (their ex. 22): count nouns carry `one` or
    `aggregate`; noncount nouns lack COUNT (`none` at the entry). -/
inductive Count where
  | one
  | aggregate
  deriving DecidableEq, Repr

/-- A noun's agreement-relevant lexical entry: the four chain positions. -/
structure Noun where
  lemma_ : String
  decl : Declension
  concord : ConcordF
  index : IndexF
  sex : SexRestriction
  count : Option Count
  deriving DecidableEq, Repr

/-! ### The three chain constraints (their exs. 15, 17, 18, 22) -/

/-- DecCon (ex. 15): class I nouns have masculine or neuter concord
    gender; class II/III nouns have feminine concord gender. Pluralia
    tantum lie outside the singular declension classification (their §6),
    so the constraint is vacuous for them — their break, when any, is at
    a later link. -/
def DecCon (n : Noun) : Prop :=
  match n.decl with
  | .I => n.concord.gender = .masculine ∨ n.concord.gender = .neuter
  | .II | .III => n.concord.gender = .feminine
  | .pluralia => True

/-- ConInd (ex. 17): the noun's CONCORD and INDEX share number and
    gender (structure sharing in the original). -/
def ConInd (n : Noun) : Prop :=
  n.concord.number = n.index.number ∧ n.concord.gender = n.index.gender

/-- IndSem, gender half (ex. 18): a female-restricted noun has feminine
    index, a male-restricted noun masculine index; vacuous otherwise. -/
def IndSemGen (n : Noun) : Prop :=
  (n.sex = .female → n.index.gender = .feminine) ∧
  (n.sex = .male → n.index.gender = .masculine)

/-- IndSem, number half (ex. 22): aggregate reference gives plural
    index; nonaggregate and noncount give singular. -/
def IndSemNum (n : Noun) : Prop :=
  match n.count with
  | some .aggregate => n.index.number = .plural
  | _ => n.index.number = .singular

/-- The index–semantics link: both halves. -/
def IndSem (n : Noun) : Prop := IndSemGen n ∧ IndSemNum n

instance (n : Noun) : Decidable (DecCon n) := by unfold DecCon; split <;> infer_instance
instance (n : Noun) : Decidable (ConInd n) := by unfold ConInd; infer_instance
instance (n : Noun) : Decidable (IndSemGen n) := by unfold IndSemGen; infer_instance
instance (n : Noun) : Decidable (IndSemNum n) := by unfold IndSemNum; split <;> infer_instance
instance (n : Noun) : Decidable (IndSem n) := inferInstanceAs (Decidable (_ ∧ _))

/-! ### Mismatch patterns -/

/-- The three links of the chain (their ex. 4, read left to right). -/
inductive ChainLink where
  | decCon
  | conInd
  | indSem
  deriving DecidableEq, Repr, Fintype

/-- Does a given link hold for a noun? -/
def linkHolds (n : Noun) : ChainLink → Prop
  | .decCon => DecCon n
  | .conInd => ConInd n
  | .indSem => IndSem n

instance (n : Noun) (l : ChainLink) : Decidable (linkHolds n l) := by
  cases l <;> simp only [linkHolds] <;> infer_instance

/-- A noun's mismatch pattern: the set of broken links (their ex. 5,
    the double bars). -/
def brokenLinks (n : Noun) : Finset ChainLink :=
  Finset.univ.filter (fun l => ¬ linkHolds n l)

/-- A noun is regular iff every link holds. -/
def Regular (n : Noun) : Prop := ∀ l, linkHolds n l

instance (n : Noun) : Decidable (Regular n) :=
  inferInstanceAs (Decidable (∀ _, _))

/-! ### The Serbo-Croatian lexicon (their Table 3, exs. 14, 16, 20, 29,
35, 39, 45)

Number values at the entry are those of the singular citation form for
ordinary count nouns; collectives and pluralia tantum carry their
lexically fixed values. -/

/-- *knjiga* 'book': perfectly regular class II feminine (ex. 14). -/
def knjiga : Noun :=
  { lemma_ := "knjiga", decl := .II,
    concord := ⟨.singular, .feminine⟩,
    index := ⟨.third, .singular, .feminine⟩,
    sex := .unrestricted, count := some .one }

/-- *žena* 'woman': regular, female-denoting (their §1). -/
def žena : Noun :=
  { lemma_ := "žena", decl := .II,
    concord := ⟨.singular, .feminine⟩,
    index := ⟨.third, .singular, .feminine⟩,
    sex := .female, count := some .one }

/-- *muž* 'husband': regular class I masculine (their §4.3). -/
def muž : Noun :=
  { lemma_ := "muž", decl := .I,
    concord := ⟨.singular, .masculine⟩,
    index := ⟨.third, .singular, .masculine⟩,
    sex := .male, count := some .one }

/-- *Steva*: masculine name declining in class II — the
    declension ∥ concord break (their exs. 28–29). *sudija* 'judge'
    applied to males patterns identically (ex. 19a). -/
def steva : Noun :=
  { lemma_ := "Steva", decl := .II,
    concord := ⟨.singular, .masculine⟩,
    index := ⟨.third, .singular, .masculine⟩,
    sex := .male, count := some .one }

/-- *deca* 'children': class II collective, feminine singular CONCORD,
    neuter plural INDEX — the concord ∥ index break (their ex. 45–46). -/
def deca : Noun :=
  { lemma_ := "deca", decl := .II,
    concord := ⟨.singular, .feminine⟩,
    index := ⟨.third, .plural, .neuter⟩,
    sex := .unrestricted, count := some .aggregate }

/-- *gospoda* 'gentlemen': like *deca* but male-restricted with
    masculine plural index (their ex. 40, §7.1). -/
def gospoda : Noun :=
  { lemma_ := "gospoda", decl := .II,
    concord := ⟨.singular, .feminine⟩,
    index := ⟨.third, .plural, .masculine⟩,
    sex := .male, count := some .aggregate }

/-- *makaze* 'scissors' on its nonaggregate reading ('one pair'):
    plural declension/concord/index against singular reference — the
    index ∥ semantics break (their exs. 34–35, with *naočare*
    'glasses'). Declension is `pluralia` (Table 3 value "pl", not a
    numbered class); the feminine concord gender is supplied (Table 3
    leaves makaze's gender unspecified) and is inessential to the
    break. -/
def makazeNonAggregate : Noun :=
  { lemma_ := "makaze", decl := .pluralia,
    concord := ⟨.plural, .feminine⟩,
    index := ⟨.third, .plural, .feminine⟩,
    sex := .unrestricted, count := some .one }

/-- *devojče* 'girl': female-denoting diminutive with neuter index —
    an index ∥ semantics (gender) break (their exs. 11, Table 3). -/
def devojče : Noun :=
  { lemma_ := "devojče", decl := .I,
    concord := ⟨.singular, .neuter⟩,
    index := ⟨.third, .singular, .neuter⟩,
    sex := .female, count := some .one }

/-- *braća* 'brothers': male-only with feminine singular concord and
    neuter plural index — the unique double break, concord ∥ index and
    index ∥ semantics (their ex. 39). -/
def braća : Noun :=
  { lemma_ := "braća", decl := .II,
    concord := ⟨.singular, .feminine⟩,
    index := ⟨.third, .plural, .neuter⟩,
    sex := .male, count := some .aggregate }

/-! ### The mismatch typology, derived (their §5–§7) -/

/-- Regular nouns satisfy the whole chain. -/
theorem regulars_satisfy_chain :
    Regular knjiga ∧ Regular žena ∧ Regular muž := by decide

/-- *Steva* breaks exactly declension ∥ concord (their ex. 29). -/
theorem steva_breaks_decCon : brokenLinks steva = {.decCon} := by decide

/-- *deca* breaks exactly concord ∥ index (their ex. 46). -/
theorem deca_breaks_conInd : brokenLinks deca = {.conInd} := by decide

/-- *gospoda* breaks exactly concord ∥ index (their §7.1). -/
theorem gospoda_breaks_conInd : brokenLinks gospoda = {.conInd} := by
  decide

/-- *makaze* (nonaggregate) breaks exactly index ∥ semantics (their
    ex. 35). -/
theorem makaze_breaks_indSem :
    brokenLinks makazeNonAggregate = {.indSem} := by decide

/-- *devojče* breaks exactly index ∥ semantics (gender half). -/
theorem devojče_breaks_indSem : brokenLinks devojče = {.indSem} := by
  decide

/-- *braća* breaks both concord ∥ index and index ∥ semantics — the
    predicted-rare double break (their ex. 39). -/
theorem braća_double_break :
    brokenLinks braća = {.conInd, .indSem} := by decide

/-! ### Seven logical patterns, three predicted (their §9, n. 3)

A two-type mismatch pattern is a bipartition of the four chain
positions; identify it with its cell containing `declension`
(position 0). There are `2³ − 1 = 7` such bipartitions. The theory
admits only breaks *at chain links*, so the cell must be an initial
segment of the chain — and there are exactly 3 of those, realized by
*Steva*, *deca*, and *makaze* respectively. -/

/-- Bipartitions of the four chain positions, as proper subsets
    containing position 0. -/
def bipartitions : Finset (Finset (Fin 4)) :=
  Finset.univ.filter (fun S => (0 : Fin 4) ∈ S ∧ S ≠ Finset.univ)

/-- The cell of position 0 under a single break at link `l`: an initial
    segment of the chain. -/
def cellOfBreak : ChainLink → Finset (Fin 4)
  | .decCon => {0}
  | .conInd => {0, 1}
  | .indSem => {0, 1, 2}

/-- Seven logically possible two-type mismatch patterns a priori (their
    §9, n. 3). -/
theorem seven_logical_patterns : bipartitions.card = 7 := by decide

/-- Of the seven, the theory predicts the three contiguous ones — the
    initial-segment cells realized by *Steva*, *deca*, *makaze* (their
    §9: "our theory predicts three to be possible"). -/
theorem three_contiguous_predicted :
    (bipartitions.filter
      (fun S => ∃ l : ChainLink, S = cellOfBreak l)).card = 3 := by
  decide

/-- The attested single-break patterns are exactly the three contiguous
    cells — *Steva*, *deca*/*gospoda*, *makaze*/*devojče* (their
    Table 3: "Only contiguous cells in a row are connected by
    constraints, so we predict exactly the pattern observed"). -/
theorem attested_patterns_are_contiguous :
    brokenLinks steva = {.decCon} ∧
    brokenLinks deca = {.conInd} ∧
    brokenLinks makazeNonAggregate = {.indSem} := by decide

/-! ### Target checking through the carrier mixins (§3.3)

NP-internal targets (determiners, attributive adjectives) check
CONCORD: case, number, gender. Pronouns and finite verbs check INDEX:
person, number, gender. Both run through the shared `HasX.Compatible`
relations. A target may be underspecified for a feature (`none`), where
the flat-order wildcard semantics of `Compatible` does real work — see
`kojih`, the concord-underspecified plural relative pronoun (§7.4). -/

/-- A realized NP-internal target's inflectional features: the noun's
    lexical concord plus contextual case (their ex. 12). A feature is
    `none` when the target is unmarked for it (e.g. *kojih*, §7.4). -/
structure ConcordTarget where
  case : Option Case
  number : Option Number
  gender : Option Gender
  deriving DecidableEq, Repr

instance : HasCase ConcordTarget := ⟨ConcordTarget.case⟩
instance : HasNumber ConcordTarget := ⟨ConcordTarget.number⟩
instance : HasGender ConcordTarget := ⟨ConcordTarget.gender⟩

/-- The noun's realized concord bundle at a contextual case value (the
    noun's own concord is always fully specified). -/
def Noun.concordAt (n : Noun) (c : Case) : ConcordTarget :=
  ⟨some c, some n.concord.number, some n.concord.gender⟩

/-- An index-checking target's features (pronoun, finite verb). -/
structure IndexTarget where
  person : Person
  number : Number
  gender : Gender
  deriving DecidableEq, Repr

instance : HasPerson IndexTarget := ⟨fun t => some t.person⟩
instance : HasNumber IndexTarget := ⟨fun t => some t.number⟩
instance : HasGender IndexTarget := ⟨fun t => some t.gender⟩

/-- The noun's index bundle as a checking target. -/
def Noun.indexTarget (n : Noun) : IndexTarget :=
  ⟨n.index.person, n.index.number, n.index.gender⟩

/-- Concord agreement: the target's case, number, and gender are each
    compatible with the noun's realized concord. -/
def concordAgrees (a : ConcordTarget) (n : Noun) (c : Case) : Prop :=
  HasCase.Compatible a (n.concordAt c) ∧
  HasNumber.Compatible a (n.concordAt c) ∧
  HasGender.Compatible a (n.concordAt c)

instance (a : ConcordTarget) (n : Noun) (c : Case) :
    Decidable (concordAgrees a n c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Index agreement: the target's person, number, and gender are each
    compatible with the noun's index. -/
def indexAgrees (p : IndexTarget) (n : Noun) : Prop :=
  HasPerson.Compatible p n.indexTarget ∧
  HasNumber.Compatible p n.indexTarget ∧
  HasGender.Compatible p n.indexTarget

instance (p : IndexTarget) (n : Noun) : Decidable (indexAgrees p n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ### The *deca* paradigm (their exs. 41–43)

*Posmatrali smo ovu dobru decu. Ona su spavala.* — feminine singular on
the accusative determiner and adjective (CONCORD), neuter plural on the
coreferential pronoun (INDEX); the crossed combinations fail. -/

/-- *ovu*/*dobru*: accusative feminine singular modifier (ex. 41). -/
def ovu : ConcordTarget := ⟨some .acc, some .singular, some .feminine⟩

/-- *ona*: neuter plural pronoun (ex. 41). -/
def ona : IndexTarget := ⟨.third, .plural, .neuter⟩

/-- *ova stara* (nominative feminine singular, ex. 6) agrees with
    regular *knjiga* in concord — and *je* (3sg feminine) in index. -/
theorem knjiga_regular_targets :
    concordAgrees ⟨some .nom, some .singular, some .feminine⟩ knjiga .nom ∧
    indexAgrees ⟨.third, .singular, .feminine⟩ knjiga := by decide

/-- **Mixed agreement with *deca*** (exs. 41–42): the f.sg modifier
    checks CONCORD and the nt.pl pronoun checks INDEX —
    simultaneously. -/
theorem deca_mixed_agreement :
    concordAgrees ovu deca .acc ∧ indexAgrees ona deca := by decide

/-- The crossed combinations fail: a neuter plural modifier does not
    stand in concord agreement with *deca*, and a feminine singular
    pronoun does not stand in index agreement with it (cf. *je* in
    their ex. 62). -/
theorem deca_crossed_combinations_fail :
    ¬ concordAgrees ⟨some .acc, some .plural, some .neuter⟩ deca .acc ∧
    ¬ indexAgrees ⟨.third, .singular, .feminine⟩ deca := by decide

/-- *kojih*: the genitive plural relative pronoun, unmarked for CONCORD
    gender and number (§7.4). Its wildcard concord features make it
    compatible with *deca* (and with a feminine-singular noun) — the
    case where `Compatible`'s flat-order semantics is not mere equality. -/
def kojih : ConcordTarget := ⟨some .gen, none, none⟩

/-- *kojih* agrees in concord with *deca* despite *deca*'s f.sg concord
    and *kojih*'s plural index — its underspecified concord is a
    wildcard. A fully-specified neuter-plural modifier does not
    (`deca_crossed_combinations_fail`). -/
theorem kojih_underspecified_agrees :
    concordAgrees kojih deca .gen := by decide

/-- For chain-intact nouns the split is invisible: a target's concord
    agreement coincides with index agreement on the shared number/gender
    features (the "illusion … that a single feature bundle on the noun
    is responsible for all the agreeing items", their §3.3). -/
theorem regular_nouns_mask_the_split (n : Noun) (hn : ConInd n)
    (t : IndexTarget) :
    HasNumber.Compatible t n.indexTarget ↔
      HasNumber.Compatible t (n.concordAt .nom) := by
  obtain ⟨hnum, _⟩ := hn
  simp only [HasNumber.Compatible, Noun.indexTarget, Noun.concordAt,
    HasNumber.numberOf, hnum]

/-- The single-φ-bundle view (`Word.phi`/`Word.Agree`) cannot host
    *deca*: its CONCORD-bearing attributive (f.sg) and its INDEX-bearing
    pronoun (nt.pl) do not `Word.Agree`, so they cannot both copy one
    fully-valued source bundle. This is §3.3's "illusion", as a
    refutation against the library's one-bundle primitive — note a
    *featureless* word would tolerate both (wildcards), so the claim is
    about the two specified surface forms, not about compatibility. -/
theorem no_single_phi_bundle_for_deca :
    ¬ Word.Agree
        ⟨"dobra", .ADJ, { gender := some .Fem, number := some .Sing }⟩
        ⟨"ona", .PRON, { gender := some .Neut, number := some .Plur }⟩ := by
  decide

/-! ### The Agreement Hierarchy, derived (their §8)

Corbett's hierarchy lives as `Agreement.Target`; W&Z's
contribution is `readsIndex`, the bundle-access derivation of it.
Attributives lack referential indices (read only CONCORD); pronouns and
verbs read INDEX, which alone connects to the semantics. The predicate
position is open in the paper (§7.3): secondary predication points to
concord (ex. 50), coordination to index (exs. 51–53). -/

open _root_.Agreement (Target)

/-- Whether a target reads the INDEX bundle — the precondition for
    semantic agreement (their §8). `predReadsIndex` is the open predicate
    position (§7.3, "left for future research"); the hierarchy's
    monotonicity (`indexReaders_lowerSet`) holds for either value. -/
def readsIndex (predReadsIndex : Bool) : Target → Prop
  | .attributive => False
  | .predicate => predReadsIndex
  | .relativePronoun => True
  | .personalPronoun => True
  | .verb => True

instance (p : Bool) : DecidablePred (readsIndex p) := fun t => by
  cases t <;> simp only [readsIndex] <;> infer_instance

/-- **The hierarchy skeleton**: the index readers form a lower set in the
    `Agreement.Target` order (higher = more syntactic), so semantic
    agreement can surface only at more-semantic targets — and this holds
    whichever way the open predicate position resolves. This is the
    *categorical* claim W&Z derive (their §8, "concord elements should
    never show semantic agreement unless the pronouns do"); it explains
    but does not reproduce Corbett's gradient, corpus-level likelihood
    law ([corbett-1998]; their fn. 21). W&Z rank no INDEX-reader above
    another, and none is needed: `verb`, off the hierarchy, reads INDEX
    outright (`readsIndex_verb`). -/
theorem indexReaders_lowerSet (p : Bool) (t u : Target)
    (h : u ≤ t) : readsIndex p t → readsIndex p u := by
  cases p <;> revert t u <;> decide

/-- Verbs read INDEX unconditionally (they agree in person, which only
    INDEX carries) — no hierarchy position needed. -/
theorem readsIndex_verb (p : Bool) : readsIndex p .verb := trivial

end WechslerZlatic2000
