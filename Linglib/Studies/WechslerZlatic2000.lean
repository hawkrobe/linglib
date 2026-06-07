import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Linglib.Features.Case.Capabilities
import Linglib.Features.Gender.Capabilities
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities

/-!
# Wechsler & Zlatić 2000: Agreement via the Declension–Concord–Index–Semantics chain
[wechsler-zlatic-2000] [corbett-1991] [pollard-sag-1994]

Four lexical features of a noun are relevant to agreement — declension
class, CONCORD features (case, number, gender), the referential INDEX's
features (person, number, gender), and semantic conditions on reference
— correlated by a chain of binary constraints (their ex. 4):

    declension ⇔ concord ⇔ index ⇔ semantics

Regular nouns (*knjiga* 'book', *žena* 'woman') satisfy every link.
Hybrid nouns break exactly one link — *Steva*-type masculine names in
the feminine declension (declension ∥ concord, their ex. 29), *deca*
'children'-type collectives (concord ∥ index, ex. 46), pluralia tantum
*makaze* 'scissors' on nonaggregate reference (index ∥ semantics,
ex. 35) — and *braća* 'brothers' breaks two (ex. 39). The headline
prediction (their §9, n. 3): of the seven logically possible two-type
mismatch patterns, only the **three contiguous** ones can arise, and
exactly those three are attested (`seven_logical_three_contiguous`,
`attested_patterns_are_contiguous`).

NP-internal targets (determiners, attributive adjectives) check CONCORD
— case, number, gender — while pronouns and finite verbs check INDEX —
person, number, gender (§3.3). Both checks run through the shared
carrier mixins (`HasCase`/`HasNumber`/`HasGender`/`HasPerson` and their
`Compatible` relations), so *ova dobra deca* / *ona su spavala* (exs.
41–42) verify by concord- and index-compatibility respectively, and the
mismatched variants fail. Corbett's AGREEMENT HIERARCHY
(attributive < predicate < relative pronoun < personal pronoun,
[corbett-1991]) falls out: attributives lack referential indices, so
they can only read CONCORD; pronouns read INDEX, which alone connects
to the semantics (their §8) — `indexAccess_monotone`.

Not formalized here: the nominative f.sg ~ nt.pl syncretism of concord
endings (their Table 2) and the resulting participle indeterminacy
(§7.3, left open by the paper); pragmatic agreement (masculine plural
pronouns for mixed groups, §3.1); the HPSG spell-out function φ
(Appendix).

## Main declarations

* `WechslerZlatic2000.Noun` — lexical entry: declension, CONCORD,
  INDEX, semantic conditions (sex restriction, COUNT)
* `WechslerZlatic2000.DecCon`/`ConInd`/`IndSem` — the three chain
  constraints (their exs. 15, 17, 18 + 22)
* `WechslerZlatic2000.brokenLinks` — a noun's mismatch pattern
* `WechslerZlatic2000.seven_logical_three_contiguous` — 7 bipartitions
  of the chain, 3 contiguous; `attested_patterns_are_contiguous`
* `WechslerZlatic2000.concordAgrees`/`indexAgrees` — target checking
  through the `HasX.Compatible` mixins, with the *deca* paradigm
  (exs. 41–42) as positive/negative tests
-/

set_option autoImplicit false

namespace WechslerZlatic2000

/-! ### Feature bundles (§3.3)

CONCORD comprises case, number, and gender; INDEX comprises person,
number, and gender. Case is contextual (valued in syntax), so the
lexical CONCORD carries number and gender; a *realized* NP-internal
target adds the case value. -/

/-- Serbo-Croatian declension classes (their Table 1). -/
inductive Declension where
  | I
  | II
  | III
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
    gender; class II/III nouns have feminine concord gender. -/
def DecCon (n : Noun) : Prop :=
  match n.decl with
  | .I => n.concord.gender = .masculine ∨ n.concord.gender = .neuter
  | .II | .III => n.concord.gender = .feminine

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
    'glasses'). -/
def makazeNonAggregate : Noun :=
  { lemma_ := "makaze", decl := .II,
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

/-- **Seven logically possible two-type patterns, three contiguous**
    (their §9: "there are seven logical possibilities a priori …
    our theory predicts three to be possible"). -/
theorem seven_logical_three_contiguous :
    bipartitions.card = 7 ∧
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
person, number, gender. Both run through the shared
`HasX.Compatible` relations — concord checking is the first live
consumer of `HasCase.Compatible`. -/

/-- A realized NP-internal target's inflectional features: the noun's
    lexical concord plus contextual case (their ex. 12). -/
structure ConcordTarget where
  case : Case
  number : Number
  gender : Gender
  deriving DecidableEq, Repr

instance : HasCase ConcordTarget := ⟨fun t => some t.case⟩
instance : HasNumber ConcordTarget := ⟨fun t => some t.number⟩
instance : HasGender ConcordTarget := ⟨fun t => some t.gender⟩

/-- The noun's realized concord bundle at a contextual case value. -/
def Noun.concordAt (n : Noun) (c : Case) : ConcordTarget :=
  ⟨c, n.concord.number, n.concord.gender⟩

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
def ovu : ConcordTarget := ⟨.acc, .singular, .feminine⟩

/-- *ona*: neuter plural pronoun (ex. 41). -/
def ona : IndexTarget := ⟨.third, .plural, .neuter⟩

/-- *ova stara* (nominative feminine singular, ex. 6) agrees with
    regular *knjiga* in concord — and *je* (3sg feminine) in index. -/
theorem knjiga_regular_targets :
    concordAgrees ⟨.nom, .singular, .feminine⟩ knjiga .nom ∧
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
    ¬ concordAgrees ⟨.acc, .plural, .neuter⟩ deca .acc ∧
    ¬ indexAgrees ⟨.third, .singular, .feminine⟩ deca := by decide

/-- For chain-intact nouns the distinction is invisible: any target
    agreeing in concord number/gender also agrees in index
    number/gender (the "illusion … that a single feature bundle on the
    noun is responsible for all the agreeing items", their §3.3). -/
theorem regular_nouns_mask_the_split (n : Noun) (hn : ConInd n)
    (num : Number) (g : Gender) :
    (num = n.concord.number ∧ g = n.concord.gender) ↔
    (num = n.index.number ∧ g = n.index.gender) := by
  obtain ⟨hnum, hgen⟩ := hn
  rw [hnum, hgen]

/-! ### The Agreement Hierarchy, derived (their §8)

Corbett's hierarchy — attributive < predicate < relative pronoun <
personal pronoun, with semantic agreement increasing monotonically
([corbett-1991]) — follows from which bundle each target can read:
attributives lack referential indices and read only CONCORD; relative
pronouns are NP-internal *and* bound, reading both (their §7.4);
personal pronouns read only INDEX. Since INDEX alone is linked to the
semantics, semantic agreement can only surface where INDEX is read. -/

/-- Corbett's target positions, ordered (their ex. 63). Predicates are
    placed by the paper between attributives and relative pronouns;
    whether Serbo-Croatian participles read concord or index is left
    open by their §7.3. -/
inductive Target where
  | attributive
  | predicate
  | relativePronoun
  | personalPronoun
  deriving DecidableEq, Repr, Fintype

/-- Hierarchy position (ex. 63, left to right). -/
def Target.rank : Target → Fin 4
  | .attributive => 0
  | .predicate => 1
  | .relativePronoun => 2
  | .personalPronoun => 3

/-- Whether a target can read the INDEX bundle — the precondition for
    semantic agreement (their §8: attributives "lack referential
    indices"; relative pronouns are bound; predicates pattern with
    index targets in primary predication, their §7.3 ex. 51–53). -/
def Target.readsIndex : Target → Prop
  | .attributive => False
  | _ => True

instance : DecidablePred Target.readsIndex := fun t => by
  cases t <;> simp only [Target.readsIndex] <;> infer_instance

/-- **The hierarchy as monotonicity**: index access never decreases
    rightward along Corbett's hierarchy — so semantic agreement, which
    requires reading INDEX, increases monotonically (their §8:
    "concord elements should never show semantic agreement unless the
    pronouns do so"). -/
theorem indexAccess_monotone :
    ∀ t u : Target, t.rank ≤ u.rank → t.readsIndex → u.readsIndex := by
  decide

end WechslerZlatic2000
