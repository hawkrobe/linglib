import Mathlib.Order.UpperLower.Basic
import Linglib.Features.Case.Basic
import Linglib.Morphology.Exponence.Containment.Contiguity
import Linglib.Syntax.Case.Order
import Linglib.Fragments.Dargwa.Case
import Linglib.Fragments.Finnish.Case
import Linglib.Fragments.German.Case
import Linglib.Fragments.Greek.Case
import Linglib.Fragments.Hindi.Case
import Linglib.Fragments.Hungarian.Case
import Linglib.Fragments.Icelandic.Case
import Linglib.Fragments.Japanese.Case
import Linglib.Fragments.Korean.Case
import Linglib.Fragments.Latin.Case
import Linglib.Fragments.Mongolian.Case
import Linglib.Fragments.Slavic.Belarusian.Case
import Linglib.Fragments.Slavic.Case
import Linglib.Fragments.Slavic.Cassubian.Case
import Linglib.Fragments.Slavic.Czech.Case
import Linglib.Fragments.Slavic.Polish.Case
import Linglib.Fragments.Slavic.Russian.Case
import Linglib.Fragments.Slavic.Serbian.Case
import Linglib.Fragments.Slavic.Slovak.Case
import Linglib.Fragments.Slavic.Slovenian.Case
import Linglib.Fragments.Slavic.Sorbian.Case
import Linglib.Fragments.Slavic.Ukrainian.Case
import Linglib.Fragments.SwissGerman.Case
import Linglib.Fragments.Tamil.Case
import Linglib.Fragments.Telugu.Case
import Linglib.Fragments.Turkish.Case
import Linglib.Fragments.Yakut.Case

/-!
# Caha 2009: the nanosyntax of case

Each case's morphosyntactic representation contains the representations of every case below it on
the universal sequence — nominative inside accusative inside genitive inside dative inside the
prepositional cases. Two consequences are formalized here. An inventory must be downward closed
under that containment: a language with a dative has a genitive, and so on down. And within a
paradigm the cells sharing a form must be contiguous in the sequence, which is not an independent
axiom but the generative capacity of nanosyntactic spellout — lexical entries competing under the
Superset Principle realize exactly the contiguous patterns.

Every case inventory in the Fragments is downward closed but two, and both exceptions are
principled: Dargwa is ergative, and containment is keyed to accusative alignment, while Hungarian
has no morphological genitive, the textbook surface counterexample to the hierarchy, which the
literature resolves by treating its dative as expressing the possessor. Finnish looks like a third
but is not: its locative richness is on the orthogonal directional dimension, so on the nominal
chain it has only nominative, accusative and genitive.

The paradigm-shape half covers the four Slavic languages analysed in detail. The syncretism shapes
they attest are collected once and checked for contiguity, and each language's section records
which of them it attests, together with the violations Caha acknowledges and treats as
phonological conflation or accidental homophony.

## Main definitions

* `RespectsCahaContainment` — downward closure of an inventory under containment
* `Slavic.Paradigm`, `Slavic.IsContiguous` — a declension's syncretism shape and contiguity
* `Slavic.SyncretismPatterns.contiguousShapes`, `nonContiguousShapes` — the shapes Caha's Slavic
  data attests

## Main results

* `respectsCahaContainment_iff_isLowerSet` — the containment condition is an order-theoretic
  closure property
* `conformers_respectCaha`, `dargwa_not_respectsCaha`, `hungarian_not_respectsCaha` — the
  inventories and the two principled exceptions
* `Slavic.universalContiguity_iff_spellable` — contiguity is what the spellout engine generates
* the per-language `all_attested_contiguous` and `Counterexamples.all_attested_not_contiguous`

## References

* [caha-2009]
* [caha-2008]
* [blake-1994]
* [pantcheva-2011]
-/
namespace Caha2009

open scoped Case.Caha

/-! ## Caha containment-respect predicate

Does an inventory respect Caha's containment hierarchy? True iff `inv`
is downward-closed under the scoped Caha order (`Case.Caha`;
containment) defined in `Syntax/Case/Order.lean`: whenever `c ∈ inv` and
`d ≤ c`, then `d ∈ inv`. Off-hierarchy cases (ERG, ABS, INST, COM, …)
impose no constraint — in the Caha order they only have `c ≤ c`, so
the downward-closure condition is vacuous. On-hierarchy `c` of rank
`r` forces every lower on-hierarchy case (ranks `0, …, r-1`) into
`inv`, which is exactly the prefix-contiguity Caha demands.

-/

def RespectsCahaContainment (inv : Finset Case) : Prop :=
  ∀ c ∈ inv, ∀ d, d ≤ c → d ∈ inv

instance (inv : Finset Case) : Decidable (RespectsCahaContainment inv) := by
  unfold RespectsCahaContainment; infer_instance

/-- Containment-respect is `IsLowerSet` under the scoped Caha order — the
    Caha analogue of `Case.isValidInventory_iff_ordConnected` (Blake).
    The two contiguity predicates on `Finset Case` are thus both
    order-theoretic closure properties, on the partial Caha order and the
    total Blake rank respectively. -/
theorem respectsCahaContainment_iff_isLowerSet (inv : Finset Case) :
    RespectsCahaContainment inv ↔ IsLowerSet (inv : Set Case) := by
  simp only [RespectsCahaContainment, IsLowerSet, Finset.mem_coe]
  exact ⟨fun h _ _ hba ha => h _ ha _ hba, fun h _ hc _ hdc => h hdc hc⟩

/-! ## Slavic substrate: containment lemmas

Decoupled from `Fragments/Slavic/Case.lean` so that the Fragment
substrate file does not pull in the Caha-specific containment
predicate (which lives here in this study file, not in `Core/`). -/

theorem slavicCore_respectsCaha :
    RespectsCahaContainment Slavic.Case.coreInventory := by decide

/-- Vacuous: `Case.containmentRank .voc = none` faithfully
    encodes Caha's own scope choice ([caha-2009] §1.1 fn. 4,
    p. 9: "Vocatives ... are ignored throughout this dissertation"). -/
theorem slavicSeven_respectsCaha :
    RespectsCahaContainment Slavic.Case.sevenCaseInventory := by decide

/-! ## Inventories

The Slavic inventories each alias one core inventory, so their conformance is structural rather
than coincidental; the list covers every modern Slavic language with productive case morphology,
Bulgarian and Macedonian having lost noun case entirely. -/

/-- The conforming Fragment case inventories. -/
def conformers : List (Finset Case) :=
  [ -- non-Slavic
    German.Case.caseInventory, Greek.Case.caseInventory, Hindi.Case.caseInventory,
    Icelandic.Case.caseInventory, Japanese.Case.caseInventory, Korean.Case.caseInventory,
    Latin.Case.caseInventory, Mongolian.Case.caseInventory, SwissGerman.Case.caseInventory,
    Tamil.Case.caseInventory, Telugu.Case.caseInventory, Turkish.Case.caseInventory,
    Yakut.Case.caseInventory,
    -- Slavic (each aliases Slavic.Case.coreInventory)
    Belarusian.Case.caseInventory, Cassubian.Case.caseInventory, Czech.Case.caseInventory,
    Polish.Case.caseInventory, Russian.Case.caseInventory, Serbian.Case.caseInventory,
    Slovak.Case.caseInventory, Slovenian.Case.caseInventory, Sorbian.Case.caseInventory,
    Ukrainian.Case.caseInventory ]

theorem conformers_respectCaha :
    ∀ inv ∈ conformers, RespectsCahaContainment inv := by decide

/-! ## § 3: Predicted violators -/

/-- Dargwa is ergative; Caha's containment is keyed to accusative
    alignment. ABS/ERG are off-hierarchy in `containmentRank`, so
    Dargwa's `[abs, erg, gen, dat, com, ess]` fails downward closure
    (GEN/DAT present without NOM/ACC). -/
theorem dargwa_not_respectsCaha :
    ¬ RespectsCahaContainment Dargwa.Case.caseInventory := by decide

/-- Finnish *respects* nominal Caha containment — vacuously. Under the
    faithful spatial decomposition (`Syntax/Case/Order.lean`), Finnish's
    locatives are the off-chain spatial cells (INE/ELA/ILL, ADE/ABL/ALL,
    on the orthogonal *directional* containment, not the nominal one), so
    its only on-nominal-chain cases are NOM/ACC/GEN — downward-closed.
    The richness Finnish shows is on the directional dimension
    ([pantcheva-2011]); on the nominal chain it has no LOC-without-DAT
    gap. (Its allative-for-dative recipient function lives in
    `Finnish.Case.allative_extends_to_dative`.) -/
theorem finnish_respectsCaha :
    RespectsCahaContainment Finnish.Case.caseInventory := by decide

/-- Hungarian has no morphological genitive — both standard reference
    grammars ([kenesei-vago-fenyvesi-1998] §1.10, [rounds-2001]
    ch. 6) gloss -nak / -nek exclusively as dative; [caha-2008] §5
    (pp. 266–267) explicitly addresses Hungarian as the textbook
    Blake-hierarchy surface counterexample, citing Blake's own footnote
    that the GEN-less inventory is resolved by treating the dative as
    expressing possessor function. The inventory has rank 3 (DAT) on
    Caha's containment hierarchy without rank 2 (GEN), failing
    downward closure. (Note: this is a counterexample to the
    `containmentRank`-based downward-closure predicate, which encodes
    Blake's hierarchy in Caha's notation; it is *not* a counterexample
    to Caha 2008's (28), which is about suffix-vs-postposition ordering
    and holds vacuously here since Hungarian marks all cases suffixally.) -/
theorem hungarian_not_respectsCaha :
    ¬ RespectsCahaContainment Hungarian.Case.caseInventory := by decide

/-! ## § 4: Slavic paradigm-shape syncretism (Caha §§8.3.1-4)

The conformer theorems above only check inventory cardinality — a
trivial agreement, since every Slavic 6-case set obviously satisfies
downward-closure. Caha's substantive prediction is about **paradigm
shape**: which morphological cells syncretize within a noun's
declension. This section formalizes the paradigm-shape predictions
for all four Slavic languages Caha analyses in detail. Distinct
shapes are factored into `Slavic.SyncretismPatterns` (§ 4.1) so
per-language sections are docstring + attestation lists.

Distinct shapes are collected once below, so each language's section is its attestation list. -/

namespace Slavic

/-- Caha's Slavic-specific Case sequence ([caha-2009] (16), p. 12
    for Russian; (7) p. 238 confirms the same for Serbian): NOM – ACC –
    GEN – PREP/LOC – DAT – INS. Re-export from
    `Case.cahaSlavicRank` (the substrate definition). For
    the relationship to `containmentRank` (LOC at top, INST
    off-hierarchy), see `Case.cahaSlavicRank_vs_containmentRank`. -/
abbrev slavicRank : Case → Option (Fin 6) :=
  Case.cahaSlavicRank

/-- A morphological paradigm encoded as a form-class index per cell.
    Indices correspond to the Slavic case sequence: 0=NOM, 1=ACC,
    2=GEN, 3=PREP/LOC, 4=DAT, 5=INS. Two cells share a form iff their
    indices are equal. -/
abbrev Paradigm := Fin 6 → Nat

/-- Caha's Universal Contiguity ([caha-2009] (10), p. 10) on a
    Slavic paradigm. A `Paradigm` is definitionally an n = 6
    `Morphology.Paradigm`, so this is the domain-independent
    contiguity predicate itself (which
    `Morphology.Case.Allomorphy.AllomorphyPattern.IsContiguous`
    specializes at n = 4). -/
abbrev IsContiguous (p : Paradigm) : Prop :=
  Morphology.IsContiguous p

/-- **Universal Contiguity derived** ([caha-2009] (10)): a paradigm is
    realizable by nanosyntactic spellout — context-free lexical entries
    competing under the Superset Principle — iff it is contiguous. The
    constraint Caha states as (10) is the generative capacity of the
    spellout engine, not an independent axiom
    (`Morphology.Containment.isContiguous_iff_spelloutGenerable` at
    n = 6, mirroring Caha's own ch. 2 derivation from the Superset
    Principle). Captures the within-sequence contiguity half of (10);
    the cross-linguistic invariance of the sequence is fixed here
    per-instance by the `Fin 6` order. -/
theorem universalContiguity_iff_spellable (p : Paradigm) :
    IsContiguous p ↔ Morphology.Containment.SupersetSpellable p :=
  Morphology.Containment.isContiguous_iff_spelloutGenerable p

namespace SyncretismPatterns

/-! ### § 4.1: Distinct syncretism patterns attested in Caha's Slavic data

Each pattern is a `Paradigm` (form-class index per cell, indexed
0=NOM, 1=ACC, 2=GEN, 3=LOC/PREP, 4=DAT, 5=INS). Same pattern across
languages = same `def` here; per-language sections below attest which
Caha-cited noun in which language exemplifies each pattern. Names
classify by syncretism structure, not witness lexeme. -/

/-! ### Contiguous patterns (UC-respecting) -/

/-- Animate masculine singular: ACC=GEN + PREP=DAT (Serbian son sîn /
    man muž; Slovene farmer kmèt / I jaz; Ukrainian cashier kasír /
    me ja). Caha 11b + 11d (Serbian); 15b + 15c (Slovene). -/
def animMascSg : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 3

/-- Inanimate masculine / neuter / m-sg-adjective: NOM=ACC + PREP=DAT.
    Serbian city grâd / village sèlo / heart srce; Slovene apple
    jábolko / peach brêskev; Ukrainian big velík (m sg adj).
    Caha 11a + 11d (Serbian); 15a + 15c (Slovene). -/
def inanimMascSg : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 3

/-- Feminine a-stem singular: just PREP=DAT (Serbian sheep òvca).
    Caha 11d. -/
def femAStemSg : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 3 | 5 => 4

/-- Feminine i-stem singular: NOM=ACC + GEN=PREP=DAT triple. Serbian
    death smrt (the (11c) GEN-PREP paradigm Caha cites by name);
    Slovene thread nìt. -/
def femIStemSg : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 2

/-- Plural with NOM≠ACC + PREP=DAT=INS triple. Serbian son sînovi.
    Caha 11d + 11e. -/
def plDistinct : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 3 | 5 => 3

/-- Plural with NOM=ACC + PREP=DAT=INS triple. Serbian village sèla /
    sheep ôvce / death smrti. Caha 11a + 11d + 11e. -/
def plNomAcc : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 2

/-- Dual with NOM=ACC + DAT=INS. Slovene table mîz / farmer kmèt
    (dual). Caha 15a + 15d. -/
def dualNomAccDatIns : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 3

/-- Maximally syncretic contiguous: NOM=ACC + GEN=PREP + DAT=INS
    (three pair-syncretisms). Slovene 'both' dva. -/
def threePairs : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2

/-- Adjective plural: NOM=ACC + GEN=PREP. Ukrainian big velík (pl). -/
def adjPlNomAccGenPrep : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 3

/-- Singular with NOM=ACC=GEN triple. Ukrainian knowledge znannjá. -/
def nomAccGenTripleSg : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3

/-- Singular with GEN=PREP=DAT triple, no NOM=ACC. Ukrainian mother
    mátir (Caha (69) p. 269). -/
def genPrepDatTripleSg : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 2 | 4 => 2 | 5 => 3

/-- Maximally syncretic of all attested: NOM=ACC + GEN=PREP=DAT=INS
    quadruple. Ukrainian '100' sto. -/
def nomAccObliqueQuadSg : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1

/-- NOM=ACC with all 4 oblique cells distinct. Czech window okno sg,
    machine stroj pl, castle kost pl (Caha (29), (30) p. 248). The
    most "minimal" attested non-trivial Slavic paradigm shape — only
    the universal NOM=ACC syncretism, nothing else. -/
def nomAccObliquesDistinct : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4

/-- ACC=GEN (contiguous) plus PREP=INS skipping DAT (non-contiguous).
    Czech bigger m.sg větší (Caha (25) p. 246, (67)i p. 266 prep-ins
    case in m/n adjectives sg). Caha defends the prep-ins component
    as phonological conflation. -/
def accGenPrepInsSkipDat : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 2

/-- TWO non-contiguous syncretisms in one paradigm: NOM=GEN (ABA over
    ACC) + ACC=PREP=DAT (ABA over GEN). Czech ulice 'street' sg
    (Caha (29) p. 248, analyzed via pronominal-vs-nominal endings
    split in (40)–(41) p. 252–253; treated as two accidental
    homophonies restricted to this single paradigm). -/
def streetDoubleABA : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 2

/-! ### Attested non-contiguous patterns (Caha-acknowledged
counterexamples to UC, defended in Caha's prose as phonological or
accidental — see per-language `Counterexamples` sub-namespaces for
witness attribution). -/

/-- PREP=INS skipping DAT — Slovene 'this n.' tô (Caha (18) p. 241,
    defended via -em vs -im phonological collapse in (19) p. 242);
    Ukrainian 'endless' bezkrájij less-frequent variant (Caha (71)
    p. 269, same defense). -/
def prepInsSkipDat : Paradigm
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 2

/-- NOM=INS at the extreme ends of the sequence — Slovene 'traveller'
    pótniki pl (Caha (18) p. 241, defended via tonal differences and
    otrôc-i / otrók-i stem alternation, p. 243). -/
def nomInsExtremeEnds : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 0

/-- ACC=INS skipping GEN/PREP/DAT — Slovene 'this f.' tâ (Caha (18)
    p. 241, admitted as accidental homophony in restricted lexical
    niche, p. 243). -/
def accInsRestricted : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 3 | 5 => 1

/-! ### Which shapes are contiguous -/

/-- The syncretism shapes that respect Universal Contiguity. -/
def contiguousShapes : List Paradigm :=
  [animMascSg, inanimMascSg, femAStemSg, femIStemSg, plDistinct, plNomAcc, dualNomAccDatIns,
   threePairs, adjPlNomAccGenPrep, nomAccGenTripleSg, genPrepDatTripleSg, nomAccObliqueQuadSg,
   nomAccObliquesDistinct]

/-- The attested shapes that violate it, which Caha treats as phonological conflations of distinct
representations or as accidental homophony. -/
def nonContiguousShapes : List Paradigm :=
  [prepInsSkipDat, nomInsExtremeEnds, accInsRestricted, accGenPrepInsSkipDat, streetDoubleABA]

theorem contiguousShapes_contiguous : ∀ p ∈ contiguousShapes, IsContiguous p := by decide

theorem nonContiguousShapes_not_contiguous :
    ∀ p ∈ nonContiguousShapes, ¬ IsContiguous p := by decide

end SyncretismPatterns

/-! ### Hypothetical (non-attested) ABA patterns

Showing the predicate has bite for arbitrary ABA shapes beyond the
specific patterns Caha addresses. Caha predicts these patterns are
unattested in any language. -/

namespace Refutations

/-- NOM=GEN with distinct ACC — would skip an intermediate cell. -/
def nomGenSkipAcc : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 9 | 4 => 9 | 5 => 9

/-- PREP=INS with distinct DAT — would skip the intervening DAT. -/
def hypotheticalPrepInsSkipDat : Paradigm
  | 0 => 9 | 1 => 9 | 2 => 9 | 3 => 0 | 4 => 1 | 5 => 0

/-- NOM=DAT with the three cells between distinct from NOM — a long-range violation spanning four
positions. -/
def nomDatSkipMiddle : Paradigm
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 9

/-- The shapes Caha predicts no language has. -/
def refutedShapes : List Paradigm :=
  [nomGenSkipAcc, hypotheticalPrepInsSkipDat, nomDatSkipMiddle]

theorem refutedShapes_not_contiguous : ∀ p ∈ refutedShapes, ¬ IsContiguous p := by decide

end Refutations

namespace Serbian

/-! ### § 4.2: Serbian (§8.3.1, p. 238-240). Caha's headline: "Serbian can be
thought of as another poster child for Universal Contiguity, with no
violations thereof" (p. 239). Caha's five named syncretism types
(Caha (11), p. 239):

  (a) NOM-ACC: neuters in sg+pl; feminine plurals
  (b) ACC-GEN: singular masculine animates
  (c) GEN-PREP: singular of the 'death' paradigm
  (d) PREP-DAT: almost omnipresent (Caha p. 238 notes PREP/DAT
      differ only in stress on monosyllabic nouns, segmentally
      identical — entertains "in fact only a single 'surface' dat/prep
      case in Serbian")
  (e) DAT-INS: plurals

Serbian attests no Caha-acknowledged counterexamples. -/

/-- All Serbian shapes attested in Caha (9) p. 238 (singular,
    7 nouns) and (10) p. 239 (plural, 7 nouns). The 7 sg paradigms
    reduce to 4 distinct shapes; the 7 pl reduce to 2. -/
def attestedShapes : List Paradigm :=
  [SyncretismPatterns.animMascSg,
   SyncretismPatterns.inanimMascSg,
   SyncretismPatterns.femAStemSg,
   SyncretismPatterns.femIStemSg,
   SyncretismPatterns.plDistinct,
   SyncretismPatterns.plNomAcc]

theorem all_attested_contiguous :
    ∀ p ∈ attestedShapes, IsContiguous p := by decide

end Serbian

namespace Slovene

/-! ### § 4.3: Slovene (§8.3.2, p. 240-244). Per Caha (13) p. 240, Slovene uses
the same Slavic sequence NOM-ACC-GEN-PREP-DAT-INS but, unlike Serbian,
"keeps all the six cases distinct: there is no prep – dat annexion."
Slovene also has dual number — paradigms below are
per-noun-and-number-cell.

Caha's four widespread syncretism types in (15) p. 240:

  (a) NOM-ACC: widespread; in all neuters, in all duals
  (b) ACC-GEN: most pronouns, all masculine animate sg nouns
  (c) PREP-DAT: all singular nouns
  (d) DAT-INS: all duals

Plus the rarer GEN-PREP syncretism (16) p. 241, attested in plural
adjectives, plural/dual personal pronouns, and certain feminine sg
declensions.

Crucially, Slovene also has three Caha-acknowledged counterexamples
(Caha (18) p. 241–242) — see `Counterexamples` sub-namespace below. -/

/-- All Slovene contiguous shapes attested in Caha (14) p. 240,
    (16) p. 241, (17) p. 241. -/
def attestedShapes : List Paradigm :=
  [SyncretismPatterns.animMascSg,    -- 'farmer' kmèt sg, 'jaz' I
   SyncretismPatterns.inanimMascSg,  -- 'apple' jábolko sg, 'peach' brêskev sg
   SyncretismPatterns.dualNomAccDatIns,  -- 'table' mîz du, 'farmer' kmèt du
   SyncretismPatterns.femIStemSg,    -- 'thread' nìt sg
   SyncretismPatterns.threePairs]    -- 'both' dva

theorem all_attested_contiguous :
    ∀ p ∈ attestedShapes, IsContiguous p := by decide

namespace Counterexamples

/-! Three paradigms (Caha (18) p. 241–242) that violate Universal
Contiguity at the segmental level. Caha defends each in the
surrounding prose (p. 242–243) as either phonological conflation
((19): 'this n.' PREP=INS via -em vs -im tonal collapse, visible
distinctly in 'that' tîst-em vs tîst-im where prefixation strips
the tone; tonal: 'traveller' NOM=INS via acute/circumflex pl tone
plus the otrôc-i / otrók-i 'child' stem alternation evidence) or
accidental homophony (ACC=INS in 'this f.', restricted to one
declension of feminine singulars). -/

/-- Slovene attestations of non-contiguous patterns:
    - `prepInsSkipDat` ← 'this' n. tô
    - `nomInsExtremeEnds` ← 'traveller' pótniki pl
    - `accInsRestricted` ← 'this' f. tâ -/
def attestedShapes : List Paradigm :=
  [SyncretismPatterns.prepInsSkipDat,
   SyncretismPatterns.nomInsExtremeEnds,
   SyncretismPatterns.accInsRestricted]

theorem all_attested_not_contiguous :
    ∀ p ∈ attestedShapes, ¬ IsContiguous p := by decide

end Counterexamples

end Slovene

namespace Ukrainian

/-! ### § 4.4: Ukrainian (§8.3.4, p. 268-271). Per Caha §8.3.4 p. 268, Ukrainian
also conforms to the Slavic Universal Contiguity sequence
NOM-ACC-GEN-PREP-DAT-INS. Caha's data (68) p. 268 illustrates
NOM-ACC, ACC-GEN, GEN-PREP, and PREP-DAT pairs. Two "possibly
offensive" syncretisms exist (paradigm variants of 'region' (70) and
adjective 'endless' (71)), but Caha argues they are
paradigm-variant-conditioned and isolated.

Caha (74b) p. 271 highlights that Ukrainian has *removed* a
contiguity violation that earlier stages of the language showed,
"in a way that is predicted by the Superset Principle." -/

/-- All Ukrainian contiguous shapes attested in Caha (68) p. 268
    and (69) p. 269. -/
def attestedShapes : List Paradigm :=
  [SyncretismPatterns.animMascSg,         -- 'cashier' kasír sg, 'me' ja
   SyncretismPatterns.inanimMascSg,       -- 'big' velík m sg adj
   SyncretismPatterns.adjPlNomAccGenPrep, -- 'big' velík pl adj
   SyncretismPatterns.nomAccGenTripleSg,  -- 'knowledge' znannjá sg
   SyncretismPatterns.genPrepDatTripleSg, -- 'mother' mátir sg
   SyncretismPatterns.nomAccObliqueQuadSg] -- '100' sto

theorem all_attested_contiguous :
    ∀ p ∈ attestedShapes, IsContiguous p := by decide

namespace Counterexamples

/-! The "less frequently found alternative" variant of the soft-stem
adjective 'endless' (bezkrájij) shows PREP=INS skipping DAT —
identical shape to Slovene's `Counterexamples.thisN`, addressable
by the same phonological-conflation analysis Caha applies to Slovene
(Caha p. 271, "the homophony represents a phonological conflation of
two underlyingly distinct patterns"). -/

/-- Ukrainian attestation of `prepInsSkipDat` ← 'endless' bezkrájij
    m sg less-frequent variant. -/
def attestedShapes : List Paradigm :=
  [SyncretismPatterns.prepInsSkipDat]

theorem all_attested_not_contiguous :
    ∀ p ∈ attestedShapes, ¬ IsContiguous p := by decide

end Counterexamples

end Ukrainian

namespace Czech

/-! ### § 4.5: Czech (§8.3.3, p. 244-267). Caha's most permissive Slavic
language for syncretism: "When it comes to syncretism, it seems at
first blush that 'anything goes'" (p. 244). Three of Czech's six
cases (ACC, PREP, INS) show 4 of the 5 logically possible
syncretisms with other cases. Caha then argues that most apparent
violations are phonological conflations of distinct underlying
representations or accidental homophonies in restricted niches;
Czech "in fact provides good support for the Universal Contiguity"
(p. 267).

Caha's (67) p. 266 summary table — 10 attested syncretism types in
Czech with extension and status:

  (a) NOM-ACC: widespread, **non-accidental**
  (b) NOM-GEN: 'street' sg only, **accidental homophony**
  (c) NOM-INS: soft C-final m anim Ns, **phonological conflation**
  (d) ACC-GEN: m anim sg, pronouns, **non-accidental**
  (e) ACC-PREP: 'street' sg only, **accidental homophony**
  (f) ACC-INS: f.sg adjs, 'sir' pl, **phonological conflation**
  (g) GEN-PREP: As in pl, Num 'two', some Ns sg, **non-accidental**
  (h) PREP-DAT: nouns sg, **non-accidental**
  (i) PREP-INS: m/n As sg, **phonological conflation**
  (j) DAT-INS: Num 'two', for all-oblique conflation, **non-accidental**

The 5 contiguous types (a, d, g, h, j) all reuse existing
`SyncretismPatterns` shapes attested in Serbian/Slovene/Ukrainian.
The 5 non-contiguous types (b, c, e, f, i) include three already-
encoded shapes (`nomInsExtremeEnds` for c, `accInsRestricted` for f,
`prepInsSkipDat`-style for i) plus two Czech-distinctive shapes
(`streetDoubleABA` for b+e bundled in the ulice paradigm,
`accGenPrepInsSkipDat` for i with ACC=GEN context). -/

/-- Czech contiguous shapes attested per Caha (29)–(33) and (67)
    p. 266. Witness lexemes: machine stroj sg/pl, both oba, that
    f.pl ty, man muž sg, good adj pl m dobrý, etc. -/
def attestedShapes : List Paradigm :=
  [SyncretismPatterns.animMascSg,           -- (67d) m anim sg muž
   SyncretismPatterns.inanimMascSg,         -- machine stroj sg
   SyncretismPatterns.threePairs,           -- (67g+h+j) bundled in 'both' oba
   SyncretismPatterns.adjPlNomAccGenPrep,   -- (67g) good adj pl m dobrý, that f.pl ty
   -- (67a) widespread NOM=ACC: window okno sg, machine stroj pl, castle kost pl
   SyncretismPatterns.nomAccObliquesDistinct]

theorem all_attested_contiguous :
    ∀ p ∈ attestedShapes, IsContiguous p := by decide

namespace Counterexamples

/-! Czech (67b, c, e, f, i) — five non-contiguous syncretism types.
Caha defends each in §8.3.3 prose:

  - NOM-INS (67c): phonological conflation -y → -i after soft
    consonants (Caha p. 248-251, see paradigm 'man' muž pl)
  - NOM-GEN + ACC-PREP (67b+e): both accidental homophonies in
    the ulice 'street' paradigm; Caha (40)-(41) p. 252-253 argues
    pronominal vs nominal ending series split -e1 vs -e2 and -i1 vs -i2
  - ACC-INS (67f): phonological conflation in f.sg adjectives like
    dobrá 'good' (= same shape as Slovene 'this f.' tâ)
  - PREP-INS (67i): phonological conflation in m/n sg adjectives
    like větší 'bigger' (= same shape as Slovene 'this n.' tô,
    plus contiguous ACC=GEN context) -/

def attestedShapes : List Paradigm :=
  [SyncretismPatterns.nomInsExtremeEnds,    -- (67c) man muž pl
   SyncretismPatterns.streetDoubleABA,      -- (67b+e) ulice sg
   SyncretismPatterns.accInsRestricted,     -- (67f) good f.sg dobrá
   SyncretismPatterns.accGenPrepInsSkipDat] -- (67i) bigger m sg větší

theorem all_attested_not_contiguous :
    ∀ p ∈ attestedShapes, ¬ IsContiguous p := by decide

end Counterexamples

end Czech

/-! ### Across the Slavic languages

The five languages investigated share one template, nominative – accusative – genitive –
prepositional – dative – instrumental, and the attestations that violate it are treated as
phonological conflations of distinct representations or, in a few restricted niches, as accidental
homophony. Serbian attests none, Ukrainian one, Slovene three, and Czech, the most permissive,
five. Russian is the running example of the earlier chapters rather than a section of its own, and
takes the same sequence. -/

end Slavic

end Caha2009
