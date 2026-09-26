module

public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Linglib.Fragments.Slavic.Czech.Nouns
public import Linglib.Fragments.Slavic.Serbian.Declension
public import Linglib.Fragments.Slavic.Slovak.Declension
public import Linglib.Fragments.Slavic.Slovenian.Declension
public import Linglib.Fragments.Slavic.Ukrainian.Declension
public import Linglib.Studies.Blake1994

/-!
# Caha (2009): The Nanosyntax of Case

This file formalizes Caha's Universal Contiguity (10): non-accidental case syncretism targets
contiguous regions of a sequence of cases that is the same in every language, nominative,
accusative, genitive, dative, instrumental, comitative. The evidence is the Slavic declensions of
chapter 8, read along the Slavic sequence with the prepositional between the genitive and the
dative (13). The paradigms of Caha's tables that are not contiguous are the ones whose syncretism
he treats as a phonological conflation or an accidental homophony, a Ukrainian variant he leaves
open, and a Slovene paradigm he passes over.

## Main definitions

* `sequence`, `slavicSequence`: the Case sequence (10b) and its Slavic refinement (13)
* `shape`: a paradigm's forms along the Slavic sequence
* `accounts`, `analyses`: Caha's treatment of the paradigms with an offending syncretism
* `Declines`: a noun of the Czech fragment declines a paradigm of the tables at a cell

## Main results

* `exists_position_lt`: Blake's hierarchy orders the cases of the sequence as it does
* `not_isContiguous_iff`: the paradigms of the tables that are not contiguous
* `supersetSpellable_shape`: Superset spellout generates the other paradigms
* `isContiguous_analysis`: the underlying forms Caha gives are contiguous
* `isNone_iff_adjacent`: the syncretisms (67) calls non-accidental are the adjacent ones
* `declines_czechNouns`, `declines_hrad_mesto_iff`, `declines_colloquial_iff`: Caha's literary
  Czech noun paradigms are the fragment's declensions after Short and *Mluvnice češtiny*

## Implementation notes

Two cells are syncretic when their forms are identical, which ignores Caha's shading. Some of his
column headings are wrong, and the fragments gloss the forms: Czech *kost* is 'bone', not 'castle',
the Czech *ta* of note 26 is feminine singular, and the Slovene *dva* of (16) is 'two', not
'both'. The Ukrainian *velíkıj* 'big' is printed *velík-ij* in (69).

## References

* [caha-2009]
* [blake-1994]
* [short-1993-czech]
* [komarek-etal-1986]
-/

@[expose] public section

namespace Caha2009

open Slavic.Declension Morphology Morphology.Containment

/-! ### The Case sequence -/

/-- `sequence` is the Case sequence (10b): nominative, accusative, genitive, dative,
instrumental, comitative. -/
def sequence : Fin 6 → Case := ![.nom, .acc, .gen, .dat, .inst, .com]

/-- Blake's hierarchy, less the positions the sequence leaves out, orders the cases of the sequence
as the sequence does (48): each has a position, and a later case a later one. -/
theorem exists_position_lt {i j : Fin 6} (h : i < j) :
    ∃ p q, Blake1994.position (sequence i) = some p ∧ Blake1994.position (sequence j) = some q ∧
      p < q := by
  revert i j; decide

/-! ### The Slavic paradigms -/

/-- `slavicSequence` is the Slavic sequence (13): nominative, accusative, genitive, prepositional,
dative, instrumental. -/
def slavicSequence : Fin 6 → Cell :=
  ![cell .nom, cell .acc, cell .gen, cell .loc, cell .dat, cell .inst]

/-- `shape p` lists the forms of `p` along the Slavic sequence. -/
def shape (p : Paradigm) : Fin 6 → String := p.form ∘ slavicSequence

/-- `paradigms` lists the paradigms of Caha's Slavic tables. -/
def paradigms : List Paradigm :=
  Serbian.Declension.paradigms ++ Slovenian.Declension.paradigms ++ Czech.Declension.paradigms ++
    Slovak.Declension.paradigms ++ Ukrainian.Declension.paradigms

/-- Caha accounts for an offending syncretism as a phonological conflation of distinct forms or as
an accidental homophony of distinct lexical entries. -/
inductive Account
  | conflation
  | accidental
  deriving DecidableEq, Repr

/-- `accounts` pairs each paradigm Caha accounts for with his account. -/
def accounts : List (Paradigm × Account) :=
  [(Slovenian.Declension.ta_n, .conflation), (Slovenian.Declension.potnik_pl, .conflation),
    (Slovenian.Declension.ta_f, .accidental), (Ukrainian.Declension.bezkrajij_msg', .conflation),
    (Czech.Declension.ulice_sg, .accidental), (Czech.Declension.muz_pl, .conflation),
    (Czech.Declension.dobry_fsg, .conflation), (Czech.Declension.vetsi_msg, .conflation),
    (Czech.Declension.vetsi_nsg, .conflation), (Czech.Declension.vul_pl, .conflation),
    (Czech.Declension.hoch_pl, .conflation), (Czech.Declension.kluk_pl, .conflation)]

/-- `offenders` lists the paradigms Caha accounts for, the Ukrainian variant of 'region' he leaves
open (70), and the Slovene 'lady' (16), whose accusative–instrumental *gospó* he leaves unshaded
although he takes that syncretism to be confined to the declension of 'this'. -/
def offenders : List Paradigm :=
  accounts.map Prod.fst ++ [Ukrainian.Declension.kraj_sg', Slovenian.Declension.gospa_sg]

/-- A paradigm of the tables is not contiguous exactly when it is an offender. -/
theorem not_isContiguous_iff :
    ∀ p ∈ paradigms, ¬ IsContiguous (shape p) ↔ p ∈ offenders := by
  decide +kernel

/-- Superset spellout generates every paradigm of the tables but the offenders. -/
theorem supersetSpellable_shape {p : Paradigm} (hp : p ∈ paradigms) (h : p ∉ offenders) :
    SupersetSpellable (shape p) :=
  (isContiguous_iff_spelloutGenerable _).1 <|
    not_not.1 fun hc ↦ h ((not_isContiguous_iff p hp).1 hc)

/-- `analyses` pairs a paradigm with the underlying ending or lexical index Caha gives each cell,
or `""`: the indexed endings of 'street' (40), the underlying endings of (19), (32), (52), (58)
and note 26, and the endings of p. 270. -/
def analyses : List (Paradigm × (Cell → String)) :=
  [(Czech.Declension.ulice_sg, forms "e1" "i1" "e2" "i2" "i2" "í2"),
    (Czech.Declension.muz_pl, forms "i" "" "" "" "" "y"),
    (Czech.Declension.hoch_pl, forms "" "" "" "" "" "yø"),
    (Czech.Declension.vetsi_nsg, forms "e" "e" "eho" "em" "emu" "ím"),
    (Czech.Declension.dobry_fsg, forms "a" "u" "é" "é" "é" "ou"),
    (Slovenian.Declension.ta_n, forms "" "" "" "" "" "îm"),
    (Ukrainian.Declension.bezkrajij_msg', forms "" "" "" "im" "" "ım")]

/-- Each analyzed paradigm is an offender, and its forms paired with their underlying endings
are contiguous. -/
theorem isContiguous_analysis :
    ∀ a ∈ analyses,
      a.1 ∈ offenders ∧ IsContiguous fun i ↦ (shape a.1 i, a.2 (slavicSequence i)) := by
  decide

/-! ### The Czech syncretisms -/

/-- `Adjacent c d` holds when `d` follows `c` in the Slavic sequence. -/
def Adjacent (c d : Case) : Prop :=
  ∃ i : Fin 5, (slavicSequence i.castSucc).1 = c ∧ (slavicSequence i.succ).1 = d

instance (c d : Case) : Decidable (Adjacent c d) := inferInstanceAs (Decidable (∃ _, _))

/-- `table67` is Caha's summary of the Czech syncretisms (67), each with his account, `none` for
the non-accidental ones. -/
def table67 : List (Case × Case × Option Account) :=
  [(.nom, .acc, none), (.nom, .gen, some .accidental), (.nom, .inst, some .conflation),
    (.acc, .gen, none), (.acc, .loc, some .accidental), (.acc, .inst, some .conflation),
    (.gen, .loc, none), (.loc, .dat, none), (.loc, .inst, some .conflation), (.dat, .inst, none)]

/-- The syncretisms (67) calls non-accidental are the ones of adjacent cases. -/
theorem isNone_iff_adjacent : ∀ r ∈ table67, r.2.2 = none ↔ Adjacent r.1 r.2.1 := by
  decide

/-! ### Caha's Czech nouns and Short's declensions

Caha's Czech noun paradigms are those of the fragment's declension classes, the classes of
[short-1993-czech]'s tables with the stem conditions of [komarek-etal-1986]: each form of the
literary paradigms is one of the forms the fragment gives the noun. The plural of *kluk* 'boy'
depends on the stem conditions, since the tables alone would give *kluki* and *klukech* where Caha
has *kluci* and *klucích*. Caha's *hradu* and *městu* are the locative singular in *-u* that Short
describes beside the tables' *-ě* for the hard inanimates (p. 466) and the neuters (p. 467), and
his colloquial paradigms depart from the literary declension in the locative and the
instrumental. -/

/-- The cell of a Czech noun's declension that a cell of the tables names in the number `m`. -/
def czechCell (c : Cell) (m : Czech.Declension.numbers) : Czech.Declension.Cell :=
  (Subtype.map id (fun _ h ↦ Slavic.Case.coreInventory_subset_fullInventory h) c, m)

/-- A noun of the fragment declines a paradigm of the tables at a cell when the paradigm's form
there is one of the noun's forms at that cell in the paradigm's number. -/
def Declines (n : Czech.Noun) (p : Paradigm) (c : Cell) : Prop :=
  ∃ h : p.number ∈ Czech.Declension.numbers,
    Czech.Declension.segments (p.form c) ∈ n.forms (czechCell c ⟨_, h⟩)

instance (n : Czech.Noun) (p : Paradigm) (c : Cell) : Decidable (Declines n p c) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- The literary paradigms of the tables that decline nouns of the fragment, with the nouns. -/
def czechNouns : List (Paradigm × Czech.Noun) :=
  [(Czech.Declension.muz_sg, Czech.muz), (Czech.Declension.muz_pl, Czech.muz),
    (Czech.Declension.stroj_sg, Czech.stroj), (Czech.Declension.stroj_pl, Czech.stroj),
    (Czech.Declension.kost_sg, Czech.kost), (Czech.Declension.kost_pl, Czech.kost),
    (Czech.Declension.zena_sg, Czech.zena), (Czech.Declension.zena_pl, Czech.zena),
    (Czech.Declension.kluk_pl, Czech.kluk)]

/-- The fragment declines each literary paradigm of the tables in every cell. -/
theorem declines_czechNouns : ∀ x ∈ czechNouns, ∀ c, Declines x.2 x.1 c := by
  decide +kernel

/-- The endings of Short's table on the bare stem do not give Caha's *kluci* and *klucích*. -/
theorem kluk_pl_not_mem_table :
    Czech.Declension.segments (Czech.Declension.kluk_pl.form (cell .nom)) ∉
        (Czech.Declension.Class.chlap.endings (.of .nom .plural)).map (Czech.kluk.stem ++ ·) ∧
      Czech.Declension.segments (Czech.Declension.kluk_pl.form (cell .loc)) ∉
        (Czech.Declension.Class.chlap.endings (.of .loc .plural)).map (Czech.kluk.stem ++ ·) := by
  decide +kernel

/-- The fragment declines Caha's *hrad* and *město* in every cell but the locative, where Caha has
*hradu* and *městu* and the fragment the tables' *hradě* and *městě*. -/
theorem declines_hrad_mesto_iff (c : Cell) :
    (Declines Czech.hrad Czech.Declension.hrad_sg c ↔ c ≠ cell .loc) ∧
      (Declines Czech.mesto Czech.Declension.mesto_sg c ↔ c ≠ cell .loc) := by
  revert c; decide +kernel

/-- The colloquial *klukách* and *klukama* and *mužema* are not the literary declension, which
the colloquial paradigms follow in the other cells. -/
theorem declines_colloquial_iff (c : Cell) :
    (Declines Czech.kluk Czech.Declension.kluk_pl_colloquial c ↔
        c ≠ cell .loc ∧ c ≠ cell .inst) ∧
      (Declines Czech.muz Czech.Declension.muz_pl_colloquial c ↔ c ≠ cell .inst) := by
  revert c; decide +kernel

end Caha2009
