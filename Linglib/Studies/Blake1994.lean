module

public import Mathlib.Data.Finset.Option
public import Mathlib.Order.UpperLower.Basic
public import Linglib.Syntax.Case.Order
public import Linglib.Fragments.Dargwa.Case
public import Linglib.Fragments.Finnish.Case
public import Linglib.Fragments.German.Case
public import Linglib.Fragments.Greek.Ancient.Case
public import Linglib.Fragments.Greek.StandardModern.Case
public import Linglib.Fragments.Hindi.Case
public import Linglib.Fragments.Hungarian.Case
public import Linglib.Fragments.Icelandic.Case
public import Linglib.Fragments.Japanese.Case
public import Linglib.Fragments.Korean.Case
public import Linglib.Fragments.Latin.Case
public import Linglib.Fragments.Slavic.Czech.Case
public import Linglib.Fragments.Slavic.Polish.Case
public import Linglib.Fragments.Slavic.Serbian.Case
public import Linglib.Fragments.Slavic.Slovak.Case
public import Linglib.Fragments.Tamil.Case
public import Linglib.Fragments.Telugu.Case
public import Linglib.Fragments.Turkish.Case

/-!
# Blake (1994): Case

Blake surveys inflectional case systems from two members to a dozen and finds that they tend to
be built up in one order: nominative, then accusative or ergative, genitive, dative, locative,
ablative or instrumental, and then the rest. A language with a case at some position usually has
a case at every position to its left. The vocative is set aside, since it marks no relation of a
dependent to a head.

Blake stresses that this is a tendency and not an implicational universal. Bound pronouns and
word order can do the work of a higher case, which leaves a gap, as with the Nanai genitive. And
the lowest case of a small system is an elsewhere case of many functions, labelled by convention
for the highest of them, which leaves an apparent gap where a lower function sits. The Latin
ablative is such a case, merging an older ablative, instrumental and locative, and its label is
in Blake's words somewhat arbitrary: the Latin labels skip the locative position, and the
functions the Latin cases express fill it.

## Main definitions

* `Position`, `position`: the positions of the hierarchy and the position of a case, with the
  vocative off the hierarchy.
* `positions`, `gaps`: the positions an inventory fills, and the unfilled ones to the left of a
  filled one.
* `Conforms`: an inventory fills every position to the left of each position it fills.

## Main results

* `Conforms.total`: the position sets of two conforming inventories are nested, so that conforming
  systems lie along a single line of growth.
* `gaps_subset_of_conforms`: when the functions of a language's cases conform, a gap among its
  case labels is a position filled by a function some case is not labelled for.
* `systems_conform`, `gaps_nanai`, `gaps_tarascan`: the systems Blake cites at each stage conform,
  and his two gapped systems each miss one position.
* `gaps_latin_inventory`, `conforms_latin_functions`: the Latin labels skip the locative and the
  Latin functions do not.
* `latin_abl_functions_ancient_greek`, `latin_dat_functions_ssubset_ancient_greek`: Greek has no
  ablative, its genitive and dative expressing the functions of the Latin one, and its dative is
  the more comprehensive case.
* `gaps_finnish`, `gaps_hungarian`, `gaps_dargwa`: the gaps among the fragment inventories.

## Implementation notes

The absolutive is placed with the nominative, since Blake calls the unmarked case of an ergative
system nominative. His systems with a purposive, Toda, Irula and Warndarang, are left out, the
purposive not being a `Case` value. The text was checked in the second edition ([blake-2001]).

## References

* [blake-1994]
* [blake-2001]
-/

@[expose] public section

namespace Blake1994

/-! ### The hierarchy -/

/-- The positions of the hierarchy, from the nominative down. Accusative and ergative share a
position, as do ablative and instrumental, and the cases past them all share the last. -/
inductive Position where
  | nom
  | accErg
  | gen
  | dat
  | loc
  | ablInst
  | other
  deriving DecidableEq, Fintype, Repr

/-- The place of a position in the sequence. -/
def Position.rank : Position → Fin 7
  | .nom => 0
  | .accErg => 1
  | .gen => 2
  | .dat => 3
  | .loc => 4
  | .ablInst => 5
  | .other => 6

theorem Position.rank_injective : Function.Injective Position.rank := by decide

instance : LinearOrder Position := LinearOrder.lift' Position.rank Position.rank_injective

/-- The position of a case. A local case goes by its direction, a case of rest with the locative
and a case of source with the ablative, and the vocative has no position. -/
def position : Case → Option Position
  | .nom | .abs => some .nom
  | .acc | .erg => some .accErg
  | .gen => some .gen
  | .dat => some .dat
  | .inst => some .ablInst
  | .voc => none
  | c =>
    match c.dirOf with
    | some .place => some .loc
    | some .source => some .ablInst
    | _ => some .other

/-- The positions an inventory fills. -/
def positions (inv : Finset Case) : Finset Position := inv.biUnion fun c ↦ (position c).toFinset

/-- An inventory conforms to the hierarchy when it fills every position to the left of each
position it fills. -/
def Conforms (inv : Finset Case) : Prop := IsLowerSet (positions inv : Set Position)

/-- The gaps of an inventory are the unfilled positions to the left of a filled one. -/
def gaps (inv : Finset Case) : Finset Position :=
  Finset.univ.filter fun q ↦ q ∉ positions inv ∧ ∃ p ∈ positions inv, q < p

variable {inv inv' : Finset Case} {p q : Position}

theorem mem_positions : p ∈ positions inv ↔ ∃ c ∈ inv, position c = some p := by
  simp [positions, Option.mem_def]

theorem mem_gaps : q ∈ gaps inv ↔ q ∉ positions inv ∧ ∃ p ∈ positions inv, q < p := by
  simp [gaps]

instance : Decidable (Conforms inv) :=
  inferInstanceAs (Decidable (∀ a b : Position, b ≤ a → a ∈ positions inv → b ∈ positions inv))

/-- Conformity in Blake's own wording, that a language with a case at some position has a case at
each position to its left. -/
theorem conforms_iff :
    Conforms inv ↔
      ∀ c ∈ inv, ∀ p, position c = some p → ∀ q < p, ∃ d ∈ inv, position d = some q := by
  refine ⟨fun h c hc p hp q hq ↦ mem_positions.1 (h hq.le (mem_positions.2 ⟨c, hc, hp⟩)),
    fun h p q hqp hp ↦ ?_⟩
  obtain ⟨c, hc, hcp⟩ := mem_positions.1 hp
  rcases hqp.eq_or_lt with rfl | hlt
  · exact hp
  · exact mem_positions.2 (h c hc p hcp q hlt)

theorem conforms_iff_gaps_eq_empty : Conforms inv ↔ gaps inv = ∅ := by
  refine ⟨fun h ↦ Finset.eq_empty_of_forall_notMem fun q hq ↦ ?_, fun h p q hqp hp ↦ ?_⟩
  · obtain ⟨hq, p, hp, hqp⟩ := mem_gaps.1 hq
    exact hq (h hqp.le hp)
  · by_contra hq
    rcases hqp.eq_or_lt with rfl | hlt
    · exact hq hp
    · exact Finset.notMem_empty q (h ▸ mem_gaps.2 ⟨hq, p, hp, hlt⟩)

theorem positions_mono (h : inv ⊆ inv') : positions inv ⊆ positions inv' :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- Conforming systems lie along one line of growth, since of any two one fills every position
the other fills. -/
theorem Conforms.total (h : Conforms inv) (h' : Conforms inv') :
    positions inv ⊆ positions inv' ∨ positions inv' ⊆ positions inv := by
  simpa using IsLowerSet.total h h'

/-- The vocative is off the hierarchy, so adding it changes nothing. -/
theorem positions_insert_voc : positions (insert .voc inv) = positions inv := by
  simp [positions, Finset.biUnion_insert, position]

/-- Labelling a case for the highest of its functions leaves only apparent gaps. When the case
functions of a language conform, each gap among its case labels is a position that some case
fills with a function it is not labelled for. -/
theorem gaps_subset_of_conforms (h : inv ⊆ inv') (h' : Conforms inv') :
    gaps inv ⊆ positions inv' \ positions inv := fun q hq ↦ by
  obtain ⟨hq, p, hp, hqp⟩ := mem_gaps.1 hq
  exact Finset.mem_sdiff.2 ⟨h' hqp.le (positions_mono h hp), hq⟩

/-! ### The systems Blake cites -/

/-- Classical Armenian, with the Proto-Indo-European system less the vocative. -/
def classicalArmenian : Finset Case := {.nom, .acc, .gen, .dat, .loc, .abl, .inst}

/-- Nanai, where a bound pronoun cross-references the possessor. -/
def nanai : Finset Case := {.nom, .acc, .dat, .loc, .abl, .inst, .all}

/-- Tarascan, where recipients and beneficiaries take the accusative and the locative covers
source and goal as well as location. -/
def tarascan : Finset Case := {.nom, .acc, .gen, .loc, .inst, .com}

/-- The systems Blake cites for the successive stages of the hierarchy, with the four cases of
Ancient Greek (beside its vocative), German and Icelandic, the six of the Slavonic languages and of
Turkish, the seven of Classical Armenian and the eight of Tamil. -/
def systems : List (Finset Case) :=
  [Greek.Ancient.Case.inventory, German.Case.inventory, Icelandic.Case.inventory,
    Polish.Case.inventory, Czech.Case.inventory, Slovak.Case.inventory, Serbian.Case.inventory,
    Turkish.Case.inventory, classicalArmenian, Tamil.Case.inventory]

theorem systems_conform : ∀ inv ∈ systems, Conforms inv := by decide

/-- Nanai has every position down to the last but the genitive. -/
theorem gaps_nanai : gaps nanai = {.gen} := by decide

/-- Tarascan has every position down to the last but the dative. -/
theorem gaps_tarascan : gaps tarascan = {.dat} := by decide

/-! ### Latin

Blake gives Latin as the five-case stage, nominative, accusative, genitive, dative and a last case
of many functions whose label is somewhat arbitrary. -/

/-- The Latin case labels skip the locative. -/
theorem gaps_latin_inventory : gaps Latin.Case.inventory = {.loc} := by decide

/-- The functions the Latin cases express fill every position. -/
theorem positions_latin_functions : positions Latin.Case.functions = Finset.univ := by decide

theorem conforms_latin_functions : Conforms Latin.Case.functions := by decide

/-- The Latin gap is apparent, the locative being a function of a case labelled for another. -/
theorem gaps_latin_inventory_subset :
    gaps Latin.Case.inventory ⊆ positions Latin.Case.functions \ positions Latin.Case.inventory :=
  gaps_subset_of_conforms Latin.Case.inventory_subset_functions conforms_latin_functions

/-! ### Ancient Greek

Blake sets the Ancient Greek dative beside the Latin one to show that cases are compared by the
functions they cover and not by their labels. Greek has no ablative, and the functions of the
Latin ablative fall to the Greek genitive, which expresses source, and to the Greek dative, which
expresses location and instrument, so that the Greek dative is the more comprehensive case. -/

/-- Greek has no ablative, and the functions of the Latin ablative fall to its genitive and
dative. -/
theorem latin_abl_functions_ancient_greek :
    .abl ∉ Greek.Ancient.Case.inventory ∧
      Latin.Case.abl.functions ⊆
        Greek.Ancient.Case.gen.functions ∪ Greek.Ancient.Case.dat.functions := by
  decide

/-- The Greek dative is a more comprehensive case than the Latin dative. -/
theorem latin_dat_functions_ssubset_ancient_greek :
    Latin.Case.dat.functions ⊂ Greek.Ancient.Case.dat.functions := by decide

/-! ### The other case inventories of the fragments -/

/-- Modern Greek, Hindi, Japanese, Korean and Telugu conform. -/
theorem fragments_conform :
    ∀ inv ∈ [Greek.StandardModern.Case.inventory, Hindi.Case.inventory, Japanese.Case.inventory,
      Korean.Case.inventory, Telugu.Case.inventory], Conforms inv := by
  decide

/-- Finnish has no dative, the allative marking the recipient. -/
theorem gaps_finnish : gaps Finnish.Case.inventory = {.dat} := by decide

/-- Hungarian has no genitive, the dative marking the possessor, as in the Pama-Nyungan languages
Blake mentions. -/
theorem gaps_hungarian : gaps Hungarian.Case.inventory = {.gen} := by decide

/-- The grammatical cases of Dargwa skip the locative and the ablative, which belong to its
separate series of local cases. -/
theorem gaps_dargwa : gaps Dargwa.Case.inventory = {.loc, .ablInst} := by decide

end Blake1994
