import Linglib.Morphology.Paradigm.Morphome
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Card

/-!
# The typological diversity of morphomes
[herce-2023] [aronoff-1994]

Two paradigm fragments from [herce-2023] (*The Typological Diversity of
Morphomes*, OUP) instantiate `Morphology.IsMorphome`: the Spanish
**L-morphome** and a Darma agreement syncretism. Each is a systematic
syncretism whose cell set is captured by no feature-value conjunction — the
book's operationalization of "unnatural" (a natural class is one
"coextensive with a value or conjunction of values", §1.4). Naturalness is
supplied here as the value-or-conjunction predicate, the canonical
instantiation of `Morphology`'s `Natural` parameter.

Systematicity — recurrence under more than one exponent — is what
distinguishes a morphome from an accidental homophony: the Spanish set
recurs across three lexemes with three different stem alternations, the
Darma set across two voice allomorphs.

## Source caveat

The book's paradigm tables are images, so only cell sets and exponent labels
recoverable from the surrounding prose are encoded (verbatim quotes cited
below); full form-per-cell grids are not reproduced. Location cites are
source-verified: Spanish §1.3 / Table 1.2, pp. 7-8; the definition §1.4,
pp. 10-11; Darma §4.2.2.4, p. 149 (data from Willis 2007).

## Main declarations

* `Herce2023.spanishL_morphome_venir` / `_nacer` / `_caber` — the L-morphome
  is a morphome under three distinct stem alternations
* `Herce2023.darma_morphome_intr` / `_tr` — the Darma 1PL/2 syncretism is a
  morphome under both voice allomorphs
-/

namespace Herce2023

open Morphology

/-! ### Morphome from a kernel-class `Finset`

A reusable bridge: a nontrivial ker-class `Finset` that coincides with no
`Natural` class is a `Morphology.IsMorphome`. -/

section Bridge

variable {Cell S : Type*} [Fintype Cell] [DecidableEq S]

/-- The kernel class of `a` under `f`, as a `Finset`: the cells `f` sends to
`f a`. Its coercion is `Morphology.syncretismClass`. -/
def kerClass (f : Cell → S) (a : Cell) : Finset Cell :=
  Finset.univ.filter (fun c => f c = f a)

theorem coe_kerClass (f : Cell → S) (a : Cell) :
    ↑(kerClass f a) = syncretismClass f a := by
  ext c; simp [kerClass, syncretismClass]

/-- A nontrivial ker-class `Finset` that equals no natural class is a
morphome. -/
theorem isMorphome_of_kerClass (f : Cell → S) (a : Cell) (X : Finset Cell)
    (Natural : Set Cell → Prop) (hker : kerClass f a = X)
    (hnt : 1 < X.card) (hnat : ¬ Natural ↑X) :
    IsMorphome f Natural ↑X := by
  refine ⟨?_, Finset.nontrivial_coe.mpr (Finset.one_lt_card_iff_nontrivial.mp hnt), hnat⟩
  have hX : (↑X : Set Cell) = syncretismClass f a := by rw [← hker, coe_kerClass]
  rw [hX]; exact syncretismClass_mem_classes f a

end Bridge

/-! ### Spanish L-morphome (§1.3, Table 1.2, pp. 7-8)

Verbatim (p. 7): the pattern "encompasses the 1SG present indicative and all
the present subjunctive cells". The present-tense paradigm coordinates below
are local slices (indicative/subjunctive × three persons × two numbers). -/

inductive Mood | ind | sbjv deriving DecidableEq, Fintype, Repr
inductive Per | first | second | third deriving DecidableEq, Fintype, Repr
inductive Num | sg | pl deriving DecidableEq, Fintype, Repr

/-- A present-tense cell: mood, person, number. -/
abbrev SpCell := Mood × Per × Num

/-- The L-morphome cell set: 1SG present indicative together with all six
present subjunctive cells (7 cells). -/
def Lset : Finset SpCell :=
  insert (.ind, .first, .sg) (Finset.univ.filter (fun c => c.1 = .sbjv))

/-- *venir* 'come': velar /g/ stem in the L-cells (vengo, venga…), base
elsewhere. Defined by position, not by `Lset` — the syncretism is derived. -/
def venirStem : SpCell → String
  | (.ind, .first, .sg) => "veng"
  | (.sbjv, _, _)       => "veng"
  | _                   => "ven"

/-- *nacer* 'be born': velar /k/ stem in the L-cells (nazco, nazca…). -/
def nacerStem : SpCell → String
  | (.ind, .first, .sg) => "naθk"
  | (.sbjv, _, _)       => "naθk"
  | _                   => "naθ"

/-- *caber* 'fit': suppletive stem in the L-cells (quepo, quepa…). -/
def caberStem : SpCell → String
  | (.ind, .first, .sg) => "kep"
  | (.sbjv, _, _)       => "kep"
  | _                   => "kab"

/-- A feature specification: each feature is fixed to a value or left open.
A **natural class** is the set of cells matching some spec (coextensive with
a value or conjunction of values, [herce-2023] §1.4). -/
abbrev SpSpec := Option Mood × Option Per × Option Num

/-- Does cell `c` match spec `s` (open features vacuously match)? -/
def spMatches (s : SpSpec) (c : SpCell) : Bool :=
  (match s.1 with | none => true | some m => decide (m = c.1)) &&
  (match s.2.1 with | none => true | some p => decide (p = c.2.1)) &&
  (match s.2.2 with | none => true | some n => decide (n = c.2.2))

/-- The cells matching spec `s`. -/
def spNaturalClass (s : SpSpec) : Finset SpCell :=
  Finset.univ.filter (fun c => spMatches s c = true)

/-- Naturalness for the Spanish space: coextensive with some feature-value
conjunction. -/
def SpNatural (X : Set SpCell) : Prop := ∃ s : SpSpec, ↑(spNaturalClass s) = X

theorem venir_kerClass : kerClass venirStem (.ind, .first, .sg) = Lset := by decide
theorem nacer_kerClass : kerClass nacerStem (.ind, .first, .sg) = Lset := by decide
theorem caber_kerClass : kerClass caberStem (.ind, .first, .sg) = Lset := by decide

theorem Lset_card : 1 < Lset.card := by decide

/-- No feature-value conjunction is coextensive with the L-set: it crosses
the indicative/subjunctive divide, so it is unnatural. -/
theorem Lset_no_natural_class : ∀ s : SpSpec, spNaturalClass s ≠ Lset := by decide

theorem Lset_not_SpNatural : ¬ SpNatural ↑Lset := by
  rintro ⟨s, hs⟩; exact Lset_no_natural_class s (Finset.coe_inj.mp hs)

/-- The L-morphome under *venir*'s velar /g/ alternation. -/
theorem spanishL_morphome_venir : IsMorphome venirStem SpNatural ↑Lset :=
  isMorphome_of_kerClass venirStem (.ind, .first, .sg) Lset SpNatural
    venir_kerClass Lset_card Lset_not_SpNatural

/-- The same cell set under *nacer*'s velar /k/ alternation — recurrence
across a distinct exponent is what makes it systematic. -/
theorem spanishL_morphome_nacer : IsMorphome nacerStem SpNatural ↑Lset :=
  isMorphome_of_kerClass nacerStem (.ind, .first, .sg) Lset SpNatural
    nacer_kerClass Lset_card Lset_not_SpNatural

/-- The same cell set under *caber*'s stem suppletion. -/
theorem spanishL_morphome_caber : IsMorphome caberStem SpNatural ↑Lset :=
  isMorphome_of_kerClass caberStem (.ind, .first, .sg) Lset SpNatural
    caber_kerClass Lset_card Lset_not_SpNatural

/-! ### Darma 1PL/2 syncretism (§4.2.2.4, p. 149; Willis 2007)

Verbatim: "verbal agreement is characterized by a syncretism of 1PL and 2 …
The formal affinity … is, therefore, morphomic." The shared n-based suffix
is *-he* in intransitive verbs, *-de* in transitive verbs. Only the attested
three-cell set and the two allomorph labels are encoded; the full grid is an
image (see the source caveat). -/

/-- The two voice allomorphs of the n-suffix (-he intr, -de tr). -/
inductive Voice | intr | tr deriving DecidableEq, Fintype, Repr

/-- A Darma agreement cell: person, number. -/
abbrev DCell := Per × Num

/-- The syncretic set: 1PL, 2SG, 2PL (three cells). -/
def Dset : Finset DCell := {(.first, .pl), (.second, .sg), (.second, .pl)}

/-- The n-based agreement suffix, keyed by voice: the syncretic cells bear
it (value = the voice allomorph), other cells are left uncharacterized
(`none`), since the full grid is not recoverable. Defined by position. -/
def darmaAgr (v : Voice) : DCell → Option Voice
  | (.first, .pl)  => some v
  | (.second, _)   => some v
  | _              => none

/-- A Darma feature spec (person × number). -/
abbrev DSpec := Option Per × Option Num

def dMatches (s : DSpec) (c : DCell) : Bool :=
  (match s.1 with | none => true | some p => decide (p = c.1)) &&
  (match s.2 with | none => true | some n => decide (n = c.2))

def dNaturalClass (s : DSpec) : Finset DCell :=
  Finset.univ.filter (fun c => dMatches s c = true)

def DNatural (X : Set DCell) : Prop := ∃ s : DSpec, ↑(dNaturalClass s) = X

theorem darma_kerClass_intr : kerClass (darmaAgr .intr) (.second, .sg) = Dset := by decide
theorem darma_kerClass_tr : kerClass (darmaAgr .tr) (.second, .sg) = Dset := by decide

theorem Dset_card : 1 < Dset.card := by decide

/-- {1PL, 2SG, 2PL} crosses persons 1 and 2 and fixes no number, so no
feature-value conjunction is coextensive with it. -/
theorem Dset_no_natural_class : ∀ s : DSpec, dNaturalClass s ≠ Dset := by decide

theorem Dset_not_DNatural : ¬ DNatural ↑Dset := by
  rintro ⟨s, hs⟩; exact Dset_no_natural_class s (Finset.coe_inj.mp hs)

/-- The 1PL/2 syncretism is a morphome under the intransitive allomorph -he. -/
theorem darma_morphome_intr : IsMorphome (darmaAgr .intr) DNatural ↑Dset :=
  isMorphome_of_kerClass (darmaAgr .intr) (.second, .sg) Dset DNatural
    darma_kerClass_intr Dset_card Dset_not_DNatural

/-- …and under the transitive allomorph -de: recurrence across the two
allomorphs establishes systematicity. -/
theorem darma_morphome_tr : IsMorphome (darmaAgr .tr) DNatural ↑Dset :=
  isMorphome_of_kerClass (darmaAgr .tr) (.second, .sg) Dset DNatural
    darma_kerClass_tr Dset_card Dset_not_DNatural

end Herce2023
