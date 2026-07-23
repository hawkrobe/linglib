import Linglib.Features.Number.Basic
import Linglib.Features.Person.Basic

/-!
# Gã Fragment
[allotey-2021]

Language data for Gã (ISO: gaa), a Kwa (Niger-Congo) language spoken in
Greater Accra, Ghana, covering what [allotey-2021] ("Overt Pronouns of
Infinitival Predicates of Gã") needs for the obligatory-control facts:
pronoun paradigm, TAM marking, complementizer inventory, and embedded
clause typology.

## Coverage

- Subject proclitics (person × number; the paper's Table 3)
- TAM prefixes (future, progressive, perfective) and the irrealis
  marker `á`, realized in embedded control clauses as high tone on
  the subject pronoun
- Complementizer inventory (`akɛ`, `kɛji`, `ni`) with finite vs.
  irrealis distinction; `ni` is optionally overt with some
  control verbs (*tao* 'want', [allotey-2021] ex 34) and
  obligatory with others (*hiɛ-kã-nɔ* 'hope', ex 35)
- Embedded clause typology (three-way: `finiteAke`, `finiteKeji`,
  `irrealisNi`)
- Pro-drop profile

## Identifier policy

Lean 4 does not accept the IPA characters `ɛ` (U+025B) or `ŋ` (U+014B)
as identifier characters. Constructor and definition names use plain
Latin orthography (`ake`, `keji`, `nye`), while the IPA form is
preserved in the corresponding `String` value.

## What is NOT covered (deliberately)

The verb-movement/negation-placement diagnostic ([allotey-2021]'s fifth
non-finiteness argument, after [pollock-1989]: finite verbs raise past
the suffixal negation `-ee`, `-ko`, while irrealis embedded clauses show
a free preverbal negator `ka`, her exx 120–125). Formalizing the raising
argument needs phrase-structure substrate beyond this fragment's
clause-typology schema; the finiteness split it diagnoses is already
carried by `ClauseProperties.unrestrictedTAM`.
-/

namespace Ga

/-! ### Pronoun paradigm -/

/-- Subject proclitic forms (plain subjective series, [allotey-2021]
    Table 3), on the canonical person/number inventory; `none` for cells
    outside Gã's 3 × 2 paradigm. Not covered: the clipped past-tense 1SG
    variant *ĩ* and the impersonal subject pronoun *a*.

    Gã subject pronouns are proclitics on the inflected verb. In
    [allotey-2021]'s OC examples, the embedded subject of a controlled
    `ni`-clause is realized as an overt subject proclitic (ex 3a: `e-` for
    a 3SG controllee) — the embedded subject position cannot be silent.
    Merged with the irrealis marker `á` the 1SG proclitic surfaces as the
    portmanteau *má* (ex 34) rather than plain *mi*. -/
def subjectProclitic : Person → Number → Option String
  | .first,  .singular => some "mi"
  | .second, .singular => some "o"
  | .third,  .singular => some "e"
  | .first,  .plural   => some "wɔ"
  | .second, .plural   => some "nyɛ"
  | .third,  .plural   => some "amɛ"
  | _,       _         => none

/-! ### TAM marking -/

/-- Prefixal TAM categories of the Gã verb (bare root = default past).

    [allotey-2021] uses the future, progressive, and perfective prefixes
    to argue that embedded clauses introduced by `akɛ` and `kɛji` allow
    the full TAM paradigm (finite), while clauses introduced by `ni`
    prohibit tense/aspect marking of any kind and are restricted to
    irrealis (her exx 119, tense-restriction diagnostic). -/
inductive TAM where
  /-- Future prefix `baa-` (historically the ingressive deictic `bà`
      plus the irrealis marker `á`) -/
  | future
  /-- Progressive prefix `mii-` -/
  | progressive
  /-- Perfective prefix `é-` (high tone) -/
  | perfective
  /-- Irrealis marker `á`: no independent verbal prefix in embedded
      control clauses; realized as high tone on the subject pronoun
      (portmanteau *má* for 1SG). True subjunctives double it — high
      tone on pronoun AND verb ([allotey-2021] Table 4). -/
  | irrealis
  deriving DecidableEq, Repr

/-- Segmental exponent of a TAM category; `none` for the irrealis, whose
    marking in embedded control clauses is tonal (on the subject
    pronoun) rather than prefixal. -/
def TAM.exponent : TAM → Option String
  | .future      => some "baa-"
  | .progressive => some "mii-"
  | .perfective  => some "é-"
  | .irrealis    => none

/-- Whether this TAM is part of the unrestricted (finite) paradigm.

    Per [allotey-2021], finite embedded clauses (introduced by
    `akɛ` or `kɛji`) freely host any of the four TAM categories;
    `ni`-clauses are restricted to `.irrealis`. -/
def TAM.isFinite : TAM → Bool
  | .irrealis => false
  | _         => true

/-! ### Complementizers -/

/-- The three complementizers [allotey-2021] discusses. -/
inductive Complementizer where
  /-- `akɛ` — finite complementizer for declarative complements
      (typically utterance and propositional attitude verbs) -/
  | ake
  /-- `kɛji` — finite complementizer for conditional and
      conditional-like complements -/
  | keji
  /-- `ni` — irrealis complementizer; introduces controlled clauses
      (a weak CP: no focus fronting, no independent tense,
      [allotey-2021] exx 107–109). Optionally overt with some control
      verbs (*tao* 'want', ex 34) and obligatory with others
      (*hiɛ-kã-nɔ* 'hope', ex 35). -/
  | ni
  deriving DecidableEq, Repr

def Complementizer.form : Complementizer → String
  | .ake  => "akɛ"
  | .keji => "kɛji"
  | .ni   => "ni"

/-- Whether the complementizer projects a finite (full-TAM) clause. -/
def Complementizer.isFinite : Complementizer → Bool
  | .ni   => false
  | _     => true

/-! ### Embedded clause typology -/

/-- Three embedded clause types in Gã, distinguished by complementizer
    and TAM properties ([allotey-2021]).

    Note: Gã `irrealisNi` clauses always carry an OVERT subject proclitic
    in controlled contexts — there is no null-PRO option. The OC
    properties hold of this overt-subject configuration. -/
inductive EmbeddedClauseType where
  /-- Finite `akɛ`-clause: full TAM, free subject reference, no OC -/
  | finiteAke
  /-- Finite `kɛji`-clause: full TAM, free subject reference, no OC -/
  | finiteKeji
  /-- Irrealis `ni`-clause: irrealis only, obligatory coreference, OC.
      The complementizer `ni` itself may be optional or obligatory
      depending on the matrix verb; the irrealis tone marking and OC
      behavior are constant. -/
  | irrealisNi
  deriving DecidableEq, Repr

/-- Properties distinguishing the three clause types. -/
structure ClauseProperties where
  /-- All four TAM categories available -/
  unrestrictedTAM : Bool
  /-- Noncoreferential embedded subject possible -/
  noncoreferentialSubject : Bool
  /-- Selects one of the finite complementizers (`akɛ`, `kɛji`) -/
  finiteComplementizer : Bool
  deriving DecidableEq, Repr

def clauseProperties : EmbeddedClauseType → ClauseProperties
  | .finiteAke   => ⟨true,  true,  true⟩
  | .finiteKeji  => ⟨true,  true,  true⟩
  | .irrealisNi  => ⟨false, false, false⟩

def clauseComplementizer : EmbeddedClauseType → Complementizer
  | .finiteAke   => .ake
  | .finiteKeji  => .keji
  | .irrealisNi  => .ni

-- The complementizer's finiteness equals the clause's
-- `finiteComplementizer` flag — by construction, not bridge.
theorem complementizer_isFinite_eq_finiteFlag (c : EmbeddedClauseType) :
    (clauseComplementizer c).isFinite = (clauseProperties c).finiteComplementizer := by
  cases c <;> rfl

/-! ### Typological profile -/

/-- Gã does NOT allow null pronominal subjects in matrix clauses:
    every clause requires an overt subject proclitic ([allotey-2021]). -/
def allowsProDrop : Bool := false

end Ga
