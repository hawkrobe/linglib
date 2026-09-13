/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Features.Number.Basic
import Linglib.Features.Person.Basic
import Linglib.Syntax.Category.Complementizer.Basic
import Linglib.Syntax.Category.Verb.Complement.Basic

/-!
# Gã Fragment
[allotey-2021]

Language data for Gã (ISO: gaa), a Kwa (Niger-Congo) language spoken in
Greater Accra, Ghana, covering what [allotey-2021] ("Overt Pronouns of
Infinitival Predicates of Gã") needs for the obligatory-control facts:
pronoun paradigm, TAM marking, complementizer inventory, and embedded
clause typology.

## Coverage

- Pronouns by person, number and case (the paper's Table 3)
- TAM prefixes (future, progressive, perfective) and the irrealis
  marker `á`, realized in embedded control clauses as high tone on
  the subject pronoun
- Complementizer inventory (`akɛ`, `kɛji`, `ni`) as `Complementizer`
  entries; `ni` is optionally overt with some control verbs (*tao*
  'want', [allotey-2021] ex 34) and obligatory with others
  (*hiɛ-kã-nɔ* 'hope', ex 35)
- Embedded clause typology (three-way: `finiteAke`, `finiteKeji`,
  `irrealisNi`), each type with its complementizer and its complement
  `Frame`; the complement-taking verbs live in `Fragments/Ga/Predicates`
- Pro-drop profile

## Identifier policy

Lean 4 does not accept the IPA characters `ɛ` (U+025B) or `ŋ` (U+014B)
as identifier characters. Constructor and definition names use plain
Latin orthography (`ake`, `keji`, `nye`), while the IPA form is
preserved in the corresponding `String` value.

## What is NOT covered (deliberately)

The verb-movement/negation-placement diagnostic ([allotey-2021]'s fifth
non-finiteness argument, after [pollock-1989]: finite verbs raise past
the suffixal negation `-ee`, `-ŋ`, `-ko`, while irrealis embedded clauses
show a free preverbal negator `ka`, exx 120–125). Formalizing the raising
argument needs phrase-structure substrate beyond this fragment's
clause-typology schema; the finiteness split it diagnoses is already
carried by `ClauseProperties.unrestrictedTAM`.

## References

* [allotey-2021]
* [landau-2004]
* [noonan-2007]
* [pollock-1989]
-/

namespace Ga

/-! ### Pronoun paradigm -/

/-- The three case forms of Gã pronouns ([allotey-2021] Table 3). -/
inductive PronounCase where
  | subjective
  | objective
  | possessive
  deriving DecidableEq, Repr

/-- Pronoun forms by person, number and case ([allotey-2021] Table 3); `none`
    outside the 3 × 2 paradigm. Subject pronouns are proclitics on the
    inflected verb and cannot be dropped; only second and third person
    singular distinguish subjective from objective forms, and the possessive
    always matches the subjective. Not covered: the clipped past-tense 1SG
    variant *ĩ* and the impersonal subject pronoun *a*. -/
def pronoun : Person → Number → PronounCase → Option String
  | .first,  .singular, _           => some "mi"
  | .second, .singular, .objective  => some "bo"
  | .second, .singular, _           => some "o"
  | .third,  .singular, .objective  => some "lɛ"
  | .third,  .singular, _           => some "e"
  | .first,  .plural,   _           => some "wɔ"
  | .second, .plural,   _           => some "nyɛ"
  | .third,  .plural,   _           => some "amɛ"
  | _,       _,         _           => none

/-- Subject proclitic forms (the subjective column of Table 3). In
    [allotey-2021]'s OC examples the embedded subject of a controlled
    `ni`-clause is one of these, never silent; merged with the irrealis marker
    the 1SG proclitic surfaces as the portmanteau *má*. -/
def subjectProclitic (p : Person) (n : Number) : Option String := pronoun p n .subjective

/-! ### TAM marking -/

/-- Prefixal TAM categories of the Gã verb (bare root = default past).

    [allotey-2021] uses the future, progressive, and perfective prefixes
    to argue that embedded clauses introduced by `akɛ` and `kɛji` allow
    the full TAM paradigm (finite), while clauses introduced by `ni`
    prohibit tense/aspect marking of any kind and are restricted to
    irrealis (her exx 118–119, tense-restriction diagnostic). -/
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

/-- *akɛ* — the finite declarative complementizer, typing the complements
    of utterance and attitude verbs ([allotey-2021] exx 47–49, 89a). -/
def ake : Complementizer where
  morphs := [.free "akɛ"]
  coding := some .indicative
  force := some .declarative
  verbForm := some .Fin

/-- *kɛji* — the finite complementizer of conditional clauses (ex 97a) and,
    under *le* 'know', of polar and alternative questions ('know if they
    will come', 'know whether you or he bought it', exx 104, 108); glossed
    COND throughout the paper. -/
def keji : Complementizer where
  morphs := [.free "kɛji"]
  coding := some .indicative
  force := some .interrogative
  verbForm := some .Fin

/-- *ni* — the irrealis complementizer of controlled clauses, glossed C and
    the complement's verb INF: a weak CP with no focus fronting and no
    independent tense (exx 107–109). Optionally overt with some control
    verbs (*tao* 'want', ex 34) and obligatory with others (*hiɛ-kã-nɔ*
    'hope', ex 35); homophonous with the focus marker (ex 27). -/
def ni : Complementizer where
  morphs := [.free "ni"]
  coding := some .infinitive
  verbForm := some .Inf

/-- The three clause introducers that can head an embedded C (§5.5.1). -/
def complementizers : List Complementizer := [ake, keji, ni]

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
  /-- The controlled irrealis `ni`-clause: irrealis only, obligatory
      coreference, OC. The complementizer `ni` itself may be optional or
      obligatory depending on the matrix verb; the irrealis tone marking
      and OC behavior are constant. NOT every `ni`-headed clause is of
      this type: `ni` also introduces true subjunctives with lexical
      subjects (*Osa kplɛnɔ ni Taki á-tsɛ́ Momo*, ex 105) and, with
      *dwɛŋ* 'think', finite low-tone complements (exx 110–111). -/
  | irrealisNi
  deriving DecidableEq, Repr

/-- Properties distinguishing the three clause types ([allotey-2021] §5.5). -/
structure ClauseProperties where
  /-- All four TAM categories available (exx 110–111 vs 118–119). -/
  unrestrictedTAM : Bool
  /-- Tense independent of the matrix clause ([landau-2004]'s `[±T]`):
      finite complements host past/progressive/future freely, while
      `ni`-clauses have only "the tense of a possible future" (ex 109). -/
  independentTense : Bool
  /-- Noncoreferential embedded subject possible (exx 110 vs 112). -/
  noncoreferentialSubject : Bool
  /-- Matrix negation licenses an embedded NPI across this clause's
      boundary (exx 116 vs 117). -/
  npiTransparent : Bool
  /-- Focus fronting inside the clause (exx 107–108). -/
  focusFronting : Bool
  /-- Negation precedes the verb (the free negator *ka*, exx 122, 125)
      rather than following it as a suffix (exx 121, 124). -/
  preverbalNegation : Bool
  deriving DecidableEq, Repr

def clauseProperties : EmbeddedClauseType → ClauseProperties
  | .finiteAke   => ⟨true,  true,  true,  false, true,  false⟩
  | .finiteKeji  => ⟨true,  true,  true,  false, true,  false⟩
  | .irrealisNi  => ⟨false, false, false, true,  false, true⟩

/-- The complementizer heading each clause type. -/
def clauseComplementizer : EmbeddedClauseType → Complementizer
  | .finiteAke   => ake
  | .finiteKeji  => keji
  | .irrealisNi  => ni

/-- The complement frame a verb selecting each clause type records: a finite
    declarative for `akɛ`, a finite interrogative for `kɛji`, and for `ni` an
    infinitival whose subject is an overt proclitic in the subjective
    (nominative) form of Table 3 — never null and never a lexical DP
    (exx 40–42). -/
def EmbeddedClauseType.frame : EmbeddedClauseType → Frame
  | .finiteAke  => Frame.finiteClause
  | .finiteKeji => [.clausal (coding := some .indicative) (force := some .interrogative)]
  | .irrealisNi =>
    [.clausal (coding := some .infinitive) (embeddedSubject := some (.overt (some .nom)))]

/-! ### Typological profile -/

/-- Gã does NOT allow null pronominal subjects in matrix clauses:
    every clause requires an overt subject proclitic ([allotey-2021]). -/
def allowsProDrop : Bool := false

end Ga
