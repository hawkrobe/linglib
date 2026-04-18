import Linglib.Core.Gender
import Linglib.Core.Lexical.Word

/-!
# Gã Fragment
@cite{allotey-2021}

Language data for Gã (ISO: gaa), a Kwa (Niger-Congo) language spoken in
Greater Accra, Ghana. The data here covers what is needed to formalize
the obligatory control facts in @cite{allotey-2021}: pronoun paradigm,
TAM marking, complementizer inventory, and embedded clause typology.

## Coverage

- Pronoun paradigm (subject proclitics, person × number)
- TAM prefixes (future, progressive, perfect) and irrealis tone
- Complementizer inventory (`akɛ`, `kɛji`, `ni`) with finite vs.
  irrealis distinction; `ni` is recorded as optionally-overt because
  @cite{allotey-2021} ex 34 shows it dropping in some controlled
  clauses while ex 35–38 show it obligatorily present
- Embedded clause typology (three-way: `finiteAke`, `finiteKeji`,
  `irrealisNi`)
- Pro-drop / overt-subject profile

## Identifier policy

Lean 4 does not accept the IPA characters `ɛ` (U+025B) or `ŋ` (U+014B)
as identifier characters. Constructor and definition names use the
plain Latin orthography (`ake`, `keji`, `nye`, `kpleno`, `kpang`),
while the IPA form is preserved in the corresponding `String` value.

## What is NOT covered (deliberately)

Verbal negation morphology and the V-to-T raising claim. Both rely on
independent morphological argumentation (@cite{pollock-1989}'s
diagnostic requires a free Neg head; Gã `-ee` and `-ko` appear
suffixal) that is orthogonal to the OC story.
-/

namespace Fragments.Ga

-- ════════════════════════════════════════════════════════════════
-- § 1: Person and Number
-- ════════════════════════════════════════════════════════════════

inductive Person where | first | second | third
  deriving DecidableEq, Repr

inductive Number where | sg | pl
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Pronoun Paradigm
-- ════════════════════════════════════════════════════════════════

/-- Subject proclitic forms.

    Gã subject pronouns are proclitics on the inflected verb. In
    @cite{allotey-2021}'s OC examples, the embedded subject of a
    controlled `ni`-clause is realized as an overt subject proclitic
    (e.g., `e-` for 3SG controllees) — the embedded subject position
    cannot be silent. -/
def subjectProclitic : Person → Number → String
  | .first,  .sg => "mi"
  | .second, .sg => "o"
  | .third,  .sg => "e"
  | .first,  .pl => "wɔ"
  | .second, .pl => "nyɛ"
  | .third,  .pl => "amɛ"

-- ════════════════════════════════════════════════════════════════
-- § 3: TAM Marking
-- ════════════════════════════════════════════════════════════════

/-- Prefixal TAM categories of the Gã verb.

    @cite{allotey-2021} uses the future, progressive, and perfect
    prefixes to argue that embedded clauses introduced by `akɛ` and
    `kɛji` allow the full TAM paradigm (finite), while clauses
    introduced by `ni` are restricted to irrealis (no future,
    progressive, or perfect prefix). -/
inductive TAM where
  /-- Future prefix `baa-` -/
  | future
  /-- Progressive prefix `mii-` -/
  | progressive
  /-- Perfect prefix `é-` (high tone) -/
  | perfect
  /-- Irrealis: no overt prefix; marked by stem high tone (`á`) -/
  | irrealis
  deriving DecidableEq, Repr

def TAM.exponent : TAM → String
  | .future      => "baa-"
  | .progressive => "mii-"
  | .perfect     => "é-"
  | .irrealis    => "á"

/-- Whether this TAM is part of the unrestricted (finite) paradigm.

    Per @cite{allotey-2021}, finite embedded clauses (introduced by
    `akɛ` or `kɛji`) freely host any of the four TAM categories;
    `ni`-clauses are restricted to `.irrealis`. -/
def TAM.isFinite : TAM → Bool
  | .irrealis => false
  | _         => true

-- ════════════════════════════════════════════════════════════════
-- § 4: Complementizers
-- ════════════════════════════════════════════════════════════════

/-- The three complementizers @cite{allotey-2021} discusses. -/
inductive Complementizer where
  /-- `akɛ` — finite complementizer for declarative complements
      (typically utterance and propositional attitude verbs) -/
  | ake
  /-- `kɛji` — finite complementizer for conditional and
      conditional-like complements -/
  | keji
  /-- `ni` — irrealis complementizer; introduces controlled clauses.
      Allotey ex 34 shows `ni` is optional in some controlled clauses
      while ex 35–38 show it obligatorily present. -/
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

-- ════════════════════════════════════════════════════════════════
-- § 5: Embedded Clause Typology
-- ════════════════════════════════════════════════════════════════

/-- Three embedded clause types in Gã, distinguished by complementizer
    and TAM properties (@cite{allotey-2021}).

    Note: Gã `irrealisNi` clauses always carry an OVERT subject proclitic
    in controlled contexts — there is no null-PRO option. The OC
    properties hold of this overt-subject configuration. -/
inductive EmbeddedClauseType where
  /-- Finite `akɛ`-clause: full TAM, free subject reference, no OC -/
  | finiteAke
  /-- Finite `kɛji`-clause: full TAM, free subject reference, no OC -/
  | finiteKeji
  /-- Irrealis `ni`-clause: irrealis only, obligatory coreference, OC.
      The complementizer `ni` itself may be optional (Allotey ex 34) or
      obligatory (ex 35–38) depending on the matrix verb; the irrealis
      tone marking and OC behavior are constant. -/
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

-- ════════════════════════════════════════════════════════════════
-- § 6: Typological Profile
-- ════════════════════════════════════════════════════════════════

/-- Gã does NOT allow null pronominal subjects in matrix clauses:
    every clause requires an overt subject proclitic (@cite{allotey-2021}). -/
def allowsProDrop : Bool := false

/-- Gã has SVO basic order. -/
def basicWordOrder : String := "SVO"

/-- Controlled subjects in `irrealisNi` clauses must be OVERT proclitics
    (@cite{allotey-2021}'s central empirical observation). Null PRO is
    ungrammatical in this position. -/
def controlledSubjectMustBeOvert : Bool := true

end Fragments.Ga
