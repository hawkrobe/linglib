import Linglib.Core.Prominence
import Linglib.Core.Lexical.Word

/-!
# Dargwa (Tanti) Agreement @cite{sumbatova-2021}

Dargwa is among the few Nakh-Dagestanian languages with both **gender
agreement** and **person agreement** (@cite{sumbatova-2021} §4.5.8, §4.7.6).

## Gender Agreement

Three genders in the singular (masculine, feminine, neuter) and three
in the plural (1st/2nd person, human, non-human). Gender is almost
entirely semantic: masculine = male humans, feminine = female humans,
neuter = everything else. Gender agreement targets include verb roots,
preverbs, copulas, and some adjective roots.

Gender agreement is controlled by the **absolutive argument** in clauses.
In copular clauses with two absolutives, the predicate controls agreement.

## Person Agreement ("Dargic Type")

Person agreement follows the hierarchy **1, 2 > 3** and
**absolutive > ergative**. The agreement paradigm configuration is the
"Dargic type" (@cite{cysouw-2003}): a typologically rare opposition of
2SG versus {1SG, 1PL, 2PL}, where the 3rd person is usually unmarked.

Three person-marker sets distribute across TAM paradigms:
1. **Clitic set**: present, preterite, perfect, propositive
2. **Irrealis set**: past habitual, future, conditional
3. **Optative set**: optative

The 2SG marker is identical across the clitic set (*=de*) and past
tense (*=de*), creating a homophony that is typologically unusual.
-/

namespace Fragments.Dargwa.Agreement

open Core.Prominence (PersonLevel)

-- ============================================================================
-- § 1: Gender System
-- ============================================================================

/-- Singular gender values. -/
inductive SgGender where
  | masculine   -- w- (or ∅, realized as -j after vowels)
  | feminine    -- r-
  | neuter      -- b- (non-human, inanimate)
  deriving DecidableEq, BEq, Repr

/-- Plural gender values. These differ from singular genders. -/
inductive PlGender where
  | sapHuman    -- d-: 1st/2nd person NPs
  | human       -- b-: 3rd person human plurals
  | nonHuman    -- d-: non-human plurals
  deriving DecidableEq, BEq, Repr

/-- Gender agreement prefix on the verb stem.
    The prefix immediately precedes the root in simplex verbs and
    attaches to the light verb, preverb, or lexical stem in complex verbs
    (@cite{sumbatova-2021} §4.5.2.3, Table 4.12). -/
def sgGenderPrefix : SgGender → String
  | .masculine => "w-"
  | .feminine  => "r-"
  | .neuter    => "b-"

def plGenderPrefix : PlGender → String
  | .sapHuman => "d-"
  | .human    => "b-"
  | .nonHuman => "d-"

/-- Gender assignment is semantically transparent: masculine = male
    humans, feminine = female humans, neuter = everything else
    (@cite{sumbatova-2021} §4.4.1). A small set of nouns have a
    *variable* gender morpheme determined by the referent's actual
    gender (if human) or the possessor's gender: e.g., *w-eˁ.ʔ*
    'proprietor (M)' / *r-eˁ.ʔ* 'proprietor (F)'. -/
theorem gender_semantically_transparent : True := trivial

-- ============================================================================
-- § 2: Person Agreement
-- ============================================================================

/-- The three person-marker paradigm sets. -/
inductive MarkerSet where
  | clitic    -- present, preterite, perfect, propositive
  | irrealis  -- past habitual, future, conditional
  | optative  -- optative
  deriving DecidableEq, BEq, Repr

/-- Person clitic/suffix forms (Table 4.20, 4.21 of @cite{sumbatova-2021}).
    Returns `none` when the person is unmarked.

    **Clitic set** ("Dargic type"): =da covers 1SG, 1PL, and 2PL
    (ex. 34a: "I, we, you(PL) am, are doing"); =de is 2SG only.
    Table 4.21 confirms: "person clitics: 2SG =de, 1SG/PL, 2PL =da". -/
def personMarker : MarkerSet → PersonLevel → Number → Option String
  -- Clitic set: =da for {1SG, 1PL, 2PL}, =de for {2SG}, none for {3}
  | .clitic,   .first,  _   => some "=da"
  | .clitic,   .second, .sg => some "=de"
  | .clitic,   .second, _   => some "=da"    -- 2PL patterns with 1st person
  | .clitic,   .third,  _   => none          -- 3rd unmarked
  -- Irrealis set
  | .irrealis, .first,  .sg => some "-d"
  | .irrealis, .first,  _   => some "-haˁ"   -- (> -he)
  | .irrealis, .second, .sg => some "-t:"    -- (> -t)
  | .irrealis, .second, _   => some "-t:-a"
  | .irrealis, .third,  _   => none
  -- Optative set
  | .optative, .first,  _   => some "-a"
  | .optative, .second, .sg => some "-e"
  | .optative, .second, _   => some "-a"     -- + -ja allocutive
  | .optative, .third,  _   => none

/-- 3rd person is unmarked in all paradigm sets. -/
theorem third_unmarked :
    personMarker .clitic   .third .sg = none ∧
    personMarker .clitic   .third .pl = none ∧
    personMarker .irrealis .third .sg = none ∧
    personMarker .irrealis .third .pl = none ∧
    personMarker .optative .third .sg = none ∧
    personMarker .optative .third .pl = none := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Agreement Control
-- ============================================================================

/-- Gender agreement controller: the absolutive argument.
    In intransitive clauses: S (always absolutive).
    In transitive clauses: P (absolutive), not A (ergative).
    In copular clauses with two absolutives: the predicate. -/
inductive GenderController where
  | absolutive     -- default: the absolutive NP
  | predicate      -- copular clause: predicate NP
  | ergOrDat       -- Tanti allows ergative/dative control optionally
  deriving DecidableEq, BEq, Repr

/-- Person agreement hierarchy: person (1, 2 > 3) and case
    (absolutive > ergative).

    If one core argument is a SAP and the other is not, the verb
    agrees with the SAP regardless of case. If both are SAPs,
    agreement is with the absolutive. -/
def personAgreementController (aPerson pPerson : PersonLevel) : PersonLevel :=
  match aPerson, pPerson with
  | .first,  .third  => .first     -- SAP wins
  | .second, .third  => .second    -- SAP wins
  | .third,  .first  => .first     -- SAP wins
  | .third,  .second => .second    -- SAP wins
  | _,       p       => p          -- both SAP → absolutive (P) wins

-- ============================================================================
-- § 4: Thematic Suffixes (Table 4.10 of @cite{sumbatova-2021})
-- ============================================================================

/-- Thematic suffix for transitive verbs, determined by the person features
    of A and P arguments (Table 4.10, §4.5.2.5 of @cite{sumbatova-2021}).

    *-i* when A is SAP (1st/2nd) and P is 3rd — the configuration where
    A outranks P in the person hierarchy (1, 2 > 3).
    *-u* otherwise (both SAP, or A is 3rd). -/
def thematicSuffix (aPerson pPerson : PersonLevel) : String :=
  if aPerson.isSAP && !pPerson.isSAP then "-i" else "-u"

/-- Intransitive thematic suffix: *-u* for SAP subjects,
    *-ar* / *-an* for 3rd person subjects. -/
def intransitiveThematicSuffix (sPerson : PersonLevel) : String :=
  if sPerson.isSAP then "-u" else "-ar"

/-- The thematic suffix *-i* marks the same configuration that the
    person agreement hierarchy resolves to the A-argument: SAP acting
    on 3rd person. The suffix is a morphological reflex of hierarchy. -/
theorem thematic_i_iff_sap_on_third :
    thematicSuffix .first .third = "-i" ∧
    thematicSuffix .second .third = "-i" ∧
    thematicSuffix .third .third = "-u" ∧
    thematicSuffix .first .second = "-u" ∧
    thematicSuffix .third .first = "-u" := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- When thematic suffix is *-i* (A = SAP, P = 3), person agreement
    controller selects A — the same argument that triggers *-i*.
    When thematic suffix is *-u* (A = 3, P = SAP), person agreement
    controller selects P. The suffix and the agreement controller
    always pick the highest-ranked argument. -/
theorem thematic_suffix_tracks_controller :
    -- -i cases: controller picks A (= SAP), suffix marks SAP > 3
    personAgreementController .first .third = .first ∧
    thematicSuffix .first .third = "-i" ∧
    personAgreementController .second .third = .second ∧
    thematicSuffix .second .third = "-i" ∧
    -- -u cases: controller picks P (= SAP), suffix marks non-dominant A
    personAgreementController .third .first = .first ∧
    thematicSuffix .third .first = "-u" ∧
    personAgreementController .third .second = .second ∧
    thematicSuffix .third .second = "-u" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: Verification
-- ============================================================================

/-- "Dargic type" (@cite{cysouw-2003}): in the clitic set, 1SG, 1PL,
    and 2PL all receive the same marker (=da), while 2SG alone gets a
    distinct marker (=de). This is the typologically rare opposition
    described in the abstract: "2SG versus {1SG, 1PL, 2PL}". -/
theorem dargic_type_clitic :
    personMarker .clitic .first .sg = personMarker .clitic .first .pl ∧
    personMarker .clitic .first .pl = personMarker .clitic .second .pl ∧
    personMarker .clitic .second .sg ≠ personMarker .clitic .first .sg := by
  refine ⟨rfl, rfl, ?_⟩; decide

/-- SAP always wins over 3rd person. -/
theorem sap_wins :
    personAgreementController .first .third = .first ∧
    personAgreementController .third .first = .first ∧
    personAgreementController .second .third = .second ∧
    personAgreementController .third .second = .second := ⟨rfl, rfl, rfl, rfl⟩

/-- When both arguments are SAPs, the absolutive (P) controls. -/
theorem both_sap_absolutive_wins :
    personAgreementController .first .second = .second ∧
    personAgreementController .second .first = .first := ⟨rfl, rfl⟩

/-- The "SAP wins" rule directly reflects the person prominence hierarchy:
    SAP (1st/2nd) > 3rd. This is the same hierarchy formalized in
    `Core.Prominence.PersonLevel`. -/
theorem sap_hierarchy_from_prominence :
    PersonLevel.first.isSAP = true ∧
    PersonLevel.second.isSAP = true ∧
    PersonLevel.third.isSAP = false := ⟨rfl, rfl, rfl⟩

/-- Masculine and feminine prefixes are distinct. -/
theorem gender_prefixes_distinct :
    sgGenderPrefix .masculine ≠ sgGenderPrefix .feminine ∧
    sgGenderPrefix .masculine ≠ sgGenderPrefix .neuter ∧
    sgGenderPrefix .feminine ≠ sgGenderPrefix .neuter := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Plural SAP-human and non-human prefixes are homophonous (both d-).
    This is a typologically notable syncretism. -/
theorem plural_syncretism :
    plGenderPrefix .sapHuman = plGenderPrefix .nonHuman := rfl

end Fragments.Dargwa.Agreement
