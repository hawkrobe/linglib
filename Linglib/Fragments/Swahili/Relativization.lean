import Linglib.Core.Relativization.Basic
import Linglib.Typology.Relativization.Defs
import Linglib.Fragments.Swahili.Basic

/-!
# Swahili Relativization Fragment
@cite{scott-2021} @cite{keenan-comrie-1977}

Swahili *amba*-relative clauses use the overt complementizer *amba*
(related to *ku-amba* 'say'), which agrees with the head noun in noun
class via a suffix. The head appears before the complementizer.

## Two Types of Resumptive Pronouns

@cite{scott-2021} shows Swahili distinguishes two types of resumptive
pronouns that coexist within the same language and are morphologically
distinct:

1. **Bound resumptives** (person-matching): *-mi* (1SG), *-we* (2SG),
   *-si* (1PL), *-nyi* (2PL). These are base-generated bound pronouns
   that obligatorily match the extractee in person features. Found inside
   adjunct islands.

2. **Movement resumptives** (personless): *-ye* (class 1 SG), *-o*
   (class 2 PL). These are lower copies of Ā-movement chains, reduced
   by chain reduction at PF (PersP deleted by MaxElide). Found in
   parasitic gap constructions.

## Resumption Trigger

Resumption is phonologically motivated: it occurs only on objects of
monosyllabic prepositions (*na* 'with', *ya* 'of', *mwa* 'in') to
satisfy a bimoraic Minimality requirement. Multisyllabic prepositions
(*katika* 'on') do not trigger resumption — they are dropped instead.

## Resumptive Pronoun Paradigm

| Person | Singular | Plural |
|--------|----------|--------|
| 1st    | -mi      | -si    |
| 2nd    | -we      | -nyi   |
| 3rd    | -ye      | -o     |

The 3rd person forms *-ye* and *-o* are also the noun class 1/2
(animate) resumptive pronouns (Table 3). The theoretical analysis of
why 1st/2nd person forms carry person features while 3rd person forms
do not is in `Phenomena/Relativization/Studies/Scott2021.lean`.

## Naming convention

Auxiliary types specific to the relativization paradigm carry the
`Rel` prefix (`RelPerson`, `RelGramNum`, `RelMonosyllabicWord`,
`RelNonTriggeringWord`) so they can live at top-level
`Fragments.Swahili` without colliding with morphology-side `Person` or
number features defined in sibling Swahili Fragment files. This follows
the mathlib convention of prefix-disambiguating small support types
rather than nesting them under a sub-namespace.
-/

namespace Fragments.Swahili

open Core

-- ============================================================================
-- § 1: Amba-RC Markers
-- ============================================================================

/-- The *amba*-complementizer with gap (subject and direct object
    extraction). Subject and object agreement are obligatory on the
    verb; no resumptive pronoun appears. -/
def ambaGap : RelClauseMarker :=
  { form := "amba"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject, .directObject]
  , notes := "amba-RC; gap; SU/DO; agreement obligatory on verb" }

/-- The *amba*-complementizer with bound resumptive pronoun
    (person-matching). Objects of monosyllabic prepositions inside
    adjunct islands obligatorily surface with person features.
    @cite{scott-2021} examples (31)–(33). -/
def ambaBound : RelClauseMarker :=
  { form := "amba + bound RP"
  , npRel := .resumptiveBound
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.oblique]
  , notes := "amba-RC; bound resumptive (person-matching); obligatory in islands" }

/-- The *amba*-complementizer with movement resumptive pronoun
    (personless). Objects of monosyllabic prepositions in parasitic
    gap constructions surface without person features.
    @cite{scott-2021} examples (36)–(37). -/
def ambaMovement : RelClauseMarker :=
  { form := "amba + movement RP"
  , npRel := .resumptiveMovement
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.oblique]
  , notes := "amba-RC; movement resumptive (personless); in parasitic gaps" }

/-- All Swahili relative clause markers. -/
def relMarkers : List RelClauseMarker := [ambaGap, ambaBound, ambaMovement]

/-- Swahili relativization profile (typological summary). -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .pronounRetention
  , rcPosition := .postNominal
  , lowestRelativizable := .oblique
  , notes := "Gap on subjects (with amba-); resumptive on obliques; "
          ++ "relative marker agrees in noun class" }

-- ============================================================================
-- § 2: Personal Pronoun Paradigm
-- ============================================================================

/-- Person feature in the Swahili relativization paradigm
    (@cite{scott-2021} Table 1). Prefixed `Rel` so it can live at
    top-level `Fragments.Swahili` without colliding with morphology-side
    person features. -/
inductive RelPerson where | first | second | third
  deriving DecidableEq, Repr

/-- Number feature in the Swahili relativization paradigm. -/
inductive RelGramNum where | sg | pl
  deriving DecidableEq, Repr

/-- Full pronoun form. -/
def fullPronoun : RelPerson → RelGramNum → String
  | .first,  .sg => "mimi"
  | .first,  .pl => "sisi"
  | .second, .sg => "wewe"
  | .second, .pl => "nyinyi"
  | .third,  .sg => "yeye"
  | .third,  .pl => "wao"

-- ============================================================================
-- § 3: Resumptive Pronoun Paradigm
-- ============================================================================

/-- Resumptive (suffixal) pronoun forms (@cite{scott-2021} Table 2).
    Person-matching forms: 1st/2nd person specify [PERS].
    Personless defaults: 3rd person = noun class agreement (no [PERS]). -/
def resumptivePronoun : RelPerson → RelGramNum → String
  | .first,  .sg => "-mi"
  | .first,  .pl => "-si"
  | .second, .sg => "-we"
  | .second, .pl => "-nyi"
  | .third,  .sg => "-ye"
  | .third,  .pl => "-o"

/-- Resumptive pronoun by noun class (@cite{scott-2021} Table 3).
    These forms express number and gender only (no person features).
    For animate classes 1/2, the forms *-ye*/*-o* are identical to the
    3rd person resumptive pronouns — this identity is what the
    PersP-deletion analysis explains. -/
def resumptiveByClass : NounClass → String
  | .cl1  => "-ye"   -- Gender A sg
  | .cl2  => "-o"    -- Gender A pl
  | .cl3  => "-o"    -- Gender B sg
  | .cl4  => "-yo"   -- Gender B pl
  | .cl5  => "-lo"   -- Gender C sg
  | .cl6  => "-yo"   -- Gender C pl
  | .cl7  => "-cho"  -- Gender D sg
  | .cl8  => "-vyo"  -- Gender D pl
  | .cl9  => "-yo"   -- Gender E sg
  | .cl10 => "-zo"   -- Gender E pl
  | .cl14 => "-o"    -- abstract
  | .cl15 => "-ko"   -- infinitive
  | .cl16 => "-po"   -- locative
  | .cl17 => "-ko"   -- locative
  | .cl18 => "-mo"   -- locative

-- ============================================================================
-- § 4: Resumptive Pronoun Features (Theory-Neutral Data)
-- ============================================================================

/-- Whether a resumptive pronoun form is person-matching (bound) or
    personless (movement copy). Theory-neutral observable. -/
def resumptivePronounIsPersonMatching : RelPerson → RelGramNum → Bool
  | .first,  _ => true
  | .second, _ => true
  | .third,  _ => false

-- ============================================================================
-- § 5: Resumption Trigger (Phonological Minimality)
-- ============================================================================

/-- Monosyllabic words that trigger resumption. @cite{scott-2021} §3.3:
    resumption is triggered when a monosyllabic word (*na*, *ya*, *mwa*,
    etc.) would otherwise be stranded, violating the bimoraic Minimality
    requirement. These include true prepositions and connectives (the
    form *na* functions as both). -/
inductive RelMonosyllabicWord where
  | na    -- preposition/connective: 'with', 'to', 'by'
  | ya    -- connective: 'of' (associative -a + class prefix)
  | mwa   -- connective: 'in' (-a + class 18 prefix mu-)
  deriving DecidableEq, Repr

/-- Words whose objects do NOT trigger resumption when relativized.
    For trisyllabic words like *katika* 'on', the preposition is dropped
    instead. Noun-like words (*uvunguni* 'under', *chini* 'below',
    *kando* 'beside') must be followed by a monosyllabic connective,
    so it is the connective (not the noun-like word) that determines
    resumption. @cite{scott-2021} (22)–(23). -/
inductive RelNonTriggeringWord where
  | katika    -- 'on', 'in' (trisyllabic; dropped under relativization)
  deriving DecidableEq, Repr

/-- Monosyllabic words always trigger resumption. -/
def RelMonosyllabicWord.triggersResumption : RelMonosyllabicWord → Bool
  | _ => true

/-- Trisyllabic words never trigger resumption. -/
def RelNonTriggeringWord.triggersResumption : RelNonTriggeringWord → Bool
  | _ => false

end Fragments.Swahili
