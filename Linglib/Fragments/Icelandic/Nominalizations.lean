import Linglib.Theories.Morphology.DM.Allosemy
import Linglib.Fragments.Icelandic.Predicates

/-!
# Icelandic Nominalization Fragment
@cite{wood-2023} @cite{wood-2015}

Icelandic deverbal nominalizations built with the suffixes -un, -an,
-ing, -sla, and -naður. @cite{wood-2023} Ch. 3 establishes that -un
is the most productive nominalizer, and that nominalizations can
receive CEN (Complex Event Nominal), SEN (Simple Event Nominal),
or RN (Result/Referring Nominal) readings depending on the allosemes
of v and n in the structure [nP n [vP v √ROOT]].

This fragment provides lexical entries for key Icelandic nominalizations,
connecting them to the -st verb data in `Predicates.lean`.
-/

namespace Fragments.Icelandic.Nominalizations

open Morphology.DM.Allosemy
open Fragments.Icelandic.Predicates

-- ============================================================================
-- § 1: Nominalizing Suffixes (@cite{wood-2023} Ch. 3)
-- ============================================================================

/-- Icelandic nominalizing suffixes. All spell out n in different
    morphological contexts — they are NOT different functional heads
    (@cite{wood-2023} Ch. 2 (2.1), Ch. 3).

    The book lists: -un, -ing, -sla, -stur, -a, -n, -Ø, -ð, plus
    others (-aður, -ning). This fragment covers the most common ones. -/
inductive NomSuffix where
  | un     -- most productive: söfn-un 'collection', opn-un 'opening'
  | ing    -- borrowed/Latinate pattern: birting 'publication'
  | sla    -- restricted: ræk-sla 'cultivation'
  | stur   -- restricted: þvo-ttur, les-tur
  | adur   -- restricted: skil-naður (stem -n- + -aður)
  deriving DecidableEq, Repr

/-- PF realization of the suffix. -/
def NomSuffix.form : NomSuffix → String
  | .un    => "-un"
  | .ing   => "-ing"
  | .sla   => "-sla"
  | .stur  => "-stur"
  | .adur  => "-aður"

-- ============================================================================
-- § 2: Nominalization Entry Structure
-- ============================================================================

/-- An Icelandic deverbal nominalization entry. -/
structure IcelandicNom where
  /-- The nominal form. -/
  nomForm : String
  /-- The base verb (active form). -/
  baseVerb : String
  /-- English gloss. -/
  gloss : String
  /-- Nominalizing suffix. -/
  suffix : NomSuffix
  /-- Available readings for this nominal. -/
  availableReadings : List NominalizationReading
  /-- Corresponding -st verb entry, if one exists. -/
  stVerb : Option IcelandicStVerb := none
  /-- Does P-prefixing apply? (Ch. 4) -/
  hasPPrefix : Bool := false
  /-- The prefixed preposition, if any. -/
  prefixedP : Option String := none
  deriving Repr, BEq

-- ============================================================================
-- § 3: Nominalization Data (@cite{wood-2023})
-- ============================================================================

/-- *opnun* 'opening' — from *opna* 'open' (@cite{wood-2023} Ch. 3, Ch. 5).
    CEN: *opnun dyranna tók langan tíma* 'the opening of the door took a long time'
    RN: *opnunin var þöng* 'the opening was narrow' -/
def opnun : IcelandicNom :=
  { nomForm := "opnun"
    baseVerb := "opna"
    gloss := "opening"
    suffix := .un
    availableReadings := [.complexEvent, .simpleEntity]
    stVerb := some opnast }

/-- *söfnun* 'collection' — from *safna* 'collect' (@cite{wood-2023} Ch. 5).
    CEN: *söfnun á sýnum* 'collecting of samples'
    The running example in Ch. 5 for argument structure in CENs. -/
def sofnun : IcelandicNom :=
  { nomForm := "söfnun"
    baseVerb := "safna"
    gloss := "collection"
    suffix := .un
    availableReadings := [.complexEvent, .simpleEntity] }

/-- *þvottur* 'washing' — from *þvo* 'wash' (@cite{wood-2023} Ch. 6).
    CEN: *þvo-ttur Guðrúnar á fötunum* 'Guðrún's washing of the clothes'
    SEN: *Þvo-ttur-inn tók langan tíma* 'The washing took a long time'
    RN: *Þvo-ttur-inn á að fara í vélina* 'The laundry should go in the machine'
    Key example: all three readings available. -/
def pvottur : IcelandicNom :=
  { nomForm := "þvottur"
    baseVerb := "þvo"
    gloss := "washing/laundry"
    suffix := .stur  -- irregular form -ttur, same n head
    availableReadings := [.complexEvent, .simpleEvent, .simpleEntity] }

/-- *misheyrn* 'mishearing' — from *misheyrast* 'mishear' (@cite{wood-2023} Ch. 5).
    Subject-experiencer -st verb; nominalization retains experiencer
    semantics via Poss head. -/
def misheyrn : IcelandicNom :=
  { nomForm := "misheyrn"
    baseVerb := "misheyrast"
    gloss := "mishearing"
    suffix := .un
    availableReadings := [.complexEvent] }

/-- *vöntun* 'need/want' — from *vanta* 'need' (@cite{wood-2023} Ch. 5).
    Ambiguous between target and experiencer interpretations:
    *vöntun góðs starfsfólks* can mean 'need for good employees' (target)
    or 'the company's need' (experiencer). -/
def vontun : IcelandicNom :=
  { nomForm := "vöntun"
    baseVerb := "vanta"
    gloss := "need"
    suffix := .un
    availableReadings := [.complexEvent, .simpleEvent] }

/-- *viðvörun* 'warning' — from *viðvara* 'warn' (@cite{wood-2023} Ch. 6).
    CEN: *viðvörun Guðrúnar á hættunni* 'Guðrún's warning of the danger'
    SEN/State: *Viðvörunin stóð í mörg ár* 'The warning stood for many years'
    Simple entity: *Ég snerti viðvörunina* 'I touched the warning' -/
def vidvorun : IcelandicNom :=
  { nomForm := "viðvörun"
    baseVerb := "viðvara"
    gloss := "warning"
    suffix := .un
    availableReadings := [.complexEvent, .simpleEvent, .simpleState, .simpleEntity] }

/-- *notkun* 'use' — from *nota* 'use' (@cite{wood-2023} Ch. 5).
    CEN reading; the verbalizer -ka appears in the nominal but not
    in the verb (*nota* vs *not-k-un*). -/
def notkun : IcelandicNom :=
  { nomForm := "notkun"
    baseVerb := "nota"
    gloss := "use"
    suffix := .un
    availableReadings := [.complexEvent] }

/-- *aðdáun* 'admiration' — from *dást að* 'admire' (@cite{wood-2023} Ch. 6).
    P-prefixing: *að* 'to' must be prefixed to the noun.
    CEN: *Aðdáun Guðrúnar á Maríu* 'Guðrún's admiration of María'
    SEN/State: *Aðdáunin stóð í mörg ár* 'The admiration lasted for many years'
    No concrete entity reading (6.13c is unacceptable). -/
def addaun : IcelandicNom :=
  { nomForm := "aðdáun"
    baseVerb := "dást að"
    gloss := "admiration"
    suffix := .un
    availableReadings := [.complexEvent, .simpleEvent, .simpleState]
    hasPPrefix := true
    prefixedP := some "að" }

/-- *viðgerð* 'repair' — from *gera við* 'fix/repair' (@cite{wood-2023} Ch. 4).
    P-prefixing pattern 2: *við* conditions root meaning and must be
    prefixed, but cannot be doubled as complement. -/
def vidgerd : IcelandicNom :=
  { nomForm := "viðgerð"
    baseVerb := "gera við"
    gloss := "repair"
    suffix := .stur  -- irregular form -ð, same n head
    availableReadings := [.complexEvent, .simpleEntity]
    hasPPrefix := true
    prefixedP := some "við" }

/-- *umönnun* 'taking care of' — from *annast um* (@cite{wood-2023} Ch. 4).
    P-prefixing pattern 2. -/
def umonnun : IcelandicNom :=
  { nomForm := "umönnun"
    baseVerb := "annast um"
    gloss := "taking care of"
    suffix := .un
    availableReadings := [.complexEvent]
    hasPPrefix := true
    prefixedP := some "um" }

/-- All nominalization entries. -/
def allNoms : List IcelandicNom :=
  [opnun, sofnun, pvottur, misheyrn, vontun, vidvorun, notkun,
   addaun, vidgerd, umonnun]

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- -un is the most common suffix in the fragment. -/
theorem un_most_common :
    (allNoms.filter (fun n => n.suffix == .un)).length ≥
    (allNoms.filter (fun n => n.suffix != .un)).length := by decide

/-- All nominalizations have at least one available reading. -/
theorem all_have_readings :
    allNoms.all (fun n => !n.availableReadings.isEmpty) = true := by decide

/-- *opnun* connects to the -st verb *opnast*. -/
theorem opnun_from_opnast :
    opnun.stVerb = some opnast := rfl

/-- *opnun* and *opnast* share the same base verb. -/
theorem opnun_opnast_same_base :
    opnun.baseVerb = (opnast.activeForm.getD "") := rfl

/-- P-prefixed nominalizations have a prefixed preposition. -/
theorem pprefixed_have_p :
    (allNoms.filter (·.hasPPrefix)).all
      (fun n => n.prefixedP.isSome) = true := by decide

/-- *þvottur* has all three basic readings (CEN, SEN, RN). -/
theorem pvottur_three_readings :
    pvottur.availableReadings.length = 3 := rfl

end Fragments.Icelandic.Nominalizations
