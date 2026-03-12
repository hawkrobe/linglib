import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry
import Linglib.Phenomena.ArgumentStructure.Studies.BeaversUdayana2022

/-!
# Indonesian Verbal Predicates
@cite{sneddon-1996} @cite{beavers-udayana-2022}

Indonesian verb entries with voice paradigm forms (*meN-*, *ber-*,
*ter-*, *di-*) and root class annotations from
@cite{beavers-udayana-2022}.

## Root classes

The paper distinguishes three root classes that determine the default
interpretation of the suppressed variable *z* in *ber-* middles:

- **Reflexive roots** (body care/grooming): the conventional expectation
  is self-action, so the default reading of *z* is coreferent with the
  surface subject. Examples: *dandan* 'dress', *cukur* 'shave'.
- **Obviative roots** (all others): the conventional expectation is
  disjoint reference, so the default reading is dispositional/passive.
  Examples: *jual* 'sell', *masak* 'cook'.
- **Causer-unspecified roots** (change-of-state without entailed
  external cause): the verb does not entail an external causer, and
  *ber-* surfaces as *ter-* with an anticausative reading.
  Examples: *buka* 'open', *pecah* 'break'.

## Incorporation

Some verbs additionally license noun incorporation (*ber-V=NP*),
where the incorporated NP classifies the patient. Body-part nouns
are the most productive class. When *diri* 'self' is incorporated,
a reflexive reading arises even for obviative roots.
-/

namespace Fragments.Indonesian.Predicates

open Core.Verbs
open Phenomena.ArgumentStructure.Studies.BeaversUdayana2022

-- ============================================================================
-- § 1: Root Classes
-- ============================================================================

/-- Root class of Indonesian verbs, determining the default interpretation
    of the suppressed variable in *ber-* middles
    (@cite{beavers-udayana-2022}, §3.5, table (58)). -/
inductive RootClass where
  /-- Body care/grooming verbs: default coreferent (*z* = surface subject). -/
  | reflexive
  /-- All other transitive verbs: default disjoint (*z* ≠ surface subject). -/
  | obviative
  /-- Change-of-state verbs without entailed external cause: anticausative
      via *ter-*. The causer is left unspecified in the verb root. -/
  | causerUnspecified
  deriving DecidableEq, BEq, Repr

/-- The root class predicts the default reading of the suppressed variable
    in non-incorporation *ber-* forms. -/
def RootClass.defaultReading : RootClass → SuppressedVarReading
  | .reflexive => .coreferent
  | .obviative => .disjoint
  | .causerUnspecified => .disjoint

-- ============================================================================
-- § 2: Indonesian Verb Entry
-- ============================================================================

/-- An Indonesian verb entry extending VerbCore with voice paradigm forms.

    The four voice prefixes from @cite{sneddon-1996} §§3.1–3.6:
    - *meN-*: agent voice (active)
    - *di-*: patient voice (passive)
    - *ber-*: middle voice (reflexive/dispositional/incorporation)
    - *ter-*: anticausative (allomorph of *ber-* for causer-unspecified roots) -/
structure IndonesianVerbEntry extends VerbCore where
  /-- Active voice *meN-* form (with allomorph selection). -/
  formMeN : Option String := none
  /-- Middle voice *ber-* form. -/
  formBer : Option String := none
  /-- Anticausative *ter-* form. -/
  formTer : Option String := none
  /-- Passive voice *di-* form. -/
  formDi : Option String := none
  /-- Root class determining default middle reading. -/
  rootClass : RootClass
  /-- Body-part or lexical NPs that can incorporate with *ber-*. -/
  incorporatedNPs : List String := []
  /-- Whether *diri* 'self' can incorporate to force reflexive reading. -/
  incorporatesDiri : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- § 3: Verb Entries from Beavers & Udayana 2022
-- ============================================================================

-- § 3a: Dispositional/passive middles (the paper's table (4))

/-- *jual* 'sell': core example of dispositional/passive *ber-* middle.
    Active: *Dia men-jual mobil itu.* 'S/he sold the car.' (the paper's (6a))
    Middle: *Mobil itu ber-jual dengan mudah.* 'The car sells easily.' ((2b))
    Also licenses: incorporation (*ber-jual=baju* (18b)),
    reflexive incorporation (*ber-jual=diri* (26b)). -/
def jual : IndonesianVerbEntry :=
  { form := "jual"
  , complementType := .np
  , formMeN := some "men-jual"
  , formBer := some "ber-jual"
  , formDi := some "di-jual"
  , rootClass := .obviative
  , incorporatedNPs := ["baju", "diri"]
  , incorporatesDiri := true }

/-- *masak* 'cook': dispositional middle.
    Active: *Dia me-masak.* Middle: *ber-masak*.
    (the paper's table (4)). -/
def masak : IndonesianVerbEntry :=
  { form := "masak"
  , complementType := .np
  , formMeN := some "me-masak"
  , formBer := some "ber-masak"
  , formDi := some "di-masak"
  , rootClass := .obviative }

/-- *cuci* 'wash': both dispositional and reflexive readings.
    Active: *Dia men-cuci.* Middle: *ber-cuci*.
    Also licenses body-part incorporation: *ber-cuci=mata* (18a).
    (the paper's table (4) and (18)). -/
def cuci : IndonesianVerbEntry :=
  { form := "cuci"
  , complementType := .np
  , formMeN := some "men-cuci"
  , formBer := some "ber-cuci"
  , formDi := some "di-cuci"
  , rootClass := .obviative
  , incorporatedNPs := ["mata", "kaki", "muka", "mulut", "rambut",
                         "baju", "ikan", "pisang", "diri"]
  , incorporatesDiri := true }

/-- *tambat* 'tie': dispositional middle.
    Active: *Dia men-(t)ambat kapal itu.* 'S/he moored the boat.' ((5a))
    Middle: *Kapal itu ber-tambat dengan mudah.* 'The boat moors easily.' ((5b))
    (the paper's table (4)). -/
def tambat : IndonesianVerbEntry :=
  { form := "tambat"
  , complementType := .np
  , formMeN := some "men-tambat"
  , formBer := some "ber-tambat"
  , formDi := some "di-tambat"
  , rootClass := .obviative }

-- § 3b: Natural reflexives (the paper's table (15))

/-- *dandan* 'dress': canonical natural reflexive.
    Active: *Tono men-dandan Ali.* 'Tono dressed Ali.' ((3a))
    Middle: *Ali ber-dandan.* 'Ali dressed.' ((2a))
    Body care verb — default coreferent reading.
    (the paper's table (15)). -/
def dandan : IndonesianVerbEntry :=
  { form := "dandan"
  , complementType := .np
  , formMeN := some "men-dandan"
  , formBer := some "ber-dandan"
  , formDi := some "di-dandan"
  , rootClass := .reflexive }

/-- *cukur* 'shave': natural reflexive.
    Active: *men-cukur*. Middle: *ber-cukur*.
    (the paper's table (15)). -/
def cukur : IndonesianVerbEntry :=
  { form := "cukur"
  , complementType := .np
  , formMeN := some "men-cukur"
  , formBer := some "ber-cukur"
  , formDi := some "di-cukur"
  , rootClass := .reflexive }

/-- *jemur* 'sunbathe': natural reflexive.
    Active: *men-jemur*. Middle: *ber-jemur*.
    (the paper's table (15)). -/
def jemur : IndonesianVerbEntry :=
  { form := "jemur"
  , complementType := .np
  , formMeN := some "men-jemur"
  , formBer := some "ber-jemur"
  , formDi := some "di-jemur"
  , rootClass := .reflexive }

/-- *sisir* 'comb': natural reflexive.
    Active: *meny-(s)isir*. Middle: *ber-sisir*.
    (the paper's table (15)). -/
def sisir : IndonesianVerbEntry :=
  { form := "sisir"
  , complementType := .np
  , formMeN := some "meny-sisir"
  , formBer := some "ber-sisir"
  , formDi := some "di-sisir"
  , rootClass := .reflexive }

-- § 3c: Anticausatives (the paper's §5)

/-- *buka* 'open': anticausative via *ter-*.
    Active: *Dia mem-buka pintu.* 'S/he opened the door.'
    Anticausative: *Pintu itu ter-buka.* 'The door opened.' ((2d))
    Change-of-state verb without entailed external cause. -/
def buka : IndonesianVerbEntry :=
  { form := "buka"
  , complementType := .np
  , formMeN := some "mem-buka"
  , formTer := some "ter-buka"
  , formDi := some "di-buka"
  , rootClass := .causerUnspecified }

/-- *pecah* 'break': anticausative via *ter-*.
    Active: *Dia mem-(p)ecah jendela.* 'S/he broke the window.'
    Anticausative: *Jendela itu ter-pecah.* 'The window broke.' ((68))
    (the paper's §5, (67)–(68)). -/
def pecah : IndonesianVerbEntry :=
  { form := "pecah"
  , complementType := .np
  , formMeN := some "mem-pecah"
  , formTer := some "ter-pecah"
  , formDi := some "di-pecah"
  , rootClass := .causerUnspecified
  , levinClass := some .break_ }

-- ============================================================================
-- § 4: Root Class → Middle Type Predictions
-- ============================================================================

/-- Reflexive roots predict coreferent default reading. -/
theorem reflexive_root_coreferent :
    RootClass.reflexive.defaultReading = .coreferent := rfl

/-- Obviative roots predict disjoint default reading. -/
theorem obviative_root_disjoint :
    RootClass.obviative.defaultReading = .disjoint := rfl

-- ============================================================================
-- § 5: Per-Verb Verification Theorems
-- ============================================================================

-- § 5a: Root class verification

theorem jual_is_obviative : jual.rootClass = .obviative := rfl
theorem masak_is_obviative : masak.rootClass = .obviative := rfl
theorem cuci_is_obviative : cuci.rootClass = .obviative := rfl
theorem tambat_is_obviative : tambat.rootClass = .obviative := rfl

theorem dandan_is_reflexive : dandan.rootClass = .reflexive := rfl
theorem cukur_is_reflexive : cukur.rootClass = .reflexive := rfl
theorem jemur_is_reflexive : jemur.rootClass = .reflexive := rfl
theorem sisir_is_reflexive : sisir.rootClass = .reflexive := rfl

theorem buka_is_causerUnspecified : buka.rootClass = .causerUnspecified := rfl
theorem pecah_is_causerUnspecified : pecah.rootClass = .causerUnspecified := rfl

-- § 5b: Voice paradigm verification (formBer / formTer presence)

/-- All obviative verbs have ber- forms. -/
theorem jual_has_ber : jual.formBer.isSome = true := rfl
theorem masak_has_ber : masak.formBer.isSome = true := rfl
theorem cuci_has_ber : cuci.formBer.isSome = true := rfl
theorem tambat_has_ber : tambat.formBer.isSome = true := rfl

/-- All reflexive verbs have ber- forms. -/
theorem dandan_has_ber : dandan.formBer.isSome = true := rfl
theorem cukur_has_ber : cukur.formBer.isSome = true := rfl

/-- Causer-unspecified verbs have ter- forms, not ber- forms. -/
theorem buka_has_ter : buka.formTer.isSome = true := rfl
theorem buka_no_ber : buka.formBer.isNone = true := rfl
theorem pecah_has_ter : pecah.formTer.isSome = true := rfl
theorem pecah_no_ber : pecah.formBer.isNone = true := rfl

-- § 5c: Incorporation verification

/-- *jual* licenses diri incorporation → reflexive incorporation middle. -/
theorem jual_incorporates_diri : jual.incorporatesDiri = true := rfl

/-- *cuci* has the richest incorporation paradigm: body parts + diri. -/
theorem cuci_incorporates_diri : cuci.incorporatesDiri = true := rfl
theorem cuci_incorporation_count : cuci.incorporatedNPs.length = 9 := rfl

/-- Reflexive-root verbs (dandan, cukur) do not incorporate lexical NPs
    by default — their ber- forms are already reflexive. -/
theorem dandan_no_incorporation : dandan.incorporatedNPs.length = 0 := rfl
theorem cukur_no_incorporation : cukur.incorporatedNPs.length = 0 := rfl

-- § 5d: Predicted default reading

/-- Obviative verbs predict dispositional/passive middles (disjoint). -/
theorem jual_predicted_reading :
    jual.rootClass.defaultReading = .disjoint := rfl
theorem masak_predicted_reading :
    masak.rootClass.defaultReading = .disjoint := rfl

/-- Reflexive verbs predict inherent reflexive middles (coreferent). -/
theorem dandan_predicted_reading :
    dandan.rootClass.defaultReading = .coreferent := rfl
theorem cukur_predicted_reading :
    cukur.rootClass.defaultReading = .coreferent := rfl

-- § 5e: Levin class bridge

/-- *pecah* is a break-class verb → participates in middle alternation
    (change-of-state) and causative/inchoative alternation. -/
theorem pecah_levin_class :
    pecah.toVerbCore.levinClass = some .break_ := rfl

-- ============================================================================
-- § 6: Aggregate Properties
-- ============================================================================

/-- All 10 verbs in the fragment. -/
def allVerbs : List IndonesianVerbEntry :=
  [jual, masak, cuci, tambat, dandan, cukur, jemur, sisir, buka, pecah]

/-- Every verb has an active meN- form. -/
theorem all_have_men :
    allVerbs.all (fun (v : IndonesianVerbEntry) => v.formMeN.isSome) = true := rfl

/-- Every verb has a passive di- form. -/
theorem all_have_di :
    allVerbs.all (fun (v : IndonesianVerbEntry) => v.formDi.isSome) = true := rfl

/-- Every verb has EITHER ber- OR ter- (middle or anticausative). -/
theorem all_have_middle_or_anticausative :
    allVerbs.all (fun (v : IndonesianVerbEntry) =>
      v.formBer.isSome || v.formTer.isSome) = true := rfl

/-- No verb has BOTH ber- and ter- — they are in complementary
    distribution, as predicted by the root class analysis:
    ber- for reflexive/obviative roots, ter- for causer-unspecified. -/
theorem ber_ter_complementary :
    allVerbs.all (fun (v : IndonesianVerbEntry) =>
      !(v.formBer.isSome && v.formTer.isSome)) = true := rfl

end Fragments.Indonesian.Predicates
