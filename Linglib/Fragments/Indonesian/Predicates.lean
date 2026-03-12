import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry
import Linglib.Theories.Semantics.Events.ArgumentRealization
import Linglib.Fragments.Indonesian.Morphophonology

/-!
# Indonesian Verbal Predicates
@cite{sneddon-1996} @cite{beavers-udayana-2022}

Indonesian verb entries with voice paradigm forms (*meN-*, *ber-*,
*ter-*, *di-*), root class annotations from @cite{beavers-udayana-2022},
and *ter-* semantic classification (stative, accidental, abilitative)
from @cite{sneddon-1996} §1.265–1.275.

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

## *ter-* classification (@cite{sneddon-1996} §1.265–1.275)

The prefix *ter-* has three semantic categories:
- **Stative** (§1.266): result state, no agent (*terbuka* 'open', *tertulis* 'written')
- **Accidental** (§1.267–1.270): unintended action (*terbawa* 'accidentally carried')
- **Abilitative** (§1.272): ability (*terdengar* 'audible', *tidak terbeli* 'unaffordable')

These connect to linglib's semantic infrastructure: accidental *ter-* maps to
`Volitionality.nonvolitional`, abilitative *ter-* expresses circumstantial
modality, and stative *ter-* is agentless.

## Incorporation

Some verbs additionally license noun incorporation (*ber-V=NP*),
where the incorporated NP classifies the patient. Body-part nouns
are the most productive class. When *diri* 'self' is incorporated,
a reflexive reading arises even for obviative roots.
-/

namespace Fragments.Indonesian.Predicates

open Core.Verbs
open Semantics.Events.ArgumentRealization
open Fragments.Indonesian.Morphophonology

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
-- § 1b: ter- Classification (@cite{sneddon-1996} §1.265–1.275)
-- ============================================================================

/-- The three semantic categories of *ter-* verbs, following
    @cite{sneddon-1996} §1.265–1.275.

    - **Stative** (§1.266): refers to a resulting state, not an action.
      No agent is possible. Corresponds to *di-* passives but describes
      the state rather than the action: *tertulis* 'written (in a state)'
      vs *ditulis* 'written (by someone)'.
    - **Accidental** (§1.267–1.270): unintended, involuntary action.
      Contrasts with deliberate *di-*: *tertinggal* 'left accidentally'
      vs *ditinggalkan* 'left deliberately'. Can be intransitive or
      transitive. Suffixes (-kan, -i) are usually dropped.
    - **Abilitative** (§1.272): indicates ability to perform the action.
      Almost always negated: *tidak terbeli* 'can't afford'. Suffixes
      (-kan, -i) are regularly retained. Expresses circumstantial
      possibility (Kratzer's modal flavor).

    Some verbs are ambiguous across categories (§1.273): *terbuka* is
    primarily stative ('open') but can be accidental ('opened by accident')
    or abilitative ('managed to open'). The `terClass` field records the
    primary/default reading. -/
inductive TerClass where
  /-- Result state: no agent, no action — the state following an event. -/
  | stative
  /-- Unintended/involuntary action: the agent exists but did not intend
      the action. Suffixes usually dropped. -/
  | accidental
  /-- Ability: the agent can (or usually cannot) perform the action.
      Suffixes retained. Expresses circumstantial modality. -/
  | abilitative
  deriving DecidableEq, BEq, Repr

/-- Whether the *ter-* reading entails the existence of an agent.
    Stative *ter-* is agentless (no *oleh* 'by' phrase possible);
    accidental and abilitative *ter-* allow an (often pronoun) agent
    (@cite{sneddon-1996} §1.266 vs §1.269, §1.272). -/
def TerClass.hasAgent : TerClass → Bool
  | .stative => false
  | .accidental => true
  | .abilitative => true

/-- The volitionality entailed by a *ter-* reading.
    Accidental *ter-* explicitly encodes nonvolitional action;
    stative and abilitative are neutral (stative has no agent,
    abilitative is about capacity not intention). -/
def TerClass.volitionality : TerClass → Volitionality
  | .stative => .neutral
  | .accidental => .nonvolitional
  | .abilitative => .neutral

/-- Whether transitive suffixes (*-kan*, *-i*) are retained in the *ter-* form.
    Abilitative *ter-* regularly retains suffixes: *terpecahkan* 'can be
    solved', *terhindarkan* 'can be avoided' (§1.272, §1.274).
    Accidental *ter-* usually drops them: *terpikir* not *terpikirkan*
    for the accidental reading (§1.270, §1.274).
    Stative *ter-* has no suffix to retain (§1.266). -/
def TerClass.retainsSuffix : TerClass → Bool
  | .stative => false
  | .accidental => false
  | .abilitative => true

-- ============================================================================
-- § 2: Indonesian Verb Entry
-- ============================================================================

/-- An Indonesian verb entry extending VerbCore with voice paradigm forms.

    Voice prefixes follow @cite{sneddon-1996} (§1.167–177 for *ber-*,
    §1.265–275 for *ter-*, §3.26–40 for active/passive voice):
    - *meN-*: agent voice / active (@cite{sneddon-1996} §3.26)
    - *di-*: patient voice / passive (@cite{sneddon-1996} §3.27–28)
    - *ber-*: middle voice — reflexive, dispositional, incorporation
      (@cite{beavers-udayana-2022})
    - *ter-*: stative / accidental / abilitative (@cite{sneddon-1996} §1.265–275);
      analyzed as anticausative for causer-unspecified roots by
      @cite{beavers-udayana-2022} -/
structure IndonesianVerbEntry extends VerbCore where
  /-- Active voice *meN-* form (with allomorph selection). -/
  formMeN : Option String := none
  /-- Middle voice *ber-* form. -/
  formBer : Option String := none
  /-- Anticausative / stative / accidental / abilitative *ter-* form. -/
  formTer : Option String := none
  /-- Semantic class of the *ter-* form (@cite{sneddon-1996} §1.265–1.275). -/
  terClass : Option TerClass := none
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
    Optionally takes *diri* 'self': *ber-jemur (diri)*
    (@cite{sneddon-1996} §1.168; the paper's table (15)). -/
def jemur : IndonesianVerbEntry :=
  { form := "jemur"
  , complementType := .np
  , formMeN := some "men-jemur"
  , formBer := some "ber-jemur"
  , formDi := some "di-jemur"
  , rootClass := .reflexive
  , incorporatesDiri := true }

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
  , terClass := some .stative
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
  , terClass := some .stative
  , formDi := some "di-pecah"
  , rootClass := .causerUnspecified
  , levinClass := some .break_ }

-- § 3d: Stative ter- (@cite{sneddon-1996} §1.266)

/-- *tulis* 'write': stative *ter-*.
    Active: *Surat itu di-tulis(nya) dalam bahasa Inggris.*
      'That letter was written (by him) in English.'
    Stative: *Surat itu ter-tulis dalam bahasa Inggris.*
      'That letter is written in English.'
    The *ter-* form describes the resulting state; the *di-* form
    describes the action. No agent (*oleh*) possible with stative *ter-*.
    (@cite{sneddon-1996} §1.266). -/
def tulis : IndonesianVerbEntry :=
  { form := "tulis"
  , complementType := .np
  , formMeN := some "men-tulis"
  , formTer := some "ter-tulis"
  , terClass := some .stative
  , formDi := some "di-tulis"
  , rootClass := .obviative }

-- § 3e: Accidental ter- (@cite{sneddon-1996} §1.267–1.270)

/-- *bawa* 'carry, bring': accidental *ter-*.
    Active: *Dia mem-bawa koran saudara.* 'He carried your newspaper.'
    Accidental: *Maaf, koran saudara ter-bawa oleh saya.*
      'Sorry, I took your newspaper by mistake.'
    The accidental *ter-* form explicitly marks the action as unintended.
    Contrasts with deliberate *di-bawa*. Agent expressed with *oleh* (§1.269).
    (@cite{sneddon-1996} §1.269, §1.273). -/
def bawa : IndonesianVerbEntry :=
  { form := "bawa"
  , complementType := .np
  , formMeN := some "mem-bawa"
  , formTer := some "ter-bawa"
  , terClass := some .accidental
  , formDi := some "di-bawa"
  , rootClass := .obviative }

-- § 3f: Abilitative ter- (@cite{sneddon-1996} §1.272)

/-- *dengar* 'hear': abilitative *ter-*.
    Active: *Dia men-dengar suara dosen.* 'He heard the lecturer's voice.'
    Abilitative: *Suara dosen tidak ter-dengar dari sini.*
      'The lecturer can't be heard from here.'
    Abilitative *ter-* is usually negated, expressing inability.
    The negated form *tidak terdengar* corresponds to English 'inaudible'.
    (@cite{sneddon-1996} §1.272). -/
def dengar : IndonesianVerbEntry :=
  { form := "dengar"
  , complementType := .np
  , formMeN := some "men-dengar"
  , formTer := some "ter-dengar"
  , terClass := some .abilitative
  , formDi := some "di-dengar"
  , rootClass := .obviative }

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

theorem tulis_is_obviative : tulis.rootClass = .obviative := rfl
theorem bawa_is_obviative : bawa.rootClass = .obviative := rfl
theorem dengar_is_obviative : dengar.rootClass = .obviative := rfl

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

/-- Sneddon ter- verbs also have ter- forms (without ber-). -/
theorem tulis_has_ter : tulis.formTer.isSome = true := rfl
theorem tulis_no_ber : tulis.formBer.isNone = true := rfl
theorem bawa_has_ter : bawa.formTer.isSome = true := rfl
theorem bawa_no_ber : bawa.formBer.isNone = true := rfl
theorem dengar_has_ter : dengar.formTer.isSome = true := rfl
theorem dengar_no_ber : dengar.formBer.isNone = true := rfl

-- § 5c: Incorporation verification

/-- *jual* licenses diri incorporation → reflexive incorporation middle. -/
theorem jual_incorporates_diri : jual.incorporatesDiri = true := rfl

/-- *cuci* has the richest incorporation paradigm: body parts + diri. -/
theorem cuci_incorporates_diri : cuci.incorporatesDiri = true := rfl
theorem cuci_incorporation_count : cuci.incorporatedNPs.length = 9 := rfl

/-- *jemur* 'sunbathe' optionally incorporates *diri* 'self'
    (@cite{sneddon-1996} §1.168: *berjemur (diri)*). -/
theorem jemur_incorporates_diri : jemur.incorporatesDiri = true := rfl

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

-- § 5f: ter- class verification (@cite{sneddon-1996} §1.265–1.275)

theorem buka_ter_stative : buka.terClass = some .stative := rfl
theorem pecah_ter_stative : pecah.terClass = some .stative := rfl
theorem tulis_ter_stative : tulis.terClass = some .stative := rfl
theorem bawa_ter_accidental : bawa.terClass = some .accidental := rfl
theorem dengar_ter_abilitative : dengar.terClass = some .abilitative := rfl

-- § 5g: ter- class semantic bridges

/-- Stative *ter-* has no agent — the *oleh* 'by' phrase is impossible
    (@cite{sneddon-1996} §1.266). -/
theorem stative_no_agent : TerClass.stative.hasAgent = false := rfl

/-- Accidental *ter-* entails the agent acted nonvolitionally
    (@cite{sneddon-1996} §1.267: "unintended, unexpected, sudden"). -/
theorem accidental_nonvolitional :
    TerClass.accidental.volitionality = .nonvolitional := rfl

/-- Accidental *ter-* has an agent (expressed or implied) — unlike stative,
    which is agentless. *Maaf, koran saudara terbawa oleh saya.*
    'Sorry, I took your newspaper by mistake.' (§1.269). -/
theorem accidental_has_agent : TerClass.accidental.hasAgent = true := rfl

/-- Abilitative *ter-* retains transitive suffixes (-kan, -i) from the
    base verb, unlike accidental *ter-*, which drops them
    (@cite{sneddon-1996} §1.272, §1.274). -/
theorem abilitative_retains_suffix :
    TerClass.abilitative.retainsSuffix = true := rfl
theorem accidental_drops_suffix :
    TerClass.accidental.retainsSuffix = false := rfl

/-- The causer-unspecified roots from @cite{beavers-udayana-2022} have
    stative *ter-* — their *ter-* forms describe resulting states, not
    unintended actions or abilities. This connects B&U's root class
    analysis to Sneddon's ter- classification. -/
theorem causer_unspecified_have_stative_ter :
    [buka, pecah].all (fun (v : IndonesianVerbEntry) =>
      v.rootClass == .causerUnspecified && v.terClass == some .stative
    ) = true := rfl

-- ============================================================================
-- § 6: Aggregate Properties
-- ============================================================================

/-- All 13 verbs in the fragment. -/
def allVerbs : List IndonesianVerbEntry :=
  [jual, masak, cuci, tambat, dandan, cukur, jemur, sisir, buka, pecah,
   tulis, bawa, dengar]

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

/-- No verb has BOTH ber- and ter-. For B&U verbs this follows from
    root class (ber- for reflexive/obviative, ter- for causer-unspecified).
    For Sneddon verbs, ter- serves stative/accidental/abilitative functions
    on roots that lack ber- forms. -/
theorem ber_ter_complementary :
    allVerbs.all (fun (v : IndonesianVerbEntry) =>
      !(v.formBer.isSome && v.formTer.isSome)) = true := rfl

/-- The five *ter-* verbs in the fragment. -/
def terVerbs : List IndonesianVerbEntry :=
  allVerbs.filter (fun v => v.formTer.isSome)

/-- Every ter- verb has a ter- class assigned — no unclassified ter- forms. -/
theorem all_ter_classified :
    terVerbs.all (fun (v : IndonesianVerbEntry) =>
      v.terClass.isSome) = true := rfl

/-- The fragment covers all three ter- classes from @cite{sneddon-1996}. -/
theorem ter_classes_covered :
    [TerClass.stative, TerClass.accidental, TerClass.abilitative].all
      (fun tc => terVerbs.any (fun v => v.terClass == some tc)) = true := rfl

-- ============================================================================
-- § 7: meN- Allomorph Verification
-- ============================================================================

/-- Every verb's stored meN- form matches the phonologically derived
    form from @cite{sneddon-1996} §1.5. This proves the stipulated
    forms are not arbitrary — they follow the regular nasal assimilation
    rules. If a root or meN- form is changed incorrectly, this breaks. -/
theorem all_men_forms_derived :
    allVerbs.all (fun (v : IndonesianVerbEntry) =>
      v.formMeN == deriveMeN v.form) = true := by native_decide

end Fragments.Indonesian.Predicates
