import Linglib.Semantics.Verb.Root.Closure
import Linglib.Semantics.Verb.Root.Arity

/-!
# Yukatek Maya Roots as B&K-G Entailment Sets

A representative cross-section of Yukatek roots drawn from [lucy-1994]
ex. (1), (2), (4), and (7), encoded as [beavers-koontz-garboden-2020]-style
entailment sets. The selection covers all four salience profiles
[lucy-1994] identifies in Yukatek: agent-salient, agent-patient salient,
patient-salient, and positional.

## Main declarations

* the root defs (`siit`, `kuc`, `kiim`, `cin`, …): Yukatek roots grouped
  by salience class, each a set of B&K-G kind atoms.
* `Yukatek.Roots.arity`: Coon arity — the root transitives (`=∅` class)
  select a theme; every other sampled root is intransitive.
* `Yukatek.Roots.agentSalientRoots`, `agentPatientSalientRoots`,
  `patientSalientRoots`, `motionRoots`, `positionalRoots`: the class lists.

## Implementation notes

The roots feed the operator inventory in `Operators.lean` and the
orbit-derivation in `Studies/Lucy1994.lean`.

| Source          | Root      | gloss              | profile              | Lucy class            |
|-----------------|-----------|--------------------|----------------------|------------------------|
| ex. (1a)        | `siit'`     | "jump"             | manner               | agent-salient          |
| (text p. 628)   | `tziib`     | "write"            | manner               | agent-salient          |
| ex. (1b)        | `kuc`       | "carry"            | manner, root transitive | agent-patient salient |
| (text p. 629)   | `pis`       | "measure"          | manner, root transitive | agent-patient salient |
| (text p. 629)   | `los`       | "punch"            | manner, root transitive | agent-patient salient |
| ex. (1c) / (2)  | `kiim`      | "die"              | result               | patient-salient        |
| ex. (2)         | `haanCease` | "stop, cease, heal" | result              | patient-salient        |
| ex. (4)         | `luub`      | "fall"             | result               | patient-salient        |
| ex. (4)         | `ok`        | "enter, intrude"   | result               | patient-salient        |
| ex. (7)         | `cin`       | "bend"             | state                | positional             |
| (Yukatek lex.)  | `kul`       | "sit"              | state                | positional             |

Beyond the tabulated core, the patient-salient list also includes `'ah`
"wake", `wen` "sleep", `siih` "be born", `tú'ub'` "be forgotten",
`k'a'ah` "remember", `čú'un` "begin", `č'en` "stop, cease", `hó'op'`
"begin", `hé'el` "rest", `p'át` "remain"; the agent-salient list includes
`mìis` "sweep", `ć'eh` "shout", `paak` "weed". A small representative
subset of motion roots is added: `máan` "pass", `tàal` "come", `b'in`
"go", `nàak` "ascend", `lìik'` "rise". All are encoded with `becomesState`
atoms (no `.motion` atom; see `motion_roots_not_separate_class` for why
"motion" is not a B&K-G feature in Lucy's analysis).

Yukatek `háan` "stop/cease/heal" and `hàan` "eat" differ in vowel tone
(high vs. low): distinct roots with distinct lexical content, disambiguated
by suffixing the gloss. `haanCease` here is the patient-salient cessation
root; `Yukatek.haanEat` (in `VerbClasses.lean`) is the inactive-class but
internally-caused "eat" verb that [bohnemeyer-2004] ex. (9) takes as the
key applicative exception.

The transcription uses ASCII glosses (no IPA diacritics) for identifier
ease; original orthography is preserved in docstrings.
-/

namespace Yukatek.Roots

open Verb

/-! ### Agent-salient roots (manner only, take `=t`) -/

/-- síit' "jump" — manner-of-action activity, underived intransitive
    ([lucy-1994] ex. 1a). No `.motion` atom: jumping is manner-of-action
    regardless of incidental displacement (cf.
    `motion_roots_not_separate_class`). -/
def siit : Root := ⟨"siit'", {.hasManner "jumping"}, none, {}⟩

/-- ¢'iib "write" — manner-of-action activity ([lucy-1994] p. 628). -/
def tziib : Root := ⟨"tziib", {.hasManner "writing"}, none, {}⟩

/-- mìis "sweep" — manner-of-action activity
    ([lucy-1994] agent-salient list). -/
def miis : Root := ⟨"mìis", {.hasManner "sweeping"}, none, {}⟩

/-- ć'eh "shout" — manner-of-action activity
    ([lucy-1994] agent-salient list). -/
def cheh : Root := ⟨"ć'eh", {.hasManner "shouting"}, none, {}⟩

/-- paak "weed" — manner-of-action activity
    ([lucy-1994] agent-salient list). -/
def paak : Root := ⟨"paak", {.hasManner "weeding"}, none, {}⟩

/-! ### Agent-patient salient roots (root transitives, take `=∅`)

These roots "require two arguments and refer to events involving the
action of one entity on another" ([lucy-1994]) — their distinguishing
property is *root transitivity* (`Root.Arity.selectsTheme`, recorded
in `arity` below), not any B&K-G feature configuration. They carry no
`becomesState` atom: 'measure' and 'punch' entail no change of state
(B&K-G class *hit*-type surface-contact verbs as manner-only), so
classing them by `manner + result` would wrongly make every Yukatek
root transitive a Manner/Result-Complementarity violator. -/

/-- kuč "carry" — manner-of-action, lexically transitive
    ([lucy-1994] ex. 1b). Underived transitive; no derivation
    needed. -/
def kuc : Root := ⟨"kuc", {.hasManner "carrying"}, none, {}⟩

/-- p'is "measure" — manner-of-action, lexically transitive
    ([lucy-1994] p. 629). No entailed change of state. -/
def pis : Root := ⟨"pis", {.hasManner "measuring"}, none, {}⟩

/-- lo'š "punch" — manner-of-action, lexically transitive
    ([lucy-1994] p. 629). Surface-contact manner without entailed result,
    like B&K-G's *hit*-type; no `.contact` atom (contact is implicit in
    the manner of striking, not a B&K-G feature in Lucy's typology). -/
def los : Root := ⟨"los", {.hasManner "striking"}, none, {}⟩

/-! ### Patient-salient roots (result only, take `=s`) -/

/-- kíim "die" — spontaneous state change ([lucy-1994] ex. 1c, 2). -/
def kiim : Root := ⟨"kiim", {.becomesState "dead"}, none, {}⟩

/-- háan "stop, cease, heal" ([lucy-1994] patient-salient list,
    p. 630, ex. 2). High-tone vowel: distinct from `Yukatek.haanEat`
    "eat" (low-tone `hàan`), which is `inactive`-class but
    internally caused — see `Fragments/Mayan/Yukatek/VerbClasses.lean`
    and [bohnemeyer-2004] ex. (9). -/
def haanCease : Root := ⟨"háan", {.becomesState "stopped"}, none, {}⟩

/-- lúub' "fall" ([lucy-1994] ex. 4, Table 4). Notionally a motion verb,
    but patterns morphologically with the patient-salient change-of-state
    roots; no `.motion` atom (see `motion_roots_not_separate_class`). -/
def luub : Root := ⟨"luub'", {.becomesState "fallen"}, none, {}⟩

/-- 'ok "enter, intrude" ([lucy-1994] ex. 4, Table 4). Another
    notional motion root that takes `=s` like patient-salient state
    changes. -/
def ok : Root := ⟨"'ok", {.becomesState "inside"}, none, {}⟩

/-! Additional patient-salient roots from the page-630 list. -/

/-- 'ah "wake" ([lucy-1994] patient-salient list). -/
def ah : Root := ⟨"'ah", {.becomesState "awake"}, none, {}⟩

/-- wen "sleep" ([lucy-1994] patient-salient list). State change
    *into* sleep, not the activity of sleeping. -/
def wen : Root := ⟨"wen", {.becomesState "asleep"}, none, {}⟩

/-- siih "be born" ([lucy-1994] patient-salient list). -/
def siih : Root := ⟨"siih", {.becomesState "born"}, none, {}⟩

/-- tú'ub' "be forgotten" ([lucy-1994] patient-salient list). -/
def tuub : Root := ⟨"tú'ub'", {.becomesState "forgotten"}, none, {}⟩

/-- k'a'ah "remember" ([lucy-1994] patient-salient list). -/
def kaah : Root := ⟨"k'a'ah", {.becomesState "remembered"}, none, {}⟩

/-- čú'un "begin" ([lucy-1994] patient-salient list). -/
def chuun : Root := ⟨"čú'un", {.becomesState "begun"}, none, {}⟩

/-- č'en "stop, cease" ([lucy-1994] patient-salient list).
    Distinct from `haanCease` (Lucy lists them as separate entries). -/
def chenCease : Root := ⟨"č'en", {.becomesState "ceased"}, none, {}⟩

/-- hó'op' "begin" ([lucy-1994] patient-salient list). Doublet of
    `chuun`; both gloss as "begin" in the patient-salient list. -/
def hoop : Root := ⟨"hó'op'", {.becomesState "started"}, none, {}⟩

/-- hé'el "rest" ([lucy-1994] patient-salient list). -/
def heel : Root := ⟨"hé'el", {.becomesState "rested"}, none, {}⟩

/-- p'át "remain" ([lucy-1994] patient-salient list). -/
def paat : Root := ⟨"p'át", {.becomesState "remaining"}, none, {}⟩

/-! Motion roots from [lucy-1994] Table 4. These pattern as
    patient-salient (`becomesState` only) — the central typological
    point. See `motion_roots_not_separate_class` and
    `motion_roots_predicted_patient`. -/

/-- máan "pass" ([lucy-1994] Table 4). -/
def maan : Root := ⟨"máan", {.becomesState "passed"}, none, {}⟩

/-- tàal "come" ([lucy-1994] Table 4). -/
def taal : Root := ⟨"tàal", {.becomesState "arrived"}, none, {}⟩

/-- b'in "go" ([lucy-1994] Table 4). -/
def bin : Root := ⟨"b'in", {.becomesState "departed"}, none, {}⟩

/-- nàak "ascend" ([lucy-1994] Table 4). Distinct from
    `Yukatek.naak` "ascend" in `VerbClasses.lean`, which encodes
    Bohnemeyer's stem-class data; both refer to the same Yukatek root. -/
def naak : Root := ⟨"nàak", {.becomesState "ascended"}, none, {}⟩

/-- lìik' "rise" ([lucy-1994] Table 4). -/
def liik : Root := ⟨"lìik'", {.becomesState "risen"}, none, {}⟩

/-! ### Positional roots (state only, take `-tal`) -/

/-- čin "bow, bend down, bend over" ([lucy-1994] ex. 5, 7).
    Positional root; takes `-tal` (or `-lah`) for the inchoative stem. -/
def cin : Root := ⟨"cin", {.hasState "bent"}, none, {}⟩

/-- kul "sit" — positional root (cf. [lucy-1994] ex. 8c on
    relational positional semantics: "x is-seated [on y]"). -/
def kul : Root := ⟨"kul", {.hasState "seated"}, none, {}⟩

/-! ### Root arity -/

/-- The root transitives of this sample — [lucy-1994]'s `=∅` class
    ("some 500 roots form a transitive in this way"; here the three
    sampled members). -/
def rootTransitives : List Root := [kuc, pis, los]

/-- Coon arity for the sampled roots: the `=∅` class selects a theme
    ([coon-2019]'s √TV); every other sampled root is intransitive. -/
def arity (r : Root) : Root.Arity :=
  if r ∈ rootTransitives then .selectsTheme else .noTheme

/-! ### Per-root kind signatures -/

/-! Agent-salient roots → `{.manner}`. -/

theorem siit_signature :
    siit.kinds = {.manner} := by decide
theorem tziib_signature :
    tziib.kinds = {.manner} := by decide
theorem miis_signature :
    miis.kinds = {.manner} := by decide
theorem cheh_signature :
    cheh.kinds = {.manner} := by decide
theorem paak_signature :
    paak.kinds = {.manner} := by decide

/-! Agent-patient salient (root-transitive) roots → `{.manner}`. -/

theorem kuc_signature :
    kuc.kinds = {.manner} := by decide
theorem pis_signature :
    pis.kinds = {.manner} := by decide
theorem los_signature :
    los.kinds = {.manner} := by decide

/-! Patient-salient roots → `{.result}`. -/

theorem kiim_signature :
    kiim.kinds = {.result} := by decide
theorem haanCease_signature :
    haanCease.kinds = {.result} := by decide
theorem luub_signature :
    luub.kinds = {.result} := by decide
theorem ok_signature :
    ok.kinds = {.result} := by decide
theorem ah_signature :
    ah.kinds = {.result} := by decide
theorem wen_signature :
    wen.kinds = {.result} := by decide
theorem siih_signature :
    siih.kinds = {.result} := by decide
theorem tuub_signature :
    tuub.kinds = {.result} := by decide
theorem kaah_signature :
    kaah.kinds = {.result} := by decide
theorem chuun_signature :
    chuun.kinds = {.result} := by decide
theorem chenCease_signature :
    chenCease.kinds = {.result} := by decide
theorem hoop_signature :
    hoop.kinds = {.result} := by decide
theorem heel_signature :
    heel.kinds = {.result} := by decide
theorem paat_signature :
    paat.kinds = {.result} := by decide

/-! Motion roots (also patient-salient) → `{.result}`. -/

theorem maan_signature :
    maan.kinds = {.result} := by decide
theorem taal_signature :
    taal.kinds = {.result} := by decide
theorem bin_signature :
    bin.kinds = {.result} := by decide
theorem naak_signature :
    naak.kinds = {.result} := by decide
theorem liik_signature :
    liik.kinds = {.result} := by decide

/-! Positional roots → `{.state}`. -/

theorem cin_signature :
    cin.kinds = {.state} := by decide
theorem kul_signature :
    kul.kinds = {.state} := by decide

/-! ### Per-root closed kind signatures -/

/-! The collocational closure (`Root.Kinds.close`) adds `.state`
    to any signature containing `.result`, and `.result` + `.state` to
    any containing `.cause`. No Yukatek root here carries a `.cause`
    atom, so only the result→state edge fires. Closure does *not*
    change the Lucy 1994 salience class predicted by `classOf` for
    these roots: arity is closure-invariant, the agent / patient arms
    ignore `.state` membership, and the positional arm (signature
    exactly `{.state}`) is never produced by closure from a
    non-positional base without `.cause`
    (cf. `Lucy1994.predictedClass_closure_invariant`). -/

theorem siit_closed_signature :
    siit.closedKinds = {.manner} := by decide

theorem tziib_closed_signature :
    tziib.closedKinds = {.manner} := by decide

theorem kuc_closed_signature :
    kuc.closedKinds = {.manner} := by decide

theorem pis_closed_signature :
    pis.closedKinds = {.manner} := by decide

theorem los_closed_signature :
    los.closedKinds = {.manner} := by decide

theorem kiim_closed_signature :
    kiim.closedKinds = {.state, .result} := by decide

theorem haanCease_closed_signature :
    haanCease.closedKinds = {.state, .result} := by decide

theorem luub_closed_signature :
    luub.closedKinds = {.state, .result} := by decide

theorem ok_closed_signature :
    ok.closedKinds = {.state, .result} := by decide

theorem cin_closed_signature :
    cin.closedKinds = {.state} := by decide

theorem kul_closed_signature :
    kul.closedKinds = {.state} := by decide

/-! ### Class lists -/

/-- The agent-salient roots in this fragment: roots with manner only,
    expected to take affective `=t`. -/
def agentSalientRoots : List Root := [siit, tziib, miis, cheh, paak]

/-- The agent-patient salient roots: roots with manner and result,
    expected to take zero derivation `=∅`. -/
def agentPatientSalientRoots : List Root := [kuc, pis, los]

/-- The patient-salient roots (excluding the motion subset): roots with
    result only, expected to take causative `=s`. -/
def patientSalientRoots : List Root :=
  [kiim, haanCease, ah, wen, siih, tuub, kaah, chuun, chenCease, hoop,
   heel, paat]

/-- The notional motion roots: cross-linguistically "motion" verbs that
    [lucy-1994] shows pattern as patient-salient (not as a separate
    class) in Yukatek. -/
def motionRoots : List Root := [luub, ok, maan, taal, bin, naak, liik]

/-- The positional roots: pure stative roots, expected to take `-tal`. -/
def positionalRoots : List Root := [cin, kul]

end Yukatek.Roots
