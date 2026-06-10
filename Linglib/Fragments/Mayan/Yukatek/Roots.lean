import Linglib.Semantics.Lexical.Roots.Closure

/-!
# Yukatek Maya Roots as B&K-G Entailment Sets

[lucy-1994] [beavers-koontz-garboden-2020]

A representative cross-section of Yukatek roots, drawn from the lists
in [lucy-1994] ex. (1), (2), (4), and (7), and encoded as
[beavers-koontz-garboden-2020]-style entailment sets.

The selection covers all four salience profiles that [lucy-1994]
identifies in Yukatek (agent-salient, agent-patient salient,
patient-salient, positional). The roots feed into the operator
inventory in `Operators.lean` and the orbit-derivation in
`Studies/Lucy1994.lean`.

| Source          | Root      | gloss              | profile              | Lucy class            |
|-----------------|-----------|--------------------|----------------------|------------------------|
| ex. (1a)        | `siit'`     | "jump"             | manner               | agent-salient          |
| (text p. 628)   | `tziib`     | "write"            | manner               | agent-salient          |
| ex. (1b)        | `kuc`       | "carry"            | manner + result      | agent-patient salient  |
| (text p. 629)   | `pis`       | "measure"          | manner + result      | agent-patient salient  |
| (text p. 629)   | `los`       | "punch"            | manner + result      | agent-patient salient  |
| ex. (1c) / (2)  | `kiim`      | "die"              | result               | patient-salient        |
| ex. (2)         | `haanCease` | "stop, cease, heal" | result              | patient-salient        |
| ex. (4)         | `luub`      | "fall"             | result               | patient-salient        |
| ex. (4)         | `ok`        | "enter, intrude"   | result               | patient-salient        |
| ex. (7)         | `cin`       | "bend"             | state                | positional             |
| (Yukatek lex.)  | `kul`       | "sit"              | state                | positional             |

The patient-salient list also includes `'ah` "wake", `wen` "sleep",
`siih` "be born", `tú'ub'` "be forgotten", `k'a'ah` "remember",
`čú'un` "begin", `č'en` "stop, cease", `hó'op'` "begin", `hé'el` "rest",
`p'át` "remain"; the agent-salient list includes `mìis` "sweep",
`ć'eh` "shout", `paak` "weed". For the motion-roots non-class
argument we add a small representative subset: `máan` "pass", `tàal`
"come", `b'in` "go", `nàak` "ascend", `lìik'` "rise". These are all
encoded with `becomesState` atoms (no `.motion` atom; see
`motion_roots_not_separate_class` for why "motion" is *not* a B&K-G
feature in Lucy's analysis).

**Important orthographic note.** Yukatek `háan` "stop/cease/heal" and
`hàan` "eat" differ in vowel tone (high vs. low). They are distinct
roots with distinct lexical content. We disambiguate by suffixing the
gloss: `haanCease` here is the patient-salient cessation root;
`Yukatek.haanEat` (in `VerbClasses.lean`) is the
inactive-class but internally-caused "eat" verb that
[bohnemeyer-2004] ex. (9) takes as the key applicative exception.

The transcription uses ASCII glosses (no IPA diacritics) for ease of
identifier use; original orthography is preserved in docstrings.
-/

namespace Yukatek.Roots

-- ════════════════════════════════════════════════════
-- § 1. Agent-Salient Roots (manner only, take `=t`)
-- ════════════════════════════════════════════════════

/-- síit' "jump" — manner-of-action activity ([lucy-1994] ex. 1a).
    Underived intransitive; takes affective `=t` to transitivise.
    No `.motion` atom: per [lucy-1994], motion is *not* a B&K-G
    feature in Yukatek (cf. `motion_roots_not_separate_class`); jumping
    qualifies as a manner-of-action irrespective of whether it
    incidentally involves displacement. -/
def siit : Root := ⟨"siit'", {.hasManner "jumping"}⟩

/-- ¢'iib "write" — manner-of-action activity ([lucy-1994] p. 628). -/
def tziib : Root := ⟨"tziib", {.hasManner "writing"}⟩

/-- mìis "sweep" — manner-of-action activity
    ([lucy-1994] agent-salient list). -/
def miis : Root := ⟨"mìis", {.hasManner "sweeping"}⟩

/-- ć'eh "shout" — manner-of-action activity
    ([lucy-1994] agent-salient list). -/
def cheh : Root := ⟨"ć'eh", {.hasManner "shouting"}⟩

/-- paak "weed" — manner-of-action activity
    ([lucy-1994] agent-salient list). -/
def paak : Root := ⟨"paak", {.hasManner "weeding"}⟩

-- ════════════════════════════════════════════════════
-- § 2. Agent-Patient Salient Roots (manner + result, take `=∅`)
-- ════════════════════════════════════════════════════

/-- kuč "carry" — action with patient affected ([lucy-1994] ex. 1b).
    Underived transitive; no derivation needed. -/
def kuc : Root := ⟨"kuc",
  {.hasManner "carrying", .becomesState "transported"}⟩

/-- p'is "measure" — action with patient affected ([lucy-1994] p. 629). -/
def pis : Root := ⟨"pis",
  {.hasManner "measuring", .becomesState "measured"}⟩

/-- lo'š "punch" — action with patient affected ([lucy-1994] p. 629).
    No `.contact` atom: contact is implicit in the manner of striking
    rather than a B&K-G feature in Lucy's typology. -/
def los : Root := ⟨"los",
  {.hasManner "striking", .becomesState "punched"}⟩

-- ════════════════════════════════════════════════════
-- § 3. Patient-Salient Roots (result only, take `=s`)
-- ════════════════════════════════════════════════════

/-- kíim "die" — spontaneous state change ([lucy-1994] ex. 1c, 2). -/
def kiim : Root := ⟨"kiim", {.becomesState "dead"}⟩

/-- háan "stop, cease, heal" ([lucy-1994] patient-salient list,
    p. 630, ex. 2). High-tone vowel: distinct from `Yukatek.haanEat`
    "eat" (low-tone `hàan`), which is `inactive`-class but
    internally caused — see `Fragments/Mayan/Yukatek/VerbClasses.lean`
    and [bohnemeyer-2004] ex. (9). -/
def haanCease : Root := ⟨"háan", {.becomesState "stopped"}⟩

/-- lúub' "fall" ([lucy-1994] ex. 4, Table 4). A "motion verb" by
    any reasonable cross-linguistic notional taxonomy, but patterns
    morphologically with other patient-salient change-of-state roots
    in Yukatek. No `.motion` atom: motion is the *issue*, not a
    feature — see `motion_roots_not_separate_class`. -/
def luub : Root := ⟨"luub'", {.becomesState "fallen"}⟩

/-- 'ok "enter, intrude" ([lucy-1994] ex. 4, Table 4). Another
    notional motion root that takes `=s` like patient-salient state
    changes. -/
def ok : Root := ⟨"'ok", {.becomesState "inside"}⟩

/-! Additional patient-salient roots from the page-630 list. -/

/-- 'ah "wake" ([lucy-1994] patient-salient list). -/
def ah : Root := ⟨"'ah", {.becomesState "awake"}⟩

/-- wen "sleep" ([lucy-1994] patient-salient list). State change
    *into* sleep, not the activity of sleeping. -/
def wen : Root := ⟨"wen", {.becomesState "asleep"}⟩

/-- siih "be born" ([lucy-1994] patient-salient list). -/
def siih : Root := ⟨"siih", {.becomesState "born"}⟩

/-- tú'ub' "be forgotten" ([lucy-1994] patient-salient list). -/
def tuub : Root := ⟨"tú'ub'", {.becomesState "forgotten"}⟩

/-- k'a'ah "remember" ([lucy-1994] patient-salient list). -/
def kaah : Root := ⟨"k'a'ah", {.becomesState "remembered"}⟩

/-- čú'un "begin" ([lucy-1994] patient-salient list). -/
def chuun : Root := ⟨"čú'un", {.becomesState "begun"}⟩

/-- č'en "stop, cease" ([lucy-1994] patient-salient list).
    Distinct from `haanCease` (Lucy lists them as separate entries). -/
def chenCease : Root := ⟨"č'en", {.becomesState "ceased"}⟩

/-- hó'op' "begin" ([lucy-1994] patient-salient list). Doublet of
    `chuun`; both gloss as "begin" in the patient-salient list. -/
def hoop : Root := ⟨"hó'op'", {.becomesState "started"}⟩

/-- hé'el "rest" ([lucy-1994] patient-salient list). -/
def heel : Root := ⟨"hé'el", {.becomesState "rested"}⟩

/-- p'át "remain" ([lucy-1994] patient-salient list). -/
def paat : Root := ⟨"p'át", {.becomesState "remaining"}⟩

/-! Motion roots from [lucy-1994] Table 4. These pattern as
    patient-salient (`becomesState` only) — the central typological
    point. See `motion_roots_not_separate_class` and
    `motion_roots_predicted_patient`. -/

/-- máan "pass" ([lucy-1994] Table 4). -/
def maan : Root := ⟨"máan", {.becomesState "passed"}⟩

/-- tàal "come" ([lucy-1994] Table 4). -/
def taal : Root := ⟨"tàal", {.becomesState "arrived"}⟩

/-- b'in "go" ([lucy-1994] Table 4). -/
def bin : Root := ⟨"b'in", {.becomesState "departed"}⟩

/-- nàak "ascend" ([lucy-1994] Table 4). Distinct from
    `Yukatek.naak` "ascend" in `VerbClasses.lean`, which encodes
    Bohnemeyer's stem-class data; both refer to the same Yukatek root. -/
def naak : Root := ⟨"nàak", {.becomesState "ascended"}⟩

/-- lìik' "rise" ([lucy-1994] Table 4). -/
def liik : Root := ⟨"lìik'", {.becomesState "risen"}⟩

-- ════════════════════════════════════════════════════
-- § 4. Positional Roots (state only, take `-tal`)
-- ════════════════════════════════════════════════════

/-- čin "bow, bend down, bend over" ([lucy-1994] ex. 5, 7).
    Positional root; takes `-tal` (or `-lah`) for the inchoative stem. -/
def cin : Root := ⟨"cin", {.hasState "bent"}⟩

/-- kul "sit" — positional root (cf. [lucy-1994] ex. 8c on
    relational positional semantics: "x is-seated [on y]"). -/
def kul : Root := ⟨"kul", {.hasState "seated"}⟩

/-! ### Per-root feature signatures -/

/-! Agent-salient roots → `{.manner}`. -/

theorem siit_signature :
    siit.featureSignature = {.manner} := by decide
theorem tziib_signature :
    tziib.featureSignature = {.manner} := by decide
theorem miis_signature :
    miis.featureSignature = {.manner} := by decide
theorem cheh_signature :
    cheh.featureSignature = {.manner} := by decide
theorem paak_signature :
    paak.featureSignature = {.manner} := by decide

/-! Agent-patient salient roots → `{.manner, .result}`. -/

theorem kuc_signature :
    kuc.featureSignature = {.manner, .result} := by decide
theorem pis_signature :
    pis.featureSignature = {.manner, .result} := by decide
theorem los_signature :
    los.featureSignature = {.manner, .result} := by decide

/-! Patient-salient roots → `{.result}`. -/

theorem kiim_signature :
    kiim.featureSignature = {.result} := by decide
theorem haanCease_signature :
    haanCease.featureSignature = {.result} := by decide
theorem luub_signature :
    luub.featureSignature = {.result} := by decide
theorem ok_signature :
    ok.featureSignature = {.result} := by decide
theorem ah_signature :
    ah.featureSignature = {.result} := by decide
theorem wen_signature :
    wen.featureSignature = {.result} := by decide
theorem siih_signature :
    siih.featureSignature = {.result} := by decide
theorem tuub_signature :
    tuub.featureSignature = {.result} := by decide
theorem kaah_signature :
    kaah.featureSignature = {.result} := by decide
theorem chuun_signature :
    chuun.featureSignature = {.result} := by decide
theorem chenCease_signature :
    chenCease.featureSignature = {.result} := by decide
theorem hoop_signature :
    hoop.featureSignature = {.result} := by decide
theorem heel_signature :
    heel.featureSignature = {.result} := by decide
theorem paat_signature :
    paat.featureSignature = {.result} := by decide

/-! Motion roots (also patient-salient) → `{.result}`. -/

theorem maan_signature :
    maan.featureSignature = {.result} := by decide
theorem taal_signature :
    taal.featureSignature = {.result} := by decide
theorem bin_signature :
    bin.featureSignature = {.result} := by decide
theorem naak_signature :
    naak.featureSignature = {.result} := by decide
theorem liik_signature :
    liik.featureSignature = {.result} := by decide

/-! Positional roots → `{.state}`. -/

theorem cin_signature :
    cin.featureSignature = {.state} := by decide
theorem kul_signature :
    kul.featureSignature = {.state} := by decide

/-! ### Per-root closed feature signatures -/

/-! The collocational closure (`Root.FeatureSignature.close`) adds `.state`
    to any signature containing `.result`, and `.result` + `.state` to
    any containing `.cause`. No Yukatek root here carries a `.cause`
    atom, so only the result→state edge fires. Closure does *not*
    change the Lucy 1994 salience class predicted by
    `classOfSignature` for these roots: the agent / agentPatient /
    patient arms ignore `.state` membership, and the positional arm
    (signature exactly `{.state}`) is never produced by closure from a
    non-positional base without `.cause`
    (cf. `Lucy1994.predictedClass_closure_invariant`). -/

theorem siit_closed_signature :
    siit.closedFeatureSignature = {.manner} := by decide

theorem tziib_closed_signature :
    tziib.closedFeatureSignature = {.manner} := by decide

theorem kuc_closed_signature :
    kuc.closedFeatureSignature = {.state, .manner, .result} := by decide

theorem pis_closed_signature :
    pis.closedFeatureSignature = {.state, .manner, .result} := by decide

theorem los_closed_signature :
    los.closedFeatureSignature = {.state, .manner, .result} := by decide

theorem kiim_closed_signature :
    kiim.closedFeatureSignature = {.state, .result} := by decide

theorem haanCease_closed_signature :
    haanCease.closedFeatureSignature = {.state, .result} := by decide

theorem luub_closed_signature :
    luub.closedFeatureSignature = {.state, .result} := by decide

theorem ok_closed_signature :
    ok.closedFeatureSignature = {.state, .result} := by decide

theorem cin_closed_signature :
    cin.closedFeatureSignature = {.state} := by decide

theorem kul_closed_signature :
    kul.closedFeatureSignature = {.state} := by decide

-- ════════════════════════════════════════════════════
-- § 7. Class Lists
-- ════════════════════════════════════════════════════

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
