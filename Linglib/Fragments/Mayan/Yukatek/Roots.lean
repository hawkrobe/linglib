import Linglib.Theories.Semantics.Verb.Roots.Closure

/-!
# Yukatek Maya Roots as B&K-G Entailment Sets

@cite{lucy-1994} @cite{beavers-koontz-garboden-2020}

A representative cross-section of Yukatek roots, drawn from the lists
in @cite{lucy-1994} ex. (1), (2), (4), and (7), and encoded as
@cite{beavers-koontz-garboden-2020}-style entailment sets.

The selection covers all four salience profiles that @cite{lucy-1994}
identifies in Yukatek (agent-salient, agent-patient salient,
patient-salient, positional). The roots feed into the operator
inventory in `Operators.lean` and the orbit-derivation in
`Phenomena/LexicalTypology/Studies/Lucy1994.lean`.

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
`Fragments.Mayan.Yukatek.haanEat` (in `VerbClasses.lean`) is the
inactive-class but internally-caused "eat" verb that
@cite{bohnemeyer-2004} ex. (9) takes as the key applicative exception.

The transcription uses ASCII glosses (no IPA diacritics) for ease of
identifier use; original orthography is preserved in docstrings.
-/

namespace Fragments.Mayan.Yukatek.Roots

open Semantics.Verb.Roots

-- ════════════════════════════════════════════════════
-- § 1. Agent-Salient Roots (manner only, take `=t`)
-- ════════════════════════════════════════════════════

/-- síit' "jump" — manner-of-action activity (@cite{lucy-1994} ex. 1a).
    Underived intransitive; takes affective `=t` to transitivise.
    No `.motion` atom: per @cite{lucy-1994}, motion is *not* a B&K-G
    feature in Yukatek (cf. `motion_roots_not_separate_class`); jumping
    qualifies as a manner-of-action irrespective of whether it
    incidentally involves displacement. -/
def siit : Root := ⟨"siit'", [.hasManner "jumping"]⟩

/-- ¢'iib "write" — manner-of-action activity (@cite{lucy-1994} p. 628). -/
def tziib : Root := ⟨"tziib", [.hasManner "writing"]⟩

/-- mìis "sweep" — manner-of-action activity
    (@cite{lucy-1994} agent-salient list). -/
def miis : Root := ⟨"mìis", [.hasManner "sweeping"]⟩

/-- ć'eh "shout" — manner-of-action activity
    (@cite{lucy-1994} agent-salient list). -/
def cheh : Root := ⟨"ć'eh", [.hasManner "shouting"]⟩

/-- paak "weed" — manner-of-action activity
    (@cite{lucy-1994} agent-salient list). -/
def paak : Root := ⟨"paak", [.hasManner "weeding"]⟩

-- ════════════════════════════════════════════════════
-- § 2. Agent-Patient Salient Roots (manner + result, take `=∅`)
-- ════════════════════════════════════════════════════

/-- kuč "carry" — action with patient affected (@cite{lucy-1994} ex. 1b).
    Underived transitive; no derivation needed. -/
def kuc : Root := ⟨"kuc",
  [.hasManner "carrying", .becomesState "transported"]⟩

/-- p'is "measure" — action with patient affected (@cite{lucy-1994} p. 629). -/
def pis : Root := ⟨"pis",
  [.hasManner "measuring", .becomesState "measured"]⟩

/-- lo'š "punch" — action with patient affected (@cite{lucy-1994} p. 629).
    No `.contact` atom: contact is implicit in the manner of striking
    rather than a B&K-G feature in Lucy's typology. -/
def los : Root := ⟨"los",
  [.hasManner "striking", .becomesState "punched"]⟩

-- ════════════════════════════════════════════════════
-- § 3. Patient-Salient Roots (result only, take `=s`)
-- ════════════════════════════════════════════════════

/-- kíim "die" — spontaneous state change (@cite{lucy-1994} ex. 1c, 2). -/
def kiim : Root := ⟨"kiim", [.becomesState "dead"]⟩

/-- háan "stop, cease, heal" (@cite{lucy-1994} patient-salient list,
    p. 630, ex. 2). High-tone vowel: distinct from `Yukatek.haanEat`
    "eat" (low-tone `hàan`), which is `inactive`-class but
    internally caused — see `Fragments/Mayan/Yukatek/VerbClasses.lean`
    and @cite{bohnemeyer-2004} ex. (9). -/
def haanCease : Root := ⟨"háan", [.becomesState "stopped"]⟩

/-- lúub' "fall" (@cite{lucy-1994} ex. 4, Table 4). A "motion verb" by
    any reasonable cross-linguistic notional taxonomy, but patterns
    morphologically with other patient-salient change-of-state roots
    in Yukatek. No `.motion` atom: motion is the *issue*, not a
    feature — see `motion_roots_not_separate_class`. -/
def luub : Root := ⟨"luub'", [.becomesState "fallen"]⟩

/-- 'ok "enter, intrude" (@cite{lucy-1994} ex. 4, Table 4). Another
    notional motion root that takes `=s` like patient-salient state
    changes. -/
def ok : Root := ⟨"'ok", [.becomesState "inside"]⟩

/-! Additional patient-salient roots from the page-630 list. -/

/-- 'ah "wake" (@cite{lucy-1994} patient-salient list). -/
def ah : Root := ⟨"'ah", [.becomesState "awake"]⟩

/-- wen "sleep" (@cite{lucy-1994} patient-salient list). State change
    *into* sleep, not the activity of sleeping. -/
def wen : Root := ⟨"wen", [.becomesState "asleep"]⟩

/-- siih "be born" (@cite{lucy-1994} patient-salient list). -/
def siih : Root := ⟨"siih", [.becomesState "born"]⟩

/-- tú'ub' "be forgotten" (@cite{lucy-1994} patient-salient list). -/
def tuub : Root := ⟨"tú'ub'", [.becomesState "forgotten"]⟩

/-- k'a'ah "remember" (@cite{lucy-1994} patient-salient list). -/
def kaah : Root := ⟨"k'a'ah", [.becomesState "remembered"]⟩

/-- čú'un "begin" (@cite{lucy-1994} patient-salient list). -/
def chuun : Root := ⟨"čú'un", [.becomesState "begun"]⟩

/-- č'en "stop, cease" (@cite{lucy-1994} patient-salient list).
    Distinct from `haanCease` (Lucy lists them as separate entries). -/
def chenCease : Root := ⟨"č'en", [.becomesState "ceased"]⟩

/-- hó'op' "begin" (@cite{lucy-1994} patient-salient list). Doublet of
    `chuun`; both gloss as "begin" in the patient-salient list. -/
def hoop : Root := ⟨"hó'op'", [.becomesState "started"]⟩

/-- hé'el "rest" (@cite{lucy-1994} patient-salient list). -/
def heel : Root := ⟨"hé'el", [.becomesState "rested"]⟩

/-- p'át "remain" (@cite{lucy-1994} patient-salient list). -/
def paat : Root := ⟨"p'át", [.becomesState "remaining"]⟩

/-! Motion roots from @cite{lucy-1994} Table 4. These pattern as
    patient-salient (`becomesState` only) — the central typological
    point. See `motion_roots_not_separate_class` and
    `motion_roots_predicted_patient`. -/

/-- máan "pass" (@cite{lucy-1994} Table 4). -/
def maan : Root := ⟨"máan", [.becomesState "passed"]⟩

/-- tàal "come" (@cite{lucy-1994} Table 4). -/
def taal : Root := ⟨"tàal", [.becomesState "arrived"]⟩

/-- b'in "go" (@cite{lucy-1994} Table 4). -/
def bin : Root := ⟨"b'in", [.becomesState "departed"]⟩

/-- nàak "ascend" (@cite{lucy-1994} Table 4). Distinct from
    `Yukatek.naak` "ascend" in `VerbClasses.lean`, which encodes
    Bohnemeyer's stem-class data; both refer to the same Yukatek root. -/
def naak : Root := ⟨"nàak", [.becomesState "ascended"]⟩

/-- lìik' "rise" (@cite{lucy-1994} Table 4). -/
def liik : Root := ⟨"lìik'", [.becomesState "risen"]⟩

-- ════════════════════════════════════════════════════
-- § 4. Positional Roots (state only, take `-tal`)
-- ════════════════════════════════════════════════════

/-- čin "bow, bend down, bend over" (@cite{lucy-1994} ex. 5, 7).
    Positional root; takes `-tal` (or `-lah`) for the inchoative stem. -/
def cin : Root := ⟨"cin", [.hasState "bent"]⟩

/-- kul "sit" — positional root (cf. @cite{lucy-1994} ex. 8c on
    relational positional semantics: "x is-seated [on y]"). -/
def kul : Root := ⟨"kul", [.hasState "seated"]⟩

-- ════════════════════════════════════════════════════
-- § 5. Per-Root Feature Signatures
-- ════════════════════════════════════════════════════

/-! Agent-salient roots → `⟨false, true, false, false⟩`. -/

theorem siit_signature :
    siit.featureSignature = ⟨false, true, false, false⟩ := rfl
theorem tziib_signature :
    tziib.featureSignature = ⟨false, true, false, false⟩ := rfl
theorem miis_signature :
    miis.featureSignature = ⟨false, true, false, false⟩ := rfl
theorem cheh_signature :
    cheh.featureSignature = ⟨false, true, false, false⟩ := rfl
theorem paak_signature :
    paak.featureSignature = ⟨false, true, false, false⟩ := rfl

/-! Agent-patient salient roots → `⟨false, true, true, false⟩`. -/

theorem kuc_signature :
    kuc.featureSignature = ⟨false, true, true, false⟩ := rfl
theorem pis_signature :
    pis.featureSignature = ⟨false, true, true, false⟩ := rfl
theorem los_signature :
    los.featureSignature = ⟨false, true, true, false⟩ := rfl

/-! Patient-salient roots → `⟨false, false, true, false⟩`. -/

theorem kiim_signature :
    kiim.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem haanCease_signature :
    haanCease.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem luub_signature :
    luub.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem ok_signature :
    ok.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem ah_signature :
    ah.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem wen_signature :
    wen.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem siih_signature :
    siih.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem tuub_signature :
    tuub.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem kaah_signature :
    kaah.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem chuun_signature :
    chuun.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem chenCease_signature :
    chenCease.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem hoop_signature :
    hoop.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem heel_signature :
    heel.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem paat_signature :
    paat.featureSignature = ⟨false, false, true, false⟩ := rfl

/-! Motion roots (also patient-salient) → `⟨false, false, true, false⟩`. -/

theorem maan_signature :
    maan.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem taal_signature :
    taal.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem bin_signature :
    bin.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem naak_signature :
    naak.featureSignature = ⟨false, false, true, false⟩ := rfl
theorem liik_signature :
    liik.featureSignature = ⟨false, false, true, false⟩ := rfl

/-! Positional roots → `⟨true, false, false, false⟩`. -/

theorem cin_signature :
    cin.featureSignature = ⟨true, false, false, false⟩ := rfl
theorem kul_signature :
    kul.featureSignature = ⟨true, false, false, false⟩ := rfl

-- ════════════════════════════════════════════════════
-- § 6. Per-Root Closed Feature Signatures
-- ════════════════════════════════════════════════════

/-! Closure under `bkgRules` (currently `becomesState s ⇒ hasState s`)
    promotes change-of-state roots to `state = true`. This does *not*
    change the Lucy 1994 salience class predicted by `classOfSignature`,
    because the agent / agentPatient / patient arms ignore the `state`
    field, and the positional arm requires `result = false`. -/

theorem siit_closed_signature :
    siit.closedFeatureSignature = ⟨false, true, false, false⟩ := rfl

theorem tziib_closed_signature :
    tziib.closedFeatureSignature = ⟨false, true, false, false⟩ := rfl

theorem kuc_closed_signature :
    kuc.closedFeatureSignature = ⟨true, true, true, false⟩ := rfl

theorem pis_closed_signature :
    pis.closedFeatureSignature = ⟨true, true, true, false⟩ := rfl

theorem los_closed_signature :
    los.closedFeatureSignature = ⟨true, true, true, false⟩ := rfl

theorem kiim_closed_signature :
    kiim.closedFeatureSignature = ⟨true, false, true, false⟩ := rfl

theorem haanCease_closed_signature :
    haanCease.closedFeatureSignature = ⟨true, false, true, false⟩ := rfl

theorem luub_closed_signature :
    luub.closedFeatureSignature = ⟨true, false, true, false⟩ := rfl

theorem ok_closed_signature :
    ok.closedFeatureSignature = ⟨true, false, true, false⟩ := rfl

theorem cin_closed_signature :
    cin.closedFeatureSignature = ⟨true, false, false, false⟩ := rfl

theorem kul_closed_signature :
    kul.closedFeatureSignature = ⟨true, false, false, false⟩ := rfl

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
    @cite{lucy-1994} shows pattern as patient-salient (not as a separate
    class) in Yukatek. -/
def motionRoots : List Root := [luub, ok, maan, taal, bin, naak, liik]

/-- The positional roots: pure stative roots, expected to take `-tal`. -/
def positionalRoots : List Root := [cin, kul]

end Fragments.Mayan.Yukatek.Roots
