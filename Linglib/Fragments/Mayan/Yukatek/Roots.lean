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
| ex. (1a)        | `siit'`   | "jump"             | manner               | agent-salient          |
| (text p. 628)   | `tziib`   | "write"            | manner               | agent-salient          |
| ex. (1b)        | `kuc`     | "carry"            | manner + result      | agent-patient salient  |
| (text p. 629)   | `pis`     | "measure"          | manner + result      | agent-patient salient  |
| (text p. 629)   | `los`     | "punch"            | manner + result + contact | agent-patient salient |
| ex. (1c) / (2)  | `kiim`    | "die"              | result               | patient-salient        |
| ex. (2)         | `haan`    | "stop, cease, heal" | result              | patient-salient        |
| ex. (4)         | `luub`    | "fall"             | result + motion      | patient-salient        |
| ex. (4)         | `ok`      | "enter, intrude"   | result + motion      | patient-salient        |
| ex. (7)         | `cin`     | "bend"             | state                | positional             |
| (Yukatek lex.)  | `kul`     | "sit"              | state                | positional             |

The transcription uses ASCII glosses (no IPA diacritics) for ease of
identifier use; original orthography is preserved in docstrings.
-/

namespace Fragments.Mayan.Yukatek.Roots

open Semantics.Verb.Roots

-- ════════════════════════════════════════════════════
-- § 1. Agent-Salient Roots (manner only, take `=t`)
-- ════════════════════════════════════════════════════

/-- síit' "jump" — manner-of-motion activity (@cite{lucy-1994} ex. 1a).
    Underived intransitive; takes affective `=t` to transitivise. -/
def siit : Root := ⟨"siit'", [.hasManner "jumping", .motion]⟩

/-- ¢'iib "write" — manner-of-action activity (@cite{lucy-1994} p. 628). -/
def tziib : Root := ⟨"tziib", [.hasManner "writing"]⟩

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

/-- lo'š "punch" — action with patient affected (@cite{lucy-1994} p. 629). -/
def los : Root := ⟨"los",
  [.hasManner "striking", .becomesState "punched", .contact]⟩

-- ════════════════════════════════════════════════════
-- § 3. Patient-Salient Roots (result only, take `=s`)
-- ════════════════════════════════════════════════════

/-- kíim "die" — spontaneous state change (@cite{lucy-1994} ex. 1c, 2). -/
def kiim : Root := ⟨"kiim", [.becomesState "dead"]⟩

/-- háan "stop, cease, heal" (@cite{lucy-1994} ex. 2). The famous case
    that disambiguates: this is *not* "eat" — `haan` glosses as a
    cessation/recovery verb in @cite{lucy-1994}'s Table of patient-
    salient roots, taking causative `=s` to mean "stop, revoke, medicate". -/
def haan : Root := ⟨"haan", [.becomesState "stopped"]⟩

/-- lúub' "fall" (@cite{lucy-1994} ex. 4). One of the "motion" roots
    that, contra Talmy-style cross-linguistic motion classes, patterns
    morphologically with state-change roots in Yukatek. -/
def luub : Root := ⟨"luub", [.becomesState "fallen", .motion]⟩

/-- 'ok "enter, intrude" (@cite{lucy-1994} ex. 4). Another motion root
    that takes `=s` like other patient-salient state changes. -/
def ok : Root := ⟨"ok", [.becomesState "inside", .motion]⟩

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

theorem siit_signature :
    siit.featureSignature = ⟨false, true, false, false⟩ := rfl

theorem tziib_signature :
    tziib.featureSignature = ⟨false, true, false, false⟩ := rfl

theorem kuc_signature :
    kuc.featureSignature = ⟨false, true, true, false⟩ := rfl

theorem pis_signature :
    pis.featureSignature = ⟨false, true, true, false⟩ := rfl

theorem los_signature :
    los.featureSignature = ⟨false, true, true, false⟩ := rfl

theorem kiim_signature :
    kiim.featureSignature = ⟨false, false, true, false⟩ := rfl

theorem haan_signature :
    haan.featureSignature = ⟨false, false, true, false⟩ := rfl

theorem luub_signature :
    luub.featureSignature = ⟨false, false, true, false⟩ := rfl

theorem ok_signature :
    ok.featureSignature = ⟨false, false, true, false⟩ := rfl

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

theorem haan_closed_signature :
    haan.closedFeatureSignature = ⟨true, false, true, false⟩ := rfl

theorem luub_closed_signature :
    luub.closedFeatureSignature = ⟨true, false, true, false⟩ := rfl

theorem ok_closed_signature :
    ok.closedFeatureSignature = ⟨true, false, true, false⟩ := rfl

theorem cin_closed_signature :
    cin.closedFeatureSignature = ⟨true, false, false, false⟩ := rfl

theorem kul_closed_signature :
    kul.closedFeatureSignature = ⟨true, false, false, false⟩ := rfl

end Fragments.Mayan.Yukatek.Roots
