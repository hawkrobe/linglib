import Linglib.Theories.IntensionalSemantics.Causative.ProductionDependence

/-!
# Thick vs Thin Causative Verb Data (Martin, Rose & Nichols 2025)

Corpus survey data from Table 3: 37 English causative verbs classified by
four binary properties:

1. **alternating**: Participates in the causative/anticausative alternation
2. **thick**: Encodes manner of causing (subject restriction on abstract causes)
3. **ASR**: Compatible with strong adjectival resultatives (*break open*)
4. **omissionSubjects**: Compatible with omission/quality-denoting subjects

## Key Findings (§4.3)

- 12/13 thick verbs have ASR, 22/24 thin verbs accept omission subjects
- Thick ≈ causative manner verbs (Embick 2009), but *bury* is thick without ASR
- The correlation is strong but not perfect: some thick verbs (burn, lift, lock)
  are occasionally found with omission subjects in corpora

## References

- Martin, F., Rose, D. & Nichols, S. (2025). Burning facts: thick and thin
  causatives. Version 1, November 23, 2025.
-/

namespace Phenomena.Causatives.ThickThin

open MartinRoseNichols2025

/-- A single verb entry from Table 3. -/
structure ThickThinEntry where
  /-- Verb form -/
  verb : String
  /-- Participates in causative/anticausative alternation -/
  alternating : Bool
  /-- Thick = encodes manner of causing (rejects abstract subjects in physical sense) -/
  thick : Bool
  /-- Compatible with strong adjectival resultatives -/
  asr : Bool
  /-- Compatible with omission or quality-denoting subjects -/
  omissionSubjects : Bool
  /-- Thick/thin classification from theory -/
  thickThinClass : ThickThinClass := if thick then .thickManner else .thin
  deriving Repr, BEq

/-! ## Table 3 data (representative subset)

We include all 13 thick verbs and a representative set of thin verbs
covering the key patterns. Numbers in comments refer to Table 3 rows. -/

-- === Thin causatives (result-only, no manner specification) ===

def activate : ThickThinEntry :=    -- #1
  { verb := "activate", alternating := true, thick := false, asr := false, omissionSubjects := true }
def affect : ThickThinEntry :=      -- #2
  { verb := "affect", alternating := false, thick := false, asr := false, omissionSubjects := true }
def change : ThickThinEntry :=      -- #3
  { verb := "change", alternating := true, thick := false, asr := false, omissionSubjects := true }
def damage : ThickThinEntry :=      -- #6
  { verb := "damage", alternating := false, thick := false, asr := false, omissionSubjects := true }
def destroy : ThickThinEntry :=     -- #7
  { verb := "destroy", alternating := false, thick := false, asr := false, omissionSubjects := true }
def eliminate : ThickThinEntry :=   -- #9
  { verb := "eliminate", alternating := false, thick := false, asr := false, omissionSubjects := true }
def hurt : ThickThinEntry :=        -- #12
  { verb := "hurt", alternating := false, thick := false, asr := false, omissionSubjects := true }
def kill : ThickThinEntry :=        -- #13
  { verb := "kill", alternating := false, thick := false, asr := false, omissionSubjects := true }
def restore : ThickThinEntry :=     -- #17
  { verb := "restore", alternating := false, thick := false, asr := false, omissionSubjects := true }
def start : ThickThinEntry :=       -- #20
  { verb := "start", alternating := true, thick := false, asr := false, omissionSubjects := true }
def stop : ThickThinEntry :=        -- #21
  { verb := "stop", alternating := true, thick := false, asr := false, omissionSubjects := false }
def trigger : ThickThinEntry :=     -- #22
  { verb := "trigger", alternating := false, thick := false, asr := false, omissionSubjects := true,
    thickThinClass := .thin }  -- Note: trigger has Y* for ASR (requires resultative)

-- === Thick causatives (manner-encoding, restrict abstract subjects) ===

def break_ : ThickThinEntry :=      -- #25
  { verb := "break", alternating := true, thick := true, asr := true, omissionSubjects := false }
def burn : ThickThinEntry :=        -- #27
  { verb := "burn", alternating := true, thick := true, asr := true, omissionSubjects := true,
    thickThinClass := .thickManner }  -- Exception: burn found with omission subjects
def bury : ThickThinEntry :=        -- #26
  { verb := "bury", alternating := false, thick := true, asr := false, omissionSubjects := false,
    thickThinClass := .thickState }   -- Thick via state property, NOT causative manner verb
def cut : ThickThinEntry :=         -- #28
  { verb := "cut", alternating := false, thick := true, asr := true, omissionSubjects := false }
def drop : ThickThinEntry :=        -- #29
  { verb := "drop", alternating := true, thick := true, asr := true, omissionSubjects := false }
def lift : ThickThinEntry :=        -- #30
  { verb := "lift", alternating := false, thick := true, asr := true, omissionSubjects := true,
    thickThinClass := .thickManner }  -- Exception: lift found with omission subjects
def lock : ThickThinEntry :=        -- #31
  { verb := "lock", alternating := true, thick := true, asr := true, omissionSubjects := true,
    thickThinClass := .thickManner }  -- Exception: lock found with omission subjects
def melt : ThickThinEntry :=        -- #32
  { verb := "melt", alternating := true, thick := true, asr := true, omissionSubjects := false }
def mix : ThickThinEntry :=         -- #33
  { verb := "mix", alternating := true, thick := true, asr := true, omissionSubjects := false }
def shut : ThickThinEntry :=        -- #34
  { verb := "shut", alternating := true, thick := true, asr := true, omissionSubjects := false }
def spread : ThickThinEntry :=      -- #35
  { verb := "spread", alternating := true, thick := true, asr := true, omissionSubjects := false }
def stretch : ThickThinEntry :=     -- #36
  { verb := "stretch", alternating := true, thick := true, asr := true, omissionSubjects := false }
def switch : ThickThinEntry :=      -- #37
  { verb := "switch", alternating := true, thick := true, asr := true, omissionSubjects := false }

/-- All Table 3 entries. -/
def allEntries : List ThickThinEntry :=
  [ -- thin
    activate, affect, change, damage, destroy, eliminate, hurt, kill,
    restore, start, stop, trigger,
    -- thick
    break_, burn, bury, cut, drop, lift, lock, melt, mix, shut,
    spread, stretch, switch ]

/-! ## Per-datum verification theorems -/

-- Thick verbs are marked thick
theorem break_is_thick : break_.thick = true := rfl
theorem burn_is_thick : burn.thick = true := rfl
theorem bury_is_thick : bury.thick = true := rfl
theorem melt_is_thick : melt.thick = true := rfl
theorem cut_is_thick : cut.thick = true := rfl

-- Thin verbs are marked thin
theorem kill_is_thin : kill.thick = false := rfl
theorem destroy_is_thin : destroy.thick = false := rfl
theorem damage_is_thin : damage.thick = false := rfl
theorem change_is_thin : change.thick = false := rfl

-- Bury is thick via state (not manner verb), hence no ASR
theorem bury_thick_no_asr : bury.thick = true ∧ bury.asr = false := ⟨rfl, rfl⟩
theorem bury_is_thick_state : bury.thickThinClass = .thickState := rfl

/-! ## Correlation theorems

The core empirical finding: thickness correlates with ASR compatibility
and anti-correlates with omission subject compatibility. -/

/-- Most thick verbs (≥ 11/13) are ASR-compatible. -/
theorem most_thick_have_asr :
    let thickVerbs := allEntries.filter (·.thick)
    let asrThick := thickVerbs.filter (·.asr)
    asrThick.length ≥ 11 := by native_decide

/-- Most thin verbs (≥ 10/12 in our sample) accept omission subjects. -/
theorem most_thin_accept_omission :
    let thinVerbs := allEntries.filter (!·.thick)
    let omThin := thinVerbs.filter (·.omissionSubjects)
    omThin.length ≥ 10 := by native_decide

/-- No thin verb in our sample has ASR. -/
theorem no_thin_has_asr :
    (allEntries.filter (!·.thick)).all (!·.asr) = true := by native_decide

/-- Most thick verbs (≥ 9/13) reject omission subjects. -/
theorem most_thick_reject_omission :
    let thickVerbs := allEntries.filter (·.thick)
    let noOmThick := thickVerbs.filter (!·.omissionSubjects)
    noOmThick.length ≥ 9 := by native_decide

/-! ## Bridge to ThickThinClass

Verify that the data entries' classifications match the theory. -/

/-- Thick manner verbs have the production constraint. -/
theorem break_production_constraint :
    productionConstraint break_.thickThinClass = .production := rfl

/-- Thin verbs default to dependence. -/
theorem kill_dependence :
    productionConstraint kill.thickThinClass = .dependence := rfl

/-- Bury (thick state) also has the production constraint. -/
theorem bury_production_constraint :
    productionConstraint bury.thickThinClass = .production := rfl

/-- Thick manner verbs are ASR-compatible per the theory. -/
theorem break_asr_theory :
    break_.thickThinClass.strongASRCompatible = true := rfl

/-- Thick state verbs are NOT ASR-compatible per the theory. -/
theorem bury_asr_theory :
    bury.thickThinClass.strongASRCompatible = false := rfl

/-- Thin verbs are NOT ASR-compatible per the theory. -/
theorem kill_asr_theory :
    kill.thickThinClass.strongASRCompatible = false := rfl

/-! ## Alternation statistics (§7)

76% (10/13) of thick verbs alternate vs 50% (12/24) of thin verbs.
Thickness promotes the causative/anticausative alternation. -/

/-- Most thick verbs in our sample alternate. -/
theorem thick_mostly_alternate :
    let thickVerbs := allEntries.filter (·.thick)
    let altThick := thickVerbs.filter (·.alternating)
    altThick.length * 100 / thickVerbs.length ≥ 70 := by native_decide

end Phenomena.Causatives.ThickThin
