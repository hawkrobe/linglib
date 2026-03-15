import Linglib.Theories.Semantics.Causation.ProductionDependence
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Core.Lexical.DiathesisAlternation

/-!
# Thick vs Thin Causative Verb Data
@cite{martin-rose-nichols-2025} @cite{embick-2009}

Corpus survey data from Table 3: 37 English causative verbs classified by
four binary properties:

1. **alternating**: Participates in the causative/anticausative alternation
2. **thick**: Encodes manner of causing (subject restriction on abstract causes)
3. **ASR**: Compatible with strong adjectival resultatives (*break open*)
4. **omissionSubjects**: Compatible with omission/quality-denoting subjects

## Key Findings (§4.3)

- 12/13 thick verbs have ASR, 22/24 thin verbs accept omission subjects
- Thick ≈ causative manner verbs, but *bury* is thick without ASR
- The correlation is strong but not perfect: some thick verbs (burn, lift, lock)
  are occasionally found with omission subjects in corpora

-/

namespace Phenomena.Causation.ThickThin

open MartinRoseNichols2025
open Fragments.English.Predicates.Verbal (VerbEntry)
namespace V
  -- Re-export Fragment verb entries under a short alias to avoid name clashes
  -- with the ThickThinEntry definitions in this namespace.
  abbrev activate := Fragments.English.Predicates.Verbal.activate
  abbrev affect := Fragments.English.Predicates.Verbal.affect
  abbrev change := Fragments.English.Predicates.Verbal.change
  abbrev damage := Fragments.English.Predicates.Verbal.damage
  abbrev destroy := Fragments.English.Predicates.Verbal.destroy
  abbrev eliminate := Fragments.English.Predicates.Verbal.eliminate
  abbrev hurt := Fragments.English.Predicates.Verbal.hurt
  abbrev kill := Fragments.English.Predicates.Verbal.kill
  abbrev restore := Fragments.English.Predicates.Verbal.restore
  abbrev start := Fragments.English.Predicates.Verbal.start
  abbrev stop := Fragments.English.Predicates.Verbal.stop
  abbrev trigger := Fragments.English.Predicates.Verbal.trigger
  abbrev break_ := Fragments.English.Predicates.Verbal.break_
  abbrev burn := Fragments.English.Predicates.Verbal.burn
  abbrev bury := Fragments.English.Predicates.Verbal.bury
  abbrev cut := Fragments.English.Predicates.Verbal.cut
  abbrev drop := Fragments.English.Predicates.Verbal.drop
  abbrev lift := Fragments.English.Predicates.Verbal.lift
  abbrev lock := Fragments.English.Predicates.Verbal.lock
  abbrev melt := Fragments.English.Predicates.Verbal.melt
  abbrev mix := Fragments.English.Predicates.Verbal.mix
  abbrev shut := Fragments.English.Predicates.Verbal.shut
  abbrev spread := Fragments.English.Predicates.Verbal.spread
  abbrev stretch := Fragments.English.Predicates.Verbal.stretch
  abbrev switch := Fragments.English.Predicates.Verbal.switch
end V

/-- A single verb entry from Table 3, extending a Fragment VerbEntry.
    The Levin class, verb form, root profile, etc. are all inherited from
    the Fragment entry — only the @cite{martin-rose-nichols-2025} annotations are new. -/
structure ThickThinEntry extends VerbEntry where
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
  deriving Repr

/-- Verb form (convenience accessor). -/
def ThickThinEntry.verb (e : ThickThinEntry) : String := e.form

/-! ## Table 3 data (representative subset)

We include all 13 thick verbs and a representative set of thin verbs
covering the key patterns. Numbers in comments refer to Table 3 rows. -/

-- === Thin causatives (result-only, no manner specification) ===

def activate : ThickThinEntry :=    -- #1
  { toVerbEntry := V.activate, alternating := true, thick := false, asr := false, omissionSubjects := true }
def affect : ThickThinEntry :=      -- #2
  { toVerbEntry := V.affect, alternating := false, thick := false, asr := false, omissionSubjects := true }
def change : ThickThinEntry :=      -- #3
  { toVerbEntry := V.change, alternating := true, thick := false, asr := false, omissionSubjects := true }
def damage : ThickThinEntry :=      -- #6
  { toVerbEntry := V.damage, alternating := false, thick := false, asr := false, omissionSubjects := true }
def destroy : ThickThinEntry :=     -- #7
  { toVerbEntry := V.destroy, alternating := false, thick := false, asr := false, omissionSubjects := true }
def eliminate : ThickThinEntry :=   -- #9
  { toVerbEntry := V.eliminate, alternating := false, thick := false, asr := false, omissionSubjects := true }
def hurt : ThickThinEntry :=        -- #12
  { toVerbEntry := V.hurt, alternating := false, thick := false, asr := false, omissionSubjects := true }
def kill : ThickThinEntry :=        -- #13
  { toVerbEntry := V.kill, alternating := false, thick := false, asr := false, omissionSubjects := true }
def restore : ThickThinEntry :=     -- #17
  { toVerbEntry := V.restore, alternating := false, thick := false, asr := false, omissionSubjects := true }
def start : ThickThinEntry :=       -- #20
  { toVerbEntry := V.start, alternating := true, thick := false, asr := false, omissionSubjects := true }
def stop : ThickThinEntry :=        -- #21
  { toVerbEntry := V.stop, alternating := true, thick := false, asr := false, omissionSubjects := false }
def trigger : ThickThinEntry :=     -- #22
  { toVerbEntry := V.trigger, alternating := false, thick := false, asr := false, omissionSubjects := true,
    thickThinClass := .thin }

-- === Thick causatives (manner-encoding, restrict abstract subjects) ===

def break_ : ThickThinEntry :=      -- #25
  { toVerbEntry := V.break_, alternating := true, thick := true, asr := true, omissionSubjects := false }
def burn : ThickThinEntry :=        -- #27
  { toVerbEntry := V.burn, alternating := true, thick := true, asr := true, omissionSubjects := true,
    thickThinClass := .thickManner }  -- Exception: burn found with omission subjects
def bury : ThickThinEntry :=        -- #26
  { toVerbEntry := V.bury, alternating := false, thick := true, asr := false, omissionSubjects := false,
    thickThinClass := .thickState }   -- Thick via state property, NOT causative manner verb
def cut : ThickThinEntry :=         -- #28
  { toVerbEntry := V.cut, alternating := false, thick := true, asr := true, omissionSubjects := false }
def drop : ThickThinEntry :=        -- #29
  { toVerbEntry := V.drop, alternating := true, thick := true, asr := true, omissionSubjects := false }
def lift : ThickThinEntry :=        -- #30
  { toVerbEntry := V.lift, alternating := false, thick := true, asr := true, omissionSubjects := true,
    thickThinClass := .thickManner }  -- Exception: lift found with omission subjects
def lock : ThickThinEntry :=        -- #31
  { toVerbEntry := V.lock, alternating := true, thick := true, asr := true, omissionSubjects := true,
    thickThinClass := .thickManner }  -- Exception: lock found with omission subjects
def melt : ThickThinEntry :=        -- #32
  { toVerbEntry := V.melt, alternating := true, thick := true, asr := true, omissionSubjects := false }
def mix : ThickThinEntry :=         -- #33
  { toVerbEntry := V.mix, alternating := true, thick := true, asr := true, omissionSubjects := false }
def shut : ThickThinEntry :=        -- #34
  { toVerbEntry := V.shut, alternating := true, thick := true, asr := true, omissionSubjects := false }
def spread : ThickThinEntry :=      -- #35
  { toVerbEntry := V.spread, alternating := true, thick := true, asr := true, omissionSubjects := false }
def stretch : ThickThinEntry :=     -- #36
  { toVerbEntry := V.stretch, alternating := true, thick := true, asr := true, omissionSubjects := false }
def switch : ThickThinEntry :=      -- #37
  { toVerbEntry := V.switch, alternating := true, thick := true, asr := true, omissionSubjects := false }

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

-- Verb forms are inherited from Fragment entries
theorem break_verb : break_.verb = "break" := rfl
theorem kill_verb : kill.verb = "kill" := rfl
theorem destroy_verb : destroy.verb = "destroy" := rfl

-- Levin classes are inherited from Fragment entries
theorem break_levin : break_.levinClass = some .break_ := rfl
theorem kill_levin : kill.levinClass = some .murder := rfl
theorem destroy_levin : destroy.levinClass = some .destroy := rfl
theorem cut_levin : cut.levinClass = some .cut := rfl
theorem burn_levin : burn.levinClass = some .otherCoS := rfl

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

/-! ## Bridge to @cite{levin-1993} classes

The thick/thin distinction cross-cuts Levin classes: verbs in the same
general domain (change of state, causation) can be thick or thin. The
difference is whether the verb specifies manner of causing. -/

/-- Break (thick) and destroy (thin) both have CoS + causation in their
    Levin meaning components. The thick/thin split is orthogonal to
    the basic meaning component profile. -/
theorem break_destroy_same_components :
    (LevinClass.break_.meaningComponents.changeOfState =
     LevinClass.destroy.meaningComponents.changeOfState)
    ∧ (LevinClass.break_.meaningComponents.causation =
       LevinClass.destroy.meaningComponents.causation) := ⟨rfl, rfl⟩

/-- Thick manner verbs belong to Levin classes that predict the
    causative alternation. -/
theorem break_class_predicts_alternation :
    LevinClass.break_.participatesIn .causativeInchoative = true := rfl

/-- Cut (thick) is in a class that predicts conative and BPPA alternations.
    Unlike break, cut does NOT participate in causative/inchoative because
    instrument specification blocks the inchoative. -/
theorem cut_class_rich_alternation :
    LevinClass.cut.participatesIn .causativeInchoative = false
    ∧ LevinClass.cut.participatesIn .conative = true
    ∧ LevinClass.cut.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl, rfl⟩

/-- Destroy (thin) is also predicted to participate in causative alternation
    by its meaning components, but empirically it does not alternate.
    This shows the limits of meaning-component prediction. -/
theorem destroy_class_vs_empirical :
    LevinClass.destroy.participatesIn .causativeInchoative = true
    ∧ Phenomena.Causation.ThickThin.destroy.alternating = false := ⟨rfl, rfl⟩

/-- Kill (thin, murder class) is predicted to participate in causative
    alternation but empirically does not alternate. -/
theorem kill_class_vs_empirical :
    LevinClass.murder.participatesIn .causativeInchoative = true
    ∧ kill.alternating = false := ⟨rfl, rfl⟩

/-- All ThickThin verb entries (for aggregate bridge theorems). -/
def allEntries : List ThickThinEntry :=
  [ activate, affect, change, damage, destroy, eliminate, hurt, kill,
    restore, start, stop, trigger,
    break_, burn, bury, cut, drop, lift, lock, melt, mix, shut,
    spread, stretch, switch ]

end Phenomena.Causation.ThickThin
