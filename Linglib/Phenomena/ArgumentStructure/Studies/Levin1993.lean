import Linglib.Phenomena.ArgumentStructure.DiathesisAlternations.Data
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Diathesis Alternation Bridge @cite{levin-1993}

Connects empirical alternation data to the
`LevinClass.participatesIn` prediction function and Fragment verb entries.

## Agreement

All 21 data points agree with the `LevinClass.participatesIn` prediction
function. The CI rule correctly blocks *cut* via `!instrumentSpec`
(Levin p. 9–10: instrument specification requires an agent, blocking
the agentless inchoative).
-/

namespace Phenomena.ArgumentStructure.DiathesisAlternations.Bridge

open Fragments.English.Predicates.Verbal
open Phenomena.ArgumentStructure.DiathesisAlternations.Data

-- ════════════════════════════════════════════════════
-- § 1. Fragment Connection — verbClass matches Fragment levinClass
-- ════════════════════════════════════════════════════

theorem break_class_matches :
    break_.levinClass = some ci_break.verbClass := rfl

theorem cut_class_matches :
    cut.levinClass = some ci_cut.verbClass := rfl

theorem hit_class_matches :
    hit.levinClass = some ci_hit.verbClass := rfl

theorem touch_class_matches :
    touch.levinClass = some ci_touch.verbClass := rfl

theorem push_class_matches :
    push.levinClass = some con_push.verbClass := rfl

theorem spray_class_matches :
    spray.levinClass = some loc_spray.verbClass := rfl

theorem load_class_matches :
    load.levinClass = some loc_load.verbClass := rfl

theorem give_class_matches :
    give.levinClass = some dat_give.verbClass := rfl

theorem send_class_matches :
    send.levinClass = some dat_send.verbClass := rfl

-- ════════════════════════════════════════════════════
-- § 2. Per-Datum Agreement — prediction matches empirical result
-- ════════════════════════════════════════════════════

/-! Each theorem connects a datum's `result` to the output of
    `LevinClass.participatesIn`. Changing either the data or
    the prediction breaks exactly one theorem. -/

-- Break (45.1): CI ✓, Mid ✓, Con ✗, BPPA ✗

theorem ci_break_agrees :
    ci_break.result = .participates ∧
    LevinClass.break_.participatesIn .causativeInchoative = true := ⟨rfl, rfl⟩

theorem mid_break_agrees :
    mid_break.result = .participates ∧
    LevinClass.break_.participatesIn .middle = true := ⟨rfl, rfl⟩

theorem con_break_agrees :
    con_break.result = .blocked ∧
    LevinClass.break_.participatesIn .conative = false := ⟨rfl, rfl⟩

theorem bppa_break_agrees :
    bppa_break.result = .blocked ∧
    LevinClass.break_.participatesIn .bodyPartPossessorAscension = false := ⟨rfl, rfl⟩

-- Hit (18.1): CI ✗, Mid ✗, Con ✓, BPPA ✓

theorem ci_hit_agrees :
    ci_hit.result = .blocked ∧
    LevinClass.hit.participatesIn .causativeInchoative = false := ⟨rfl, rfl⟩

theorem mid_hit_agrees :
    mid_hit.result = .blocked ∧
    LevinClass.hit.participatesIn .middle = false := ⟨rfl, rfl⟩

theorem con_hit_agrees :
    con_hit.result = .participates ∧
    LevinClass.hit.participatesIn .conative = true := ⟨rfl, rfl⟩

theorem bppa_hit_agrees :
    bppa_hit.result = .participates ∧
    LevinClass.hit.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl⟩

-- Touch (20): CI ✗, Mid ✗, Con ✗, BPPA ✓

theorem ci_touch_agrees :
    ci_touch.result = .blocked ∧
    LevinClass.touch.participatesIn .causativeInchoative = false := ⟨rfl, rfl⟩

theorem mid_touch_agrees :
    mid_touch.result = .blocked ∧
    LevinClass.touch.participatesIn .middle = false := ⟨rfl, rfl⟩

theorem con_touch_agrees :
    con_touch.result = .blocked ∧
    LevinClass.touch.participatesIn .conative = false := ⟨rfl, rfl⟩

theorem bppa_touch_agrees :
    bppa_touch.result = .participates ∧
    LevinClass.touch.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl⟩

-- Push (12): Con ✓

theorem con_push_agrees :
    con_push.result = .participates ∧
    LevinClass.pushPull.participatesIn .conative = true := ⟨rfl, rfl⟩

-- Spray/Load (9.7): Locative ✓

theorem loc_spray_agrees :
    loc_spray.result = .participates ∧
    LevinClass.sprayLoad.participatesIn .locative = true := ⟨rfl, rfl⟩

theorem loc_load_agrees :
    loc_load.result = .participates ∧
    LevinClass.sprayLoad.participatesIn .locative = true := ⟨rfl, rfl⟩

-- Give/Send (13.1/11.1): Dative ✓

theorem dat_give_agrees :
    dat_give.result = .participates ∧
    LevinClass.give.participatesIn .dative = true := ⟨rfl, rfl⟩

theorem dat_send_agrees :
    dat_send.result = .participates ∧
    LevinClass.send.participatesIn .dative = true := ⟨rfl, rfl⟩

-- Cut (21.1): CI ✗, Mid ✓, Con ✓, BPPA ✓

theorem ci_cut_agrees :
    ci_cut.result = .blocked ∧
    LevinClass.cut.participatesIn .causativeInchoative = false := ⟨rfl, rfl⟩

theorem mid_cut_agrees :
    mid_cut.result = .participates ∧
    LevinClass.cut.participatesIn .middle = true := ⟨rfl, rfl⟩

theorem con_cut_agrees :
    con_cut.result = .participates ∧
    LevinClass.cut.participatesIn .conative = true := ⟨rfl, rfl⟩

theorem bppa_cut_agrees :
    bppa_cut.result = .participates ∧
    LevinClass.cut.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl⟩

end Phenomena.ArgumentStructure.DiathesisAlternations.Bridge
