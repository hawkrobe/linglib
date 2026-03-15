import Linglib.Phenomena.ArgumentStructure.DiathesisAlternations.Data
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Diathesis Alternation Bridge @cite{levin-1993}

Connects empirical alternation data to the
`LevinClass.participatesIn` prediction function and Fragment verb entries.

## Agreement

All 40 data points agree with the `LevinClass.participatesIn` prediction
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

-- ════════════════════════════════════════════════════
-- § 3. New Alternation Agreement
-- ════════════════════════════════════════════════════

-- Benefactive (§2.2)

theorem ben_carve_agrees :
    ben_carve.result = .participates ∧
    LevinClass.build.participatesIn .benefactive = true := ⟨rfl, rfl⟩

-- Substance/Source (§1.1.3)

theorem ss_radiate_agrees :
    ss_radiate.result = .participates ∧
    LevinClass.substanceEmission.participatesIn .substanceSource = true := ⟨rfl, rfl⟩

-- Material/Product (§2.4.1)

theorem mp_carve_agrees :
    mp_carve.result = .participates ∧
    LevinClass.build.participatesIn .materialProduct = true := ⟨rfl, rfl⟩

-- Unspecified Object (§1.2.1)

theorem uo_eat_agrees :
    uo_eat.result = .participates ∧
    LevinClass.eat.participatesIn .unspecifiedObject = true := ⟨rfl, rfl⟩

theorem uo_devour_agrees :
    uo_devour.result = .blocked ∧
    LevinClass.devour.participatesIn .unspecifiedObject = false := ⟨rfl, rfl⟩

-- Understood Reciprocal Object (§1.2.4)

theorem uro_meet_agrees :
    uro_meet.result = .participates ∧
    LevinClass.socialInteraction.participatesIn .understoodReciprocalObject = true := ⟨rfl, rfl⟩

-- There-Insertion (§6.1)

theorem ti_develop_agrees :
    ti_develop.result = .participates ∧
    LevinClass.appear.participatesIn .thereInsertion = true := ⟨rfl, rfl⟩

theorem ti_appear_agrees :
    ti_appear.result = .participates ∧
    LevinClass.appear.participatesIn .thereInsertion = true := ⟨rfl, rfl⟩

-- Locative Inversion (§6.2)

theorem li_live_agrees :
    li_live.result = .participates ∧
    LevinClass.exist.participatesIn .locativeInversion = true := ⟨rfl, rfl⟩

-- Instrument Subject (§3.3)

theorem is_break_agrees :
    is_break.result = .participates ∧
    LevinClass.break_.participatesIn .instrumentSubject = true := ⟨rfl, rfl⟩

theorem is_eat_agrees :
    is_eat.result = .blocked ∧
    LevinClass.eat.participatesIn .instrumentSubject = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. New Alternation Type Agreement
-- ════════════════════════════════════════════════════

-- Induced Action (§1.1.2.2)

theorem ia_run_agrees :
    ia_run.result = .participates ∧
    LevinClass.mannerOfMotion.participatesIn .inducedAction = true := ⟨rfl, rfl⟩

-- Understood Body-Part Object (§1.2.2)

theorem ubpo_wave_agrees :
    ubpo_wave.result = .participates ∧
    LevinClass.bodyProcess.participatesIn .understoodBodyPartObject = true := ⟨rfl, rfl⟩

-- Understood Reflexive Object (§1.2.3)

theorem uro_wash_agrees :
    uro_wash.result = .participates ∧
    LevinClass.dress.participatesIn .understoodReflexiveObject = true := ⟨rfl, rfl⟩

-- Total Transformation (§2.4.3)

theorem tt_turn_agrees :
    tt_turn.result = .participates ∧
    LevinClass.turn.participatesIn .totalTransformation = true := ⟨rfl, rfl⟩

-- Way Construction (§7.4)

theorem way_elbow_agrees :
    way_elbow.result = .participates ∧
    LevinClass.mannerOfMotion.participatesIn .wayConstruction = true := ⟨rfl, rfl⟩

-- Cognate Object (§7.1)

theorem co_laugh_agrees :
    co_laugh.result = .participates ∧
    LevinClass.mannerOfSpeaking.participatesIn .cognateObject = true := ⟨rfl, rfl⟩

theorem co_run_agrees :
    co_run.result = .participates ∧
    LevinClass.mannerOfMotion.participatesIn .cognateObject = true := ⟨rfl, rfl⟩

-- Directional Phrase (§7.8)

theorem dp_run_agrees :
    dp_run.result = .participates ∧
    LevinClass.mannerOfMotion.participatesIn .directionalPhrase = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Verbal Passive, Prepositional Passive, Swarm Agreement
-- ════════════════════════════════════════════════════

-- Verbal Passive (§5.1)

theorem vp_break_agrees :
    vp_break.result = .participates ∧
    LevinClass.break_.participatesIn .verbalPassive = true := ⟨rfl, rfl⟩

theorem vp_give_agrees :
    vp_give.result = .participates ∧
    LevinClass.give.participatesIn .verbalPassive = true := ⟨rfl, rfl⟩

theorem vp_eat_agrees :
    vp_eat.result = .participates ∧
    LevinClass.eat.participatesIn .verbalPassive = true := ⟨rfl, rfl⟩

theorem vp_see_agrees :
    vp_see.result = .participates ∧
    LevinClass.see.participatesIn .verbalPassive = true := ⟨rfl, rfl⟩

theorem vp_measure_agrees :
    vp_measure.result = .blocked ∧
    LevinClass.measure.participatesIn .verbalPassive = false := ⟨rfl, rfl⟩

-- Prepositional Passive (§5.2)

theorem pp_sleep_agrees :
    pp_sleep.result = .participates ∧
    LevinClass.assumePosition.participatesIn .prepositionalPassive = true := ⟨rfl, rfl⟩

theorem pp_talk_agrees :
    pp_talk.result = .participates ∧
    LevinClass.mannerOfSpeaking.participatesIn .prepositionalPassive = true := ⟨rfl, rfl⟩

-- Swarm (§2.3.4)

theorem sw_swarm_agrees :
    sw_swarm.result = .participates ∧
    LevinClass.exist.participatesIn .swarm = true := ⟨rfl, rfl⟩

theorem sw_crawl_agrees :
    sw_crawl.result = .participates ∧
    LevinClass.mannerOfMotion.participatesIn .swarm = true := ⟨rfl, rfl⟩

-- Induced Action (§1.1.2.2) — additional

theorem ia_walk_agrees :
    ia_walk.result = .participates ∧
    LevinClass.mannerOfMotion.participatesIn .inducedAction = true := ⟨rfl, rfl⟩

theorem ia_appear_agrees :
    ia_appear.result = .blocked ∧
    LevinClass.appear.participatesIn .inducedAction = false := ⟨rfl, rfl⟩

end Phenomena.ArgumentStructure.DiathesisAlternations.Bridge
