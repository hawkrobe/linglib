import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Interfaces.SyntaxSemantics.Minimalism.VoiceTheta

/-!
# Bridge: Linking Theory Predictions → Hand-Annotated θ-Roles

Two accounts of argument realization make predictions about external
argument theta roles. This bridge file tests each account's predictions
independently against hand-annotated `subjectTheta` in the English
verb fragment. Both are instantiated as `LinkingTheory` (see
`Theories/Interfaces/SyntaxSemantics/Linking.lean`).

## Account 1: Severing (Kratzer 1996, Schäfer 2008)

Voice flavor determines the theta role: Voice_AG → agent, Voice_CAUSE →
stimulus. The prediction chain is: verb → Voice selection → theta role.
`Ctx = VoiceFlavor`; `predict` ignores the verb.

The current Voice typology has only two θ-assigning flavors, so it can
only distinguish agent from stimulus. It correctly predicts ~71% of verbs
(all agents + all stimuli), but systematically fails for:
- **Experiencer subjects** (know, believe, enjoy, ...): Voice_AG predicts
  agent, but the actual role is experiencer. The typology lacks a
  Voice_EXPERIENCER flavor.
- **Theme subjects** (arrive, glow, whisper, ...): Voice_nonThematic
  predicts none (no external argument), but the subject IS the internal
  argument that moved. The severing account correctly predicts no
  *external* argument; the subject's theta role comes from V, not Voice.

## Account 2: Lexicalist (Levin 1993, Rappaport Hovav & Levin 1998)

The verb's lexical semantics determines the theta role, bypassing Voice.
`Ctx = Unit`; `predict` ignores structure. Uses attitudeBuilder,
causalSource, objectTheta, factivePresup, levinClass, unaccusative,
controlType — all verb-internal semantic properties.

Correctly predicts ~93% of verbs. Fails for 6 genuinely irreducible
cases (sweep, remember, forget, dare, bother, hesitate) and 6 verbs
with missing annotations.
-/

namespace Phenomena.ArgumentStructure.Bridge.ThetaPrediction

open Fragments.English.Predicates.Verbal
open Core.Verbs (VerbCore)
open Theories.Interfaces.SyntaxSemantics.VoiceTheta (severingTheta selectedVoice)

-- ════════════════════════════════════════════════════════════════════════
-- PART I: Severing account (Kratzer 1996) — Voice flavor → theta role
-- ════════════════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════
-- § 1. Severing: correct predictions — agent
-- ════════════════════════════════════════════════════

/-! Voice_AG correctly predicts agent for ~93 verbs. Representative sample: -/

theorem sleep_sev: severingTheta sleep.toVerbCore = sleep.subjectTheta := rfl
theorem run_sev: severingTheta run.toVerbCore = run.subjectTheta := rfl
theorem eat_sev: severingTheta eat.toVerbCore = eat.subjectTheta := rfl
theorem kick_sev: severingTheta kick.toVerbCore = kick.subjectTheta := rfl
theorem give_sev: severingTheta give.toVerbCore = give.subjectTheta := rfl
theorem kill_sev: severingTheta kill.toVerbCore = kill.subjectTheta := rfl
theorem manage_sev: severingTheta manage.toVerbCore = manage.subjectTheta := rfl
theorem stop_sev: severingTheta stop.toVerbCore = stop.subjectTheta := rfl
theorem speak_sev: severingTheta speak.toVerbCore = speak.subjectTheta := rfl
theorem chase_sev: severingTheta chase.toVerbCore = chase.subjectTheta := rfl
theorem build_sev: severingTheta build.toVerbCore = build.subjectTheta := rfl

-- ════════════════════════════════════════════════════
-- § 2. Severing: correct predictions — stimulus
-- ════════════════════════════════════════════════════

/-! Voice_CAUSE correctly predicts stimulus for all Class II psych verbs. -/

theorem frighten_sev: severingTheta frighten.toVerbCore = frighten.subjectTheta := rfl
theorem amuse_sev: severingTheta amuse.toVerbCore = amuse.subjectTheta := rfl
theorem fascinate_sev: severingTheta fascinate.toVerbCore = fascinate.subjectTheta := rfl
theorem irritate_sev: severingTheta irritate.toVerbCore = irritate.subjectTheta := rfl
theorem annoy_sev: severingTheta annoy.toVerbCore = annoy.subjectTheta := rfl
theorem bore_sev: severingTheta bore.toVerbCore = bore.subjectTheta := rfl
theorem charm_sev: severingTheta charm.toVerbCore = charm.subjectTheta := rfl
theorem impress_sev: severingTheta impress.toVerbCore = impress.subjectTheta := rfl
theorem concern_sev: severingTheta concern.toVerbCore = concern.subjectTheta := rfl
theorem interest_sev: severingTheta interest.toVerbCore = interest.subjectTheta := rfl

-- ════════════════════════════════════════════════════
-- § 3. Severing: correct predictions — none
-- ════════════════════════════════════════════════════

theorem seem_sev: severingTheta seem.toVerbCore = seem.subjectTheta := rfl
theorem rain_sev: severingTheta rain.toVerbCore = rain.subjectTheta := rfl

-- ════════════════════════════════════════════════════
-- § 4. Severing: systematic failure — experiencer
-- ════════════════════════════════════════════════════

/-! The severing typology has no Voice_EXPERIENCER. All experiencer
    verbs select Voice_AG (agentive), which predicts agent — not experiencer.
    This is a systematic gap, not a per-verb accident. -/

/-- Attitude verbs: Voice_AG predicts agent, actual is experiencer. -/
theorem know_sev_mismatch :
    severingTheta know.toVerbCore = some .agent ∧
    know.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

theorem believe_sev_mismatch :
    severingTheta believe.toVerbCore = some .agent ∧
    believe.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

theorem want_sev_mismatch :
    severingTheta want.toVerbCore = some .agent ∧
    want.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

theorem fear_sev_mismatch :
    severingTheta fear.toVerbCore = some .agent ∧
    fear.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

theorem worry_sev_mismatch :
    severingTheta worry.toVerbCore = some .agent ∧
    worry.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

/-- Class I psych verbs (experiencer-subject): same gap. -/
theorem enjoy_sev_mismatch :
    severingTheta enjoy.toVerbCore = some .agent ∧
    enjoy.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

theorem see_sev_mismatch :
    severingTheta see.toVerbCore = some .agent ∧
    see.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

/-- Factive non-attitude: same gap. -/
theorem regret_sev_mismatch :
    severingTheta regret.toVerbCore = some .agent ∧
    regret.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Severing: systematic failure — theme
-- ════════════════════════════════════════════════════

/-! Unaccusative subjects are internal arguments that move to subject
    position. Voice_nonThematic correctly predicts no EXTERNAL argument,
    but the subject's theta role (theme) comes from V, not Voice.
    The prediction (none) differs from the annotation (theme). -/

theorem arrive_sev_mismatch :
    severingTheta arrive.toVerbCore = none ∧
    arrive.subjectTheta = some .theme := ⟨rfl, rfl⟩

theorem glow_sev_mismatch :
    severingTheta glow.toVerbCore = none ∧
    glow.subjectTheta = some .theme := ⟨rfl, rfl⟩

theorem exist_sev_mismatch :
    severingTheta exist.toVerbCore = none ∧
    exist.subjectTheta = some .theme := ⟨rfl, rfl⟩

theorem whisper_sev_mismatch :
    severingTheta whisper.toVerbCore = none ∧
    whisper.subjectTheta = some .theme := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Severing: coverage summary
-- ════════════════════════════════════════════════════

/-- Severing account matches for verbs where the subject IS
    the external argument AND the role is agent or stimulus. -/
theorem sev_match_count :
    (allVerbs.filter λ v =>
      severingTheta v.toVerbCore == v.subjectTheta).length = 130 := by
  native_decide

/-- Severing account fails for experiencer subjects, theme
    subjects (unaccusatives), and unannotated verbs. -/
theorem sev_mismatch_count :
    (allVerbs.filter λ v =>
      severingTheta v.toVerbCore != v.subjectTheta).length = 53 := by
  native_decide

-- ════════════════════════════════════════════════════════════════════════
-- PART II: Lexicalist account (Levin & RH 1998) — verb semantics → theta role
-- ════════════════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════
-- § 7. Lexicalist: correct predictions — none
-- ════════════════════════════════════════════════════

theorem seem_lex: seem.toVerbCore.predictedSubjectTheta = seem.subjectTheta := rfl
theorem rain_lex: rain.toVerbCore.predictedSubjectTheta = rain.subjectTheta := rfl

-- ════════════════════════════════════════════════════
-- § 8. Lexicalist: correct predictions — stimulus
-- ════════════════════════════════════════════════════

theorem frighten_lex: frighten.toVerbCore.predictedSubjectTheta = frighten.subjectTheta := rfl
theorem amuse_lex: amuse.toVerbCore.predictedSubjectTheta = amuse.subjectTheta := rfl
theorem fascinate_lex: fascinate.toVerbCore.predictedSubjectTheta = fascinate.subjectTheta := rfl
theorem irritate_lex: irritate.toVerbCore.predictedSubjectTheta = irritate.subjectTheta := rfl
theorem annoy_lex: annoy.toVerbCore.predictedSubjectTheta = annoy.subjectTheta := rfl
theorem bore_lex: bore.toVerbCore.predictedSubjectTheta = bore.subjectTheta := rfl
theorem charm_lex: charm.toVerbCore.predictedSubjectTheta = charm.subjectTheta := rfl
theorem impress_lex: impress.toVerbCore.predictedSubjectTheta = impress.subjectTheta := rfl
theorem concern_lex: concern.toVerbCore.predictedSubjectTheta = concern.subjectTheta := rfl
theorem interest_lex: interest.toVerbCore.predictedSubjectTheta = interest.subjectTheta := rfl

-- ════════════════════════════════════════════════════
-- § 9. Lexicalist: correct predictions — experiencer
-- ════════════════════════════════════════════════════

-- Via objectTheta = stimulus
theorem see_lex: see.toVerbCore.predictedSubjectTheta = see.subjectTheta := rfl
theorem hear_lex: hear.toVerbCore.predictedSubjectTheta = hear.subjectTheta := rfl
theorem enjoy_lex: enjoy.toVerbCore.predictedSubjectTheta = enjoy.subjectTheta := rfl
theorem like_lex: like.toVerbCore.predictedSubjectTheta = like.subjectTheta := rfl
theorem love_lex: love.toVerbCore.predictedSubjectTheta = love.subjectTheta := rfl
theorem hate_lex: hate.toVerbCore.predictedSubjectTheta = hate.subjectTheta := rfl
theorem admire_lex: admire.toVerbCore.predictedSubjectTheta = admire.subjectTheta := rfl
theorem envy_lex: envy.toVerbCore.predictedSubjectTheta = envy.subjectTheta := rfl
theorem respect_lex: respect.toVerbCore.predictedSubjectTheta = respect.subjectTheta := rfl
theorem value_lex: value.toVerbCore.predictedSubjectTheta = value.subjectTheta := rfl

-- Via attitudeBuilder
theorem know_lex: know.toVerbCore.predictedSubjectTheta = know.subjectTheta := rfl
theorem realize_lex: realize.toVerbCore.predictedSubjectTheta = realize.subjectTheta := rfl
theorem discover_lex: discover.toVerbCore.predictedSubjectTheta = discover.subjectTheta := rfl
theorem notice_lex: notice.toVerbCore.predictedSubjectTheta = notice.subjectTheta := rfl
theorem believe_lex: believe.toVerbCore.predictedSubjectTheta = believe.subjectTheta := rfl
theorem think_lex: think.toVerbCore.predictedSubjectTheta = think.subjectTheta := rfl
theorem want_lex: want.toVerbCore.predictedSubjectTheta = want.subjectTheta := rfl
theorem hope_lex: hope.toVerbCore.predictedSubjectTheta = hope.subjectTheta := rfl
theorem expect_lex: expect.toVerbCore.predictedSubjectTheta = expect.subjectTheta := rfl
theorem wish_lex: wish.toVerbCore.predictedSubjectTheta = wish.subjectTheta := rfl
theorem fear_lex: fear.toVerbCore.predictedSubjectTheta = fear.subjectTheta := rfl
theorem dread_lex: dread.toVerbCore.predictedSubjectTheta = dread.subjectTheta := rfl
theorem worry_lex: worry.toVerbCore.predictedSubjectTheta = worry.subjectTheta := rfl

-- Via factivePresup && !attitudeBuilder
theorem regret_lex: regret.toVerbCore.predictedSubjectTheta = regret.subjectTheta := rfl
theorem remember_rog_lex: remember_rog.toVerbCore.predictedSubjectTheta = remember_rog.subjectTheta := rfl
theorem forget_rog_lex: forget_rog.toVerbCore.predictedSubjectTheta = forget_rog.subjectTheta := rfl

-- Via senseTag = .occasion
theorem manage_occasion_lex: manage_occasion.toVerbCore.predictedSubjectTheta = manage_occasion.subjectTheta := rfl

-- Via levinClass (.flinch, .learn)
theorem flinch_lex: flinch.toVerbCore.predictedSubjectTheta = flinch.subjectTheta := rfl
theorem learn_lex: learn.toVerbCore.predictedSubjectTheta = learn.subjectTheta := rfl

-- ════════════════════════════════════════════════════
-- § 10. Lexicalist: correct predictions — theme
-- ════════════════════════════════════════════════════

theorem arrive_lex: arrive.toVerbCore.predictedSubjectTheta = arrive.subjectTheta := rfl
theorem whisper_lex: whisper.toVerbCore.predictedSubjectTheta = whisper.subjectTheta := rfl
theorem murmur_lex: murmur.toVerbCore.predictedSubjectTheta = murmur.subjectTheta := rfl
theorem shout_lex: shout.toVerbCore.predictedSubjectTheta = shout.subjectTheta := rfl
theorem cry_lex: cry.toVerbCore.predictedSubjectTheta = cry.subjectTheta := rfl
theorem scream_lex: scream.toVerbCore.predictedSubjectTheta = scream.subjectTheta := rfl
theorem glow_lex: glow.toVerbCore.predictedSubjectTheta = glow.subjectTheta := rfl
theorem buzz_lex: buzz.toVerbCore.predictedSubjectTheta = buzz.subjectTheta := rfl
theorem bleed_lex: bleed.toVerbCore.predictedSubjectTheta = bleed.subjectTheta := rfl
theorem rust_lex: rust.toVerbCore.predictedSubjectTheta = rust.subjectTheta := rfl
theorem exist_lex: exist.toVerbCore.predictedSubjectTheta = exist.subjectTheta := rfl
theorem appear_lex: appear.toVerbCore.predictedSubjectTheta = appear.subjectTheta := rfl

-- ════════════════════════════════════════════════════
-- § 11. Lexicalist: correct predictions — agent
-- ════════════════════════════════════════════════════

theorem sleep_lex: sleep.toVerbCore.predictedSubjectTheta = sleep.subjectTheta := rfl
theorem run_lex: run.toVerbCore.predictedSubjectTheta = run.subjectTheta := rfl
theorem eat_lex: eat.toVerbCore.predictedSubjectTheta = eat.subjectTheta := rfl
theorem kick_lex: kick.toVerbCore.predictedSubjectTheta = kick.subjectTheta := rfl
theorem give_lex: give.toVerbCore.predictedSubjectTheta = give.subjectTheta := rfl
theorem put_lex: put.toVerbCore.predictedSubjectTheta = put.subjectTheta := rfl
theorem buy_lex: buy.toVerbCore.predictedSubjectTheta = buy.subjectTheta := rfl
theorem meet_lex: meet.toVerbCore.predictedSubjectTheta = meet.subjectTheta := rfl
theorem sell_lex: sell.toVerbCore.predictedSubjectTheta = sell.subjectTheta := rfl
theorem leave_lex: leave.toVerbCore.predictedSubjectTheta = leave.subjectTheta := rfl
theorem devour_lex: devour.toVerbCore.predictedSubjectTheta = devour.subjectTheta := rfl
theorem read_lex: read.toVerbCore.predictedSubjectTheta = read.subjectTheta := rfl
theorem build_lex: build.toVerbCore.predictedSubjectTheta = build.subjectTheta := rfl
theorem write_lex: write.toVerbCore.predictedSubjectTheta = write.subjectTheta := rfl
theorem sweep_instr_lex: sweep_instr.toVerbCore.predictedSubjectTheta = sweep_instr.subjectTheta := rfl
theorem stop_lex: stop.toVerbCore.predictedSubjectTheta = stop.subjectTheta := rfl
theorem quit_lex: quit.toVerbCore.predictedSubjectTheta = quit.subjectTheta := rfl
theorem start_lex: start.toVerbCore.predictedSubjectTheta = start.subjectTheta := rfl
theorem begin_lex: begin_.toVerbCore.predictedSubjectTheta = begin_.subjectTheta := rfl
theorem continue_lex: continue_.toVerbCore.predictedSubjectTheta = continue_.subjectTheta := rfl
theorem keep_lex: keep.toVerbCore.predictedSubjectTheta = keep.subjectTheta := rfl
theorem manage_lex: manage.toVerbCore.predictedSubjectTheta = manage.subjectTheta := rfl
theorem fail_lex: fail.toVerbCore.predictedSubjectTheta = fail.subjectTheta := rfl
theorem try_lex: try_.toVerbCore.predictedSubjectTheta = try_.subjectTheta := rfl
theorem persuade_lex: persuade.toVerbCore.predictedSubjectTheta = persuade.subjectTheta := rfl
theorem promise_lex: promise.toVerbCore.predictedSubjectTheta = promise.subjectTheta := rfl
theorem cause_lex: cause.toVerbCore.predictedSubjectTheta = cause.subjectTheta := rfl
theorem make_lex: make.toVerbCore.predictedSubjectTheta = make.subjectTheta := rfl
theorem let_lex: let_.toVerbCore.predictedSubjectTheta = let_.subjectTheta := rfl
theorem have_caus_lex: have_caus.toVerbCore.predictedSubjectTheta = have_caus.subjectTheta := rfl
theorem get_caus_lex: get_caus.toVerbCore.predictedSubjectTheta = get_caus.subjectTheta := rfl
theorem force_lex: force.toVerbCore.predictedSubjectTheta = force.subjectTheta := rfl
theorem kill_lex: kill.toVerbCore.predictedSubjectTheta = kill.subjectTheta := rfl
theorem break_lex: break_.toVerbCore.predictedSubjectTheta = break_.subjectTheta := rfl
theorem tear_lex: tear_.toVerbCore.predictedSubjectTheta = tear_.subjectTheta := rfl
theorem burn_lex: burn.toVerbCore.predictedSubjectTheta = burn.subjectTheta := rfl
theorem destroy_lex: destroy.toVerbCore.predictedSubjectTheta = destroy.subjectTheta := rfl
theorem melt_lex: melt.toVerbCore.predictedSubjectTheta = melt.subjectTheta := rfl
theorem activate_lex: activate.toVerbCore.predictedSubjectTheta = activate.subjectTheta := rfl
theorem affect_lex: affect.toVerbCore.predictedSubjectTheta = affect.subjectTheta := rfl
theorem change_lex: change.toVerbCore.predictedSubjectTheta = change.subjectTheta := rfl
theorem damage_lex: damage.toVerbCore.predictedSubjectTheta = damage.subjectTheta := rfl
theorem eliminate_lex: eliminate.toVerbCore.predictedSubjectTheta = eliminate.subjectTheta := rfl
theorem hurt_lex: hurt.toVerbCore.predictedSubjectTheta = hurt.subjectTheta := rfl
theorem restore_lex: restore.toVerbCore.predictedSubjectTheta = restore.subjectTheta := rfl
theorem trigger_lex: trigger.toVerbCore.predictedSubjectTheta = trigger.subjectTheta := rfl
theorem bury_lex: bury.toVerbCore.predictedSubjectTheta = bury.subjectTheta := rfl
theorem drop_lex: drop.toVerbCore.predictedSubjectTheta = drop.subjectTheta := rfl
theorem lift_lex: lift.toVerbCore.predictedSubjectTheta = lift.subjectTheta := rfl
theorem lock_lex: lock.toVerbCore.predictedSubjectTheta = lock.subjectTheta := rfl
theorem shut_lex: shut.toVerbCore.predictedSubjectTheta = shut.subjectTheta := rfl
theorem spread_lex: spread.toVerbCore.predictedSubjectTheta = spread.subjectTheta := rfl
theorem stretch_lex: stretch.toVerbCore.predictedSubjectTheta = stretch.subjectTheta := rfl
theorem switch_lex: switch.toVerbCore.predictedSubjectTheta = switch.subjectTheta := rfl
theorem speak_lex: speak.toVerbCore.predictedSubjectTheta = speak.subjectTheta := rfl
theorem talk_lex: talk.toVerbCore.predictedSubjectTheta = talk.subjectTheta := rfl
theorem investigate_lex: investigate.toVerbCore.predictedSubjectTheta = investigate.subjectTheta := rfl
theorem chase_lex: chase.toVerbCore.predictedSubjectTheta = chase.subjectTheta := rfl
theorem hit_lex: hit.toVerbCore.predictedSubjectTheta = hit.subjectTheta := rfl
theorem push_lex: push.toVerbCore.predictedSubjectTheta = push.subjectTheta := rfl
theorem pull_lex: pull.toVerbCore.predictedSubjectTheta = pull.subjectTheta := rfl
theorem carry_lex: carry.toVerbCore.predictedSubjectTheta = carry.subjectTheta := rfl
theorem drag_lex: drag.toVerbCore.predictedSubjectTheta = drag.subjectTheta := rfl
theorem call_lex: call.toVerbCore.predictedSubjectTheta = call.subjectTheta := rfl
theorem place_lex: place.toVerbCore.predictedSubjectTheta = place.subjectTheta := rfl
theorem pour_lex: pour.toVerbCore.predictedSubjectTheta = pour.subjectTheta := rfl
theorem spray_lex: spray.toVerbCore.predictedSubjectTheta = spray.subjectTheta := rfl
theorem load_lex: load.toVerbCore.predictedSubjectTheta = load.subjectTheta := rfl
theorem remove_lex: remove.toVerbCore.predictedSubjectTheta = remove.subjectTheta := rfl
theorem clean_lex: clean.toVerbCore.predictedSubjectTheta = clean.subjectTheta := rfl
theorem steal_lex: steal.toVerbCore.predictedSubjectTheta = steal.subjectTheta := rfl
theorem send_lex: send.toVerbCore.predictedSubjectTheta = send.subjectTheta := rfl
theorem drive_lex: drive.toVerbCore.predictedSubjectTheta = drive.subjectTheta := rfl
theorem donate_lex: donate.toVerbCore.predictedSubjectTheta = donate.subjectTheta := rfl
theorem obtain_lex: obtain.toVerbCore.predictedSubjectTheta = obtain.subjectTheta := rfl
theorem trade_lex: trade.toVerbCore.predictedSubjectTheta = trade.subjectTheta := rfl
theorem hold_lex: hold.toVerbCore.predictedSubjectTheta = hold.subjectTheta := rfl
theorem hide_lex: hide.toVerbCore.predictedSubjectTheta = hide.subjectTheta := rfl
theorem throw_lex: throw.toVerbCore.predictedSubjectTheta = throw.subjectTheta := rfl
theorem poke_lex: poke.toVerbCore.predictedSubjectTheta = poke.subjectTheta := rfl
theorem touch_lex: touch.toVerbCore.predictedSubjectTheta = touch.subjectTheta := rfl
theorem cut_lex: cut.toVerbCore.predictedSubjectTheta = cut.subjectTheta := rfl
theorem chop_lex: chop.toVerbCore.predictedSubjectTheta = chop.subjectTheta := rfl
theorem mix_lex: mix.toVerbCore.predictedSubjectTheta = mix.subjectTheta := rfl
theorem separate_lex: separate.toVerbCore.predictedSubjectTheta = separate.subjectTheta := rfl
theorem paint_lex: paint.toVerbCore.predictedSubjectTheta = paint.subjectTheta := rfl
theorem draw_lex: draw.toVerbCore.predictedSubjectTheta = draw.subjectTheta := rfl
theorem create_lex: create.toVerbCore.predictedSubjectTheta = create.subjectTheta := rfl
theorem grow_lex: grow.toVerbCore.predictedSubjectTheta = grow.subjectTheta := rfl
theorem perform_lex: perform.toVerbCore.predictedSubjectTheta = perform.subjectTheta := rfl
theorem appoint_lex: appoint.toVerbCore.predictedSubjectTheta = appoint.subjectTheta := rfl
theorem blame_lex: blame.toVerbCore.predictedSubjectTheta = blame.subjectTheta := rfl
theorem evaluate_lex: evaluate.toVerbCore.predictedSubjectTheta = evaluate.subjectTheta := rfl
theorem marry_lex: marry.toVerbCore.predictedSubjectTheta = marry.subjectTheta := rfl
theorem bark_lex: bark.toVerbCore.predictedSubjectTheta = bark.subjectTheta := rfl
theorem breathe_lex: breathe.toVerbCore.predictedSubjectTheta = breathe.subjectTheta := rfl
theorem cough_lex: cough.toVerbCore.predictedSubjectTheta = cough.subjectTheta := rfl
theorem dress_lex: dress.toVerbCore.predictedSubjectTheta = dress.subjectTheta := rfl
theorem drown_lex: drown.toVerbCore.predictedSubjectTheta = drown.subjectTheta := rfl
theorem bend_lex: bend.toVerbCore.predictedSubjectTheta = bend.subjectTheta := rfl
theorem boil_lex: boil.toVerbCore.predictedSubjectTheta = boil.subjectTheta := rfl
theorem increase_lex: increase.toVerbCore.predictedSubjectTheta = increase.subjectTheta := rfl
theorem straighten_lex: straighten.toVerbCore.predictedSubjectTheta = straighten.subjectTheta := rfl
theorem flatten_lex: flatten.toVerbCore.predictedSubjectTheta = flatten.subjectTheta := rfl
theorem open_lex: open_.toVerbCore.predictedSubjectTheta = open_.subjectTheta := rfl
theorem lengthen_lex: lengthen.toVerbCore.predictedSubjectTheta = lengthen.subjectTheta := rfl
theorem widen_lex: widen.toVerbCore.predictedSubjectTheta = widen.subjectTheta := rfl
theorem cool_lex: cool.toVerbCore.predictedSubjectTheta = cool.subjectTheta := rfl
theorem warm_lex: warm.toVerbCore.predictedSubjectTheta = warm.subjectTheta := rfl
theorem fidget_lex: fidget.toVerbCore.predictedSubjectTheta = fidget.subjectTheta := rfl
theorem sit_lex: sit.toVerbCore.predictedSubjectTheta = sit.subjectTheta := rfl
theorem stand_lex: stand.toVerbCore.predictedSubjectTheta = stand.subjectTheta := rfl
theorem walk_lex: walk.toVerbCore.predictedSubjectTheta = walk.subjectTheta := rfl
theorem swim_lex: swim.toVerbCore.predictedSubjectTheta = swim.subjectTheta := rfl
theorem fly_lex: fly.toVerbCore.predictedSubjectTheta = fly.subjectTheta := rfl
theorem avoid_lex: avoid.toVerbCore.predictedSubjectTheta = avoid.subjectTheta := rfl
theorem linger_lex: linger.toVerbCore.predictedSubjectTheta = linger.subjectTheta := rfl
theorem rush_lex: rush.toVerbCore.predictedSubjectTheta = rush.subjectTheta := rfl

-- ════════════════════════════════════════════════════
-- § 12. Lexicalist: mismatches — irreducible
-- ════════════════════════════════════════════════════

theorem sweep_lex_mismatch :
    sweep.toVerbCore.predictedSubjectTheta = some .agent ∧
    sweep.subjectTheta = none := ⟨rfl, rfl⟩

theorem remember_lex_mismatch :
    remember.toVerbCore.predictedSubjectTheta = some .agent ∧
    remember.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

theorem forget_lex_mismatch :
    forget.toVerbCore.predictedSubjectTheta = some .agent ∧
    forget.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

theorem dare_lex_mismatch :
    dare.toVerbCore.predictedSubjectTheta = some .agent ∧
    dare.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

theorem bother_lex_mismatch :
    bother.toVerbCore.predictedSubjectTheta = some .agent ∧
    bother.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

theorem hesitate_lex_mismatch :
    hesitate.toVerbCore.predictedSubjectTheta = some .agent ∧
    hesitate.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 13. Lexicalist: mismatches — unannotated
-- ════════════════════════════════════════════════════

theorem say_lex_unannotated :
    say.toVerbCore.predictedSubjectTheta = some .agent ∧
    say.subjectTheta = none := ⟨rfl, rfl⟩

theorem tell_lex_unannotated :
    tell.toVerbCore.predictedSubjectTheta = some .agent ∧
    tell.subjectTheta = none := ⟨rfl, rfl⟩

theorem claim_lex_unannotated :
    claim.toVerbCore.predictedSubjectTheta = some .agent ∧
    claim.subjectTheta = none := ⟨rfl, rfl⟩

theorem ask_lex_unannotated :
    ask.toVerbCore.predictedSubjectTheta = some .agent ∧
    ask.subjectTheta = none := ⟨rfl, rfl⟩

theorem wonder_lex_unannotated :
    wonder.toVerbCore.predictedSubjectTheta = some .agent ∧
    wonder.subjectTheta = none := ⟨rfl, rfl⟩

theorem depend_on_lex_unannotated :
    depend_on.toVerbCore.predictedSubjectTheta = some .agent ∧
    depend_on.subjectTheta = none := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 14. Lexicalist: coverage summary
-- ════════════════════════════════════════════════════

theorem lex_match_count :
    (allVerbs.filter λ v =>
      v.toVerbCore.predictedSubjectTheta == v.subjectTheta).length = 171 := by
  native_decide

theorem lex_mismatch_count :
    (allVerbs.filter λ v =>
      v.toVerbCore.predictedSubjectTheta != v.subjectTheta).length = 12 := by
  native_decide

end Phenomena.ArgumentStructure.Bridge.ThetaPrediction
