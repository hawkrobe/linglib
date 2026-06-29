import Linglib.Discourse.DialogueState
import Linglib.Discourse.Gameboard.Basic

/-!
# KOS's DGB as a lazy `LawfulDialogueState` instance
[ginzburg-2012]

Ginzburg's dialogue gameboard is a *lazy*, grounding-explicit scoreboard: an
assertion enters `Pending` (ungrounded), and acceptance moves it into `FACTS`.
This is exactly the discipline `Discourse.DialogueState`'s `groundedContent`
reference models, so the DGB is a genuine `LawfulDialogueState` instance — its
context-set observable (`λ w => ∀ p ∈ facts, p w`, the `HasContextSet` bridge)
coincides with the grounded content at every trace.

This is the projection the joints recut needs: KOS plugs into the shared
dialogue-state interface as the Ginzburg instance. The instance *projects* the
DGB's FACTS to a context set; it does not replace the per-participant DGB with a
single `Set W` — `completedTrace_agreement` between this and another framework is
informative precisely because it asks which gameboard's FACTS counts as the
common ground.

Content is pinned to `Set W` (`Fact = Cont = Set W`): the lazy `Pending → FACTS`
flow carries propositional content, and `LocProp`'s `Cont` is `Type`-pinned, so
`W : Type`.
-/

namespace Discourse.Gameboard

open CommonGround (HasContextSet)
open Discourse (DialogueEvent GroundingState groundedContent DialogueStep LawfulDialogueState)

variable {W P Q : Type}

/-- One lazy step of the DGB on a shared dialogue event: `assert` proposes (onto
Pending), `accept` grounds the most recent proposal (into FACTS), `reject` drops
it; question events leave FACTS and Pending untouched (they act on QUD, outside
the context-set observable). -/
def DGB.dStep (dgb : DGB P (Set W) Q (Set W)) :
    DialogueEvent W → DGB P (Set W) Q (Set W)
  | .assert p => dgb.pushPending { phon := "", cat := "", cont := p }
  | .accept   => match dgb.pending with
                 | lp :: rest => { dgb.addFact lp.cont with pending := rest }
                 | []         => dgb
  | .reject   => match dgb.pending with
                 | _ :: rest => { dgb with pending := rest }
                 | []        => dgb
  | _         => dgb

instance : DialogueStep (DGB P (Set W) Q (Set W)) W where
  init := DGB.initial
  step := DGB.dStep
  isCompleted dgb := dgb.pending = []

/-- The DGB's FACTS-as-context-set and the reference machine's `floor`, and the
Pending contents and the proposal stack, are preserved in lockstep by one step. -/
theorem dStep_sim (dgb : DGB P (Set W) Q (Set W)) (gs : GroundingState W)
    (e : DialogueEvent W)
    (hc : (fun w => ∀ p ∈ dgb.facts, p w) = gs.floor)
    (hp : dgb.pending.map (·.cont) = gs.pending) :
    (fun w => ∀ p ∈ (DGB.dStep dgb e).facts, p w) = (GroundingState.step gs e).floor
      ∧ (DGB.dStep dgb e).pending.map (·.cont) = (GroundingState.step gs e).pending := by
  cases e with
  | assert p =>
    exact ⟨by simpa [DGB.dStep, DGB.pushPending, GroundingState.step] using hc,
           by simp [DGB.dStep, DGB.pushPending, GroundingState.step, hp]⟩
  | accept =>
    rcases hd : dgb.pending with _ | ⟨lp, rest⟩
    · have hgs : gs.pending = [] := by rw [hd] at hp; simpa using hp
      exact ⟨by simp only [DGB.dStep, hd, GroundingState.step, hgs]; exact hc,
             by simp [DGB.dStep, hd, GroundingState.step, hgs]⟩
    · have hgs : gs.pending = lp.cont :: rest.map (·.cont) := by
        rw [hd] at hp; simpa using hp.symm
      refine ⟨?_, by simp [DGB.dStep, hd, GroundingState.step, hgs]⟩
      simp only [DGB.dStep, hd, DGB.addFact, GroundingState.step, hgs]
      rw [Set.inter_comm, ← hc]
      ext w; simp only [Set.mem_inter_iff, List.forall_mem_cons]; exact Iff.rfl
  | reject =>
    rcases hd : dgb.pending with _ | ⟨lp, rest⟩
    · have hgs : gs.pending = [] := by rw [hd] at hp; simpa using hp
      exact ⟨by simp only [DGB.dStep, hd, GroundingState.step, hgs]; exact hc,
             by simp [DGB.dStep, hd, GroundingState.step, hgs]⟩
    · have hgs : gs.pending = lp.cont :: rest.map (·.cont) := by
        rw [hd] at hp; simpa using hp.symm
      exact ⟨by simp only [DGB.dStep, hd, GroundingState.step, hgs]; exact hc,
             by simp [DGB.dStep, hd, GroundingState.step, hgs]⟩
  | polarQuestion p =>
    exact ⟨by simpa [DGB.dStep, GroundingState.step] using hc,
           by simpa [DGB.dStep, GroundingState.step] using hp⟩
  | whQuestion =>
    exact ⟨by simpa [DGB.dStep, GroundingState.step] using hc,
           by simpa [DGB.dStep, GroundingState.step] using hp⟩

/-- FACTS-context-set and grounded content coincide at every trace, by replaying
the one-step simulation. -/
theorem dgb_ground_invariant (es : List (DialogueEvent W))
    (dgb : DGB P (Set W) Q (Set W)) (gs : GroundingState W)
    (hc : (fun w => ∀ p ∈ dgb.facts, p w) = gs.floor)
    (hp : dgb.pending.map (·.cont) = gs.pending) :
    (fun w => ∀ p ∈ (es.foldl DGB.dStep dgb).facts, p w)
        = (es.foldl GroundingState.step gs).floor
      ∧ (es.foldl DGB.dStep dgb).pending.map (·.cont)
        = (es.foldl GroundingState.step gs).pending := by
  induction es generalizing dgb gs with
  | nil => exact ⟨hc, hp⟩
  | cons e es ih =>
    obtain ⟨hc', hp'⟩ := dStep_sim dgb gs e hc hp
    exact ih (DGB.dStep dgb e) (GroundingState.step gs e) hc' hp'

/-- The initial DGB's FACTS-context-set is the trivial (universal) context,
matching the reference machine's initial floor. -/
theorem dgb_initial_ctx :
    (fun w => ∀ p ∈ (DGB.initial : DGB P (Set W) Q (Set W)).facts, p w)
      = GroundingState.init.floor := by
  have hf : (DGB.initial : DGB P (Set W) Q (Set W)).facts = [] := rfl
  ext w; simp [hf, GroundingState.init]; trivial

/-- **KOS is a lazy lawful dialogue state.** Its FACTS-context-set coincides with
the grounded content of any trace — the per-participant DGB projects to the same
observable a perfect-communication framework reaches, *when* grounding completes. -/
instance : LawfulDialogueState (DGB P (Set W) Q (Set W)) W where
  contextSet_completed es _ :=
    (dgb_ground_invariant es DGB.initial GroundingState.init dgb_initial_ctx rfl).1

/-- The payoff fires for KOS: at any trace both frameworks complete, Ginzburg's
per-participant DGB and any other lawful framework project to the same context
set — `completedTrace_agreement` applied to the KOS instance. -/
example {S : Type} [LawfulDialogueState S W] (es : List (DialogueEvent W))
    (h₁ : DialogueStep.isCompleted (DialogueStep.run es : DGB P (Set W) Q (Set W)))
    (h₂ : DialogueStep.isCompleted (DialogueStep.run es : S)) :
    HasContextSet.toContextSet (DialogueStep.run es : DGB P (Set W) Q (Set W))
      = HasContextSet.toContextSet (DialogueStep.run es : S) :=
  completedTrace_agreement es h₁ h₂

end Discourse.Gameboard
