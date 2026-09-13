/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Reference.Character
import Linglib.Semantics.Reference.Context.Shifts

/-!
# Pure indexicals and monsters

The English pure indexicals of [kaplan-1989] read a coordinate of the speech-act context:
as access patterns on the context tower they are `AccessPattern.origin` of a coordinate
(`Kaplan.I`, `Kaplan.you`, `Kaplan.now`, `Kaplan.here`, `Kaplan.actually`), hence invariant
under every embedding shift (`AccessPattern.stable_origin`), which is Kaplan's thesis for
English. An access pattern is a character over towers with rigid content
(`AccessPattern.toCharacter`), and an origin pattern at a root tower is `Character.dthat` of
its coordinate (`AccessPattern.origin_toCharacter_root`): the tower analysis at depth zero is
Kaplan's. An access pattern stable under every shift is *Kaplan-compliant*
(`AccessPattern.IsKaplanCompliant`); a shift that moves some context is a *monster*
(`ContextShift.IsMonster`), an operator on the context of utterance rather than on the
circumstance of evaluation. A shift that is no monster leaves every access pattern stable
(`AccessPattern.stable_of_not_isMonster`), and a monster is exactly a shift under which the
innermost context itself is unstable (`ContextShift.isMonster_iff_not_stable_innermost_id`). The
identity shift that Kaplan's thesis assigns to English attitude verbs is no monster
(`ContextShift.not_isMonster_identityShift`); the attitude shift of [schlenker-2003] and
[anand-nevins-2004], which makes the holder the agent, is one whenever the holder is not the
speaker (`ContextShift.isMonster_attitudeShift`).

## References

* [kaplan-1989]
* [schlenker-2003]
* [anand-nevins-2004]
-/

namespace Reference

variable {C R W E P T : Type*}

/-! ### Monsters -/

/-- A context shift is a monster when it moves some context. -/
def ContextShift.IsMonster (σ : ContextShift C) : Prop := σ.apply ≠ id

namespace ContextShift

theorem isMonster_iff (σ : ContextShift C) : σ.IsMonster ↔ ∃ c, σ.apply c ≠ c :=
  Function.ne_iff

theorem not_isMonster_identityShift :
    ¬ (identityShift : ContextShift (Context W E P T)).IsMonster :=
  λ h => h rfl

/-- An attitude shift to a holder other than some context's agent moves that context. -/
theorem isMonster_attitudeShift (holder : E) (w' : W) (c : Context W E P T)
    (h : c.agent ≠ holder) : (attitudeShift (P := P) (T := T) holder w').IsMonster :=
  (isMonster_iff _).2 ⟨c, λ e => h (by simpa using (congrArg Context.agent e).symm)⟩

end ContextShift

namespace AccessPattern

/-- A shift that is no monster leaves every access pattern stable. -/
theorem stable_of_not_isMonster (ap : AccessPattern C R) {σ : ContextShift C}
    (h : ¬ σ.IsMonster) : ap.Stable σ := by
  have hσ : σ.apply = id := not_not.mp h
  intro t
  obtain ⟨d, f⟩ := ap
  simp only [resolve]
  congr 1
  cases d with
  | origin => simp
  | «local» =>
    rw [DepthSpec.local_resolve, DepthSpec.local_resolve, ContextTower.push_depth,
      ContextTower.push_contextAt_of_lt _ _ (Nat.lt_succ_self _), hσ, ContextTower.contextAt_depth]
    rfl
  | relative k =>
    rcases le_or_gt k t.depth with hk | hk
    · rw [DepthSpec.relative_resolve, DepthSpec.relative_resolve,
        ContextTower.push_contextAt_of_le _ _ hk]
    · rw [DepthSpec.relative_resolve, DepthSpec.relative_resolve,
        ContextTower.push_contextAt_of_lt _ _ hk, hσ, ContextTower.contextAt_saturates _ _ hk.le]
      rfl

/-- An access pattern as a character over towers: at each tower, the rigid content at its
value. -/
def toCharacter (ap : AccessPattern C R) : Character (ContextTower C) W R :=
  Character.dthat ap.resolve

@[simp] theorem toCharacter_apply (ap : AccessPattern C R) (t : ContextTower C) (w : W) :
    (ap.toCharacter : Character (ContextTower C) W R) t w = ap.resolve t :=
  rfl

theorem toCharacter_isDirectlyReferential (ap : AccessPattern C R) :
    (ap.toCharacter : Character (ContextTower C) W R).IsDirectlyReferential :=
  Character.dthat_isDirectlyReferential _

/-- At a root tower an origin pattern is Kaplan's rigidifier of its coordinate. -/
theorem origin_toCharacter_root (f : C → R) (c : C) :
    ((origin f).toCharacter : Character (ContextTower C) W R) (ContextTower.root c) =
      Character.dthat f c :=
  rfl

/-- An access pattern is Kaplan-compliant when it is stable under every shift. -/
def IsKaplanCompliant (ap : AccessPattern C R) : Prop := ∀ σ, ap.Stable σ

theorem isKaplanCompliant_origin (f : C → R) : (origin f).IsKaplanCompliant :=
  stable_origin f

end AccessPattern

/-- A shift is a monster iff the innermost context is unstable under it. -/
theorem ContextShift.isMonster_iff_not_stable_innermost_id (σ : ContextShift C) :
    σ.IsMonster ↔ ¬ (AccessPattern.innermost id).Stable σ := by
  simp only [isMonster_iff, AccessPattern.Stable, AccessPattern.innermost_resolve,
    ContextTower.push_innermost, id_eq, not_forall]
  exact ⟨λ ⟨c, hc⟩ => ⟨ContextTower.root c, by simpa using hc⟩, λ ⟨t, ht⟩ => ⟨t.innermost, ht⟩⟩

/-! ### The English pure indexicals -/

namespace Kaplan

/-- *I*: the agent of the speech-act context. -/
def I : AccessPattern (Context W E P T) E := .origin Context.agent

/-- *you*: the addressee of the speech-act context. -/
def you : AccessPattern (Context W E P T) E := .origin Context.addressee

/-- *now*: the time of the speech-act context. -/
def now : AccessPattern (Context W E P T) T := .origin Context.time

/-- *here*: the position of the speech-act context. -/
def here : AccessPattern (Context W E P T) P := .origin Context.position

/-- *actually*: the world of the speech-act context. -/
def actually : AccessPattern (Context W E P T) W := .origin Context.world

end Kaplan

end Reference
