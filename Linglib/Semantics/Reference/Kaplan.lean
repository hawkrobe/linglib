/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Reference.Character
import Linglib.Semantics.Reference.Context.Shifts

/-!
# Kaplan's theory of indexicality

The three tenets of [kaplan-1989] as [schlenker-2011] states them, over any context type with its
coordinates given as projections. Interpretation is relativized to a context, so a sentence's
character holds at a context when its content is true at that context's world (`Character.HoldsAt`),
and a character is *a priori* when it holds at every context (`Character.IsAPriori`) and *necessary*
when its content is true at every world (`Character.IsNecessary`); the two come apart because
contexts are finer than worlds: when every context is proper, its agent existing at its world, *I
exist* is a priori (`Kaplan.isAPriori_existsAgent`) without being necessary
(`Kaplan.not_isNecessary_existsAgent`), and when every context is located *I am here now* is a
priori (`Kaplan.isAPriori_locatedAgent`). The English pure indexicals read a coordinate of the
speech-act context: as access patterns on the context tower they are `AccessPattern.origin` of a
coordinate (`Kaplan.I`, `Kaplan.you`, `Kaplan.now`, `Kaplan.here`, `Kaplan.actually`), hence
invariant under every embedding shift (`AccessPattern.stable_origin`), which is Kaplan's thesis for
English. An access pattern is a character over towers with rigid content
(`AccessPattern.toCharacter`), and an origin pattern at a root tower is `Character.dthat` of its
coordinate (`AccessPattern.origin_toCharacter_root`): the tower analysis at depth zero is Kaplan's.
An access pattern stable under every shift is *Kaplan-compliant*
(`AccessPattern.IsKaplanCompliant`); a shift that moves some context is a *monster*
(`ContextShift.IsMonster`), an operator on the context of utterance rather than on the circumstance
of evaluation. A shift that is no monster leaves every access pattern stable
(`AccessPattern.stable_of_not_isMonster`), and a monster is exactly a shift under which the
innermost context itself is unstable (`ContextShift.isMonster_iff_not_stable_innermost_id`). The
identity shift that Kaplan's thesis assigns to English attitude verbs is no monster
(`ContextShift.not_isMonster_one`); the attitude shift of [schlenker-2003] and [anand-
nevins-2004], which makes the holder the agent, is one whenever the holder is not the speaker
(`ContextShift.isMonster_attitudeShift`).

## References

* [kaplan-1989]
* [schlenker-2011]
* [schlenker-2003]
* [anand-nevins-2004]
-/

namespace Reference

variable {C R W E P T : Type*}

/-! ### A priori and necessary truth -/

namespace Character

variable (world : C → W)

/-- A character holds at a context when its content is true at the world of that context:
the evaluation of a root sentence. -/
def HoldsAt (χ : Character C W Prop) (c : C) : Prop := χ c (world c)

/-- A character is a priori when it holds at every context. -/
def IsAPriori (χ : Character C W Prop) : Prop := ∀ c, χ.HoldsAt world c

/-- A character is necessary when its content is true at every world of every context. -/
def IsNecessary (χ : Character C W Prop) : Prop := ∀ (c : C) (w : W), χ c w

theorem IsNecessary.isAPriori {χ : Character C W Prop} (h : χ.IsNecessary) :
    χ.IsAPriori world :=
  λ c => h c _

end Character

namespace Kaplan

variable (agent : C → E) (world : C → W) (position : C → P) (time : C → T)
  (exists_ : E → W → Prop) (located : E → P → T → W → Prop)

/-- The character of *I exist*: the agent of the context exists at the world of evaluation. -/
def existsAgent : Character C W Prop := λ c w => exists_ (agent c) w

/-- The character of *I am here now*: the agent of the context is at its position at its
time in the world of evaluation. -/
def locatedAgent : Character C W Prop := λ c w => located (agent c) (position c) (time c) w

/-- *I exist* is a priori when every context is proper, its agent existing at its world:
Kaplan's coherence constraint on contexts. -/
theorem isAPriori_existsAgent (h : ∀ c, exists_ (agent c) (world c)) :
    (existsAgent agent exists_).IsAPriori world :=
  h

/-- *I exist* is not necessary once some agent fails to exist at some world. -/
theorem not_isNecessary_existsAgent {c : C} {w : W} (h : ¬ exists_ (agent c) w) :
    ¬ (existsAgent agent exists_).IsNecessary :=
  λ hn => h (hn c w)

/-- *I am here now* is a priori when every context is located. -/
theorem isAPriori_locatedAgent (h : ∀ c, located (agent c) (position c) (time c) (world c)) :
    (locatedAgent agent position time located).IsAPriori world :=
  h

/-- On the canonical tuple, properness of every context is `Context.Proper`. -/
theorem isAPriori_existsAgent_of_proper (h : ∀ c : Context W E P T, c.Proper exists_) :
    (existsAgent (C := Context W E P T) Context.agent exists_).IsAPriori Context.world :=
  h

end Kaplan

/-! ### Monsters -/

/-- A context shift is a monster when it is not the identity: it moves some context. -/
def ContextShift.IsMonster (σ : ContextShift C) : Prop := σ ≠ 1

namespace ContextShift

theorem isMonster_iff (σ : ContextShift C) : σ.IsMonster ↔ ∃ c : C, σ • c ≠ c :=
  show (σ : C → C) ≠ id ↔ _ from Function.ne_iff

theorem not_isMonster_one : ¬ (1 : ContextShift C).IsMonster := λ h => h rfl

/-- An attitude shift to a holder other than some context's agent moves that context. -/
theorem isMonster_attitudeShift (holder : E) (w' : W) (c : Context W E P T)
    (h : c.agent ≠ holder) : (attitudeShift (P := P) (T := T) holder w').IsMonster :=
  (isMonster_iff _).2 ⟨c, λ e => h (by simpa using (congrArg Context.agent e).symm)⟩

end ContextShift

namespace AccessPattern

/-- A shift that is no monster leaves every access pattern stable. -/
theorem stable_of_not_isMonster (ap : AccessPattern C R) {σ : ContextShift C}
    (h : ¬ σ.IsMonster) : ap.Stable σ := by
  have hσ : σ = 1 := not_not.mp h
  subst hσ
  intro t
  obtain ⟨d, f⟩ := ap
  simp only [resolve]
  congr 1
  cases d with
  | origin => simp
  | «local» =>
    rw [DepthSpec.local_resolve, DepthSpec.local_resolve, ContextTower.push_depth,
      ContextTower.push_contextAt_succ_depth, one_smul, ContextTower.contextAt_depth]
  | relative k =>
    rcases le_or_gt k t.depth with hk | hk
    · rw [DepthSpec.relative_resolve, DepthSpec.relative_resolve,
        ContextTower.push_contextAt_of_le _ _ hk]
    · rw [DepthSpec.relative_resolve, DepthSpec.relative_resolve,
        ContextTower.push_contextAt_of_lt _ _ hk, one_smul,
        ContextTower.contextAt_saturates _ hk.le]

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
  λ σ => stable_origin f σ

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
