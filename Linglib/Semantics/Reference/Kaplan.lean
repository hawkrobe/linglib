/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Reference.Character
import Linglib.Semantics.Reference.Context.Shifts

/-!
# Kaplan's theory of indexicality

The three tenets of [kaplan-1989] as [schlenker-2011] states them. Interpretation is
relativized to a context, so a sentence's character holds at a context when its content is
true at that context's world (`Character.HoldsAt`), and a character is *a priori* when it
holds at every context (`Character.IsAPriori`) and *necessary* when its content is true at
every world (`Character.IsNecessary`); the two come apart because contexts are finer than
worlds, and on a type whose contexts are all proper (`ContextLike.Proper`) *I exist* is a
priori (`isAPriori_exists_agent`) without being necessary (`not_isNecessary_exists_agent`),
as is *I am here now* on a located type (`isAPriori_located_agent`). The English pure
indexicals read a coordinate of the speech-act context: as access patterns on the context
tower they are `AccessPattern.origin` of a coordinate (`Kaplan.I`, `Kaplan.you`,
`Kaplan.now`, `Kaplan.here`, `Kaplan.actually`), for any context-like type, hence invariant
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
* [schlenker-2011]
* [schlenker-2003]
* [anand-nevins-2004]
-/

namespace Reference

variable {C R W E P T : Type*}

/-! ### A priori and necessary truth -/

namespace Character

variable [ContextLike C W E P T]

/-- A character holds at a context when its content is true at the world of that context:
the evaluation of a root sentence. -/
def HoldsAt (χ : Character C W Prop) (c : C) : Prop := χ c (ContextLike.world c)

/-- A character is a priori when it holds at every context. -/
def IsAPriori (χ : Character C W Prop) : Prop := ∀ c, χ.HoldsAt c

/-- A character is necessary when its content is true at every world of every context. -/
def IsNecessary (χ : Character C W Prop) : Prop := ∀ (c : C) (w : W), χ c w

theorem IsNecessary.isAPriori {χ : Character C W Prop} (h : χ.IsNecessary) : χ.IsAPriori :=
  λ c => h c _

end Character

/-- A context-like type is proper for an existence predicate when the agent of every element
exists at its world: Kaplan's coherence constraint on contexts. -/
class ContextLike.Proper (C : Type*) {W E P T : Type*} [ContextLike C W E P T]
    (exists_ : E → W → Prop) : Prop where
  proper : ∀ c : C, (ContextLike.toContext c).Proper exists_

/-- A context-like type is located for a location predicate when the agent of every element
is at its position at its time in its world. -/
class ContextLike.Located (C : Type*) {W E P T : Type*} [ContextLike C W E P T]
    (located : E → P → T → W → Prop) : Prop where
  located : ∀ c : C, (ContextLike.toContext c).Located located

section Tenets

variable [ContextLike C W E P T] (exists_ : E → W → Prop) (located : E → P → T → W → Prop)

/-- The character of *I exist*: the agent of the context exists at the world of evaluation. -/
def Kaplan.existsAgent : Character C W Prop := λ c w => exists_ (ContextLike.agent c) w

/-- The character of *I am here now*: the agent of the context is at its position at its
time in the world of evaluation. -/
def Kaplan.locatedAgent : Character C W Prop :=
  λ c w => located (ContextLike.agent c) (ContextLike.position c) (ContextLike.time c) w

/-- *I exist* is a priori on a proper type. -/
theorem isAPriori_exists_agent [ContextLike.Proper C exists_] :
    (Kaplan.existsAgent (C := C) exists_).IsAPriori :=
  ContextLike.Proper.proper

/-- *I exist* is not necessary once some agent fails to exist at some world. -/
theorem not_isNecessary_exists_agent {c : C} {w : W} (h : ¬ exists_ (ContextLike.agent c) w) :
    ¬ (Kaplan.existsAgent (C := C) exists_).IsNecessary :=
  λ hn => h (hn c w)

/-- *I am here now* is a priori on a located type. -/
theorem isAPriori_located_agent [ContextLike.Located C located] :
    (Kaplan.locatedAgent (C := C) located).IsAPriori :=
  ContextLike.Located.located

end Tenets

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

variable [ContextLike C W E P T]

/-- *I*: the agent of the speech-act context. -/
def I : AccessPattern C E := .origin ContextLike.agent

/-- *you*: the addressee of the speech-act context. -/
def you : AccessPattern C E := .origin ContextLike.addressee

/-- *now*: the time of the speech-act context. -/
def now : AccessPattern C T := .origin ContextLike.time

/-- *here*: the position of the speech-act context. -/
def here : AccessPattern C P := .origin ContextLike.position

/-- *actually*: the world of the speech-act context. -/
def actually : AccessPattern C W := .origin ContextLike.world

end Kaplan

end Reference
