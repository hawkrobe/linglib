/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Logic.Natural.Soundness

/-!
# Signature profiles of generalized quantifiers

This file instantiates the natural-logic signature calculus at determiner denotations. The
left and right anti-additivity of Peters and Westerståhl are sectionwise anti-additivity of the
restrictor and scope positions at the `Prop` instance, and *every* and *no* receive certified
`Signature₂` profiles, with *not every* derived by profile composition.

## Main results

* `leftAntiAdditive_iff_isAntiAdditive`, `rightAntiAdditive_iff_isAntiAdditive`: the two
  anti-additivities as sectionwise `IsAntiAdditive`.
* `every_sem_soundFor`, `no_sem_soundFor`: the certified determiner profiles.

## References

* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier.GQ

open NaturalLogic

variable {α : Type*}

/-! ### Sectionwise anti-additivity -/

/-- `LeftAntiAdditive` ([peters-westerstahl-2006] §5.9) is sectionwise
anti-additivity in the restrictor, at the `Prop` instance. -/
theorem leftAntiAdditive_iff_isAntiAdditive (q : GQ α) :
    LeftAntiAdditive q ↔ ∀ S, IsAntiAdditive (fun R => q R S) :=
  ⟨fun h S R R' => propext (h R R' S), fun h R R' S => iff_of_eq (h S R R')⟩

/-- `RightAntiAdditive` is sectionwise anti-additivity in the scope. -/
theorem rightAntiAdditive_iff_isAntiAdditive (q : GQ α) :
    RightAntiAdditive q ↔ ∀ R, IsAntiAdditive (q R) :=
  ⟨fun h R S S' => propext (h R S S'), fun h R S S' => iff_of_eq (h R S S')⟩

/-! ### Certified determiner profiles -/

/-- *Every* realizes ↓MON↑ as a certified profile, the restrictor side
derived from left anti-additivity (`every_laa`). -/
theorem every_sem_soundFor :
    Signature₂.SoundFor ⟨.anti, .mono⟩ (every_sem (α := α)) :=
  ⟨fun S => soundFor_anti_iff.mpr
      (((leftAntiAdditive_iff_isAntiAdditive _).mp every_laa S).antitone),
   fun R => soundFor_mono_iff.mpr
      ((scopeUpMono_iff_monotone _).mp every_scope_up R)⟩

/-- *No* realizes ↓MON↓, both positions via anti-additivity (`no_laa`,
`no_raa`). -/
theorem no_sem_soundFor :
    Signature₂.SoundFor ⟨.anti, .anti⟩ (no_sem (α := α)) :=
  ⟨fun S => soundFor_anti_iff.mpr
      (((leftAntiAdditive_iff_isAntiAdditive _).mp no_laa S).antitone),
   fun R => soundFor_anti_iff.mpr
      (((rightAntiAdditive_iff_isAntiAdditive _).mp no_raa R).antitone)⟩

/-- *Not every* is obtained by composition, since negating *every* composes the anti-morphism
row into both positions of *every*'s profile; the scope component `.antiAddMult * .mono = .anti`
records that *any* is licensed in *not every*'s scope. -/
example : Signature₂.SoundFor ⟨.antiAddMult * .anti, .antiAddMult * .mono⟩
    (fun R S => ¬ every_sem (α := α) R S) :=
  not_soundFor_antiAddMult.comp₂ every_sem_soundFor

end Quantifier.GQ
