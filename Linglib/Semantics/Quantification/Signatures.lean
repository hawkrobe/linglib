/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Quantification.Basic
import Linglib.Logic.Natural.Soundness

/-!
# Signature profiles of generalized quantifiers
[peters-westerstahl-2006] [van-benthem-1984]

The natural-logic signature calculus instantiated at determiner
denotations: each [van-benthem-1984] double-monotonicity cell realizes a
`Sig₂` profile (`DoubleMono.toSig₂`, certified by the four cell
theorems), `LeftAntiAdditive`/`RightAntiAdditive`
([peters-westerstahl-2006] §5.9) are sectionwise `IsAntiAdditive` at the
`Prop` instance, and *every* and *no* get certified profiles — with
*not every* derived by profile composition rather than table lookup.

## Main declarations

* `DoubleMono.toSig₂` — the profile of each double-monotonicity cell.
* `sig₂_soundFor_upUp` … `sig₂_soundFor_downDown` — the cells realize
  their profiles.
* `leftAntiAdditive_iff_isAntiAdditive`,
  `rightAntiAdditive_iff_isAntiAdditive` — sectionwise anti-additivity.
* `every_sem_soundFor`, `no_sem_soundFor` — certified determiner
  profiles.
-/

namespace Quantification

open NaturalLogic

variable {α : Type*}

/-! ### The double-monotonicity cells -/

/-- The signature profile of each [van-benthem-1984] double-monotonicity
class, at mono/anti granularity. -/
def DoubleMono.toSig₂ : DoubleMono → Sig₂
  | .upUp => ⟨.mono, .mono⟩
  | .downUp => ⟨.anti, .mono⟩
  | .upDown => ⟨.mono, .anti⟩
  | .downDown => ⟨.anti, .anti⟩

/-- ↑MON↑ (e.g. *some*): both positions monotone. -/
theorem sig₂_soundFor_upUp {q : GQ α} (hr : RestrictorUpwardMono q)
    (hs : ScopeUpwardMono q) : DoubleMono.upUp.toSig₂.SoundFor q :=
  ⟨fun S => soundFor_mono_iff.mpr ((restrictorUpMono_iff_monotone q).mp hr S),
   fun R => soundFor_mono_iff.mpr ((scopeUpMono_iff_monotone q).mp hs R)⟩

/-- ↓MON↑ (e.g. *every*): restrictor antitone, scope monotone. -/
theorem sig₂_soundFor_downUp {q : GQ α} (hr : RestrictorDownwardMono q)
    (hs : ScopeUpwardMono q) : DoubleMono.downUp.toSig₂.SoundFor q :=
  ⟨fun S => soundFor_anti_iff.mpr ((restrictorDownMono_iff_antitone q).mp hr S),
   fun R => soundFor_mono_iff.mpr ((scopeUpMono_iff_monotone q).mp hs R)⟩

/-- ↑MON↓ (e.g. *not all*): restrictor monotone, scope antitone. -/
theorem sig₂_soundFor_upDown {q : GQ α} (hr : RestrictorUpwardMono q)
    (hs : ScopeDownwardMono q) : DoubleMono.upDown.toSig₂.SoundFor q :=
  ⟨fun S => soundFor_mono_iff.mpr ((restrictorUpMono_iff_monotone q).mp hr S),
   fun R => soundFor_anti_iff.mpr ((scopeDownMono_iff_antitone q).mp hs R)⟩

/-- ↓MON↓ (e.g. *no*): both positions antitone. -/
theorem sig₂_soundFor_downDown {q : GQ α} (hr : RestrictorDownwardMono q)
    (hs : ScopeDownwardMono q) : DoubleMono.downDown.toSig₂.SoundFor q :=
  ⟨fun S => soundFor_anti_iff.mpr ((restrictorDownMono_iff_antitone q).mp hr S),
   fun R => soundFor_anti_iff.mpr ((scopeDownMono_iff_antitone q).mp hs R)⟩

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
    Sig₂.SoundFor ⟨.anti, .mono⟩ (every_sem (α := α)) :=
  ⟨fun S => soundFor_anti_iff.mpr
      (((leftAntiAdditive_iff_isAntiAdditive _).mp every_laa S).antitone),
   fun R => soundFor_mono_iff.mpr
      ((scopeUpMono_iff_monotone _).mp every_scope_up R)⟩

/-- *No* realizes ↓MON↓, both positions via anti-additivity (`no_laa`,
`no_raa`). -/
theorem no_sem_soundFor :
    Sig₂.SoundFor ⟨.anti, .anti⟩ (no_sem (α := α)) :=
  ⟨fun S => soundFor_anti_iff.mpr
      (((leftAntiAdditive_iff_isAntiAdditive _).mp no_laa S).antitone),
   fun R => soundFor_anti_iff.mpr
      (((rightAntiAdditive_iff_isAntiAdditive _).mp no_raa R).antitone)⟩

/-- *Not every* by composition: negating *every* composes the
anti-morphism row into both positions of *every*'s profile. The scope
component `.antiAddMult * .mono = .anti` records that *any* is licensed
in *not every*'s scope. -/
example : Sig₂.SoundFor ⟨.antiAddMult * .anti, .antiAddMult * .mono⟩
    (fun R S => ¬ every_sem (α := α) R S) :=
  not_soundFor_antiAddMult.comp₂ every_sem_soundFor

end Quantification
