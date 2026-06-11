import Linglib.Core.Logic.Quantification.Basic
import Linglib.Semantics.Entailment.Soundness

/-!
# Per-position signature profiles for two-place operators

Linguistic operators carry one entailment signature per argument position —
*every* is anti-additive in its restrictor and monotone in its scope, *no*
is anti-additive in both ([peters-westerstahl-2006] §5.8–5.9,
[van-benthem-1984]). `Sig₂` records a signature pair, `Sig₂.SoundFor` says
each component is sound for the corresponding section, and
`EntailmentSig.SoundFor.comp₂` composes an outer context into both
positions at once — the shape of locality computations like K&L's
*not ∘ every-scope*. The "DE on a constant parameter" idiom (adversatives,
conditional antecedents) is the special case of reading one section of a
`Sig₂.SoundFor`.

The GQ bridges connect the profile to the existing per-position machinery
in `Core.Logic.Quantification`: the four `DoubleMono` cells realize
mono/anti profiles, and `Left`/`RightAntiAdditive` are sectionwise
`IsAntiAdditive` at the `Prop` instance. `every_sem` and `no_sem` get
certified profiles as worked instances.

## Main declarations

- `Sig₂`, `Sig₂.SoundFor`: per-position signature profile and its soundness;
- `EntailmentSig.SoundFor.comp₂`: outer composition acts componentwise;
- `DoubleMono.toSig₂` and the four cell theorems `sig₂_soundFor_upUp` …
  `sig₂_soundFor_downDown`;
- `leftAntiAdditive_iff_isAntiAdditive`, `rightAntiAdditive_iff_isAntiAdditive`;
- `every_sem_soundFor`, `no_sem_soundFor`: certified determiner profiles.
-/

namespace Core.NaturalLogic

open Semantics.Entailment.AntiAdditivity
open Core.Quantification

/-- A per-position signature profile for a two-place operator. For
determiners the positions are restrictor and scope; under the restrictor
analysis of conditionals, antecedent and consequent. -/
structure Sig₂ where
  restrictor : EntailmentSig
  scope : EntailmentSig
  deriving DecidableEq, Repr

section SoundFor

variable {α β γ δ : Type*} [Lattice α] [BoundedOrder α] [Lattice β]
  [BoundedOrder β] [Lattice γ] [BoundedOrder γ] [Lattice δ] [BoundedOrder δ]

/-- A profile is sound for a two-place operator when each component
signature is sound for the corresponding section (the other argument held
constant — K&L's "DE on a constant parameter" pattern, made positional). -/
def Sig₂.SoundFor (σ : Sig₂) (f : α → β → γ) : Prop :=
  (∀ y, σ.restrictor.SoundFor (fun x => f x y)) ∧
  (∀ x, σ.scope.SoundFor (f x))

/-- Composing a sound outer context into a sound two-place operator
composes the profile componentwise — the two-place form of
`EntailmentSig.SoundFor.comp`. -/
theorem EntailmentSig.SoundFor.comp₂ {ψ : EntailmentSig} {g : γ → δ}
    {σ : Sig₂} {f : α → β → γ} (hg : ψ.SoundFor g) (hf : σ.SoundFor f) :
    Sig₂.SoundFor ⟨ψ * σ.restrictor, ψ * σ.scope⟩ (fun x y => g (f x y)) :=
  ⟨fun y => hg.comp (hf.1 y), fun x => hg.comp (hf.2 x)⟩

end SoundFor

/-! ### Bridges to the GQ machinery -/

section GQBridges

variable {α : Type*}

/-- The signature profile of each [van-benthem-1984] double-monotonicity
class, at mono/anti granularity. -/
def _root_.Core.Quantification.DoubleMono.toSig₂ : DoubleMono → Sig₂
  | .upUp => ⟨.mono, .mono⟩
  | .downUp => ⟨.anti, .mono⟩
  | .upDown => ⟨.mono, .anti⟩
  | .downDown => ⟨.anti, .anti⟩

/-- ↑MON↑ (e.g. *some*): both positions monotone. -/
theorem sig₂_soundFor_upUp {q : GQ α} (hr : RestrictorUpwardMono q)
    (hs : ScopeUpwardMono q) : Sig₂.SoundFor ⟨.mono, .mono⟩ q :=
  ⟨fun S => soundFor_mono_iff.mpr ((restrictorUpMono_iff_monotone q).mp hr S),
   fun R => soundFor_mono_iff.mpr ((scopeUpMono_iff_monotone q).mp hs R)⟩

/-- ↓MON↑ (e.g. *every*): restrictor antitone, scope monotone. -/
theorem sig₂_soundFor_downUp {q : GQ α} (hr : RestrictorDownwardMono q)
    (hs : ScopeUpwardMono q) : Sig₂.SoundFor ⟨.anti, .mono⟩ q :=
  ⟨fun S => soundFor_anti_iff.mpr ((restrictorDownMono_iff_antitone q).mp hr S),
   fun R => soundFor_mono_iff.mpr ((scopeUpMono_iff_monotone q).mp hs R)⟩

/-- ↑MON↓ (e.g. *not all*): restrictor monotone, scope antitone. -/
theorem sig₂_soundFor_upDown {q : GQ α} (hr : RestrictorUpwardMono q)
    (hs : ScopeDownwardMono q) : Sig₂.SoundFor ⟨.mono, .anti⟩ q :=
  ⟨fun S => soundFor_mono_iff.mpr ((restrictorUpMono_iff_monotone q).mp hr S),
   fun R => soundFor_anti_iff.mpr ((scopeDownMono_iff_antitone q).mp hs R)⟩

/-- ↓MON↓ (e.g. *no*): both positions antitone. -/
theorem sig₂_soundFor_downDown {q : GQ α} (hr : RestrictorDownwardMono q)
    (hs : ScopeDownwardMono q) : Sig₂.SoundFor ⟨.anti, .anti⟩ q :=
  ⟨fun S => soundFor_anti_iff.mpr ((restrictorDownMono_iff_antitone q).mp hr S),
   fun R => soundFor_anti_iff.mpr ((scopeDownMono_iff_antitone q).mp hs R)⟩

/-- `LeftAntiAdditive` ([peters-westerstahl-2006] §5.9) is sectionwise
anti-additivity in the restrictor, at the `Prop` instance. -/
theorem leftAntiAdditive_iff_isAntiAdditive (q : GQ α) :
    LeftAntiAdditive q ↔ ∀ S, IsAntiAdditive (fun R => q R S) := by
  constructor
  · intro h S R R'
    show q (R ⊔ R') S = (q R S ∧ q R' S)
    exact propext (h R R' S)
  · intro h R R' S
    exact iff_of_eq (h S R R')

/-- `RightAntiAdditive` is sectionwise anti-additivity in the scope. -/
theorem rightAntiAdditive_iff_isAntiAdditive (q : GQ α) :
    RightAntiAdditive q ↔ ∀ R, IsAntiAdditive (q R) := by
  constructor
  · intro h R S S'
    show q R (S ⊔ S') = (q R S ∧ q R S')
    exact propext (h R S S')
  · intro h R S S'
    exact iff_of_eq (h R S S')

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

/-! ### Worked composition: *not every* -/

/-- Propositional negation realizes the anti-morphism row at the `Prop`
instance. -/
theorem not_soundFor_antiAddMult : EntailmentSig.SoundFor .antiAddMult Not :=
  soundFor_antiAddMult
    ⟨fun p q => propext not_or, by show (¬True) = False; simp⟩
    ⟨fun p q => propext not_and_or, by show (¬False) = True; simp⟩

/-- *Not every* by composition: negating *every* composes the anti-morphism
row into both positions of *every*'s profile. The scope component
`.antiAddMult * .mono = .anti` records that *any* is licensed in *not
every*'s scope. -/
example : Sig₂.SoundFor ⟨.antiAddMult * .anti, .antiAddMult * .mono⟩
    (fun R S => ¬ every_sem (α := α) R S) :=
  not_soundFor_antiAddMult.comp₂ every_sem_soundFor

end GQBridges

end Core.NaturalLogic
