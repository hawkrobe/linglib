/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Fragments.Hausa.TAM
import Linglib.Fragments.Hausa.Tone
import Linglib.Features.Gender.Basic

/-!
# Hausa focus and the stabilizer nē/cē

Hausa focuses a constituent by fronting it (*ex-situ*) or leaving it in
place (*in-situ*). Ex-situ focus shifts the clause's TAM to the Relative
form where one exists; the agreeing polar-tone particle *nē/cē* — Newman's
*stabilizer* ([newman-2000] §66) — may surface after the focus in either
strategy, and in-situ focus is otherwise unmarked, prosody included
([hartmann-zimmermann-2007] §2, §5).

## Main definitions

* `Strategy`: in-situ vs ex-situ focus.
* `Stabilizer`, `stabilizerFor`: the particle's two allomorphs and their
  selection by gender and number.
* `FocusConfig`: a focused clause's PAC, strategy, focus agreement
  features, and stabilizer.
* `FocusConfig.Licensed`: ex-situ focus with a Relative-capable TAM must
  surface Relative mode ([jaggar-green-2003] analyse this as movement to
  a single CP-internal position; only the licensing condition is recorded
  here).

## Main results

* `stabilizerFor_eq_cee_iff`: *cē* appears exactly with feminine-singular
  focus.
* `stabilizer_tone_is_polar`: the stabilizer's surface tone is
  `Hausa.polarOf` of the host's final tone — the same autosegmental
  operation as the genitive linker *-n*.

## Implementation notes

`Licensed` is propositional, not a `Subtype` invariant: `FocusConfig` is
unrestricted, and `exSitu_with_genCmp` is an explicit ill-licensed
configuration showing the predicate has bite. `mkInSitu`/`mkExSitu` are
ergonomic constructors; the ex-situ one takes the licensing obligation as
an argument.
-/

namespace Hausa

open Tone (TRN)

/-! ### Strategy and stabilizer -/

/-- The two focus strategies of Hausa. Pragmatic-type distinctions cut
across both strategies and live in study files. -/
inductive Strategy where
  | inSitu
  | exSitu
  deriving DecidableEq, Repr, Inhabited

/-- The stabilizer's allomorphs: *cē* with feminine-singular focus, *nē*
elsewhere ([newman-2000] §66.1). -/
inductive Stabilizer where
  | nee
  | cee
  deriving DecidableEq, Repr, Inhabited

/-- Surface form of the stabilizer. -/
def Stabilizer.form : Stabilizer → String
  | .nee => "nē"
  | .cee => "cē"

/-- The stabilizer agreeing with a focus of the given gender and number:
*cē* iff feminine singular; plurals of either gender take *nē*
([newman-2000] §66.1). -/
def stabilizerFor (g : Gender) (singular : Bool) : Stabilizer :=
  match g, singular with
  | .feminine, true => .cee
  | _, _            => .nee

/-! ### Focus configurations -/

/-- A focused clause: its PAC, focus strategy, the focused constituent's
agreement features, and whether a stabilizer surfaces. -/
structure FocusConfig where
  /-- The clause's person-aspect complex. -/
  pac      : PAC
  /-- The focus strategy. -/
  strategy : Strategy
  /-- Gender of the focused constituent (selects *nē* vs *cē*). -/
  focusG   : Gender
  /-- Whether the focused constituent is singular. -/
  focusSG  : Bool
  /-- Whether a stabilizer surfaces (optional ex-situ, sporadic
  sentence-final in-situ, [hartmann-zimmermann-2007] §2.2). -/
  hasStab  : Bool
  deriving Repr

/-- The stabilizer realised by a configuration, if any. -/
def FocusConfig.stab? (c : FocusConfig) : Option Stabilizer :=
  if c.hasStab then some (stabilizerFor c.focusG c.focusSG) else none

/-- Ex-situ focus must surface the Relative mode whenever the TAM has a
Relative form; in-situ focus is unconstrained ([newman-2000] §65–§66). -/
def FocusConfig.Licensed (c : FocusConfig) : Prop :=
  c.strategy = .exSitu → c.pac.tam.HasRelativeForm → c.pac.mode = .relative

instance (c : FocusConfig) : Decidable c.Licensed :=
  inferInstanceAs (Decidable (_ → _ → _))

/-! ### Constructors -/

/-- An in-situ focus configuration; always licensed. The stabilizer
defaults to absent but may sporadically surface sentence-finally
([hartmann-zimmermann-2007] §2.2). -/
def mkInSitu (pac : PAC) (focusG : Gender) (focusSG : Bool)
    (hasStab : Bool := false) : FocusConfig :=
  ⟨pac, .inSitu, focusG, focusSG, hasStab⟩

/-- An ex-situ focus configuration; the anonymous argument is the
licensing obligation it threads (see `mkExSitu_licensed`). -/
def mkExSitu (pac : PAC) (focusG : Gender) (focusSG : Bool)
    (_ : pac.tam.HasRelativeForm → pac.mode = .relative)
    (hasStab : Bool := true) : FocusConfig :=
  ⟨pac, .exSitu, focusG, focusSG, hasStab⟩

theorem mkInSitu_licensed (p : PAC) (g : Gender) (sg hs : Bool) :
    (mkInSitu p g sg hs).Licensed := nofun

theorem mkExSitu_licensed (p : PAC) (g : Gender) (sg : Bool)
    (h : p.tam.HasRelativeForm → p.mode = .relative) (hs : Bool) :
    (mkExSitu p g sg h hs).Licensed := fun _ => h

/-! ### Examples -/

/-- Ex-situ feminine-singular focus with the Relative completive;
licensed, surfaces *cē*. -/
def exSitu_fem_relCmp : FocusConfig :=
  mkExSitu cmp_3sm_R .feminine true (fun _ => rfl)

/-- In-situ focus with a General-mode PAC; licensed unconditionally. -/
def inSitu_any : FocusConfig := mkInSitu cmp_3sm_G .masculine true

/-- An ill-licensed ex-situ configuration with the General completive,
built directly to show `Licensed` has bite. -/
def exSitu_with_genCmp : FocusConfig :=
  ⟨cmp_3sm_G, .exSitu, .masculine, true, false⟩

/-- The licensed focus-configuration registry used downstream;
`exSitu_with_genCmp` is deliberately excluded. -/
def focusConfigs : List FocusConfig := [exSitu_fem_relCmp, inSitu_any]

/-! ### Licensing and agreement -/

/-- *cē* appears exactly with feminine-singular focus. -/
theorem stabilizerFor_eq_cee_iff (g : Gender) (sg : Bool) :
    stabilizerFor g sg = .cee ↔ g = .feminine ∧ sg = true := by
  cases g <;> cases sg <;> simp [stabilizerFor]

theorem all_focusConfigs_licensed : ∀ c ∈ focusConfigs, c.Licensed := by decide

theorem exSitu_with_genCmp_not_licensed : ¬ exSitu_with_genCmp.Licensed := by
  decide

/-- The feminine-singular ex-situ example surfaces *cē*. -/
theorem exSitu_fem_picks_cee : exSitu_fem_relCmp.stab? = some .cee := rfl

/-! ### Stabilizer tone -/

/-- Surface tone of the stabilizer after a host whose final TBU carries
the given tone: polar, i.e. the opposite of the host ([newman-2000]
§66.1). -/
def Stabilizer.toneAfter (_ : Stabilizer) (host : TRN) : TRN :=
  polarOf host

/-- The stabilizer's surface tone is `Hausa.polarOf` of the host tone —
the same autosegmental operation as the genitive linker *-n*, not a
separate stipulation. -/
theorem stabilizer_tone_is_polar (s : Stabilizer) (host : TRN) :
    s.toneAfter host = polarOf host := rfl

/-- Two applications of the stabilizer-tone map restore the host tone on
the H/L sublattice. Direct corollary of `polarOf_involutive_on_HL`. -/
theorem stabilizer_toneAfter_involutive (s : Stabilizer) (h : TRN)
    (hh : h ∈ ([.H, .L] : List TRN)) :
    polarOf (s.toneAfter h) = h :=
  polarOf_involutive_on_HL h hh

end Hausa
