import Linglib.Fragments.Hausa.TAM
import Linglib.Fragments.Hausa.Tone
import Linglib.Core.Gender

/-!
# Hausa Focus and the Stabilizer *nē/cē* — mathlib-style
@cite{newman-2000} @cite{jaggar-green-2003} @cite{hartmann-zimmermann-2007}

Hausa expresses focus by two principal strategies (@cite{newman-2000}
ch. 28, ch. 66):

1. **In-situ focus**: the focused constituent stays in its canonical
   position; focus is signaled prosodically (and contextually) without
   any morphosyntactic reflex.
2. **Ex-situ focus**: the focused constituent fronts to a clause-initial
   position. Two morphosyntactic reflexes are diagnostic:
   - the **stabilizer** *nē* (M / non-feminine-singular) or *cē*
     (F.SG) optionally surfaces after the focused phrase, agreeing in
     gender and number with the focus (@cite{newman-2000} §66.1).
   - the clause's TAM shifts to the **Relative form** (in completive
     and continuous; cf. `Hausa/TAM.lean` §1).

The Relative-form requirement is the main empirical hook: it ties
ex-situ focus to the broader morphological General/Relative split shared
with relative clauses and *wh*-questions (@cite{jaggar-green-2003}
argue this is movement to a single CP-internal position, but we stay
theory-neutral here and just record the licensing condition).

`FocusConfig.Licensed` is propositional (`Prop` with `Decidable`).
It is *not* enforced as a `Subtype` invariant: the structure is
unrestricted, and `exSitu_with_genCmp` below is an explicit
ill-licensed example used to prove the predicate non-vacuous. The
`mkInSitu`/`mkExSitu` constructors are ergonomic helpers; the ex-situ
one takes a proof obligation that licenses what it builds.
-/

namespace Fragments.Hausa.Focus

open Fragments.Hausa.Inflection (TAM Mode Subject PAC)
open Fragments.Hausa.Tone (polarOf)
open Phonology.Autosegmental.RegisterTier (TRN)
open Core (SurfaceGender)

-- ============================================================================
-- § 1: Focus Strategy
-- ============================================================================

/-- The two focus strategies in Hausa. Contrastive vs information focus
    distinctions cut across both strategies and live in study files. -/
inductive Strategy where
  | inSitu
  | exSitu
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 2: Stabilizer (@cite{newman-2000} §66)
-- ============================================================================

/-- The stabilizer surfaces with two allomorphs in agreement with the
    focused constituent: *cē* with feminine-singular focus, *nē*
    elsewhere (masculine singular and all plurals). The plural agrees
    with *nē* regardless of gender (@cite{newman-2000} §66.1). -/
inductive Stabilizer where
  | nee   -- nē
  | cee   -- cē
  deriving DecidableEq, Repr, Inhabited

/-- Surface form of the stabilizer. -/
def Stabilizer.form : Stabilizer → String
  | .nee => "nē"
  | .cee => "cē"

/-- Pick the stabilizer for a focused constituent of the given gender
    and number. The *cē* allomorph appears iff the focus is feminine
    AND singular. -/
def stabilizerFor (g : SurfaceGender) (singular : Bool) : Stabilizer :=
  match g, singular with
  | .feminine, true => .cee
  | _, _            => .nee

-- ============================================================================
-- § 3: Focus Configurations
-- ============================================================================

/-- A focused-clause configuration. The Strategy field determines
    whether the constituent fronts; in the ex-situ case, a stabilizer
    is optionally inserted and the clause's PAC must surface in
    Relative mode (when the TAM admits it). -/
structure FocusConfig where
  /-- The clause's PAC (subject + TAM + mode + form). -/
  pac      : PAC
  /-- The focus strategy. -/
  strategy : Strategy
  /-- The gender of the focused constituent (determines *nē* vs *cē*). -/
  focusG   : SurfaceGender
  /-- Whether the focused constituent is singular. -/
  focusSG  : Bool
  /-- Whether a stabilizer surfaces (optional in ex-situ; absent in-situ). -/
  hasStab  : Bool
  deriving Repr

/-- Stabilizer realised by this configuration, if any. -/
def FocusConfig.stab? (c : FocusConfig) : Option Stabilizer :=
  if c.hasStab then some (stabilizerFor c.focusG c.focusSG) else none

-- ============================================================================
-- § 4: Licensing Condition (@cite{newman-2000} §65, §66)
-- ============================================================================

/-- A FocusConfig is **licensed** iff:
    - in-situ focus places no constraint on TAM mode, or
    - ex-situ focus has the PAC in Relative mode whenever the PAC's
      TAM admits a Relative form (otherwise vacuously licensed).

    This recovers the textbook generalisation that ex-situ focus is
    incompatible with the General-form completive/continuous, but
    morphologically vacuous for TAMs that lack a Relative form. -/
def FocusConfig.Licensed (c : FocusConfig) : Prop :=
  match c.strategy with
  | .inSitu  => True
  | .exSitu  => c.pac.tam.HasRelativeForm → c.pac.mode = .relative

instance (c : FocusConfig) : Decidable c.Licensed := by
  unfold FocusConfig.Licensed
  cases c.strategy <;> infer_instance

-- ============================================================================
-- § 5: Smart Constructors
-- ============================================================================

/-- Smart constructor for an in-situ focus configuration. Always
    licensed; defaults to no stabilizer (in-situ focus carries no
    morphological reflex). -/
def mkInSitu (pac : PAC) (focusG : SurfaceGender) (focusSG : Bool) : FocusConfig :=
  ⟨pac, .inSitu, focusG, focusSG, false⟩

/-- Smart constructor for an ex-situ focus configuration. Takes a proof
    that if the TAM admits a Relative form, the PAC's mode is Relative;
    licensing then follows immediately (see `mkExSitu_licensed`). -/
def mkExSitu (pac : PAC) (focusG : SurfaceGender) (focusSG : Bool)
    (hasStab : Bool := true)
    (_ : pac.tam.HasRelativeForm → pac.mode = .relative) : FocusConfig :=
  ⟨pac, .exSitu, focusG, focusSG, hasStab⟩

/-- A FocusConfig built by `mkExSitu` is licensed: the proof obligation
    threaded through the smart constructor *is* the witness. -/
theorem mkExSitu_licensed (p : PAC) (g : SurfaceGender) (sg : Bool)
    (hs : Bool) (h : p.tam.HasRelativeForm → p.mode = .relative) :
    (mkExSitu p g sg hs h).Licensed := h

-- ============================================================================
-- § 6: Examples and Registry
-- ============================================================================

open Fragments.Hausa.Inflection

/-- Ex-situ focus of a feminine singular NP with the relative completive:
    fully licensed; surfaces with *cē*. -/
def exSitu_fem_relCmp : FocusConfig :=
  mkExSitu cmp_3sm_R .feminine true true (fun _ => rfl)

/-- In-situ focus places no morphological constraint: any PAC is OK. -/
def inSitu_any : FocusConfig := mkInSitu cmp_3sm_G .masculine true

/-- An *unlicensed* ex-situ configuration with the General completive,
    constructed directly to demonstrate that the predicate has bite. -/
def exSitu_with_genCmp : FocusConfig :=
  ⟨cmp_3sm_G, .exSitu, .masculine, true, false⟩

/-- The focus-configuration registry: licensed examples used downstream.
    `exSitu_with_genCmp` is *not* in the registry — it is the explicit
    counterexample showing the predicate is non-vacuous. -/
def focusConfigs : List FocusConfig := [exSitu_fem_relCmp, inSitu_any]

-- ============================================================================
-- § 7: Universal & Bridge Theorems
-- ============================================================================

/-- **Stabilizer agreement.** The *cē* allomorph appears exactly with
    feminine-singular focus; everything else takes *nē*. -/
theorem stabilizer_iff_FSG (g : SurfaceGender) (sg : Bool) :
    stabilizerFor g sg = .cee ↔ g = .feminine ∧ sg = true := by
  cases g <;> cases sg <;> simp [stabilizerFor]

/-- **Every registered focus configuration is licensed.** The smart
    constructors guarantee this; the universal theorem records the
    invariant for the registry as a whole. -/
theorem all_focusConfigs_licensed :
    ∀ c ∈ focusConfigs, c.Licensed := by
  intro c hc
  simp only [focusConfigs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

/-- **Ex-situ + General completive is not licensed.** The morphological
    bite of the predicate. -/
theorem exSitu_with_genCmp_not_licensed : ¬ exSitu_with_genCmp.Licensed := by
  intro h
  have : (cmp_3sm_G).mode = .relative := h trivial
  exact (by decide : (cmp_3sm_G).mode ≠ .relative) this

/-- The licensed feminine-singular ex-situ example surfaces with *cē*. -/
theorem exSitu_fem_picks_cee :
    exSitu_fem_relCmp.stab? = some .cee := rfl

-- ============================================================================
-- § 8: Stabilizer Tone — Cross-Fragment Bridge to `Tone.polarOf`
-- ============================================================================

/-- Surface tone of the stabilizer after a host whose final TBU has the
    given tone. The stabilizer *nē/cē* is **polar-toned**: it surfaces
    with the *opposite* tone of the immediately preceding syllable
    (@cite{newman-2000} §66.1). -/
def Stabilizer.toneAfter (_ : Stabilizer) (host : TRN) : TRN :=
  polarOf host

/-- **Stabilizer tone is polarity (cross-fragment).** The stabilizer's
    surface tone is *exactly* `Tone.polarOf` applied to the host's
    final tone — no separate stipulation. This grounds the polar-tone
    description of *nē/cē* in the same operator that handles the
    genitive linker *-n*, making the two cases instances of one
    autosegmental operation rather than parallel idiosyncrasies. -/
theorem stabilizer_tone_is_polar (s : Stabilizer) (host : TRN) :
    s.toneAfter host = polarOf host := rfl

/-- **Stabilizer-tone involutivity.** Iterating the stabilizer-tone
    map twice returns to the host tone (on the H/L sublattice).
    Direct corollary of `Tone.polarOf_involutive_on_HL`. -/
theorem stabilizer_toneAfter_involutive (s : Stabilizer)
    (h : TRN) (hh : h ∈ ([.H, .L] : List TRN)) :
    polarOf (s.toneAfter h) = h :=
  Fragments.Hausa.Tone.polarOf_involutive_on_HL h hh

end Fragments.Hausa.Focus
