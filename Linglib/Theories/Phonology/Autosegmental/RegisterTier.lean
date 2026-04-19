import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Count
import Mathlib.Algebra.Order.Group.Defs

/-!
# Register Tier Theory
@cite{snider-1999} @cite{snider-2020}

Register features as independent phonological primitives, following
@cite{snider-1999}'s Register Tier Theory. Register features are
**syntagmatic**: they effect a pitch shift relative to the preceding
context, unlike **paradigmatic** tone features which specify absolute
pitch targets within a register.

## Geometry of tone (@cite{snider-2020})

```
    h / l     Register tier
    H / L     Tonal tier
      ○       Tonal root node (TRN)
      |
     TBU      Tone-bearing unit
```

The TRN bundles register and tone features. In register-only systems
like Drubea and Numèè (@cite{lionnet-2025}), the tonal tier is absent
and the system is fully described by register features alone.

## Key distinction

- **Tone-based systems**: tonal contrasts defined paradigmatically
  (H is higher than L in the same context)
- **Register-based systems**: tonal contrasts defined syntagmatically
  (a downstepped unit is lower than the preceding unit)

This distinction enriches @cite{hyman-2006}'s word-prosodic typology.
-/

namespace Phonology.Autosegmental.RegisterTier

section Features

/-- Register features (@cite{snider-1999}, @cite{snider-2020}).

    Syntagmatically defined: each feature effects a register shift
    relative to the preceding register setting.

    - `h`: raise register (upstep) — higher than preceding
    - `l`: lower register (downstep) — lower than preceding -/
inductive RegisterFeature where
  /-- Upstep — raise register (Snider's `h`). -/
  | h
  /-- Downstep — lower register (Snider's `l`). -/
  | l
  deriving DecidableEq, Repr, Inhabited

/-- Tone features (@cite{yip-1980}, @cite{clements-1981}).

    Paradigmatically defined: specify a pitch target within the current
    register setting.

    Note: some autosegmental analyses treat M as derived (e.g., H+L or
    registerless). We include it as a primitive to accommodate three-level
    tone systems like Mwaghavul (Chadic) and Yoruba (Benue-Congo) where
    H/M/L contrast lexically. -/
inductive ToneFeature where
  /-- High pitch target (upper half of register). -/
  | H
  /-- Mid pitch target (center of register). -/
  | M
  /-- Low pitch target (lower half of register). -/
  | L
  deriving DecidableEq, Repr, Inhabited

end Features

section Geometry

/-- Tonal root node (TRN): bundles register and tone features into
    a single prosodic specification (@cite{snider-2020}).

    In register-based analyses, surface tones decompose as register + tone:
    - High = `Hh` (high tone, raised register)
    - Low  = `Ll` (low tone, lowered register)
    - Downstepped High = `Hl`

    Mid tones can be treated as derived (various register+tone combinations)
    or as a primitive `ToneFeature.M`, depending on the system. Three-level
    tone languages like Mwaghavul and Yoruba use `ToneFeature.M` directly.

    Register-only systems (Drubea/Numèè) use `tone = none`. -/
structure TonalRootNode where
  register : Option RegisterFeature
  tone     : Option ToneFeature
  deriving DecidableEq, Repr

/-- The prosodic domain that carries register/tone specifications.

    In most tone languages this is the syllable; in Drubea and Numèè
    it is the mora (@cite{lionnet-2025}). -/
inductive TBUKind where
  | mora
  | syllable
  deriving DecidableEq, Repr

end Geometry

section Realization

/-- Register specification on a single register-bearing unit (RBU).
    `none` = registerless (prosodically unspecified). -/
abbrev RegisterSpec := Option RegisterFeature

/-- Numeric pitch effect of a register specification: each `l`
    contributes `-1`, each `h` contributes `+1`, and `none` is inert.
    Used to define both `realizePitch` and the natural `≤` ordering on
    register specs. -/
def RegisterSpec.pitchEffect : RegisterSpec → Int
  | some .l => -1
  | none    => 0
  | some .h => 1

/-- Realize a sequence of register specifications as a sequence of
    pitch levels relative to some starting offset.

    Models **terracing**: each `l` lowers by one step, each `h` raises
    by one step, and registerless units maintain the current level.
    Pitch levels are integers; the offset is an arbitrary anchor — the
    theory-meaningful content is the *differences* between adjacent
    levels, captured directly by `pitchDeltas`. -/
def realizePitch : Int → List RegisterSpec → List Int
  | _,     []                  => []
  | level, none      :: rest   => level :: realizePitch level rest
  | level, some .l   :: rest   => (level - 1) :: realizePitch (level - 1) rest
  | level, some .h   :: rest   => (level + 1) :: realizePitch (level + 1) rest

/-- A uniform `cons` rewrite for `realizePitch` in terms of `pitchEffect`. -/
@[simp] theorem realizePitch_cons (level : Int) (s : RegisterSpec)
    (rest : List RegisterSpec) :
    realizePitch level (s :: rest) =
      (level + s.pitchEffect) :: realizePitch (level + s.pitchEffect) rest := by
  cases s with
  | none => simp [realizePitch, RegisterSpec.pitchEffect]
  | some r => cases r with
    | l => simp [realizePitch, RegisterSpec.pitchEffect, Int.sub_eq_add_neg]
    | h => simp [realizePitch, RegisterSpec.pitchEffect]

/-- **Pitch deltas — the theory-primary view.** Cumulative register
    shifts produced by a spec sequence, expressed as integer offsets
    *from the start of the sequence*. Each output value at position `i`
    is the running sum of `pitchEffect`s up to that position: how many
    register steps the sequence has dropped (negative) or risen
    (positive) since position 0.

    Register Tier Theory (@cite{snider-1999}) is **syntagmatic**: a
    register feature effects a shift relative to its predecessor, and
    only the differences between adjacent positions are linguistically
    meaningful. There is no privileged "zero" pitch — `pitchDeltas`
    makes that honest by reporting only relative quantities.

    `realizePitch offset specs` is the same information shifted by an
    arbitrary anchor; see `realizePitch_eq_pitchDeltas_shift`. The
    offset only matters when *comparing* two anchors, e.g. when an ip
    boundary resets a compressed register back to the original starting
    height (@cite{beckman-pierrehumbert-1986}). -/
def pitchDeltas (specs : List RegisterSpec) : List Int :=
  realizePitch 0 specs

/-- The offset acts additively: shifting the starting offset by `d`
    shifts every output by `d`. The deeper content is that `realizePitch`
    only depends on the offset up to addition. -/
private theorem realizePitch_shift (n d : Int) (specs : List RegisterSpec) :
    realizePitch (n + d) specs = (realizePitch n specs).map (· + d) := by
  induction specs generalizing n with
  | nil => rfl
  | cons s rest ih =>
    simp only [realizePitch_cons, List.map_cons]
    have h : n + d + s.pitchEffect = (n + s.pitchEffect) + d := by omega
    rw [h, ih]

/-- `realizePitch n specs` is `pitchDeltas specs` with each value
    shifted by the offset `n`. The offset is an additive anchor; no
    information lives in its absolute value. -/
theorem realizePitch_eq_pitchDeltas_shift (n : Int) (specs : List RegisterSpec) :
    realizePitch n specs = (pitchDeltas specs).map (· + n) := by
  have := realizePitch_shift 0 n specs
  rwa [Int.zero_add] at this

/-- Utterance-initial neutralization: an `l` feature on the first RBU
    is not phonetically realized (no preceding register to contrast with),
    but remains phonologically active (@cite{lionnet-2025}). -/
def uttInitialNeutralize : List RegisterSpec → List RegisterSpec
  | (some .l) :: rest => none :: rest
  | other             => other

end Realization

section Constraints

/-- **Culminativity**: a stem contains at most one `l` feature.

    Holds for all native Drubea and Numèè stems (@cite{lionnet-2025}). -/
def IsCulminative (specs : List RegisterSpec) : Prop :=
  specs.count (some .l) ≤ 1

instance : DecidablePred IsCulminative := fun _ => Nat.decLe _ _

end Constraints

section Postlexical

/-- **Pre-downstep h-epenthesis** (@cite{lionnet-2025}): insert
    an `h` feature on the registerless RBU immediately before a downstep.

    This raises the pitch of the preceding syllable, reinforcing the
    downward contrast. The operation is postlexical and optional. This
    models the default case where only the immediately preceding RBU is
    raised; for the spreading variant in which raising propagates back
    through a sequence of registerless RBUs, see `hEpenthesisSpread`. -/
def hEpenthesis : List RegisterSpec → List RegisterSpec
  | [] => []
  | [x] => [x]
  | none :: (some .l) :: rest => (some .h) :: (some .l) :: hEpenthesis rest
  | x :: rest => x :: hEpenthesis rest

/-- **Spreading h-epenthesis**: raise *all* registerless RBUs in the
    sequence preceding a downstep, not just the immediately preceding
    one.

    This models the **abrupt-spreading** variant of pre-downstep raising
    (@cite{lionnet-2025}), in which a run of registerless RBUs preceding
    a downstep is raised flat to the same higher pitch. The alternative
    **gradual** variant, where pitch rises through interpolation across
    the run, is not modelled here. -/
def hEpenthesisSpread : List RegisterSpec → List RegisterSpec
  | [] => []
  | (some .l) :: rest => (some .l) :: hEpenthesisSpread rest
  | (some .h) :: rest => (some .h) :: hEpenthesisSpread rest
  | none :: rest =>
      let rest' := hEpenthesisSpread rest
      match rest' with
      | (some .l) :: _ | (some .h) :: _ => (some .h) :: rest'
      | _                               => none      :: rest'

end Postlexical

section Typology

/-- Word-prosodic system types (@cite{hyman-2006}, enriched by
    @cite{lionnet-2025}).

    @cite{hyman-2006} defines two prototypical systems: tone and stress
    accent. @cite{lionnet-2025} shows that tone systems split into
    tone-based (paradigmatic) and register-based (syntagmatic). -/
inductive WordProsodicType where
  /-- Paradigmatic H/L contrast (e.g., Yoruba, Mandarin). -/
  | toneBased
  /-- Syntagmatic downstep contrast (e.g., Drubea, Numèè). -/
  | registerBased
  /-- Prominence-based (e.g., English, Russian). -/
  | stressAccent
  /-- Both tone and register (e.g., Paicî, Baga Pukur). -/
  | mixed
  deriving DecidableEq, Repr

/-- Core definitional properties of downstep, following @cite{leben-2018}
    as refined by @cite{lionnet-2025}.

    Properties (a)–(c) are definitional; (d)–(f) are cross-linguistic
    tendencies that need not hold in every system. Fields are `Bool`
    because each is a stipulative annotation about a specific system,
    not a derivable property. -/
structure DownstepProperties where
  /-- (a) Affects the entire prosodic domain, not just a single tone. -/
  affectsDomain : Bool
  /-- (b) Changes the register for what follows. -/
  changesRegister : Bool
  /-- (c) Cumulative: multiple downsteps stack (unlimited in principle). -/
  isCumulative : Bool
  /-- (d) Utterance-initially, no phonetic contrast with undownstepped. -/
  uttInitialNeutral : Bool
  /-- (e) Characteristically affects H tones. -/
  characteristicallyAffectsH : Bool
  /-- (f) Functions contrastively (phonological, syntactic,
      morphophonological, or lexical). -/
  functionsContrastively : Bool
  deriving Repr

/-- Inventory of primitives in a phonological analysis.

    Used to compare competing analyses of the same data — the analysis
    with fewer primitives and processes is preferred, all else being
    equal (@cite{lionnet-2025}). -/
structure AnalysisInventory where
  /-- Distinct representational units (underlying + derived). -/
  underlyingPrimitives : Nat
  /-- Postlexical rules / constraints. -/
  postlexicalProcesses : Nat
  deriving Repr, DecidableEq

end Typology

section Verification

/-- Registerless sequences have uniform pitch. -/
theorem registerless_uniform (n : Int) :
    realizePitch n [none, none, none] = [n, n, n] := rfl

/-- A single downstep lowers pitch by one step. -/
theorem downstep_lowers (n : Int) :
    realizePitch n [none, some .l] = [n, n - 1] := rfl

/-- Multiple downsteps produce cumulative terracing. -/
theorem terracing (n : Int) :
    realizePitch n [some .l, some .l, some .l] =
      [n - 1, n - 1 - 1, n - 1 - 1 - 1] := rfl

/-- The deltas-only view of three downsteps: pitch falls by 1, 2, 3
    register steps from the start. This is the theory-primary content;
    no anchor required. -/
theorem terracing_deltas :
    pitchDeltas [some .l, some .l, some .l] = [-1, -2, -3] := by decide

/-- Concrete terracing from offset 4 (mid-high on the 1–5 scale).
    This is just `terracing_deltas` shifted by `+4`. -/
theorem terracing_from_4 :
    realizePitch 4 [some .l, some .l, some .l] = [3, 2, 1] := by decide

/-- h-epenthesis raises the RBU before a downstep. -/
theorem h_epenthesis_before_downstep :
    hEpenthesis [none, some .l, none] =
      [some .h, some .l, none] := rfl

/-- h-epenthesis + realization: the raised RBU is higher than baseline. -/
theorem h_epenthesis_raises_pitch :
    realizePitch 4 (hEpenthesis [none, some .l, none]) = [5, 4, 4] := by decide

/-- Utterance-initial neutralization removes an initial downstep. -/
theorem utt_initial_neutralizes :
    uttInitialNeutralize [some .l, none, none] = [none, none, none] := rfl

/-- After neutralization, the utterance starts at baseline. -/
theorem utt_initial_pitch :
    realizePitch 4 (uttInitialNeutralize [some .l, none]) = [4, 4] := by decide

/-- Culminativity: a single `l` is culminative. -/
theorem single_l_culminative : IsCulminative [none, some .l, none] := by decide

/-- Non-culminative: two `l` features violate culminativity. -/
theorem double_l_not_culminative : ¬ IsCulminative [some .l, some .l] := by decide

end Verification

section Monotonicity

/-- Spec-level ordering: `s₁ ≤ s₂` iff `s₁` has a smaller pitch effect
    than `s₂`, i.e. `l ≤ none ≤ h`. Equivalent to "`s₁` is at least as
    lowering as `s₂`". -/
def RegisterSpec.le (s₁ s₂ : RegisterSpec) : Prop :=
  s₁.pitchEffect ≤ s₂.pitchEffect

instance : DecidableRel RegisterSpec.le := fun _ _ => Int.decLe _ _

/-- **Monotonicity of `realizePitch` in the baseline**: a higher starting
    pitch produces pointwise higher output for any fixed register-spec
    sequence.

    This is the structural basis for catathesis blocking
    (@cite{beckman-pierrehumbert-1986}): when an ip boundary resets the
    register to the original baseline, subsequent pitches are higher
    than if catathesis had continued from a compressed baseline. -/
theorem realizePitch_baseline_mono (specs : List RegisterSpec)
    {n m : Int} (h : n ≤ m) :
    List.Forall₂ (· ≤ ·) (realizePitch n specs) (realizePitch m specs) := by
  induction specs generalizing n m with
  | nil => exact .nil
  | cons s rest ih =>
    have hstep : n + s.pitchEffect ≤ m + s.pitchEffect := Int.add_le_add_right h _
    simp only [realizePitch_cons]
    exact .cons hstep (ih hstep)

/-- **Full monotonicity of `realizePitch`**: if each spec in `specs1` is
    at least as lowering as the corresponding spec in `specs2`, and the
    baseline `n ≤ m`, then the realized pitches are pointwise `≤`.

    Captures the linguistic generalization that adding lowering features
    can only compress pitch range further, never raise it. Subsumes
    `realizePitch_baseline_mono` as a special case. -/
theorem realizePitch_mono
    {specs1 specs2 : List RegisterSpec}
    (hspecs : List.Forall₂ RegisterSpec.le specs1 specs2)
    {n m : Int} (hnm : n ≤ m) :
    List.Forall₂ (· ≤ ·) (realizePitch n specs1) (realizePitch m specs2) := by
  induction hspecs generalizing n m with
  | nil => exact .nil
  | @cons s₁ s₂ rest1 rest2 hhead _ ih =>
    have hstep : n + s₁.pitchEffect ≤ m + s₂.pitchEffect :=
      Int.add_le_add hnm hhead
    simp only [realizePitch_cons]
    exact .cons hstep (ih hstep)

end Monotonicity

end Phonology.Autosegmental.RegisterTier
