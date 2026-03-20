/-!
# Register Tier Theory
@cite{snider-1999} @cite{snider-2020}

Register features as independent phonological primitives, following
Snider's (1999, 2020) Register Tier Theory. Register features are
**syntagmatic**: they effect a pitch shift relative to the preceding
context, unlike **paradigmatic** tone features which specify absolute
pitch targets within a register.

## Geometry of tone (Snider 2020)

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

namespace Theories.Phonology.Autosegmental.RegisterTier

-- ============================================================================
-- § 1: Register and Tone Features
-- ============================================================================

/-- Register features (@cite{snider-1999}, @cite{snider-2020}).

    Syntagmatically defined: each feature effects a register shift
    relative to the preceding register setting.

    - `h`: raise register (upstep) — higher than preceding
    - `l`: lower register (downstep) — lower than preceding -/
inductive RegisterFeature where
  | h  -- upstep: raise register
  | l  -- downstep: lower register
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Tone features (@cite{yip-1980}, @cite{clements-1981}).

    Paradigmatically defined: specify a pitch target within the current
    register setting.

    - `H`: high pitch target (upper half of register)
    - `L`: low pitch target (lower half of register) -/
inductive ToneFeature where
  | H  -- High tone
  | L  -- Low tone
  deriving DecidableEq, BEq, Repr, Inhabited

-- ============================================================================
-- § 2: Tonal Geometry
-- ============================================================================

/-- Tonal root node (TRN): bundles register and tone features into
    a single prosodic specification (@cite{snider-2020}: 23).

    Standard tones decompose as register + tone:
    - High  = `Hh` (high tone, raised register)
    - Low   = `Ll` (low tone, lowered register)
    - Mid   = `Lh` or `Hl`
    - Downstepped High = `Hl`

    Register-only systems (Drubea/Numèè) use `tone = none`. -/
structure TonalRootNode where
  register : Option RegisterFeature
  tone     : Option ToneFeature
  deriving DecidableEq, BEq, Repr

/-- The prosodic domain that carries register/tone specifications.

    In most tone languages this is the syllable; in Drubea and Numèè
    it is the mora (@cite{lionnet-2025} §4.2). -/
inductive TBUKind where
  | mora
  | syllable
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 3: Register Specification and Realization
-- ============================================================================

/-- Register specification on a single register-bearing unit (RBU).
    `none` = registerless (prosodically unspecified). -/
abbrev RegisterSpec := Option RegisterFeature

/-- Realize a sequence of register specifications as pitch levels.

    Models **terracing**: starting from a baseline pitch level, each `l`
    lowers by one step and each `h` raises by one step. Registerless
    units maintain the current level.

    This captures the staircase-descent seen in utterances with multiple
    downsteps (@cite{lionnet-2025}: ex. 11, 12, Figure 7). -/
def realizePitch : Nat → List RegisterSpec → List Nat
  | _, [] => []
  | level, none :: rest => level :: realizePitch level rest
  | level, some .l :: rest => (level - 1) :: realizePitch (level - 1) rest
  | level, some .h :: rest => (level + 1) :: realizePitch (level + 1) rest

/-- Utterance-initial neutralization: an `l` feature on the first RBU
    is not phonetically realized (no preceding register to contrast with),
    but remains phonologically active (@cite{lionnet-2025} §3.5, §4.5). -/
def uttInitialNeutralize : List RegisterSpec → List RegisterSpec
  | (some .l) :: rest => none :: rest
  | other => other

-- ============================================================================
-- § 4: Constraints
-- ============================================================================

/-- **Culminativity**: a stem contains at most one `l` feature.

    This constraint holds for all native Drubea and Numèè stems
    (@cite{lionnet-2025} §3.10, Table 2). -/
def isCulminative (specs : List RegisterSpec) : Bool :=
  match specs.filter (· == some .l) |>.length with
  | 0 | 1 => true
  | _ => false

-- ============================================================================
-- § 5: Postlexical Operations
-- ============================================================================

/-- **Pre-downstep h-epenthesis** (@cite{lionnet-2025} §4.4): insert
    an `h` feature on the registerless RBU immediately before a downstep.

    This raises the pitch of the preceding syllable, reinforcing the
    downward contrast. The operation is postlexical and optional.

    This models the **abrupt** raising pattern (the most common case).
    For the **gradual** pattern where raising extends over multiple
    registerless RBUs, see `hEpenthesisSpread`. -/
def hEpenthesis : List RegisterSpec → List RegisterSpec
  | [] => []
  | [x] => [x]
  | none :: (some .l) :: rest => (some .h) :: (some .l) :: hEpenthesis rest
  | x :: rest => x :: hEpenthesis rest

/-- **Spreading h-epenthesis**: raise ALL registerless RBUs in the
    sequence preceding a downstep, not just the immediately preceding one.

    This models the spreading pattern described in @cite{lionnet-2025}
    §3.2 (ex. 16), where pitch raising "extends through a sequence of
    registerless syllables" before a downstep. -/
def hEpenthesisSpread (specs : List RegisterSpec) : List RegisterSpec :=
  let rec mark : List RegisterSpec → List RegisterSpec
    | [] => []
    | (some .l) :: rest => (some .l) :: mark rest
    | none :: rest =>
        let rest' := mark rest
        -- If a downstep follows (possibly after other raised RBUs), raise
        match rest'.head? with
        | some (some .l) | some (some .h) => (some .h) :: rest'
        | _ => none :: rest'
    | x :: rest => x :: mark rest
  mark specs

-- ============================================================================
-- § 6: Word-Prosodic Typology
-- ============================================================================

/-- Word-prosodic system types (@cite{hyman-2006}, enriched by
    @cite{lionnet-2025} §6.2).

    Hyman (2006) defines two prototypical systems: tone and stress accent.
    Lionnet (2025) shows that tone systems split into tone-based
    (paradigmatic) and register-based (syntagmatic). -/
inductive WordProsodicType where
  | toneBased      -- Paradigmatic H/L contrast (e.g., Yoruba, Mandarin)
  | registerBased  -- Syntagmatic downstep contrast (e.g., Drubea, Numèè)
  | stressAccent   -- Prominence-based (e.g., English, Russian)
  | mixed          -- Both tone and register (e.g., Paicî, Baga Pukur)
  deriving DecidableEq, BEq, Repr

/-- Core definitional properties of downstep, following @cite{leben-2018}
    as refined by @cite{lionnet-2025} §6.1.

    Properties (a–c) are definitional; (d–f) are cross-linguistic
    tendencies that need not hold in every system. -/
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
  /-- (f) Functions contrastively (phonological, syntactic, morphophonological,
      or lexical). -/
  functionsContrastively : Bool
  deriving Repr

/-- Inventory of primitives in a phonological analysis.

    Used to compare competing analyses of the same data — the
    analysis with fewer primitives and processes is preferred,
    all else being equal (@cite{lionnet-2025} §5). -/
structure AnalysisInventory where
  underlyingPrimitives : Nat  -- distinct representational units (underlying + derived)
  postlexicalProcesses : Nat  -- postlexical rules/constraints needed
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- § 7: Verification Theorems
-- ============================================================================

/-- Registerless sequences have uniform pitch. -/
theorem registerless_uniform (n : Nat) :
    realizePitch n [none, none, none] = [n, n, n] := by
  simp [realizePitch]

/-- A single downstep lowers pitch by one step. -/
theorem downstep_lowers (n : Nat) :
    realizePitch n [none, some .l] = [n, n - 1] := by
  simp [realizePitch]

/-- Multiple downsteps produce cumulative terracing. -/
theorem terracing (n : Nat) :
    realizePitch n [some .l, some .l, some .l] =
      [n - 1, n - 1 - 1, n - 1 - 1 - 1] := by
  simp [realizePitch]

/-- Concrete terracing from baseline 4 (mid-high on 1–5 scale). -/
theorem terracing_from_4 :
    realizePitch 4 [some .l, some .l, some .l] = [3, 2, 1] := by
  native_decide

/-- h-epenthesis raises the RBU before a downstep. -/
theorem h_epenthesis_before_downstep :
    hEpenthesis [none, some .l, none] =
      [some .h, some .l, none] := by
  rfl

/-- h-epenthesis + realization: the raised RBU is higher than baseline. -/
theorem h_epenthesis_raises_pitch :
    realizePitch 4 (hEpenthesis [none, some .l, none]) = [5, 4, 4] := by
  native_decide

/-- Utterance-initial neutralization removes an initial downstep. -/
theorem utt_initial_neutralizes :
    uttInitialNeutralize [some .l, none, none] = [none, none, none] := by
  rfl

/-- After neutralization, the utterance starts at baseline. -/
theorem utt_initial_pitch :
    realizePitch 4 (uttInitialNeutralize [some .l, none]) = [4, 4] := by
  native_decide

/-- Culminativity: a single `l` is culminative. -/
theorem single_l_culminative :
    isCulminative [none, some .l, none] = true := by native_decide

/-- Non-culminative: two `l` features violate culminativity. -/
theorem double_l_not_culminative :
    isCulminative [some .l, some .l] = false := by native_decide

end Theories.Phonology.Autosegmental.RegisterTier
