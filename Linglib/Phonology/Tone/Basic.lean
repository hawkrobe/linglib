/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Count
import Mathlib.Algebra.Order.Group.Defs
import Linglib.Features.Basic

/-!
# Tonal Root Nodes and Subtonal Features

Tone is paradigmatic. A **Tonal Root Node** (TRN) is a bundle of
**subtonal features** `[±upper]` and `[±raised]` ([yip-1980]
[pulleyblank-1986]), each of which links to a TBU (mora, syllable).
This file follows [lionnet-2022]'s reformulation of register-tier
geometry: the four tier organisation (subtonal features → TRN → TBU)
is shared with [snider-1999], but the features themselves are
*paradigmatic* targets, not *syntagmatic* shifts.

## Main definitions

* `Subtonal` — the two paradigmatic subtonal feature dimensions
  `[±upper]` and `[±raised]`.
* `TRN` — Tonal Root Node, a bundle of `Option Bool` values for the two
  subtonal features. Linked to its `Subtonal → Option Bool` view by
  `TRN.toBundle` / `TRN.ofBundle`.
* `TRN.empty`, `TRN.downstep`, `TRN.upstep` — register-only TRNs for
  Drubea/Numèè-style systems.
* `TRN.H`, `TRN.M`, `TRN.L`, `TRN.superHigh` — the four `[±u, ±r]`
  combinations underlying the Laal-style 3-tone system.
* `realizePitch`, `pitchDeltas`, `realizePitchUtterance` — terracing
  realisation (cumulative register shifts).
* `TRN.absolutePitch` — paradigmatic Laal-style realisation.
* `ThreeToneGap` — the four typological classes of 3-tone systems.
* `TBUKind`, `WordProsodicType`, `DownstepProperties`,
  `AnalysisInventory` — prosodic typology primitives.
* `IsCulminative` — at most one `[-raised]` TRN per stem.
* `hEpenthesis`, `hEpenthesisSpread` — postlexical operations.
* `subtonalAssimilate`, `mergeTRN`, `dockFloating` —
  subtonal feature operations via the bundle view.

## Implementation notes

### Why paradigmatic, not syntagmatic

[snider-1999]'s `h`/`l` features are defined both paradigmatically
(specifying register half) **and** syntagmatically ("higher / lower than
the preceding register"). [lionnet-2022] argues this dual
definition is overloaded: the same feature does double duty as a
representational primitive and as a phonological process trigger.
Switching to purely paradigmatic `[±upper]`/`[±raised]` separates the
two roles — the features are the representation, the operations
(spreading, OCP merger, deletion) are the processes.

### Geometry

```
    [±upper]    Register-half subtonal feature tier
    [±raised]   Within-register subtonal feature tier
       ○        Tonal Root Node (TRN) — bundles both features
       |
      TBU       Tone-bearing unit (mora / syllable)
```

A TRN is the structural node that gathers a `[±upper]` value and a
`[±raised]` value and links them to a TBU. Either or both features may
be **underspecified** (`none`), with surface values filled in by default.
-/

namespace Tone

/-! ### Subtonal features -/

/-- The two paradigmatic subtonal feature dimensions
    ([lionnet-2022] ex. 51, after [yip-1980],
    [pulleyblank-1986]).

    - `upper`: which register half (upper / lower)
    - `raised`: which target within the register (higher / lower)

    Each takes a value in `Bool`: `true ≡ +`, `false ≡ -`. A subtonal
    feature is `none` (underspecified), `some true` (`+`), or
    `some false` (`-`). -/
inductive Subtonal where
  | upper
  | raised
  deriving DecidableEq, Repr, Inhabited

/-! ### Tonal root node -/

/-- A **Tonal Root Node**: a structural node that bundles a `[±upper]`
    and a `[±raised]` subtonal-feature value and links them to a TBU.

    Either or both fields may be `none` (underspecified). For the
    register-only Drubea/Numèè system the `upper` field is uniformly
    `none`; for full 3-tone Laal both fields are usually specified.

    Implemented as a structure rather than `Subtonal → Option Bool`
    so that `DecidableEq` and `Repr` derive automatically (and `BEq`
    follows from `DecidableEq`, below) and so that `decide`-based proofs
    over concrete TRN literals reduce cleanly. The bundle view is
    recovered by `TRN.toBundle`. -/
structure TRN where
  upper  : Option Bool
  raised : Option Bool
  deriving DecidableEq, Repr, Inhabited

namespace TRN

/-- Boolean equality on TRN as decidable equality, so that `LawfulBEq`
    holds. Required for `simp`-based reasoning over `(t == t)`. -/
instance : BEq TRN := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq TRN where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- The empty / fully underspecified TRN. In the Drubea/Numèè register-
    only system, this is the **registerless** mora. -/
@[match_pattern] def empty : TRN := ⟨none, none⟩

/-- A floating `[-raised]` subtonal feature, no `[upper]` value.
    In the register-only system this is the **downstep** TRN: it lowers
    the running register baseline. -/
@[match_pattern] def downstep : TRN := ⟨none, some false⟩

/-- A floating `[+raised]` subtonal feature, no `[upper]` value.
    In the register-only system this is the **upstep** TRN — used by
    pre-downstep h-epenthesis ([lionnet-2025]). -/
@[match_pattern] def upstep : TRN := ⟨none, some true⟩

/-- The **High** tone of Laal-style 3-tone systems: `[+upper, -raised]`
    ([lionnet-2022] ex. 51). Highest pitch. -/
def H : TRN := ⟨some true, some false⟩

/-- The **Mid** tone of Laal-style 3-tone systems: `[-upper, +raised]`
    ([lionnet-2022] ex. 51). M is one of the four `[±u, ±r]`
    combinations, derived from the binary subtonal features — not a
    primitive enum constructor. -/
def M : TRN := ⟨some false, some true⟩

/-- The **Low** tone of Laal-style 3-tone systems: `[-upper, -raised]`
    ([lionnet-2022] ex. 51). Lowest pitch. -/
def L : TRN := ⟨some false, some false⟩

/-- The fourth combination `[+upper, +raised]` — *unattested* in Laal,
    where it is the gap of the subtonal system ([lionnet-2022] ex. 51:
    "Missing from this system is the subtonal specification
    `[+upper, +raised]`"). Provided for completeness; an attested 4-tone
    language or a different 3-tone gap would use this. -/
def superHigh : TRN := ⟨some true, some true⟩

/-- View a TRN as a `Subtonal → Option Bool` (the parametric
    foundation in `Features.Bundle`). The bundle algebra
    (merge, assimilate, delete, set, refines) is then directly available
    via this view. -/
def toBundle (t : TRN) : Subtonal → Option Bool
  | .upper  => t.upper
  | .raised => t.raised

/-- Recover a TRN from a generic subtonal-feature bundle. Inverse of
    `toBundle`. -/
def ofBundle (b : Subtonal → Option Bool) : TRN :=
  ⟨b .upper, b .raised⟩

@[simp] theorem toBundle_upper  (t : TRN) : t.toBundle .upper  = t.upper  := rfl
@[simp] theorem toBundle_raised (t : TRN) : t.toBundle .raised = t.raised := rfl

@[simp] theorem ofBundle_toBundle (t : TRN) : ofBundle t.toBundle = t := by
  cases t; rfl

end TRN

/-! ### Pitch realisation -/

/-- Syntagmatic register shift contributed by a TRN, used by the
    terracing realisation `realizePitch`. Reads only the `[raised]`
    subtonal feature: `[-raised]` lowers, `[+raised]` raises,
    underspecified is inert.

    This is *not* the paradigmatic interpretation of `[raised]`
    ([lionnet-2022] §5.1). It is the realisation pattern attested in
    register-only systems like Drubea and Numèè ([lionnet-2025]),
    where each `[-raised]` triggers a downstep operation that resets
    the register baseline. -/
def TRN.pitchEffect (t : TRN) : Int :=
  match t.raised with
  | none       => 0
  | some false => -1
  | some true  => 1

/-- **Terracing realisation**: realise a TRN sequence as a sequence of
    pitch levels, where each `[-raised]` cumulatively lowers the
    baseline ([snider-1999] [lionnet-2025]).

    Used for register-only systems (Drubea, Numèè) and for catathesis
    in Japanese / English intonation ([beckman-pierrehumbert-1986]).
    For the paradigmatic Laal-style realisation see `TRN.absolutePitch`.

    Defined by direct case-split on the `[raised]` value so that
    `realizePitch n [TRN.empty, …]` reduces to `n :: …` definitionally
    (the alternative `level + t.pitchEffect` form does not reduce for
    opaque `n : Int`, since `n + 0 = n` is not definitional). -/
def realizePitch : Int → List TRN → List Int
  | _,     []                              => []
  | level, ⟨_, none⟩       :: rest         => level       :: realizePitch level       rest
  | level, ⟨_, some false⟩ :: rest         => (level - 1) :: realizePitch (level - 1) rest
  | level, ⟨_, some true⟩  :: rest         => (level + 1) :: realizePitch (level + 1) rest

/-- A uniform `cons` rewrite for `realizePitch` in terms of `pitchEffect`. -/
@[simp] theorem realizePitch_cons (level : Int) (t : TRN)
    (rest : List TRN) :
    realizePitch level (t :: rest) =
      (level + t.pitchEffect) :: realizePitch (level + t.pitchEffect) rest := by
  obtain ⟨u, r⟩ := t
  cases r with
  | none => simp [realizePitch, TRN.pitchEffect]
  | some b =>
    cases b with
    | false => simp [realizePitch, TRN.pitchEffect, Int.sub_eq_add_neg]
    | true  => simp [realizePitch, TRN.pitchEffect]

/-- **Pitch deltas** — the theory-primary view ([snider-1999]
    [lionnet-2025]). Cumulative register shifts produced by a TRN
    sequence, expressed as integer offsets from the start. There is no
    privileged "zero" pitch; only the differences are meaningful. -/
def pitchDeltas (ts : List TRN) : List Int := realizePitch 0 ts

private theorem realizePitch_shift (n d : Int) (ts : List TRN) :
    realizePitch (n + d) ts = (realizePitch n ts).map (· + d) := by
  induction ts generalizing n with
  | nil => rfl
  | cons t rest ih =>
    simp only [realizePitch_cons, List.map_cons]
    have h : n + d + t.pitchEffect = (n + t.pitchEffect) + d := by omega
    rw [h, ih]

/-- `realizePitch n ts` is `pitchDeltas ts` shifted by the offset `n`. -/
theorem realizePitch_eq_pitchDeltas_shift (n : Int) (ts : List TRN) :
    realizePitch n ts = (pitchDeltas ts).map (· + n) := by
  have := realizePitch_shift 0 n ts
  rwa [Int.zero_add] at this

/-- **Utterance-initial phonetic neutralisation**: an utterance-initial
    `[-raised]` TRN is realised at the starting pitch (no preceding
    register to contrast with — [lionnet-2025] §3.5, §4.5). The
    feature is **not** removed from the underlying form: it remains
    phonologically active for blocking pre-downstep h-epenthesis on
    itself and for feeding raising on a following registerless TRN. -/
def realizePitchUtterance (level : Int) : List TRN → List Int
  | []          => []
  | t :: rest   =>
      if t.raised = some false ∧ t.upper = none then
        level :: realizePitch level rest
      else
        realizePitch level (t :: rest)

/-- **Paradigmatic Laal-style pitch realisation** ([lionnet-2022]
    §4). Pitch is computed from `[upper]` (×2) plus `[raised]` (×1),
    *independently* per TRN — no terracing, no register-baseline state.

    Unspecified features contribute 0. The four combinations give:
    `H = 2`, `M = 1`, `L = 0`, `superHigh = 3` (Laal's gap). -/
def TRN.absolutePitch (t : TRN) : Int :=
  let u : Int := if t.upper  = some true then 2 else 0
  let r : Int := if t.raised = some true then 1 else 0
  u + r

/-! ### Lionnet's 3-tone typology -/

/-- The four classes of 3-tone system definable over the binary subtonal
    features `[±upper]`/`[±raised]` ([lionnet-2022] ex. 51): with four
    full specifications available, a 3-tone system realises three of them,
    and the unselected combination is the *gap*. The four-way classification
    by gap is a systematisation of Lionnet's binary-feature account (Laal
    itself has the `[+upper, +raised]` gap), not a typology the paper
    surveys. -/
inductive ThreeToneGap where
  /-- Gap = `[+upper, +raised]` (Laal pattern). -/
  | upperRaised
  /-- Gap = `[+upper, -raised]`. -/
  | upperLowered
  /-- Gap = `[-upper, +raised]`. -/
  | lowerRaised
  /-- Gap = `[-upper, -raised]`. -/
  | lowerLowered
  deriving DecidableEq, Repr

/-- Which TRN combination is the gap for a given 3-tone language type. -/
def ThreeToneGap.gap : ThreeToneGap → TRN
  | .upperRaised  => TRN.superHigh        -- ⟨+u, +r⟩
  | .upperLowered => TRN.H                -- ⟨+u, -r⟩
  | .lowerRaised  => TRN.M                -- ⟨-u, +r⟩
  | .lowerLowered => TRN.L                -- ⟨-u, -r⟩

/-- Laal's gap is `[+upper, +raised]` ([lionnet-2022] ex. 51). -/
theorem laal_gap_eq_superHigh : ThreeToneGap.upperRaised.gap = TRN.superHigh := rfl

/-! ### TBU and word-prosodic typology -/

/-- The prosodic domain that carries TRN specifications. In most tone
    languages this is the syllable; in Drubea and Numèè it is the mora
    ([lionnet-2025]). -/
inductive TBUKind where
  | mora
  | syllable
  deriving DecidableEq, Repr

/-- Word-prosodic system types ([hyman-2006], enriched by
    [lionnet-2025]).

    Tone systems split into **tone-based** (paradigmatic — full TRN
    contrasts) and **register-based** (only `[raised]` varies, with
    cumulative terracing realisation). -/
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

/-- Core definitional properties of downstep, following [leben-2018]
    as refined by [lionnet-2025].

    Properties (a)–(c) are definitional; (d)–(f) are cross-linguistic
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
  /-- (f) Functions contrastively (phonological, syntactic,
      morphophonological, or lexical). -/
  functionsContrastively : Bool
  deriving Repr

/-- Inventory of primitives in a phonological analysis ([lionnet-2025]). -/
structure AnalysisInventory where
  underlyingPrimitives : Nat
  postlexicalProcesses : Nat
  deriving Repr, DecidableEq

/-! ### Culminativity -/

/-- **Register culminativity**: at most one `[-raised]` TRN per stem.

    Holds for all native Drubea and Numèè stems
    ([lionnet-2025] §3.10). The Lionnet 2022 framing: a stem
    contains at most one bundle whose `[raised]` value is `some false`. -/
abbrev IsCulminative (ts : List TRN) : Prop :=
  (ts.countP (fun t => t.raised == some false)) ≤ 1

/-! ### Postlexical operations -/

/-- **Pre-downstep h-epenthesis** ([lionnet-2025]): insert an
    upstep TRN immediately before a downstep, on a registerless host.

    The rule fires when an empty (`⟨none, none⟩`) TRN is immediately
    followed by a downstep TRN (`⟨none, some false⟩`); the empty TRN
    is replaced by an upstep (`⟨none, some true⟩`). An *underlying*
    downstep blocks the rule on itself — that is the diagnostic that
    survives utterance-initial phonetic neutralisation. -/
def hEpenthesis : List TRN → List TRN
  | []                                => []
  | [t]                               => [t]
  | TRN.empty :: TRN.downstep :: rest =>
      TRN.upstep :: TRN.downstep :: hEpenthesis rest
  | t :: rest                         => t :: hEpenthesis rest

/-- **Spreading h-epenthesis**: raise *all* registerless TRNs in the
    sequence preceding a downstep, not just the immediately preceding
    one ([lionnet-2025] §3.2). Models the **abrupt-spreading**
    variant. -/
def hEpenthesisSpread : List TRN → List TRN
  | []                       => []
  | TRN.downstep :: rest     => TRN.downstep :: hEpenthesisSpread rest
  | TRN.upstep   :: rest     => TRN.upstep   :: hEpenthesisSpread rest
  | TRN.empty    :: rest     =>
      let rest' := hEpenthesisSpread rest
      match rest' with
      | TRN.downstep :: _ | TRN.upstep :: _ => TRN.upstep :: rest'
      | _                                   => TRN.empty  :: rest'
  | t :: rest                => t :: hEpenthesisSpread rest

/-! ### Subtonal feature operations -/

/-- **Subtonal assimilation** at feature `f`: the target TRN takes its
    value at `f` from the source TRN, leaving its other feature
    untouched. The Laal **M-lowering** rule ([lionnet-2022] §5.2)
    is `subtonalAssimilate Subtonal.raised src tgt`: a `[-raised]`
    value spreads from `src` to `tgt`, so a target M (`⟨-u, +r⟩`)
    becomes L (`⟨-u, -r⟩`) without altering its `[upper]` value. -/
def subtonalAssimilate (f : Subtonal) (src tgt : TRN) : TRN :=
  TRN.ofBundle (Features.Bundle.assimilate f src.toBundle tgt.toBundle)

/-- **Binary TRN merger** ([lionnet-2022] ex. 53–54): merge two TRNs' subtonal
    features into one, taking each feature from the left TRN where it is specified and
    falling back to the right (`Features.Bundle.merge`). Models the autosegmental fusion
    of two associated tones ([goldsmith-1976]); the tier-level OCP merger that
    collapses a run of identical tones is `OCP.collapse`. -/
def mergeTRN (t₁ t₂ : TRN) : TRN :=
  TRN.ofBundle (Features.Bundle.merge t₁.toBundle t₂.toBundle)

/-- Merging a TRN with itself is the identity: `mergeTRN` is idempotent on equal
    tones. -/
@[simp] theorem mergeTRN_self (t : TRN) : mergeTRN t t = t := by
  simp only [mergeTRN, Features.Bundle.merge_self, TRN.ofBundle_toBundle]

/-- **Floating-feature docking** ([lionnet-2022] §5.3): a free
    `[±f]` subtonal feature docks onto a target TRN, overwriting
    whatever value it had at `f`. Used for the morphosyntactic
    `[-raised]` suffix in Laal that triggers M-lowering. -/
def dockFloating (f : Subtonal) (v : Bool) (t : TRN) : TRN :=
  TRN.ofBundle (Features.Bundle.set f v t.toBundle)

/-! ### Verification: Laal subtonal identities -/

/-- The Laal H/M/L tones are exactly three of the four binary
    `[±u, ±r]` combinations — the gap is `superHigh`. -/
theorem laal_three_tones :
    TRN.H ≠ TRN.M ∧ TRN.M ≠ TRN.L ∧ TRN.H ≠ TRN.L ∧
    TRN.H ≠ TRN.superHigh ∧ TRN.M ≠ TRN.superHigh ∧
    TRN.L ≠ TRN.superHigh := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Paradigmatic pitch ordering: `L < M < H < superHigh`. -/
theorem laal_paradigmatic_pitch :
    TRN.L.absolutePitch = 0 ∧
    TRN.M.absolutePitch = 1 ∧
    TRN.H.absolutePitch = 2 ∧
    TRN.superHigh.absolutePitch = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **M-lowering as `[-raised]` assimilation** ([lionnet-2022]
    §5.2). When a `[-raised]` source assimilates onto an M target, the
    result is L: M's `[+raised]` is overwritten to `[-raised]`, and its
    `[-upper]` is preserved.

    Critically, the `[upper]` feature is *not* changed — this is what
    makes the operation subtonal-level rather than full-tone replacement. -/
theorem m_lowering_via_assimilation :
    subtonalAssimilate Subtonal.raised TRN.L TRN.M = TRN.L := by decide

/-- The same operation has no effect when the source itself is M:
    assimilating `[+raised]` onto M leaves M unchanged. -/
theorem m_lowering_vacuous_on_m :
    subtonalAssimilate Subtonal.raised TRN.M TRN.M = TRN.M := by decide

/-- **Floating `[-raised]` docking onto M produces L**
    ([lionnet-2022] §5.3): the morphosyntactic suffix is a free
    floating feature that overwrites the target's `[raised]` value. -/
theorem floating_minus_raised_lowers_m :
    dockFloating Subtonal.raised false TRN.M = TRN.L := by decide

/-! ### Verification: Drubea/Numèè register-only realisation -/

/-- Registerless sequences have uniform pitch. -/
theorem registerless_uniform (n : Int) :
    realizePitch n [TRN.empty, TRN.empty, TRN.empty] = [n, n, n] := rfl

/-- A single downstep lowers pitch by one step. -/
theorem downstep_lowers (n : Int) :
    realizePitch n [TRN.empty, TRN.downstep] = [n, n - 1] := rfl

/-- Multiple downsteps produce cumulative terracing. -/
theorem terracing (n : Int) :
    realizePitch n [TRN.downstep, TRN.downstep, TRN.downstep] =
      [n - 1, n - 1 - 1, n - 1 - 1 - 1] := rfl

/-- Deltas-only view of three downsteps: pitch falls by 1, 2, 3 register
    steps from the start. No anchor required. -/
theorem terracing_deltas :
    pitchDeltas [TRN.downstep, TRN.downstep, TRN.downstep] = [-1, -2, -3] := by
  decide

/-- Concrete terracing from offset 4 (mid-high on the 1–5 scale). -/
theorem terracing_from_4 :
    realizePitch 4 [TRN.downstep, TRN.downstep, TRN.downstep] = [3, 2, 1] := by
  decide

/-- h-epenthesis raises the registerless TRN before a downstep. -/
theorem h_epenthesis_before_downstep :
    hEpenthesis [TRN.empty, TRN.downstep, TRN.empty] =
      [TRN.upstep, TRN.downstep, TRN.empty] := rfl

/-- h-epenthesis + realisation: the raised TRN is higher than baseline. -/
theorem h_epenthesis_raises_pitch :
    realizePitch 4 (hEpenthesis [TRN.empty, TRN.downstep, TRN.empty]) =
      [5, 4, 4] := by decide

/-- An underlying downstep blocks h-epenthesis on itself: the rule only
    targets *registerless* TRNs immediately preceding a downstep. This
    is what the underlying initial downstep (preserved by
    `realizePitchUtterance`) buys us — the contrast `/X ⁺Y/` (raises X)
    vs `/⁺X ⁺Y/` (no raising on ⁺X) survives even when the initial X
    is utterance-initial and phonetically flat. -/
theorem l_blocks_own_h_epenthesis :
    hEpenthesis [TRN.downstep, TRN.downstep] =
      [TRN.downstep, TRN.downstep] := rfl

/-- Phonetic suppression of an utterance-initial downstep: the realized
    pitch sequence starts flat, indistinguishable from a registerless
    initial. -/
theorem utt_initial_phonetic_suppression :
    realizePitchUtterance 4 [TRN.downstep, TRN.empty, TRN.empty] =
      [4, 4, 4] := by decide

/-- The phonetic neutralisation is *only* utterance-initial: a
    non-initial downstep still drops pitch, even after the suppression
    rule fires. -/
theorem utt_initial_only_first :
    realizePitchUtterance 4 [TRN.downstep, TRN.downstep, TRN.empty] =
      [4, 3, 3] := by decide

/-- Underlying culminativity is preserved under utterance-initial
    suppression: an initial downstep still counts toward the stem-level
    `[-raised]` budget. The phonetic interface does not delete it. -/
theorem utt_initial_l_underlyingly_present :
    IsCulminative [TRN.downstep, TRN.empty] ∧
      realizePitchUtterance 4 [TRN.downstep, TRN.empty] =
        realizePitch 4 [TRN.empty, TRN.empty] := by
  refine ⟨by decide, by decide⟩

/-- Culminativity: a single `[-raised]` is culminative. -/
theorem single_l_culminative :
    IsCulminative [TRN.empty, TRN.downstep, TRN.empty] := by decide

/-- Non-culminativity: two `[-raised]` TRNs violate culminativity. -/
theorem double_l_not_culminative :
    ¬ IsCulminative [TRN.downstep, TRN.downstep] := by decide

/-! ### Monotonicity (catathesis-blocking) -/

/-- TRN order by syntagmatic pitch effect: `t₁ ≤ t₂` iff `t₁` is at least
    as lowering as `t₂`. Lifted from the `Int` order along `TRN.pitchEffect`
    (`Preorder.lift`) — a `Preorder`, not a `PartialOrder`, since TRNs
    sharing a `[raised]` value share a pitch effect. -/
instance : Preorder TRN := Preorder.lift TRN.pitchEffect

instance : DecidableRel ((· ≤ ·) : TRN → TRN → Prop) := fun _ _ => Int.decLe _ _

/-- **Monotonicity of `realizePitch` in the baseline**: a higher starting
    pitch produces pointwise higher output for any fixed TRN sequence.

    Structural basis for catathesis blocking
    ([beckman-pierrehumbert-1986]): when an ip boundary resets the
    register, subsequent pitches are higher than if catathesis had
    continued from a compressed baseline. -/
theorem realizePitch_baseline_mono (ts : List TRN)
    {n m : Int} (h : n ≤ m) :
    List.Forall₂ (· ≤ ·) (realizePitch n ts) (realizePitch m ts) := by
  induction ts generalizing n m with
  | nil => exact .nil
  | cons t rest ih =>
    have hstep : n + t.pitchEffect ≤ m + t.pitchEffect := Int.add_le_add_right h _
    simp only [realizePitch_cons]
    exact .cons hstep (ih hstep)

/-- **Full monotonicity of `realizePitch`**: pointwise lowering features
    plus a lower baseline give pointwise lower output. Subsumes
    `realizePitch_baseline_mono`. -/
theorem realizePitch_mono
    {ts₁ ts₂ : List TRN}
    (hts : List.Forall₂ (· ≤ ·) ts₁ ts₂)
    {n m : Int} (hnm : n ≤ m) :
    List.Forall₂ (· ≤ ·) (realizePitch n ts₁) (realizePitch m ts₂) := by
  induction hts generalizing n m with
  | nil => exact .nil
  | @cons t₁ t₂ rest1 rest2 hhead _ ih =>
    have hstep : n + t₁.pitchEffect ≤ m + t₂.pitchEffect :=
      Int.add_le_add hnm hhead
    simp only [realizePitch_cons]
    exact .cons hstep (ih hstep)

end Tone
