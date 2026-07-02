import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Minimalist.Features
import Linglib.Features.Aktionsart

/-!
# Aspect Heads (Outer / Inner Split)
[travis-2010] [macdonald-2008] [tsai-2008] [sybesma-2017]

Substrate types for the bipartite split-aspect cartography that has emerged
from work on Mandarin and Cantonese (and before them, English event-structure
decomposition). Following the convention that `.Voice` is a single `Cat`
constructor distinguished by `VoiceFlavor` (`Syntax/Minimalist/Verbal/Voice.lean`),
we keep `Cat.Asp` as a single F2 constructor and represent the
`AspP_outer` / `AspP_inner` distinction as `AspFlavor` on an `AspHead`
record. This avoids a new constructor (no fValue collision below v at F1)
and keeps `Cat` consumers — the 30+ files that pattern-match on `Cat` —
unchanged.

## What lives here

- `AspFlavor` — outer / inner.
- `AspHead` — the analytical record (flavor + selectional spec + optional
  Probe + feature stack), parallel to `VoiceHead`.
- A small number of substrate predicates (`isOuter`, `isInner`, `defaultFLevel`).

## What does NOT live here

- The viewpoint-aspect denotation (`Semantics/Aspect/Basic.lean`
  `ViewpointType`). Travis, MacDonald, Tsai disagree on AspO denotation, so
  "AspP_outer hosts viewpoint aspect" is *not* a uniform substrate identity.
  Per-morpheme bridges live in the relevant Fragment files (e.g.,
  `-le ↦ ViewpointType.perfective` in `Fragments/Mandarin/Aspect.lean`);
  the substrate stays neutral.

- The [±D] dynamic feature analysis ([lin-liu-2009]; [shen-2004]).
  `[+D]` does two distinct jobs: (a) a property of the *predicate*
  (Aktionsart-derived), (b) a *selectional requirement* on AspO to combine
  with a dynamic complement. We model only (b) here, by exposing
  `selectsDynamicity : Option Features.Dynamicity`. The predicate-side
  property already lives in `Features/Aktionsart.lean` (`Dynamicity`); this
  field on AspHead encodes which value (if any) the head requires.

- [liu-yip-2026]'s Cantonese -faan does NOT carry the dynamicity
  restriction (it composes with stative *jau* 'have'). Encoded by leaving
  `selectsDynamicity = none` on -faan's AspHead; encoding it as
  `some .dynamic` would over-predict.

- Per-morpheme syntactic typing (Mandarin *you*, *zai*, *-le*, *-guo*, *-zhe*;
  Cantonese *-faan*, *-gwo*, *jau*, *zoi*) lives in the per-language Fragment files.

- The "split aspect" framework as a *named theory* (the cluster of
  [travis-2010], [macdonald-2008], [tsai-2008],
  [sybesma-2017]) — its analytical claims live in
  `Studies/LiuYip2026.lean`, which is the first
  paper-anchored consumer of this substrate. Promotion to a separate
  `SplitAspect.lean` theory file would follow when a second study consumes
  the same primitives.
-/

namespace Minimalist

-- ============================================================================
-- § 1. Aspect Flavors
-- ============================================================================

/-- Flavor of an aspect head.

    The outer/inner cut is the binary simplification ([travis-2010],
    [macdonald-2008], [tsai-2008], [sybesma-2017]) of
    [cinque-1999]'s finer-grained adverbial sequence. Outer aspect sits
    above vP (and is what `viewpoint` morphemes like Mandarin *-le*, *-guo*,
    *-zhe* and Cantonese *-zo*, *-gwo*, *-gan*, *-faan* canonically associate
    with); inner aspect sits inside the v-shell (and is what Aktionsart
    morphemes like phase complements *-dao*, *-hao*, *-wan*, *-diao* or
    Cantonese *-dim*, *-dou*, *-zoek*, *-jyun*, *-hou* canonically associate
    with).

    This file does NOT take a position on whether the cut is binary
    cross-linguistically; languages with finer cartographies (e.g.,
    [cinque-1999]'s 30+ adverbial heads) would need a richer flavor
    type. -/
inductive AspFlavor where
  /-- Outer aspect: above vP, viewpoint-host position. -/
  | outer
  /-- Inner aspect: inside the v-shell, Aktionsart-host position. -/
  | inner
  deriving DecidableEq, Repr, Inhabited

/-- Predicate: this flavor is outer aspect. -/
def AspFlavor.isOuter : AspFlavor → Bool
  | .outer => true
  | .inner => false

/-- Predicate: this flavor is inner aspect. -/
def AspFlavor.isInner : AspFlavor → Bool
  | .outer => false
  | .inner => true

/-- The two flavors partition `AspFlavor`. -/
theorem AspFlavor.outer_xor_inner (f : AspFlavor) :
    f.isOuter = true ↔ f.isInner = false := by
  cases f <;> decide

/-- The `fValue` "slot" an aspect head conventionally occupies, given its
    flavor.

    Outer aspect lives at `fValue 2` (alongside `T`, `Mod`, `Neg`, `Pol`,
    `Evid`, `Q`, `Path`) — the specification domain.
    Inner aspect lives inside the v-shell, structurally below `v` (`fValue 1`)
    but above `V` (`fValue 0`). The current `fValue : Cat → Nat` scheme has
    no integer slot between F0 and F1; we report the v-shell parent's level
    (1) as a conservative approximation. The semantics-audit-flagged refactor
    to a finer `fValue` (e.g., `Rat`-valued, or sub-ranks) would let `.inner`
    return a value strictly between 0 and 1; until that lands, downstream
    consumers should not rely on inner-vs-outer ordering at the `fValue` level
    and should consult `flavor` directly. -/
def AspFlavor.defaultFLevel : AspFlavor → Nat
  | .outer => 2
  | .inner => 1

-- ============================================================================
-- § 2. Aspect Heads
-- ============================================================================

/-- An aspect head, parallel to `VoiceHead`.

    Carries: (a) which flavor (outer/inner), (b) optional selectional
    requirement on the complement's dynamicity, (c) optional `Probe.Profile`
    when the head is itself an Agree probe ([liu-yip-2026] analyzes
    Mandarin *you* and Cantonese -faan as probe-bearing AspO heads),
    (d) any Agree-relevant features (e.g., `[+EXP]` on the experiential
    AspO that licenses -guo).

    The `selectsDynamicity` field separates *selectional* dynamicity
    (head-borne) from *predicate* dynamicity (Features.Dynamicity,
    Aktionsart-derived). A head with `selectsDynamicity := some .dynamic`
    requires its complement to be a dynamic predicate; a head with
    `selectsDynamicity := none` is indifferent. -/
structure AspHead where
  /-- The flavor (outer or inner). -/
  flavor : AspFlavor
  /-- Selectional requirement on the complement's dynamicity, if any.
      `none` = no requirement (compatible with stative or dynamic complements);
      `some .dynamic` = requires dynamic complement ([lin-liu-2009]'s [+D]);
      `some .stative` = requires stative complement (rare; defensive default). -/
  selectsDynamicity : Option Features.Dynamicity := none
  /-- Optional probe profile: populated when the head triggers Agree.
      The probe's `probeHead` is conventionally `.Asp`; the flavor field on
      `AspHead` disambiguates outer-vs-inner at the analytical level. -/
  probe : Option Probe.Profile := none
  /-- Agree-relevant features on the head (e.g., `[+EXP]` for experiential AspO,
      `[uD]` for the AspO that triggers *you*-movement). -/
  features : FeatureBundle := ⊥
  deriving Repr

/-- Convenience constructor: a bare outer-aspect head with no selectional
    or featural commitments. Used for AspO heads whose only role is to
    project the position (e.g., when a moved adverb lands in Spec,AspP_outer
    without the head itself imposing constraints). -/
def AspHead.bareOuter : AspHead := { flavor := .outer }

/-- Convenience constructor: a bare inner-aspect head. -/
def AspHead.bareInner : AspHead := { flavor := .inner }

/-- Outer-aspect head with a `[+D]` dynamic-complement selectional
    requirement ([lin-liu-2009]). Used to type Mandarin's matrix
    Asp_outer when it needs to license *you* via Agree. -/
def AspHead.outerDynamic : AspHead :=
  { flavor := .outer, selectsDynamicity := some .dynamic }

-- ============================================================================
-- § 3. Predicates and trivial theorems
-- ============================================================================

/-- A head is outer iff its flavor is `.outer`. -/
def AspHead.isOuter (h : AspHead) : Bool := h.flavor.isOuter

/-- A head is inner iff its flavor is `.inner`. -/
def AspHead.isInner (h : AspHead) : Bool := h.flavor.isInner

/-- A head carries a probe iff `probe.isSome`. -/
def AspHead.isProbeBearing (h : AspHead) : Bool := h.probe.isSome

/-- Dynamicity-licensing: this head licenses a complement of the given
    dynamicity. A head with no requirement (`selectsDynamicity = none`)
    licenses any complement; otherwise the complement's dynamicity must
    match. -/
def AspHead.licensesDynamicity (h : AspHead) (d : Features.Dynamicity) : Bool :=
  match h.selectsDynamicity with
  | none => true
  | some required => required = d

/-- A `bareOuter` head has no selectional requirement. -/
theorem bareOuter_no_dyn_req :
    AspHead.bareOuter.selectsDynamicity = none := rfl

/-- A `bareInner` head has no selectional requirement. -/
theorem bareInner_no_dyn_req :
    AspHead.bareInner.selectsDynamicity = none := rfl

/-- A `bareOuter` head licenses both dynamic and stative complements. -/
theorem bareOuter_licenses_all (d : Features.Dynamicity) :
    AspHead.bareOuter.licensesDynamicity d = true := by
  simp [AspHead.licensesDynamicity, AspHead.bareOuter]

/-- An `outerDynamic` head licenses dynamic but not stative complements
    — this is the [lin-liu-2009] [+D] constraint, derived rather
    than stipulated. -/
theorem outerDynamic_licenses_dynamic_only :
    AspHead.outerDynamic.licensesDynamicity .dynamic = true ∧
    AspHead.outerDynamic.licensesDynamicity .stative = false := by
  refine ⟨?_, ?_⟩ <;> simp [AspHead.licensesDynamicity, AspHead.outerDynamic]

end Minimalist
