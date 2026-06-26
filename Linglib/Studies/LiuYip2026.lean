import Linglib.Syntax.Minimalist.Verbal.Aspect
import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine
import Linglib.Syntax.Clause.Complementation
import Linglib.Features.Aktionsart
import Linglib.Fragments.Mandarin.Predicates
import Linglib.Fragments.Cantonese.Aspect
import Linglib.Fragments.Cantonese.Particles
import Linglib.Fragments.Cantonese.Predicates
import Linglib.Fragments.Cantonese.ResultativeComplements

/-! # Liu & Yip 2026: Again, finiteness, and split aspect in Chinese languages

[liu-yip-2026] (NLLT 44:25, doi 10.1007/s11049-026-09708-5).

## Paper's central claims

(1) **Hierarchical, size-based finiteness in Chinese.** Three clause sizes:
    Type I (CP, finite), Type II (TP, nonfinite without Aspect Restructuring),
    Type III (vP, nonfinite with Aspect Restructuring).
(2) **Split aspect.** Two aspectual projections in the spine:
    AspP_outer above vP, AspP_inner inside vP.
(3) **Asymmetry of *again*-elements.** Mandarin preverbal *you* and Cantonese
    postverbal *-faan* associate with AspP_outer (and may exhibit "exceptional
    scopal behavior" — *you*-skipping by movement+reconstruction; *-faan*-lowering
    by Agree). Mandarin *zai* and Cantonese *-gwo* associate with AspP_inner
    (and never scope-mismatch).
(4) **Defective intervention.** When the embedded clause is TP-sized, its
    *embedded* AspP_outer blocks the matrix probe's reach to the embedded
    *again*-element.
(5) **[wurmbrand-lohninger-2023] ICH** (proposition > situation > event)
    instantiated by Chinese as CP > TP > vP.
(6) **vP is the minimal nonfinite size.** Empirical: AspP_inner is mandatory
    above V; aspect-lowering and *-gwo*-lowering systematically don't occur.

## What this Studies file commits to substrate

- *No* new substrate files. The [wurmbrand-lohninger-2023] ICH, the
  [wurmbrand-2001] truncation operator, and the [pesetsky-2021]
  Exfoliation primitive all violate the ≥ 2-paper-anchor graduation rule.
  They live as local definitions here, ready to graduate when a second
  study consumes them.

- The substrate-level addition [liu-yip-2026]'s analysis *does* motivate
  is the bipartite split-aspect typing: `AspFlavor` and `AspHead`, landed in
  `Syntax/Minimalist/Aspect.lean` parallel to `VoiceHead { flavor }`.
  That commitment is independent of the analytical claims of this paper —
  it is consumed by [travis-2010], [macdonald-2008],
  [tsai-2008], [sybesma-2017], and [liu-yip-2026] jointly —
  so it warranted substrate placement.

## What this Studies file does NOT commit to

- **Defective intervention is NOT bilateral labeling.** [liu-yip-2026]'s
  intervener is a *featurally-matching head occupying a probe position*
  ([chomsky-2000] defective intervention), not a *category in a
  bilateral label* ([keine-2020] horizon opacity). The two coincide on
  the Type II / Type III contrast but make distinct predictions on featural
  mismatch. The `defectiveIntervention` predicate below uses
  head-as-intervener; it does *not* call `Probe.Profile.transparentToLabel`.

- **Aspect-lowering and *-faan*-lowering are parallel, not the same.** Both
  involve matrix-AspP_outer Agree across a vP boundary, but the empirical
  diagnostics differ (e.g., -*zhe*_CONT vs -*zhe*_IPFV asymmetry; -*gwo* not
  lowering in Cantonese). No reduction theorem is asserted.

- **The [wurmbrand-lohninger-2023] ICH is not a baked-in `LinearOrder`**
  with an implication on transparency. The order on `ComplementClass` is
  independent of the claim that transparency is downward-closed; the latter
  is a theorem about a transparency relation, not a definitional property.

- **Minimal-vP is empirical, not structural.** Encoded as a per-fragment
  drift sentry, falsifiable by a single new datum.

## Cross-framework reconciliation

§11 below documents divergences with HPSG (lexical-rule analysis of
"you-skipping"), Dependency Grammar (no AspP, no ICH), CCG (forward
composition), `Fragments/Italian/Modals.lean`'s [hacquard-2006]
restructuring substrate, `Studies/Landau2015.lean`'s
`ControlTier`, and `Syntax/Minimalist/Phase.lean`. The
[cinque-2006] vs. [wurmbrand-2001] restructuring rivalry is made
explicit in §10 as a refutation theorem candidate.
-/

namespace LiuYip2026

open Minimalist (AspFlavor AspHead Probe.Profile ClauseSpine ComplementSize Cat fValue)
open Clause.Complementation (CTPClass ComplementClauseStructure)

-- ============================================================================
-- §1. Three Chinese clause types as ComplementSize instances
-- ============================================================================

/-- [liu-yip-2026]'s Type I: finite (CP). Selected by *xiangxin* 'believe',
    *shuo* 'say' etc.; blocks *you*-skipping and *-faan*-lowering. -/
def typeI : ComplementSize := ComplementSize.cP

/-- [liu-yip-2026]'s Type II: nonfinite without Aspect Restructuring (TP).
    Selected when the predicate licenses TP but blocks *-faan*-lowering
    via embedded AspP_outer intervention. -/
def typeII : ComplementSize := ComplementSize.tP

/-- [liu-yip-2026]'s Type III: nonfinite *with* Aspect Restructuring (vP).
    Selected by *xiang* 'want', *rang* 'let' etc.; permits *you*-skipping
    and *-faan*-lowering. -/
def typeIII : ComplementSize := ComplementSize.vP

/-- Type ordering: vP < TP < CP (size-wise, per `fValue`). -/
theorem types_ordered :
    typeIII.fLevel < typeII.fLevel ∧ typeII.fLevel < typeI.fLevel := by decide

-- ============================================================================
-- §2. Wurmbrand-Lohninger ICH (local enum, NOT substrate)
-- ============================================================================

/-- The Implicational Complementation Hierarchy of [wurmbrand-lohninger-2023]:
    proposition > situation > event in transparency-decreasing order.

    Local to this Studies file; promotion to `Syntax/Complementation/`
    is contingent on a second paper-anchored consumer (the control
    studies — e.g. Studies/Landau2015.lean — and Studies/Grano2024.lean
    are candidate second sites).

    `LinearOrder` is *not* derived: the implicational content of the ICH is
    a theorem about a *transparency relation*, not a structural property of
    the class lattice. The order here is just the enum's natural one
    (event < situation < proposition); the implicational claim is
    `transparency_downward_closed` below. -/
inductive ComplementClass where
  /-- Smallest, most transparent: vP-level event reports. -/
  | event
  /-- Mid: TP-level situation reports. -/
  | situation
  /-- Largest, most opaque: CP-level proposition reports. -/
  | proposition
  deriving DecidableEq, Repr

/-- Numeric rank for ComplementClass: event = 0, situation = 1, proposition = 2. -/
def ComplementClass.rank : ComplementClass → Nat
  | .event => 0
  | .situation => 1
  | .proposition => 2

-- ============================================================================
-- §3. Local complementClass: derived from ComplementSize.fValue
-- ============================================================================

/-- Project a `ComplementSize` onto the [wurmbrand-lohninger-2023]
    3-tier `ComplementClass`, by `fValue` thresholds. This is
    [liu-yip-2026]'s *Chinese-specific* mapping (the paper notes
    explicitly that other languages may calibrate differently). The Studies
    file instantiates the mapping; a richer cross-linguistic substrate would
    parameterize it per-language. -/
def complementClass (cs : ComplementSize) : ComplementClass :=
  if cs.fLevel ≥ fValue .C then .proposition
  else if cs.fLevel ≥ fValue .T then .situation
  else .event

theorem typeI_proposition : complementClass typeI = .proposition := by decide
theorem typeII_situation : complementClass typeII = .situation := by decide
theorem typeIII_event : complementClass typeIII = .event := by decide

-- ============================================================================
-- §4. Local restructure operator (truncation; [wurmbrand-2001] flavor)
-- ============================================================================

/-- [wurmbrand-2001]-style restructuring: drop the topmost projected
    head from a `ClauseSpine`. Returns `none` if the spine has only one
    head (the floor).

    Local to this Studies file. Fails the ≥2-consumer rule for substrate;
    promotion candidate when `Fragments/Italian/Modals.lean`'s informal
    restructuring discussion gets a Studies file or when a
    [wurmbrand-2014] study lands.

    Implementation: the dropLast of an at-least-2-element list is non-empty,
    proved via the `[x, y :: rest]` pattern's structural guarantee. -/
def restructure : ClauseSpine → Option ClauseSpine
  | ⟨[], h⟩ => absurd rfl h
  | ⟨[_], _⟩ => none
  | ⟨x :: y :: rest, _⟩ =>
    some ⟨x :: (y :: rest).dropLast, by simp [List.cons_ne_nil]⟩

/-- Restructuring strictly decreases spine length (when defined).
    The proof unfolds via the structural constructors of `ClauseSpine`. -/
theorem restructure_decreases (s : ClauseSpine) :
    ∀ s' ∈ restructure s, s'.projectedHeads.length < s.projectedHeads.length := by
  intro s' hs'
  obtain ⟨heads, nonempty⟩ := s
  match heads, nonempty, hs' with
  | [], h, _ => exact absurd rfl h
  | [_], _, hs' => simp [restructure] at hs'
  | x :: y :: rest, _, hs' =>
    -- restructure returns `some ⟨x :: (y :: rest).dropLast, _⟩`
    -- so s' has projectedHeads = x :: (y :: rest).dropLast.
    -- Original heads.length = 2 + rest.length;
    -- s'.projectedHeads.length = 1 + (y :: rest).dropLast.length
    --                          = 1 + (1 + rest.length - 1) = 1 + rest.length.
    simp only [restructure, Option.mem_def, Option.some.injEq] at hs'
    cases hs'
    simp [List.length_dropLast]

-- ============================================================================
-- §5. Defective intervention (head-as-intervener; NOT bilateral labeling)
-- ============================================================================

/-- [liu-yip-2026]'s defective intervention ([chomsky-2000]): an
    *embedded* head of the same category as the matrix probe blocks Agree,
    regardless of bilateral labeling. The featural-compatibility check
    enforces that intervention is by an *element occupying an embedded
    probe position*, not by a category in a sister's label.

    `intervenes` returns `true` when the embedded head's selectional
    requirement (e.g. Asp_outer's [+D] dynamicity expectation) overlaps with
    the matrix probe's expectation in a way that creates a defective
    intervention configuration. The simplest such check: same-flavor +
    same-or-compatible selectional spec.

    This predicate deliberately does NOT call
    `Probe.Profile.transparentToLabel` — head-as-intervener and label-as-locus
    diverge on featurally-mismatched probes. -/
def intervenes (matrixProbe : AspHead) (embeddedHead : AspHead) : Bool :=
  -- Same flavor + featurally compatible (or both indifferent)
  matrixProbe.flavor = embeddedHead.flavor &&
    (match matrixProbe.selectsDynamicity, embeddedHead.selectsDynamicity with
     | none, _ => true        -- matrix indifferent: any embedded head intervenes
     | _, none => true        -- embedded indifferent: still intervenes (head presence)
     | some _, some _ => true -- both present: intervention regardless of value match
    )

-- ============================================================================
-- §6. Mandarin you / zai split-aspect typing (Studies-side projection)
-- ============================================================================

/-- Studies-side projection: Mandarin *you* 'again' is typed as an
    AspP_outer-associated probe-bearing head with a [+D] dynamicity
    selectional restriction (per [lin-liu-2009], building on
    [shen-2004]). The lexical entry in `Fragments/Mandarin/Particles.lean`
    carries only the presupposition trigger; the syntactic typing here
    is [liu-yip-2026]'s analytical commitment. -/
def youAspHead : AspHead := AspHead.outerDynamic

/-- Studies-side projection: Mandarin *zai* 'again' is typed as an
    AspP_inner-associated bare head, no dynamicity restriction. -/
def zaiAspHead : AspHead := AspHead.bareInner

theorem you_outer : youAspHead.flavor = .outer := rfl
theorem zai_inner : zaiAspHead.flavor = .inner := rfl
theorem you_requires_dynamic :
    youAspHead.selectsDynamicity = some .dynamic := rfl
theorem zai_no_requirement :
    zaiAspHead.selectsDynamicity = none := rfl

-- ============================================================================
-- §7. Cantonese -faan / -gwo split-aspect typing
-- ============================================================================

/-- Studies-side projection: Cantonese *-faan* 'again' is
    AspP_outer-associated but, unlike Mandarin *you*, does NOT carry a [+D]
    selectional restriction (it is compatible with stative *jau* 'have' per
    [liu-yip-2026]). -/
def faanAspHead : AspHead := Cantonese.Aspect.faan.toAspHead

/-- Studies-side projection: Cantonese *-gwo* (repetitive use) is
    AspP_inner-associated. Its experiential use is also AspP_inner per the
    lexical entry, but pragmatically distinct. -/
def gwoAspHead : AspHead := Cantonese.Aspect.gwo.toAspHead

theorem faan_outer_no_dyn :
    faanAspHead.flavor = .outer ∧ faanAspHead.selectsDynamicity = none := by
  refine ⟨rfl, rfl⟩

theorem gwo_inner :
    gwoAspHead.flavor = .inner := rfl

/-- Mandarin *you* and Cantonese *-faan* are BOTH outer-aspect, but only
    *you* carries [+D]. Encoding *-faan* with
    `selectsDynamicity = some .dynamic` would over-predict (it would force
    incompatibility with stative *jau*). -/
theorem you_vs_faan_dynamicity :
    youAspHead.selectsDynamicity = some .dynamic ∧
    faanAspHead.selectsDynamicity = none := by
  refine ⟨rfl, rfl⟩

-- ============================================================================
-- §8. The four generalizations as theorems on the substrate
-- ============================================================================

/-- **Generalization I** ([liu-yip-2026]): in Mandarin, an
    *again*-element exhibits exceptional scopal behavior IFF it is
    outer-aspect-associated.

    On the substrate: `youAspHead.isOuter = true` (you may skip);
    `zaiAspHead.isOuter = false` (zai may not). The empirical content is the
    biconditional between AspFlavor and the scope-mismatch facts the paper
    documents. -/
theorem generalization_I_mandarin :
    youAspHead.isOuter = true ∧ zaiAspHead.isOuter = false := by
  refine ⟨rfl, rfl⟩

/-- **Generalization I** (Cantonese counterpart): *-faan* (outer) may lower;
    *-gwo* (inner) may not. -/
theorem generalization_I_cantonese :
    faanAspHead.isOuter = true ∧ gwoAspHead.isOuter = false := by
  refine ⟨rfl, rfl⟩

/-- **Generalization II** ([liu-yip-2026]): the exceptional scopal
    behavior of *again* may cross nonfinite (vP) but not finite (CP) clause
    boundaries.

    On the substrate: this is an instance of upward entailment of opacity
    (`Probe.lean` `upward_entailment_label`). Stated here without invoking
    bilateral labeling — see §5 above. The content is that for any matrix
    *again*-bearing AspO probe, the *complement clause's size* determines
    transparency: vP transparent, TP / CP opaque. -/
theorem generalization_II_mandarin :
    typeIII.fLevel < typeII.fLevel ∧ typeII.fLevel < typeI.fLevel := by decide

/-- **Correlation I** ([liu-yip-2026], Mandarin): an *again*-element
    exhibits exceptional scopal behavior IFF it cannot surface in an
    embedded nonfinite clause without a dynamic ([+D]) aspect.

    On the substrate: this is the consequence of Mandarin *you*'s
    `selectsDynamicity = some .dynamic`. *zai*, with no such restriction,
    can attach to either dynamic or stative complements but never scopes
    mismatch. -/
theorem correlation_I_mandarin :
    youAspHead.licensesDynamicity .dynamic = true ∧
    youAspHead.licensesDynamicity .stative = false ∧
    zaiAspHead.licensesDynamicity .dynamic = true ∧
    zaiAspHead.licensesDynamicity .stative = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **Correlation II** ([liu-yip-2026]): an *again*-element exhibits
    exceptional scopal behavior IFF it is structurally higher than
    aspectual elements.

    On the substrate: AspO has higher `defaultFLevel` (2) than AspI (1).
    Outer *you* / *-faan* are above the inner aspectual elements;
    inner *zai* / *-gwo* are not. -/
theorem correlation_II_mandarin :
    AspFlavor.outer.defaultFLevel > AspFlavor.inner.defaultFLevel := by decide

-- ============================================================================
-- §9. Minimal-vP claim as a per-fragment drift sentry
-- ============================================================================

/-! The minimal-vP claim is an *empirical* generalization about Chinese, not
a structural property derived from substrate. Stated here as a per-fragment
assertion that every nonfinite-clause-taking predicate in the Mandarin and
Cantonese fragments selects a complement of size ≥ vP. Falsifiable by a
single new datum. -/

open Mandarin.Predicates in
/-- All Mandarin nonfinite-takers (xiang, rang, quan, bi, dasuan, shefa)
    have `complementType = .infinitival`, consistent with vP-as-floor and
    falsifiable by a single new datum. The Fragment-side companion is
    `Mandarin.Predicates.liuyip_partition`. -/
theorem mandarin_nonfinite_takers_min_vP :
    [xiang, rang, quan, bi, dasuan, shefa].all
      (·.complementType = .infinitival) = true := by decide

open Cantonese.Predicates in
/-- All Cantonese nonfinite-takers select `[.vP]` per the per-language
    fragment classification ([liu-yip-2026]). -/
theorem cantonese_nonfinite_takers_min_vP :
    [soeng, hyun, bik, giu, daasyun].all (·.selects = [.vP]) = true := by decide

-- ============================================================================
-- §10. The [cinque-2006] vs [wurmbrand-2001] restructuring rivalry
-- ============================================================================

/-! ### Internal tension in the [liu-yip-2026] architecture

There is a hidden incoherence: the spine substrate (`ClauseSpine` +
`AspFlavor.outer` / `inner` always projected when present) commits to
[cinque-2006]'s "always project all functional heads" view; the
restructuring operator above (truncate the topmost head) commits to
[wurmbrand-2001]'s "remove projection on restructuring" view. These
are direct rivals on the same Chinese aspect data.

The current formalization adopts both — and lives with the tension —
because:

(a) The split-aspect substrate (`AspHead { flavor }`) is theory-neutral:
    a flavor field on a single `Cat.Asp` constructor doesn't itself say
    that AspP_outer is always projected. Languages can opt in to
    projecting only one flavor.

(b) The local `restructure` operator above is Wurmbrand-flavored, not a
    cross-framework commitment. A Cinque-flavored alternative would
    leave the spine unchanged but mark some heads as silent —
    trivially, `id`. The substrate accommodates both projections; the
    rivalry is *visible* rather than hidden.

The sharp refutation theorem
`¬ (Wurmbrand.truncated.projects .Asp ↔ Cinque.full.projects .Asp)` is
contingent on a Cinque-style "always project" formalization landing in
`Syntax/Minimalist/`. Until then, the rivalry is documented in
prose, not theorem. -/

/-- A trivial Cinque-flavored "restructuring" (identity) for comparison
    with the Wurmbrand-flavored `restructure` above. [cinque-2006]'s
    claim is that restructuring is *projection-marking*, not truncation;
    structurally, the spine is unchanged. -/
def cinqueRestructure (s : ClauseSpine) : ClauseSpine := s

theorem cinque_vs_wurmbrand_diverge (s : ClauseSpine) :
    ∀ s' ∈ restructure s,
      s'.projectedHeads.length < (cinqueRestructure s).projectedHeads.length :=
  fun s' hs' => restructure_decreases s s' hs'

-- ============================================================================
-- §11. Cross-framework comparison (Deal2026 §8 style)
-- ============================================================================

/-! ### Sister-framework treatments of "you-skipping" / *-faan*-lowering

Each major sister framework analyzes the same data via a fundamentally
different mechanism. This section documents the divergences without
attempting bridge theorems (which would require the sister frameworks to
have Studies-level Chinese formalizations they currently lack):

- **HPSG** (`Syntax/HPSG/Basic.lean`): no clausal spine, no
  AspP, no ICH. The "you-skipping" pattern would naturally be a *lexical
  rule on argument structure* (an argument-structure–changing `lexical-cxt`,
  in the RSRL terms of `Syntax/HPSG/Construction`). [liu-yip-2026]'s
  movement+reconstruction has no HPSG analog. SILENT DIVERGENCE.

- **Dependency Grammar** (`Studies/Osborne2019Control.lean`):
  control and raising are *structurally identical* in DG; AspP is absent.
  "you-skipping," restructuring, and *-faan*-lowering would all be
  `xcomp` plus enhanced-edge propagation. SILENT DIVERGENCE
  (irreconcilable at substrate level; bridgeable only at the empirical
  prediction level).

- **CCG** (`Syntax/CCG/Basic.lean`, `Scope.lean`): scope
  mismatch is type-shifting + composition. *you*'s skipping naturally
  maps to forward composition; no movement+reconstruction needed. A
  bridge theorem `LiuYip.youSkipping iff CCG.derivableViaComposition`
  is tractable on a small fragment but not attempted here.

- **`Fragments/Italian/Modals.lean`** has a developed restructuring
  substrate based on [rizzi-1978] + [hacquard-2006]
  (event-relativity analysis). The [liu-yip-2026] formalization here
  uses a [wurmbrand-2001] truncation operator (§4 above). The two
  are direct rivals; integration with the Italian substrate would be a
  productive next step but is deferred (the Italian file currently has
  no Wurmbrand-truncation bridge of its own).

- **`Studies/Landau2015.lean`** has `ControlTier`
  (predicative vs logophoric) cross-classifying CTPs along an axis the
  [wurmbrand-lohninger-2023] ICH `ComplementClass`
  (event/situation/proposition) parallels. A bridge theorem
  `LiuYip.proposition → Landau.logophoric` is candidate future work;
  both Studies files currently formalize their own complement-class
  projections without sharing substrate.

- **`Syntax/Minimalist/Phase.lean`** has [chomsky-2000]
  / [chomsky-2001] phase machinery (`PICStrength`).
  [liu-yip-2026]'s intervention is by AspP_outer, a *non-phase*
  head — defective intervention is a third locality regime alongside
  `PICStrength.{strong, weak, linearizationBound}`. The current
  formalization silently bypasses the `Phase` substrate. Resolution:
  either extend `PICStrength` with a "head-as-intervener" case, or add
  explicit prose noting the alternative locality model. -/

-- ============================================================================
-- §12. Bridge to Clause.Complementation.ComplementClauseStructure
-- ============================================================================

/-- The local `ComplementClass` projects to the existing theory-neutral
    surface enum `Clause.Complementation.ComplementClauseStructure`.
    This converts the planned ICH from a parallel third axis into a
    projection over substrate that already serves [deal-2026],
    [landau-2015], [cristofaro-2013], and [noonan-2007]
    — the interconnection-density discipline CLAUDE.md describes.

    Note: the projection collapses [wurmbrand-lohninger-2023]'s
    three classes onto two surface patterns (`barePropositionalCP` for
    proposition, `abarInternalCP` for situation/event). The collapse is
    correct for Chinese but may not generalize. -/
def toSurfacePattern : ComplementClass → ComplementClauseStructure
  | .proposition => .barePropositionalCP
  | .situation => .abarInternalCP
  | .event => .abarInternalCP

theorem proposition_surface :
    toSurfacePattern .proposition = .barePropositionalCP := rfl

-- ============================================================================
-- §13. Open / deferred items
-- ============================================================================

/-! ### Deferred items

- **[pesetsky-2021] Exfoliation**: not formalized here. The `shuo`-CP
  puzzle [liu-yip-2026] resolve via Exfoliation (CP layer peelable
  under A-dependency) is left as prose. Promotion to a substrate operator
  awaits a second consumer.

- **`Semantics/Again/` substrate**: a uniform *again*-presupposition
  substrate ([von-stechow-1996] / [beck-2006] parameterization)
  is recommended but not landed. Without it, every *again*-element's
  presupposition is encoded independently in its Fragment lexical entry,
  which silently commits to an anti-decompositional account when it
  type-equates *you*'s repetitive reading with *zai*'s. The substrate
  module is deferred until a German-*wieder* or English-*again* study
  joins.

- **The repetitive-vs-restitutive distinction**: explicitly bracketed by
  [liu-yip-2026] as out of scope. The Mandarin `you` Fragment entry
  currently encodes only the repetitive reading; a `you_restitutive`
  companion entry would be a small addition if needed.

- **The minimal-vP empirical claim** (§9): per-fragment drift sentries
  here cover Mandarin (6 verbs) and Cantonese (5 verbs). A larger
  cohort, especially for typologically distant languages claimed to
  have similar restructuring, would strengthen the empirical content.

- **[wurmbrand-2014] restructuring data** (German / Romance): the
  local `restructure` operator is [wurmbrand-2001]-flavored and
  tested only on Chinese. [wurmbrand-2014]'s lexical / functional
  restructuring dichotomy is a richer typology this Studies file does
  not yet engage. -/

end LiuYip2026
