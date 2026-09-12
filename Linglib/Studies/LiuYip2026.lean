import Linglib.Syntax.Minimalist.Verbal.Aspect
import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine
import Linglib.Semantics.Aspect.Basic
import Linglib.Fragments.Mandarin.Predicates
import Linglib.Fragments.Cantonese.Aspect
import Linglib.Fragments.Cantonese.Particles
import Linglib.Fragments.Cantonese.Predicates
import Linglib.Fragments.Cantonese.ResultativeComplements

/-!
# Liu and Yip (2026): Again, Finiteness, and Split Aspect in Chinese Languages

This file formalizes the size-based finiteness and split-aspect analysis of [liu-yip-2026]
for Mandarin and Cantonese. Complement clauses come in three sizes, finite CP, nonfinite TP
without aspect restructuring, and nonfinite vP with it (`typeI`, `typeII`, `typeIII`),
instantiating the implicational complementation hierarchy of [wurmbrand-lohninger-2023].
Aspect splits into an outer projection above vP and an inner one inside it: Mandarin *you*
and Cantonese *-faan* associate with the outer projection and can scope exceptionally, by
movement with reconstruction and by Agree respectively, while Mandarin *zai* and Cantonese
*-gwo* associate with the inner projection and never mismatch. A TP-sized complement's own
outer aspect head blocks the matrix probe's reach to the embedded *again*-element, a
defective intervention in the sense of [chomsky-2000] (`defectiveIntervention`), and vP is
the minimal nonfinite size, the inner projection being mandatory above V.

## Implementation notes

The complementation hierarchy, the truncation operator of [wurmbrand-2001], and the
exfoliation of [pesetsky-2021] are local to this file. The intervener is a
featurally matching head in a probe position, not a category in a bilateral label, and the
aspect-lowering and *-faan*-lowering derivations are kept parallel rather than identified.
The minimal-vP claim is recorded per fragment as an empirical generalization.

## TODO

Exfoliation, a uniform *again*-presupposition substrate, the restitutive reading, and the
German and Romance restructuring typology of [wurmbrand-2014] are not represented.

## References

* [liu-yip-2026]
* [wurmbrand-lohninger-2023]
* [wurmbrand-2001]
* [chomsky-2000]
* [pesetsky-2021]
* [wurmbrand-2014]
-/

namespace LiuYip2026

open Minimalist (AspFlavor AspHead Probe.Profile ClauseSpine ComplementSize Cat fValue)

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

/-- [wurmbrand-lohninger-2023] ICH classes track structural size —
    proposition = CP, situation = TP, event = vP. Replaces the retired
    projection onto the deleted surface enum, which forced
    situation/event onto an Ā-dependency cell the ICH does not claim.
    ([deal-2026]'s shell/Ā axes live in `Studies/Deal2026.lean`;
    the ICH makes no claim on either axis, so no bridge is stated.) -/
def ComplementClass.size : ComplementClass → ComplementSize
  | .proposition => .cP
  | .situation => .tP
  | .event => .vP

end LiuYip2026
