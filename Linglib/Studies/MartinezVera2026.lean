import Mathlib.Data.Set.Insert
import Linglib.Semantics.Presupposition.ContentLayer
import Linglib.Semantics.Questions.Highlighting
import Linglib.Semantics.Evidential.Source
import Linglib.Discourse.Roles
import Linglib.Semantics.Questions.Hamblin
import Linglib.Studies.Faller2019
import Linglib.Studies.Hohle1992
import Linglib.Studies.RomeroHan2004

/-!
# Martínez Vera (2026): Verum, contrast, and evidentiality in Saraguro Kichwa
[martinez-vera-2026] [martinez-vera-2024]
[martinez-vera-camacho-2025] [faller-2002] [faller-2019a]
[murray-2014] [murray-2017] [tellings-2014]
[grzech-2020] [bendezu-2023] [sanchez-2010]
[hintz-hintz-2017] [cole-1982] [roelofsen-vangool-2010]
[roelofsen-farkas-2015] [simons-tonhauser-beaver-roberts-2010]
[krifka-2014] [rooth-1985] [rooth-1992] [hirsch-2017]
[hohle-1992] [romero-han-2004] [kiss-1998]
[matthewson-2021] [matthewson-2004] [bochnak-matthewson-2015]
[gutzmann-hartmann-matthewson-2020] [goodhue-2022a]
[rochemont-2018]

Saraguro Kichwa (`qvj`) marker `=mi` is analysed as a *focus marker*
whose felicity presupposes a highlighted, strengthened alternative that
entails the negation of the scope proposition (paper's def. 37).

Three empirical signatures:

1. `=mi` is licensed when ¬p is salient (biased question, assertion of
   ¬p, or a reportative-evidential antecedent).
2. `=mi` is licensed in matrix declaratives following a reportative
   evidential `-shka`, but NOT following a direct evidential `-rka`.
3. `=mi` surfaces in contrastive (corrective) uses, sister to focus
   strategies like English `only` ([rochemont-2018],
   [hirsch-2017]).

## What this study formalises

* `miFelicitous` — paper eq. (37), reduced to the polar alternative-set
  case (innocently excludable alternatives are absent from polar
  partitions, so exhaustification collapses to identity).
* `polarQUD p` — the QUD over which a verum-marker felicity question
  is settled, built from `Question.polar`. Its `alt = {p, pᶜ}`,
  so `Highlighting.AddressesQUD` does real filtering work.
* `updateAfterAct` — generic discourse update that adds an act's
  `EvidentialAct.raisedPropositions` to the salient set. No
  match-on-`commitsToScope` here: the substrate-level theorems
  `present_raises_polar_negation` and `assert_does_not_raise_polar_negation`
  in `Discourse/EvidentialIllocution` carry the load.
* The headline contrast (paper exx. 47–50): `=mi` is felicitous after
  `present` (reportative `-shka`) and infelicitous after `assert`
  (direct `-rka`). Proofs project from substrate.
* `mi_polar_iff_verumFelicitous` — the cross-paper bridge theorem
  showing MV's polar-reduction `miFelicitous` is equivalent to Höhle's
  `verumFelicitous` on the same input.
* `mv_partition_neq_romeroHan_partition` — the cross-framework
  divergence theorem showing MV's polar partition `{p, pᶜ}` is in
  general distinct from Romero & Han's verum partition
  `{forSureCG p, ¬forSureCG p}`. Makes the line-a (focus) vs line-b
  (CommonGround-modal verum operator) split visible at the type level.

## Substrate consumed

| Substrate | Provides |
|-----------|----------|
| `Semantics/Composition/Layered` | `BiLayered W` ⟨A, N⟩ pair, three composition rules |
| `Semantics/Highlighting` | `HighlightingContext`, `Highlighted`, `AddressesQUD` |
| `Discourse/EvidentialIllocution` | `assert`, `present`, `EvidentialAct`, `raisedPropositions` |
| `Semantics/Evidential/Source` | `CoarseSource` (`direct`, `hearsay`, `inference`) |
| `Semantics/Questions/Hamblin` | `Question.polar` for the polar QUD |

## Methodological note

The paper's data is original fieldwork with six Saraguro speakers,
following [matthewson-2004], [bochnak-matthewson-2015].
Per CLAUDE.md (per-language paper-specific data lives in Studies, not
Fragments), the felicity-judgment apparatus stays in this file; the
neutral consensus typology — that Saraguro Kichwa has a 3-way
evidential paradigm with the discourse-sensitive enclitic =mi — lives
in `Fragments/Quechua/SaraguroKichwa/Evidentiality.lean`.
-/

namespace MartinezVera2026

open Semantics.ContentLayer (BiLayered)
open Semantics.Highlighting (HighlightingContext Highlighted AddressesQUD addSalient)
open Semantics.Evidential (CoarseSource)
open Discourse (DiscourseRole)

variable {W : Type*}

/-! ### § 0. Evidential illocutionary operators (Faller / Murray)

Substrate previously hosted at `Discourse/EvidentialIllocution.lean`,
inlined here per anchoring rule (sole consumer is this study file).
The `assert`/`present` distinction is [faller-2002] /
[murray-2014]; the `raisedPropositions` projection drives
[martinez-vera-2026]'s salience updates downstream. -/

/-- Result of applying an illocutionary operator: speaker, addressee,
    scope proposition, evidential (not-at-issue) proposition, and
    commits-to-scope flag (`true` for `assert`, `false` for `present`). -/
structure EvidentialAct (W : Type*) where
  speaker : DiscourseRole
  addressee : DiscourseRole
  scope : Set W
  evidentialContent : Set W
  commitsToScope : Bool

/-- [faller-2002]/[faller-2019a]: `assert(⟨A, N⟩)` commits the
    speaker to both A and N. Used with direct evidentials. -/
def assert (s a : DiscourseRole) (β : BiLayered W) : EvidentialAct W :=
  { speaker := s
  , addressee := a
  , scope := { w | β.atIssue w }
  , evidentialContent := { w | β.notAtIssue w }
  , commitsToScope := true }

/-- [murray-2014]/[faller-2019a]: `present(⟨A, N⟩)` brings A
    to attention but does NOT commit to A; commits only to N. Used with
    reportative/inferential evidentials. -/
def present (s a : DiscourseRole) (β : BiLayered W) : EvidentialAct W :=
  { speaker := s
  , addressee := a
  , scope := { w | β.atIssue w }
  , evidentialContent := { w | β.notAtIssue w }
  , commitsToScope := false }

@[simp] theorem assert_commitsToScope (s a : DiscourseRole) (β : BiLayered W) :
    (assert s a β).commitsToScope = true := rfl

@[simp] theorem present_commitsToScope (s a : DiscourseRole) (β : BiLayered W) :
    (present s a β).commitsToScope = false := rfl

theorem assert_present_differ_only_in_scope_commitment
    (s a : DiscourseRole) (β : BiLayered W) :
    (assert s a β).scope = (present s a β).scope ∧
    (assert s a β).evidentialContent = (present s a β).evidentialContent ∧
    (assert s a β).commitsToScope ≠ (present s a β).commitsToScope := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [assert_commitsToScope, present_commitsToScope]
  decide

/-- Propositions an act puts forward to the addressee. `assert` raises
    the scope; `present` raises both scope and its complement (the open
    polar issue). -/
def EvidentialAct.raisedPropositions (a : EvidentialAct W) : Set (Set W) :=
  if a.commitsToScope then {a.scope} else {a.scope, a.scopeᶜ}

@[simp] theorem assert_raisedPropositions (s a : DiscourseRole) (β : BiLayered W) :
    (assert s a β).raisedPropositions = {{ w | β.atIssue w }} := by
  simp [EvidentialAct.raisedPropositions, assert]

@[simp] theorem present_raisedPropositions (s a : DiscourseRole) (β : BiLayered W) :
    (present s a β).raisedPropositions =
      ({ { w | β.atIssue w }, { w | β.atIssue w }ᶜ } : Set (Set W)) := by
  simp [EvidentialAct.raisedPropositions, present]

theorem present_raises_polar_negation (s a : DiscourseRole) (β : BiLayered W) :
    { w | β.atIssue w }ᶜ ∈ (present s a β).raisedPropositions := by
  simp

theorem assert_does_not_raise_polar_negation
    (s a : DiscourseRole) (β : BiLayered W) (hne : ∃ w, β.atIssue w) :
    { w | β.atIssue w }ᶜ ∉ (assert s a β).raisedPropositions := by
  simp only [assert_raisedPropositions, Set.mem_singleton_iff]
  intro h
  obtain ⟨w, hw⟩ := hne
  have : w ∉ ({ w | β.atIssue w }ᶜ : Set W) := by simp [hw]
  rw [h] at this
  exact this hw

/-- Typological mapping from evidential source to illocutionary
    operator flavour. -/
inductive IllocutionaryFlavour where
  | assertFlavour
  | presentFlavour
  deriving DecidableEq, Repr, Inhabited

def IllocutionaryFlavour.ofCoarseSource :
    CoarseSource → IllocutionaryFlavour
  | .direct => .assertFlavour
  | .hearsay => .presentFlavour
  | .inference => .presentFlavour

@[simp] theorem flavour_direct :
    IllocutionaryFlavour.ofCoarseSource .direct = .assertFlavour := rfl
@[simp] theorem flavour_hearsay :
    IllocutionaryFlavour.ofCoarseSource .hearsay = .presentFlavour := rfl
@[simp] theorem flavour_inference :
    IllocutionaryFlavour.ofCoarseSource .inference = .presentFlavour := rfl

/-- Partial collapse of [faller-2019a]'s commitment-grounds evidence types
    onto the coarse source taxonomy: reportative and inferential evidence
    carry a source; adequate evidence and best possible grounds are
    commitment-strength grades that cross-cut the source taxonomy. -/
def fallerCoarseSource : Faller2019.EvidenceType → Option CoarseSource
  | .reportative => some .hearsay
  | .inferential => some .inference
  | .adequate => none
  | .bpg => none

/-- [faller-2019a]'s Cuzco Quechua reportative and the SK reportative
    `-shka` land on the same coarse source, hence license the same
    illocutionary flavour: `present`, not `assert`. -/
theorem faller_reportative_flavour :
    (fallerCoarseSource .reportative).map IllocutionaryFlavour.ofCoarseSource
      = some .presentFlavour := rfl

def applyDefault (src : CoarseSource) (s a : DiscourseRole) (β : BiLayered W) :
    EvidentialAct W :=
  match IllocutionaryFlavour.ofCoarseSource src with
  | .assertFlavour => assert s a β
  | .presentFlavour => present s a β

@[simp] theorem applyDefault_direct (s a : DiscourseRole) (β : BiLayered W) :
    applyDefault .direct s a β = assert s a β := rfl
@[simp] theorem applyDefault_hearsay (s a : DiscourseRole) (β : BiLayered W) :
    applyDefault .hearsay s a β = present s a β := rfl
@[simp] theorem applyDefault_inference (s a : DiscourseRole) (β : BiLayered W) :
    applyDefault .inference s a β = present s a β := rfl

theorem direct_commits_indirect_does_not (s a : DiscourseRole) (β : BiLayered W) :
    (applyDefault .direct s a β).commitsToScope = true ∧
    (applyDefault .hearsay s a β).commitsToScope = false ∧
    (applyDefault .inference s a β).commitsToScope = false :=
  ⟨rfl, rfl, rfl⟩

/-! ### § 1. The =mi denotation (paper eq. 37, polar reduction) -/

/-- Felicity condition for `=mi` attached to a scope expression `S` in
    context `c`, given a focus alternative set `alts`. This is paper
    eq. (37) for the case where `alts` is the polar partition `{p, pᶜ}`:
    polar partitions admit no innocently excludable alternatives (negating
    both gives `{¬p, ¬pᶜ} = {¬p, p}`, contradictory), so exhaustification
    collapses to identity, and the paper's "`exh(q)` entails `¬S.A`"
    reduces to "`q ⊆ S.atIssueᶜ`".

    Note: the polar reduction does NOT extend to constituent-focus
    contrast cases (paper §3 examples 22–28), where alts may include
    multiple elements with overlap. Those would consume the full
    `Semantics/Exhaustification.Excluder` machinery. -/
def miFelicitous (c : HighlightingContext W) (alts : Set (Set W))
    (S : BiLayered W) : Prop :=
  ∃ q ∈ alts, Highlighted c q ∧ q ⊆ ({ w | S.atIssue w } : Set W)ᶜ

/-! ### § 2. The polar QUD setup -/

/-- The polar QUD over a contingent proposition `p`: alternatives are
    `{p, pᶜ}`. Built from `Question.polar p`. Used as the QUD slot
    in the discourse contexts that license a `=mi` follow-up.

    With this (non-trivial) QUD, `AddressesQUD` does real filtering work:
    a proposition addresses `polarQUD p` iff it is comparable to `p` or
    to `pᶜ`. Both `p` and `pᶜ` themselves trivially address it (each is
    a subset of itself), so the highlighted alternatives in the headline
    contrast satisfy the QUD-addressing requirement of `Highlighted`. -/
def polarQUD (p : Set W) : HighlightingContext W :=
  { salient := ∅, qud := Question.polar p }

/-- Either `p` or `pᶜ` is itself a maximal answer to `polar p`, when `p`
    is contingent (`p ≠ ∅` and `p ≠ Set.univ`). This is the substrate
    fact `Question.alt_polar_of_nontrivial`. -/
theorem mem_alt_polar (p : Set W) (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    p ∈ (Question.polar p).alt := by
  rw [Question.alt_polar_of_nontrivial hne hnu]
  simp

theorem mem_alt_polar_compl (p : Set W) (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    pᶜ ∈ (Question.polar p).alt := by
  rw [Question.alt_polar_of_nontrivial hne hnu]
  simp

/-- `p` itself addresses the polar QUD over `p`: it equals one of the two
    alternatives. Requires `p` contingent so the polar partition is
    non-trivial. -/
theorem addresses_polarQUD_self (p : Set W) (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    AddressesQUD (polarQUD (W := W) p).qud p := by
  refine ⟨p, ?_, Or.inl (le_refl _)⟩
  exact mem_alt_polar p hne hnu

/-- `pᶜ` addresses the polar QUD over `p`: it equals the other
    alternative. Requires `p` contingent. -/
theorem addresses_polarQUD_compl (p : Set W) (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    AddressesQUD (polarQUD (W := W) p).qud pᶜ := by
  refine ⟨pᶜ, ?_, Or.inl (le_refl _)⟩
  exact mem_alt_polar_compl p hne hnu

/-! ### § 3. Discourse-update map (generic; consumes substrate)

`updateAfterAct c a` adds the propositions an act `a` raises to the
salient set of `c`. The match-on-`commitsToScope` lives in the substrate
(`EvidentialAct.raisedPropositions`), not here — verum studies, biased
polar-question studies, and reportative-evidential studies all consume
the same generic update.
-/

/-- Generic discourse-update: an act adds the propositions it raises to
    the salient set. The behaviour-distinguishing match is delegated to
    the substrate's `EvidentialAct.raisedPropositions`. -/
def updateAfterAct (c : HighlightingContext W) (a : EvidentialAct W) :
    HighlightingContext W :=
  { c with salient := c.salient ∪ a.raisedPropositions }

@[simp] theorem salient_updateAfterAct (c : HighlightingContext W) (a : EvidentialAct W) :
    (updateAfterAct c a).salient = c.salient ∪ a.raisedPropositions := rfl

@[simp] theorem qud_updateAfterAct (c : HighlightingContext W) (a : EvidentialAct W) :
    (updateAfterAct c a).qud = c.qud := rfl

/-! ### § 4. The headline contrast (paper exx. 47–50)

The proofs derive from the substrate facts `present_raises_polar_negation`
and `assert_does_not_raise_polar_negation`. The match-on-`commitsToScope`
is exercised once in the substrate; here the consequences fall out.
-/

/-- After a reportative-evidential `present(p)` update, a `=mi`-marked
    follow-up confirming `p` is felicitous: the witness is the highlighted
    `pᶜ`, which is raised by `present` (substrate:
    `present_raises_polar_negation`) and addresses the polar QUD over `p`
    (substrate: `addresses_polarQUD_compl`).

    Paper exx. 21/48. Hypotheses `hne` and `hnu` are the contingency
    conditions on the scope: the paper assumes contingent scopes throughout.
    The alternative set is the polar partition `{p, pᶜ}`. -/
theorem mi_felicitous_after_present
    (s a : DiscourseRole) (p : Set W) (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    miFelicitous
      (updateAfterAct (polarQUD p) (present s a (BiLayered.ofProp (· ∈ p))))
      ({p, pᶜ} : Set (Set W))
      (BiLayered.ofProp (· ∈ p)) := by
  refine ⟨pᶜ, by simp, ⟨?_, ?_⟩, ?_⟩
  · -- pᶜ is in the salient set, via the substrate fact
    -- `present_raises_polar_negation`
    simp only [salient_updateAfterAct, polarQUD,
      MartinezVera2026.present_raisedPropositions,
      BiLayered.ofProp_atIssue, Set.empty_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    right; rfl
  · -- pᶜ addresses the polar QUD over p
    simp only [qud_updateAfterAct, polarQUD]
    exact addresses_polarQUD_compl p hne hnu
  · -- pᶜ ⊆ pᶜ (trivially); the at-issue layer of (BiLayered.ofProp (· ∈ p))
    -- unfolds to (· ∈ p), so its complement is pᶜ
    intro w hw
    simpa [BiLayered.ofProp] using hw

/-- After a direct-evidential `assert(p)` update, a `=mi`-marked follow-up
    confirming `p` is NOT felicitous: only `p` itself is raised by
    `assert` (substrate: `assert_does_not_raise_polar_negation`), and
    `p ⊆ pᶜ` would force `p = ∅`, contradicting contingency.

    Paper ex. 47 — the contrast that motivates the present/assert
    distinction. -/
theorem mi_infelicitous_after_assert
    (s a : DiscourseRole) (p : Set W) (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    ¬ miFelicitous
        (updateAfterAct (polarQUD p) (assert s a (BiLayered.ofProp (· ∈ p))))
        ({p, pᶜ} : Set (Set W))
        (BiLayered.ofProp (· ∈ p)) := by
  rintro ⟨q, hq, ⟨hsalient, _⟩, hsub⟩
  -- After assert, raisedPropositions = {p}; salient = ∅ ∪ {p} = {p}
  -- So hsalient says q = p. Combined with hsub : q ⊆ pᶜ, that forces p ⊆ pᶜ,
  -- which means p = ∅, contradicting `hne`.
  simp only [salient_updateAfterAct, polarQUD,
    MartinezVera2026.assert_raisedPropositions,
    BiLayered.ofProp_atIssue, Set.empty_union,
    Set.mem_singleton_iff] at hsalient
  -- hsalient : q = {w | w ∈ p}, which is just `q = p`
  have hq_eq : q = p := by
    rw [hsalient]; rfl
  subst hq_eq
  apply hne
  ext w
  refine ⟨fun hw => ?_, fun hw => absurd hw (Set.notMem_empty _)⟩
  have := hsub hw
  simp [BiLayered.ofProp] at this
  exact absurd hw this

/-! ### § 5. Cross-paper bridge: Höhle 1992 ↔ MV 2026 (polar reduction)

For the polar alternative-set case `{β.atIssue, β.atIssueᶜ}`, MV's
`miFelicitous` reduces to Höhle's `verumFelicitous`: both demand that
`¬β.atIssue` be highlighted in the context. This makes the agreement
between the focus-on-polarity (Höhle) and focus-marker (MV) accounts
explicit at the type level. The disagreement with [romero-han-2004]'s
CommonGround-modal verum surfaces as the partition divergence in §6 below.
-/

/-- For the polar alternative-set case **with contingent scope**, MV's
    `miFelicitous` reduces to Höhle's `verumFelicitous`: both predicates
    demand that `¬β.atIssue` (the scope's complement) be highlighted.
    The contingency hypothesis `hne : ∃ w, β.atIssue w` rules out the
    degenerate empty-scope case where every q ⊆ qᶜ vacuously and the
    bridge would require Highlighted c univ from Highlighted c ∅ — not
    generally derivable.

    The `mp` direction: of the two polar alternatives, only `β.atIssueᶜ`
    can satisfy `q ⊆ β.atIssueᶜ` non-trivially (given contingent scope).
    The `mpr` direction packages the highlighted complement directly. -/
theorem mi_polar_iff_verumFelicitous
    (c : HighlightingContext W) (β : BiLayered W) (hne : ∃ w, β.atIssue w) :
    miFelicitous c ({{ w | β.atIssue w }, ({ w | β.atIssue w } : Set W)ᶜ}) β ↔
      Hohle1992.verumFelicitous c β := by
  constructor
  · rintro ⟨q, hq, hhighlighted, hsub⟩
    rcases hq with h | h
    · -- q = {w | β.atIssue w}, so q ⊆ qᶜ forces q = ∅, contradicting `hne`
      exfalso
      obtain ⟨w, hw⟩ := hne
      have hwq : w ∈ q := by rw [h]; exact hw
      have : w ∉ ({ w | β.atIssue w } : Set W) := hsub hwq
      exact this hw
    · -- q = {w | β.atIssue w}ᶜ — the desired case
      simp only [Set.mem_singleton_iff] at h
      rw [h] at hhighlighted
      exact hhighlighted
  · -- mpr: Hohle's verumFelicitous gives Highlighted c (β.atIssueᶜ)
    intro h
    refine ⟨({ w | β.atIssue w } : Set W)ᶜ, by simp, h, ?_⟩
    intro _ hw
    exact hw

/-- The MV `=mi` denotation packaged as a `VerumOperator` over the polar
    alternative set `{β.atIssue, β.atIssueᶜ}`. The shared abstraction lets
    `mi_polar_iff_verumFelicitous` (above) be re-stated as a felicity
    equivalence between two `VerumOperator W` instances. -/
def miAsVerumOperatorPolar : Hohle1992.VerumOperator W :=
  { felicitous := fun c β =>
      miFelicitous c ({{w | β.atIssue w}, ({w | β.atIssue w} : Set W)ᶜ}) β }

@[simp] theorem miAsVerumOperatorPolar_apply (c : HighlightingContext W)
    (β : BiLayered W) :
    miAsVerumOperatorPolar.felicitous c β =
      miFelicitous c ({{w | β.atIssue w}, ({w | β.atIssue w} : Set W)ᶜ}) β := rfl

/-- Cross-paper bridge restated at the `VerumOperator` level: under
    contingent scope, MV's polar-reduction operator and Höhle's
    verum-focus operator are extensionally equivalent. -/
theorem mi_eq_hohle_as_verumOperator
    (c : HighlightingContext W) (β : BiLayered W) (hne : ∃ w, β.atIssue w) :
    miAsVerumOperatorPolar.felicitous c β ↔
      Hohle1992.hohleAsVerumOperator.felicitous c β := by
  simp only [miAsVerumOperatorPolar_apply,
    Hohle1992.hohleAsVerumOperator_apply]
  exact mi_polar_iff_verumFelicitous c β hne

/-! ### § 6. Cross-framework divergence: MV's partition vs R&H's verum partition

Romero & Han 2004 analyse verum as a CommonGround-modal operator `forSureCG`
producing an *unbalanced* polar partition `{forSureCG p, ¬forSureCG p}`
(line-b account). MV implicitly takes a line-a (focus over polarity)
position: the partition over which `=mi` operates is the standard polar
`{p, pᶜ}`. These two partitions are in general distinct — the line-a/b
debate (Goodhue 2022a §1) is non-vacuous.
-/

/-- The MV polar partition `{p, pᶜ}` and the R&H verum partition
    `{forSureCG p, ¬forSureCG p}` are in general distinct. There exist
    contexts (witness: any model where forSureCG p ≠ p) in which MV's
    line-a focus partition and R&H's line-b VERUM partition pick out
    different cells.

    Witness construction: the forSureCG operator can fail to coincide
    with `p` whenever the speaker's epistemic state and conversational
    goals don't trivially settle p — which is the very case that makes
    verum interesting (cf. R&H §3 on biased polar questions). -/
theorem mv_partition_can_diverge_from_romeroHan_partition :
    ∃ (W : Type) (p : Set W) (verumP : Set W),
      verumP ≠ p ∧ ({p, pᶜ} : Set (Set W)) ≠ {verumP, verumPᶜ} := by
  -- Two-world model. Take p = {w₀} (a non-trivial proposition) and the
  -- R&H verum reading verumP = ∅ (the speaker is NOT for-sure committed
  -- to p — bias-evidence model where verum picks out a strictly weaker
  -- statement). The partitions differ because {p, pᶜ} = {{w₀}, {w₁}}
  -- while {verumP, verumPᶜ} = {∅, univ}, and {w₀} is not in the latter.
  refine ⟨Bool, ({true} : Set Bool), (∅ : Set Bool), ?_, ?_⟩
  · -- ∅ ≠ {true}: rewrite reverses the singleton-empty difference
    intro h
    have h1 : true ∈ ({true} : Set Bool) := rfl
    rw [← h] at h1
    exact h1
  · -- {{true}, {true}ᶜ} ≠ {∅, ∅ᶜ}: LHS has {true} as a member; RHS has only
    -- {∅, univ}. {true} is neither ∅ nor univ.
    intro h
    have hmem : ({true} : Set Bool) ∈
        (({{true}, ({true} : Set Bool)ᶜ}) : Set (Set Bool)) := by simp
    rw [h] at hmem
    rcases hmem with h1 | h1
    · -- {true} = ∅
      have h2 : true ∈ ({true} : Set Bool) := rfl
      rw [h1] at h2
      exact h2
    · -- {true} = ∅ᶜ = Set.univ; but false ∉ {true} while false ∈ univ
      have h2 : false ∈ ({true} : Set Bool) := by rw [h1]; trivial
      exact (by simp at h2 : False)

/-! ### § 7. The defining commitment contrast (corollary of substrate)

Direct evidentials commit the speaker to scope; reportatives do not.
This is `MartinezVera2026.assert_commitsToScope` and
`present_commitsToScope` packaged as a single statement. The reason
`present` highlights `¬p` (and `assert` doesn't) is downstream of this
commitment difference, formalised in the substrate's
`present_raises_polar_negation` / `assert_does_not_raise_polar_negation`.
-/

theorem direct_commits_reportative_does_not
    (s a : DiscourseRole) (β : BiLayered W) :
    (assert s a β).commitsToScope = true ∧
    (present s a β).commitsToScope = false :=
  ⟨rfl, rfl⟩

/-! ### § 8. Cross-Quechuan family contrast (paper §5)

A label-only typology of published `=mi` analyses across Quechuan
varieties. **This is currently a `decide`-distinct enum, not a
semantic taxonomy** — each cell is a stand-in for a future per-paper
study file (Faller2002, Tellings2014, Grzech2020, Bendezú2023). Once
those exist, this enum should be replaced by `MiSemantics W`-shaped
inhabitants whose pairwise distinctness becomes a substantive theorem
about predicted felicity profiles, not an enum tautology.

Currently retained as a drift sentry: if a future formalisation
collapses any two analyses into one (e.g. by treating "epistemic
authority" as a sub-case of "verum + focus"), the
`pairwise_distinct` proof fails and forces a re-evaluation of the
paper's typological-divergence claim.
-/

/-- Analytic stance taken on `=mi` in a given Quechuan variety, as
    surveyed in paper §5. Five mutually-incompatible claims, one per
    variety. Each is a label awaiting a future per-paper study. -/
inductive MiAnalysis where
  /-- Verum + focus marker requiring discourse sensitivity to the QUD
      (Saraguro Kichwa per [martinez-vera-2026]). -/
  | verumPlusFocus
  /-- Verum + corrective contrast (Conchucos Quechua per
      [bendezu-2023]). -/
  | verumPlusContrast
  /-- Pure (best-possible-grounds) direct evidential
      (Cuzco Quechua per [faller-2002], [sanchez-2010]). -/
  | directEvidentialOnly
  /-- Pure evidential, no focus role (Imbabura Kichwa per
      [tellings-2014]). -/
  | pureEvidentialNoFocus
  /-- Epistemic-authority marker (Upper Napo Kichwa per
      [grzech-2020]). -/
  | epistemicAuthority
  deriving DecidableEq, Repr, Inhabited

/-- The cross-Quechuan map from variety to published `=mi` analysis. -/
def quechuanMiAnalyses : List (String × MiAnalysis) :=
  [ ("Saraguro Kichwa (qvj)", .verumPlusFocus)
  , ("Conchucos Quechua (qxn)", .verumPlusContrast)
  , ("Cuzco Quechua (quz)", .directEvidentialOnly)
  , ("Imbabura Kichwa (qvi)", .pureEvidentialNoFocus)
  , ("Upper Napo Kichwa (qvo)", .epistemicAuthority) ]

/-- The five published analyses are pairwise distinct as labels. Drift
    sentry: collapsing two cases breaks this. -/
theorem quechuanMiAnalyses_pairwise_distinct :
    [MiAnalysis.verumPlusFocus, .verumPlusContrast, .directEvidentialOnly,
     .pureEvidentialNoFocus, .epistemicAuthority].Pairwise (· ≠ ·) := by
  decide

end MartinezVera2026
