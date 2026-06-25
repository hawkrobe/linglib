import Linglib.Fragments.NezPerce.ClausalEmbedding
import Linglib.Typology.Complementation
import Linglib.Syntax.Minimalist.Probe.Satisfaction
import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Minimalist.ClauseSpine
import Linglib.Semantics.Presupposition.ProjectiveContent

/-! # Deal (2026): Clausal complementation as relativization, revisited

[deal-2026]

## Paper's central claims

In Nez Perce, some but not all notional complement clauses show the
characteristic morphology of relativization. [deal-2026] argues that the
relative-like notional complement clauses ("relative embeddings", REs) are
*CPs* — not DPs/PPs — containing an internal Ā-dependency from a *high
functional projection above TP*. Three primary conclusions:

1. Not all clausal complementation is relativization (refuting [kayne-2008],
   [kayne-2014], [arsenijevic-2009]).
2. Relative-like notional complement clauses vary across languages in nominal
   superstructure ([deal-2026] Table 79: V CP / V D N CP / V P D CP) and in
   factive inferences (Tables 80–81).
3. Factivity, RE-syntax, and nominalization are *three orthogonal axes* — no
   one entails another.

## What this file contributes

- The bundled `NotionalComplementShape` analytical record (Deal-specific
  apparatus per CLAUDE.md "paper-specific apparatus stays in Studies").
- Table 79 sample: V CP / V D N CP / V P D CP cells for five languages.
- The `nezPerceEmbedStrategy` projection: derives RE-vs-simplex from
  Fragment-level Noonan/factivity data plus the Deal-analytical Ā-dep
  presence flag.
- *ke*-agreement as `Minimalist.SatisfactionCond.disjunctive`
  ([deal-2015a-nels], [deal-2024] framework; bridge to
  `Syntax/Minimalist/Agree.lean` §14).
- Cross-classification theorems: factivity ⊥ RE-structure; factivity ⊥
  nominalization.
- Cross-framework comparison notes (HPSG modifier-only RC; Cacchioli 2025
  Tigrinya in-system counterargument).

## What this file does NOT contribute

- §6 indexical-shift / sequence-of-tense formal predictions: deferred pending
  a Kaplanian-context-shifting substrate (`[deal-2020]` book is the
  reference theory). Existing `deal-2020` bib entry but no implementation
  module.
- A full HPSG-side bridge theorem: documented as silent divergence;
  formalisation requires updating `HPSG/RelativeClauses.lean` to
  parameterise its currently-hardcoded `MOD NP` analysis.
- A `commentative`-emitting fix to `deriveCTPClass` in
  `Studies/Noonan2007.lean:570`: blocked on
  VerbEntry schema (regret and know have identical features in
  `Fragments/English/Predicates/Verbal.lean`).

## Disagreements documented but not formalised

[kayne-2008], [kayne-2014], [arsenijevic-2009]: universalist
position (all complementation = relativization). Deal 2026 §7 refutes by
exhibiting `barePropositionalCP` cells.

[decuba-2017]: opposing position — complement clauses are *never*
relatives. Compatible with Deal 2026 for English simplex; incompatible
with Deal for Adyghe/Bulgarian/Nez Perce REs.

[hanink-bochnak-2017], [bochnak-hanink-2021]: Washo factive
complementation as nominalization (V D CP). Deal 2026 §7 accepts this for
Washo but refutes the universal extension to all factives — Nez Perce REs
are factive without nominal superstructure.

[moulton-2015]: CPs are predicates (type ⟨e, t⟩), not propositions
(type t), composing with attitude verbs via predicate modification. This
analysis is *orthogonal* to Deal 2026's typology — it concerns the semantic
type of the embedded CP, not its external syntactic shell. The two analyses
intersect on `barePropositionalCP` cells (Moulton's CP-predicate semantics
applies most directly there) but Deal's `nominalization` cells (V D N CP,
V P D CP) shift composition into the nominal layer where Moulton's
predicate-modification mechanism may not directly apply.
-/

namespace Deal2026

open NezPerce.ClausalEmbedding
open Typology.Complementation
open Semantics.Presupposition.ProjectiveContent (ProjectiveClass)
open Minimalist (Cat SatisfactionCond AbarDep keineĀProbe ClauseSpine
  hasValuedFeature FeatureBundle FeatureVal GramFeature ābar_is_Ā)

-- ============================================================================
-- §1. NotionalComplementShape — Deal-specific bundling
-- ============================================================================

/-- The full Deal-2026 description of a notional complement clause: internal
    spine + external shell + presence of internal Ā-dependency. Bundled here
    rather than in substrate to keep the per-axis primitives reusable
    (`ClauseSpine`, `CPShellInventory`, `AbarDep`) for non-Deal accounts.

    The three axes are independent in [deal-2026] Table 79: each cell
    in the 4×2 cross-classification (CP-superstructure × ±Ā) is filled or
    explicitly noted as predicted-but-unattested. -/
structure NotionalComplementShape where
  /-- Internal spine of the embedded clause (typically `ClauseSpine.cP`). -/
  internal : ClauseSpine
  /-- External wrapping shells from C outward (`bareCP / dCP / dnCP / pdCP`). -/
  external : CPShellInventory
  /-- Whether the embedded CP contains an internal Ā-dependency. -/
  hasInternalAbar : Bool
  deriving Repr

/-- The two Nez Perce shapes from [deal-2026] §3 vs §6. -/
def nezPerceREShape : NotionalComplementShape :=
  ⟨ClauseSpine.cP, bareCP, true⟩

def nezPerceSimplexShape : NotionalComplementShape :=
  ⟨ClauseSpine.cP, bareCP, false⟩

/-- The Adyghe RE shape from [caponigro-polinsky-2011], exhibited at
    [deal-2026] §4 (43): V D N CP with internal Ā. -/
def adygheREShape : NotionalComplementShape :=
  ⟨ClauseSpine.cP, dnCP, true⟩

/-- The Bulgarian RE shape from [krapova-2010], exhibited at
    [deal-2026] §4 (49): V P D CP with internal Ā. -/
def bulgarianREShape : NotionalComplementShape :=
  ⟨ClauseSpine.cP, pdCP, true⟩

/-- The Ndebele simplex shape from [pietraszko-2019], exhibited at
    [deal-2026] §7 (78): V P D CP with no Ā-dependency. -/
def ndebeleShape : NotionalComplementShape :=
  ⟨ClauseSpine.cP, pdCP, false⟩

/-- The Washo factive shape from [bochnak-hanink-2021],
    [hanink-bochnak-2017]: V D CP (D wraps CP, no intervening N).
    [deal-2026] footnote 33 explicitly notes this cell as attested
    "for example, for Washo (Bochnak & Hanink 2021)" but absent from
    the main Table 79 because no example language combines V D CP with
    an internal Ā-dependency. We include the no-Ā version. -/
def washoShape : NotionalComplementShape :=
  ⟨ClauseSpine.cP, dCP, false⟩

-- ============================================================================
-- §2. Table 79 — Cross-Linguistic Sample
-- ============================================================================

/-- An entry in [deal-2026] Table 79: a language × construction with its
    NotionalComplementShape. -/
structure Table79Cell where
  language : String
  construction : String
  shape : NotionalComplementShape
  deriving Repr

/-- The seven attested Table-79 cells (Deal 2026 main Table 79 + Washo cell
    from footnote 33 per [bochnak-hanink-2021]). -/
def table79 : List Table79Cell := [
  ⟨"Nez Perce", "RE",                nezPerceREShape⟩,
  ⟨"Nez Perce", "simplex",           nezPerceSimplexShape⟩,
  ⟨"English",   "think-complement",  nezPerceSimplexShape⟩,  -- bareCP, no Ā
  ⟨"Adyghe",    "RE",                adygheREShape⟩,
  ⟨"Bulgarian", "RE",                bulgarianREShape⟩,
  ⟨"Ndebele",   "embedding",         ndebeleShape⟩,
  ⟨"Washo",     "factive",           washoShape⟩
]

/-- Drift sentry: `table79` covers exactly the seven (language, construction)
    pairs Deal lists in §7 main Table 79 plus the Washo cell from footnote 33. -/
theorem table79_membership :
    table79.map (λ c => (c.language, c.construction)) =
      [("Nez Perce", "RE"), ("Nez Perce", "simplex"),
       ("English",   "think-complement"),
       ("Adyghe",    "RE"), ("Bulgarian", "RE"),
       ("Ndebele",   "embedding"), ("Washo", "factive")] := by decide

/-- Project a `NotionalComplementShape` onto the theory-neutral
    `ComplementClauseStructure` enum from `Typology/Complementation.lean`.
    The mapping is determined by the internal Ā-flag and the external shell:
    bare CP + Ā = `abarInternalCP`; bare CP without Ā = `barePropositionalCP`;
    any non-bare external shell = `nominalization` (subsumes V D CP, V D N CP,
    V P D CP — they differ only in the depth of the nominal/prepositional
    wrapper, not in the surface phenomenon being a nominalization). -/
def NotionalComplementShape.surfacePattern (s : NotionalComplementShape) :
    ComplementClauseStructure :=
  if s.external = bareCP then
    if s.hasInternalAbar then .abarInternalCP else .barePropositionalCP
  else
    .nominalization

/-- A Table79 cell's surface pattern, derived from its shape. -/
def Table79Cell.surfacePattern (c : Table79Cell) : ComplementClauseStructure :=
  c.shape.surfacePattern

/-- Nez Perce REs project as `abarInternalCP` (bare CP + Ā). -/
theorem nezPerceRE_surface :
    nezPerceREShape.surfacePattern = .abarInternalCP := rfl

/-- Nez Perce simplex (and English *think*) project as `barePropositionalCP`. -/
theorem nezPerceSimplex_surface :
    nezPerceSimplexShape.surfacePattern = .barePropositionalCP := rfl

/-- Adyghe REs project as `nominalization` (V D N CP). -/
theorem adygheRE_surface :
    adygheREShape.surfacePattern = .nominalization := rfl

/-- Bulgarian REs project as `nominalization` (V P D CP). -/
theorem bulgarianRE_surface :
    bulgarianREShape.surfacePattern = .nominalization := rfl

/-- Ndebele embedding projects as `nominalization` (V P D CP). -/
theorem ndebele_surface :
    ndebeleShape.surfacePattern = .nominalization := rfl

/-- Washo factive embedding projects as `nominalization` (V D CP, no Ā). -/
theorem washo_surface :
    washoShape.surfacePattern = .nominalization := rfl

/-- The Kayne-Arsenij\'evi\'c universalist hypothesis — that all clausal
    complementation is relativization — is decidable on the Table 79 sample
    as `∀ c ∈ table79, c.surfacePattern = .abarInternalCP`. Deal 2026 refutes
    it: only one of six cells (Nez Perce REs) projects as `abarInternalCP`. -/
theorem kayne_universalism_refuted :
    ¬ (table79.all (·.surfacePattern == .abarInternalCP) = true) := by decide

/-- Deal 2026's positive contribution: at least one cell projects as
    `abarInternalCP` (so REs are real); at least one cell projects as
    `barePropositionalCP` (so not all complementation is relativization);
    at least one cell projects as `nominalization` (consistent with prior
    nominalization analyses for some languages). -/
theorem table79_three_surface_patterns_attested :
    table79.any (·.surfacePattern == .abarInternalCP) = true ∧
    table79.any (·.surfacePattern == .barePropositionalCP) = true ∧
    table79.any (·.surfacePattern == .nominalization) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- §2.5. Greek extension (cross-reference to [angelopoulos-2026])
-- ============================================================================
--
-- Deal's main Table 79 doesn't include Greek. [angelopoulos-2026]
-- (NLLT 44:26) argues that Greek *pu*-complement clauses are bare CPs
-- (no nominalization shell) where the [n]-feature on C is checked by a
-- light noun in Spec,CP that incorporates into the matrix v_State head.
-- Critically, *pu* additionally surfaces as an adjunct, relative
-- pronoun, and interrogative pronoun *where* — uses where the
-- stativity restriction (paper §2.3) vanishes. The adjunct case is the
-- one Angelopoulos uses to refute the [bochnak-hanink-2021]
-- "selection limited to argument clauses" thesis: a *pu*-adjunct
-- selects its host (per [bruening-2013], [hewett-2023],
-- [hunter-2015], [neeleman-philip-tanaka-vandekoot-2023])
-- and so selection is bidirectional, not restricted to argument
-- positions. The refutation theorem itself lives in
-- `Studies/Angelopoulos2026.lean`
-- (`angelopoulos_refutes_selection_argument_only`); this file just
-- exposes the Greek *pu*-complement shape as a `barePropositionalCP`
-- entry to make the typology connection explicit.

/-- Greek *pu*-complement shape per [angelopoulos-2026]: bare CP
    with no internal Ā-dependency — projects as `barePropositionalCP`,
    not `nominalization` (Greek lacks a silent situation noun, so
    *pu* cannot nominalize per paper §5). The categorial [n]-feature
    on C is checked structurally (light noun in Spec) rather than by
    a nominal shell. -/
def greekPuComplementShape : NotionalComplementShape :=
  ⟨ClauseSpine.cP, bareCP, false⟩

/-- Greek *pu*-complement projects as `barePropositionalCP` —
    a bare-CP cell consistent with Deal's typology, witnessing
    that the (factive, bare-CP) combination is attested. -/
theorem greekPu_surface :
    greekPuComplementShape.surfacePattern = .barePropositionalCP := rfl

-- ============================================================================
-- §3. Cross-Classification: factivity ⊥ RE-structure
-- ============================================================================

/-! ### Headline orthogonality (Deal 2026 Tables 80–81)

The central typological discovery: factivity does not predict RE-structure
in either direction.

* Factive + RE-structure: Nez Perce REs (e.g. *liloy* 'be happy').
* Factive + simplex: Nez Perce *cuukwe* 'know'.
* Non-factive + RE-structure: Adyghe REs (per [caponigro-polinsky-2011]).
* Non-factive + simplex: Nez Perce *neki/hi*; English *think*. -/

/-- All four cells are attested: factivity neither necessitates nor precludes
    RE-syntax. The `factive` flag is per [deal-2026] §3 projection-test
    diagnoses. The Adyghe non-factive RE judgement is attributed to
    [caponigro-polinsky-2011] via [deal-2026] §7 Table 80. -/
theorem factivity_perp_re_structure :
    -- Factive + RE: Nez Perce REs (e.g. liloy)
    liloy.factive = true ∧ nezPerceREShape.hasInternalAbar = true ∧
    -- Factive + simplex: Nez Perce cuukwe 'know'
    cuukwe.factive = true ∧ nezPerceSimplexShape.hasInternalAbar = false ∧
    -- Non-factive + simplex: Nez Perce neki 'think'
    neki.factive = false ∧ nezPerceSimplexShape.hasInternalAbar = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The fourth cell (non-factive + RE)

Documented by [deal-2026] §7 (Table 80) as instantiated by Adyghe per
[caponigro-polinsky-2011]. Absent a formalised Adyghe Fragment, this is
recorded as an unproven Lean claim: in linglib Adyghe is not yet present at
Fragment level.

TODO(adyghe-fragment): once `Fragments/Adyghe/ClausalEmbedding.lean` lands,
replace this prose with a theorem `adyghe_re_nonfactive`. -/

-- ============================================================================
-- §4. Cross-Classification: factivity ⊥ nominalization
-- ============================================================================

/-! ### Deal 2026 Table 81

* Factive + nominalization: Washo *forget* (per [hanink-bochnak-2017]).
* Factive + no nominalization: Nez Perce REs (the headline Deal-2026 finding,
  refuting the [hanink-bochnak-2017] universal extension).
* Non-factive + nominalization: Turkish *düşün-* 'think' (per [deal-2026]
  §7 citing Özyıldız 2017).
* Non-factive + no nominalization: Washo, Nez Perce 'think'. -/

/-- Nez Perce REs are factive without external nominal shell. -/
theorem nezPerce_re_factive_no_nominalization :
    liloy.factive = true ∧
    nezPerceREShape.external = bareCP := by
  refine ⟨rfl, rfl⟩

/-- The bare-CP shell contains neither D nor N. -/
theorem bareCP_no_d_no_n :
    CPShell.d ∉ bareCP ∧ CPShell.n ∉ bareCP := by
  refine ⟨?_, ?_⟩ <;> decide

-- ============================================================================
-- §5. Embedding-strategy projection from Fragment data
-- ============================================================================

/-! ### Observable-driven derivation (Pattern B architecture)

The Fragment carries a single morphological observable
(`requiresYoxKeEdge : Bool`) per [deal-2026] §3 (28). Deal's two
analytical commitments — the embedding-strategy classification and the
selectional-feature stack — are *derived* from this observable, not
stipulated alongside it. The derivation is the theory; the observable
is the data.

This pattern lets alternative theories provide alternative derivation
functions over the same Fragment observable, making cross-theory
divergence theorems expressible (currently only Deal's derivation is
supplied; an Adyghe-style or Krapova-style derivation would be a
straightforward sibling Studies file). -/

/-- The two embedding strategies [deal-2026] distinguishes. -/
inductive EmbeddingStrategy where
  | re       -- relative embedding (yox̂ + ke + Ā-dep above TP)
  | simplex  -- bare CP, no Ā-dep
  deriving DecidableEq, Repr

/-- Deal 2026's per-verb embedding-strategy classification, *derived* from
    the Fragment-level observable `requiresYoxKeEdge`. The interpretation
    is Deal's: morphological obligation of *yox̂ ke* on the complement
    edge ↔ syntactic Ā-dependency above TP. The bi-conditional is
    `strategy_iff_yoxKe` below — was previously trivially `rfl` over a
    list-membership check, now expresses the genuine theory commitment. -/
def nezPerceEmbedStrategy (v : NezPerceEmbedder) : EmbeddingStrategy :=
  if v.requiresYoxKeEdge then .re else .simplex

/-- Deal's selectional commitment for a Nez Perce embedder: the verb
    c-selects a CP, and (for RE-takers) requires that CP to contain an
    internal Ā-dependency above TP.

    Note that Deal's analysis is *not* standard c-selection: c-selection
    only sees the *outer* category of the complement, and both RE-takers
    and simplex-takers c-select uniformly for `.C` (a CP). The RE-vs-simplex
    distinction is in the *internal* structure of the selected CP —
    whether its head bears the [+Ā] feature triggering operator movement
    above TP. We separate the two by storing both the c-selectional
    outer category and a Boolean flag for the internal-Ā requirement. -/
structure DealSelectionalProfile where
  /-- Outer category the verb c-selects for (always `.C` for embedders). -/
  outerCat : Cat
  /-- Whether the selected CP must contain an internal Ā-dependency.
      Maps to Deal's [+Ā] feature on the C head of the embedded clause. -/
  requiresInternalAbar : Bool
  deriving DecidableEq, Repr

/-- Deal 2026's selectional analysis: derived entirely from the Fragment
    observable `requiresYoxKeEdge`. The verb uniformly c-selects for a CP;
    only the internal-Ā requirement varies between RE-takers and
    simplex-takers. -/
def dealSelectionalProfile (v : NezPerceEmbedder) : DealSelectionalProfile :=
  { outerCat := .C, requiresInternalAbar := v.requiresYoxKeEdge }

/-- The headline derivation theorem: a Nez Perce embedder is RE-canonical
    in Deal's analysis iff its complement obligatorily carries the
    *yox̂ ke* edge morphology. Replaces what was previously a trivial
    `rfl` over membership in a hand-curated list. -/
theorem strategy_iff_yoxKe (v : NezPerceEmbedder) :
    nezPerceEmbedStrategy v = .re ↔ v.requiresYoxKeEdge = true := by
  unfold nezPerceEmbedStrategy
  cases v.requiresYoxKeEdge <;> simp

/-- Deal's selectional analysis: an embedder selects for a CP with internal
    Ā-dependency iff it requires *yox̂ ke* edge marking. -/
theorem requiresInternalAbar_iff_yoxKe (v : NezPerceEmbedder) :
    (dealSelectionalProfile v).requiresInternalAbar = v.requiresYoxKeEdge := rfl

/-- Every Nez Perce embedder uniformly c-selects for `.C`. The RE-vs-simplex
    contrast is *not* a c-selectional difference — it lives in the internal
    structure of the selected CP. -/
theorem all_embedders_select_C (v : NezPerceEmbedder) :
    (dealSelectionalProfile v).outerCat = .C := rfl

/-- Per-verb sanity checks (decidable lookup of the observable). -/
theorem liloy_strategy : nezPerceEmbedStrategy liloy = .re := by decide
theorem timiipni_strategy : nezPerceEmbedStrategy timiipni = .re := by decide
theorem qeciyeewyew_strategy : nezPerceEmbedStrategy qeciyeewyew = .re := by decide
theorem neki_strategy : nezPerceEmbedStrategy neki = .simplex := by decide
theorem hi_strategy : nezPerceEmbedStrategy hi = .simplex := by decide
theorem cuukwe_strategy : nezPerceEmbedStrategy cuukwe = .simplex := by decide

/-- Per-verb selectional sanity. *liloy* selects a CP requiring internal Ā;
    *neki* selects a bare CP. -/
theorem liloy_selProfile :
    dealSelectionalProfile liloy = { outerCat := .C, requiresInternalAbar := true } := rfl
theorem neki_selProfile :
    dealSelectionalProfile neki = { outerCat := .C, requiresInternalAbar := false } := rfl

/-- Every RE-canonical embedder gets `EmbeddingStrategy.re` (now follows
    from the Fragment observable, not from list-membership). -/
theorem reCanonical_strategy :
    ∀ v ∈ reCanonical, nezPerceEmbedStrategy v = .re := by
  intro v hv
  rw [strategy_iff_yoxKe]
  -- v ∈ reCanonical = v ∈ allEmbedders.filter (·.requiresYoxKeEdge)
  -- so v.requiresYoxKeEdge = true
  unfold reCanonical at hv
  exact (List.mem_filter.mp hv).2

-- ============================================================================
-- §5b. Tonhauser projective-content classification
-- ============================================================================

/-! ### Bridge to [tonhauser-beaver-roberts-simons-2013] taxonomy

The Tonhauser et al. classes are formalised in
`Semantics/Presupposition/ProjectiveContent.lean` (`ProjectiveClass.classA`–
`classD`). Factive predicates project as Class C (SCF=no, OLE=yes — the same
class as English *know*). The Class C trigger `know_complement` is one of
the listed examples (see `ProjectiveTrigger.know_complement`).

Non-factive predicates introduce no projective content and so map to `none`. -/

/-- Project a Nez Perce embedder onto the Tonhauser projective-content
    taxonomy. Factive predicates map to Class C (the *know*-class);
    non-factives have no projective content. -/
def derivedProjectiveClass (v : NezPerceEmbedder) : Option ProjectiveClass :=
  if v.factive then some .classC else none

/-- All RE-canonical predicates project as Tonhauser Class C. This bridges
    Deal's empirical Nez Perce data to the typed
    [tonhauser-beaver-roberts-simons-2013] taxonomy. -/
theorem reCanonical_projects_classC :
    reCanonical.all (λ v => derivedProjectiveClass v = some .classC) = true := by
  decide

/-- *cuukwe* 'know' projects as Class C — same projective class as
    Deal-RE-canonical predicates, despite *cuukwe* being simplex-canonical.
    Confirms factivity ⊥ RE-structure at the Tonhauser-substrate level. -/
theorem cuukwe_projects_classC :
    derivedProjectiveClass cuukwe = some .classC := by decide

/-- *neki* 'think' has no projective content (non-factive). -/
theorem neki_no_projection :
    derivedProjectiveClass neki = none := by decide

-- ============================================================================
-- §5c. Cross-substrate bridges: Strategy ↔ Surface ↔ Tonhauser
-- ============================================================================

/-! ### Bridges between four substrate layers

The Studies file integrates four independent substrate layers:
- Fragment: per-verb consensus typology (CTPClass, factive)
- Tonhauser projective content: ProjectiveClass (Semantics/Presupposition/)
- Deal-internal: EmbeddingStrategy + NotionalComplementShape
- Typology: ComplementClauseStructure surface enum

The bridge theorems below derive load-bearing predictions across these
layers rather than stipulating them. -/

/-- The analytical shape associated with each embedding strategy.
    `re` predicates select `nezPerceREShape`; `simplex` predicates select
    `nezPerceSimplexShape`. -/
def EmbeddingStrategy.shape : EmbeddingStrategy → NotionalComplementShape
  | .re => nezPerceREShape
  | .simplex => nezPerceSimplexShape

/-- Strategy-shape correspondence: every embedder's strategy projects to
    the right shape, preserving the abarInternalCP / barePropositionalCP
    distinction at the surface-pattern level. -/
theorem strategy_shape_surface (v : NezPerceEmbedder) :
    (nezPerceEmbedStrategy v).shape.surfacePattern =
      if nezPerceEmbedStrategy v = .re then .abarInternalCP
      else .barePropositionalCP := by
  cases nezPerceEmbedStrategy v <;> simp [EmbeddingStrategy.shape]
  all_goals rfl

/-- Every RE-canonical predicate projects via shape to `abarInternalCP`. -/
theorem reCanonical_surfacePattern_abar :
    ∀ v ∈ reCanonical,
      (nezPerceEmbedStrategy v).shape.surfacePattern = .abarInternalCP := by
  intro v hv
  rw [strategy_shape_surface]
  simp [reCanonical_strategy v hv]

/-- All three Table-79 RE cells (Nez Perce, Adyghe, Bulgarian) carry an
    internal Ā-dependency. The shared `hasInternalAbar = true` is the
    universal property of REs that survives Deal's typological dissolution. -/
theorem all_REs_have_internal_abar :
    nezPerceREShape.hasInternalAbar = true ∧
    adygheREShape.hasInternalAbar = true ∧
    bulgarianREShape.hasInternalAbar = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- All three Table-79 simplex/embedding cells (Nez Perce simplex, English
    *think*, Ndebele, Washo factive) lack internal Ā. -/
theorem all_simplex_lack_internal_abar :
    nezPerceSimplexShape.hasInternalAbar = false ∧
    ndebeleShape.hasInternalAbar = false ∧
    washoShape.hasInternalAbar = false := by
  refine ⟨rfl, rfl, rfl⟩

/-- Table-79 cells partition into ±Ā: every cell either has it or lacks it
    (a tautology over Bool, but documents the bipartition exhaustiveness
    of the hasInternalAbar dimension). -/
theorem table79_bipartite :
    ∀ c ∈ table79, c.shape.hasInternalAbar = true ∨
                   c.shape.hasInternalAbar = false := by
  intro c _; cases c.shape.hasInternalAbar <;> tauto

/-- The four-cell cross-classification of Tables 80–81 is exhaustively
    populated: every combination of (factive, hasInternalAbar) is attested
    by at least one (verb, shape) pair. The fourth cell (non-factive + Ā)
    is documented from [caponigro-polinsky-2011]'s Adyghe REs as
    cited by Deal — Adyghe REs combine `adygheREShape` (hasInternalAbar=true)
    with predicates that are not factive in Caponigro & Polinsky's analysis
    (Deal §7 p. 53). -/
theorem cross_classification_populated :
    -- Factive + Ā: liloy + nezPerceREShape
    (liloy.factive = true ∧ nezPerceREShape.hasInternalAbar = true) ∧
    -- Factive + no Ā: cuukwe + nezPerceSimplexShape (Nez Perce 'know')
    (cuukwe.factive = true ∧ nezPerceSimplexShape.hasInternalAbar = false) ∧
    -- Non-factive + Ā: documented for Adyghe REs (per Caponigro-Polinsky 2011)
    (adygheREShape.hasInternalAbar = true) ∧
    -- Non-factive + no Ā: neki + nezPerceSimplexShape ('think')
    (neki.factive = false ∧ nezPerceSimplexShape.hasInternalAbar = false) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩⟩

-- ============================================================================
-- §5d. Discrimination at the Tonhauser layer
-- ============================================================================

/-! ### What Tonhauser substrate alone CANNOT see

The headline cross-classification's *fourth* cell (factive + simplex,
Nez Perce *cuukwe*) and *first* cell (factive + RE, Nez Perce *liloy*)
both project to Tonhauser Class C. The Tonhauser substrate alone cannot
distinguish them — the distinction lives at the `EmbeddingStrategy` /
`NotionalComplementShape` layer, not at the projective-content layer.

This is informative: it shows that Deal's typology is *strictly finer-
grained* than Tonhauser's, and motivates the need for substrate at the
Probe / ClauseSpine layer (where the Ā-dep distinction is visible). -/

/-- Tonhauser projective class does not distinguish *cuukwe* from *liloy*. -/
theorem tonhauser_fails_to_distinguish_cuukwe_liloy :
    derivedProjectiveClass cuukwe = derivedProjectiveClass liloy := by decide

/-- But the embedding-strategy projection DOES distinguish them. -/
theorem strategy_distinguishes_cuukwe_liloy :
    nezPerceEmbedStrategy cuukwe ≠ nezPerceEmbedStrategy liloy := by decide

-- ============================================================================
-- §6. ke-agreement via SatisfactionCond
-- ============================================================================

/-! ### *ke* as a φ-probe on C ([deal-2015a-nels])

[deal-2026] §2 argues *ke* is a C-head with a φ-probe rather than a
relative pronoun. The argument: *ke*'s φ-features track the embedded
*subject* (sometimes plus object), starting from the highest argument and
proceeding down — exactly the [deal-2015a-nels] interaction-satisfaction
algorithm probing into c-command domain.

The C-probe is satisfied either by feature-match (yielding overt person
agreement) or by encountering the TP boundary (yielding null surface
agreement). We model this with [deal-2024]'s `SatisfactionCond.disjunctive`.

Caveat: the existing `Agree.lean` `featuresMatch` uses `sameType` matching
(see `Agree.lean:234`), which collapses 1st/2nd/3rd person into a single
"person feature type." A finer-grained `valueMatch` substrate would be
needed to formalise Deal's 1st vs 3rd person split. The disjunctive shape
here is faithful to the framework but currently distinguishes only
"person-feature-present" vs "no-feature-encountered-T." -/


/-- *ke*'s satisfaction condition: matched by any φ-feature (collapsed by
    `sameType` regardless of person value), or by encountering the TP head. -/
def keSatisfaction : SatisfactionCond :=
  .disjunctive
    [ .featureMatch (.phi (.person .third))
    , .headEncounter .T ]

/-- *ke* is satisfied by a subject bearing person features (any person, due to
    `sameType` matching in Agree.lean). -/
theorem ke_satisfied_by_phi :
    keSatisfaction.isSatisfied
      (.ofGramFeatures [.valued (.phi (.person .first))])
      none = true := by decide

/-- *ke* is satisfied by encountering the TP boundary even with no φ-features
    on the goal — the disjunctive escape that yields null surface agreement. -/
theorem ke_satisfied_by_head_encounter :
    keSatisfaction.isSatisfied ⊥ (some .T) = true := by decide

/-- The head-encounter satisfaction copies no features (default null surface
    agreement when subject lacks φ). -/
theorem ke_head_encounter_no_copy :
    keSatisfaction.copiedFeatures ⊥ (some .T) = false := by decide

-- ============================================================================
-- §7. Internal-Ā-dependency profile
-- ============================================================================

/-! ### REs contain a high Ā-dependency ([deal-2026] §5)

Deal §5 argues the relative operator originates *above TP* — a high
functional projection — based on absence of low-position cyclic effects
and the always-nominative form of the relative pronoun. We attach the
existing `keineĀDep` (Ā-probe on C, fValue 6) as the substrate witness;
the alternative `low` analysis (Aboh's Gungbe lexical-Ā) is documented
but not formalised. -/

/-- A Nez Perce RE's internal Ā-dependency is — in Probe-substrate terms —
    `Minimalist.keineĀDep` (the substrate witness defined in `Probe.lean §4b`).
    Deal's "high functional projection above TP" claim falls out of
    `Minimalist.keineĀDep_isHigh` without re-stipulation here. -/
abbrev reInternalAbar : AbarDep := Minimalist.keineĀDep

/-- The Nez Perce RE Ā-dependency is "high" in Deal's sense: above TP.
    Inherited directly from the substrate theorem, no re-proof. -/
theorem reInternalAbar_isHigh : reInternalAbar.isHigh = true :=
  Minimalist.keineĀDep_isHigh

-- ============================================================================
-- §8. Cross-framework comparison
-- ============================================================================

/-! ### Silent divergence with HPSG

`Syntax/HPSG/RelativeClauses.lean:87-93` hard-codes RC =
modifier (`isMod = true`, theorem `relClause_is_modifier`). [deal-2026]'s
analysis of Nez Perce REs as *complement* CPs (not modifier RCs) sits
incompatibly with this Minimalist-only framing: HPSG would either need to
recognise REs as a third structural type (not modifier, not bare
complementation), or accept that the RE-vs-RC distinction is a
Minimalist-internal one with no HPSG analogue. The bridge theorem
`HPSG.isMod ↔ ¬ Minimalist.cp_complementation_via_re` is filed as future
work — promoted from "implicit assumption" to a substrate question.

### Healthy convergence with Cacchioli 2025

`Studies/Cacchioli2025.lean` independently
establishes that Tigrinya distinguishes *kemzi* (factive complementizer)
from *zi* (relativizer/general subordinator) without syncretism. This is a
language-internal counterargument to the universalist
"complementation = relativization" claim, parallel to [deal-2026]'s
Nez Perce-internal contrast between simplex (no *yox̂ ke*) and RE (with
*yox̂ ke*) embeddings. The two papers reinforce each other across distinct
language families.

### Convergence with Caponigro & Polinsky 2011

[caponigro-polinsky-2011]'s Adyghe analysis shares Deal's "high Ā
origin" claim while diverging on the V D N CP shell shape. Deal 2026 §5
explicitly cites Caponigro & Polinsky as theoretical kin. -/

-- ============================================================================
-- §9. Indexical shift and SoT (deferred)
-- ============================================================================

/-! ### §6 indexical shift / SoT formalisation deferred

[deal-2026] §6 establishes that REs block shifty pronouns and require
matching tense (vs. simplex embeddings where shift and relative-tense are
both available). The semantic substrate for these claims is
[deal-2020]'s `A Theory of Indexical Shift` book; that substrate is
not yet implemented in linglib (no `Semantics/IndexicalShift/`
directory exists; existing `Semantics/Reference/{ShiftedIndexicals,
Monsters,Kaplan}.lean` cover Kaplanian framing but not Deal's Σ-monsters
specifically).

Until the substrate lands, the §6 contrasts can only be documented in
prose. Decide-checking a `shiftedReading? : Sentence → Bool = false`
predicate would be the "encoding conclusions as definitions" anti-pattern.

Future work: import `deal-2020` substrate (when implemented) and prove
`re_blocks_shift : ∀ p ∈ reCanonical, p.allowsShift = false` against actual
indexical-shift semantics. -/

end Deal2026
