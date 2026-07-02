import Linglib.Features.Complementation
import Linglib.Data.UD.Basic
import Linglib.Features.Number.Capabilities

/-!
# Nez Perce Clausal Embedding Inventory

[deal-2010] [deal-2016a] [deal-2026]

Nez Perce (Sahaptian, ISO 639-3 `nez`) inventory of notional-complement-taking
predicates plus the relative-pronoun paradigm. Theory-light: each predicate
carries only consensus-typological metadata (CTP class per [noonan-2007],
factivity status per [tonhauser-beaver-roberts-simons-2013] projection
diagnostics).

## Scope and provenance

Predicate list and factivity assessments are from [deal-2026] §3 (RE-takers)
and §6 (simplex-takers); the analytical RE-vs-simplex split is *not* encoded
here as a Fragment field — it is Deal-specific apparatus and lives in the
co-located study file `Studies/Deal2026.lean` as a
Studies-side projection.

Relative-pronoun paradigm is from [deal-2016a] (Table 22 reproduced in
[deal-2026] (22)). Case and number values reuse `Core.UD` substrate.

## What is here

- `NezPerceEmbedder`: per-verb consensus typology.
- 11 verbs: 8 typically RE-only (per [deal-2026] §3) + 3 typically simplex-only
  (per [deal-2026] §6).
- `RelativePronoun`: the *yox̂/ko* paradigm cells, indexed by `Core.UD.Case`
  × `Core.UD.Number`.
- 6 paradigm-cell entries.

## What is NOT here (lives in Studies/Deal2026.lean)

- The RE-vs-simplex strategy field per verb (Deal-specific apparatus).
- The `[uĀ]` selectional feature per RE-taker (Deal-specific analytical claim).
- The Tonhauser `ProjectiveClass` projection (consumes
  `Semantics/Presupposition/ProjectiveContent.lean`).
- Cross-classification theorems (factivity ⊥ RE-structure).
- The *ke*-as-φ-probe-on-C analysis (consumes `Minimalist.SatisfactionCond`).
-/

namespace NezPerce.ClausalEmbedding

-- ============================================================================
-- §1. Predicate Schema
-- ============================================================================

/-- A Nez Perce notional-complement-taking predicate.

    Fields are theory-neutral consensus typology and morphological
    observations:
    - `ctpClass`: [noonan-2007] category. Emotive factives are
      `commentative`; cognitive factives are `knowledge`; *think* is
      `propAttitude`; *say* is `utterance`.
    - `factive`: per [tonhauser-beaver-roberts-simons-2013] projection
      diagnostics (entailment-canceling environments). Established for
      Nez Perce by [deal-2026] §3 (33)–(36).
    - `requiresYoxKeEdge`: morphological observation per [deal-2026] §3
      (28). When `true`, the predicate's notional complement obligatorily
      begins with the morpheme pair *yox̂ ke* (relative-pronoun + Cₐ̄
      complementizer per Deal's analysis); when `false`, *yox̂ ke* on the
      complement edge is ungrammatical. This field is *observable* — it
      records what the morphology does, not what it means. Theory-laden
      interpretations (selectional features, projection sites) belong in
      `Studies/Deal2026.lean`.

    A `notionalTransitivity` field would be uniformly `intransitive` for
    every predicate Deal 2026 reviews (cf. §4 (38)–(39)) and is therefore
    omitted as carrying no discriminating signal. -/
structure NezPerceEmbedder where
  form : String
  gloss : String
  ctpClass : CTPClass
  factive : Bool
  requiresYoxKeEdge : Bool
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. Predicates from [deal-2026] §3 — RE-only ("relative-embedding")
-- ============================================================================

/-! ### Emotive factives (commentative class, per [noonan-2007])

These predicates require their notional complement to carry the relative-
pronoun + complementizer pair *yox̂ ke* ([deal-2026] (28)). Their factivity
is established by Deal's projection-test trials (§3, (33)–(34)). -/

/-- *liloy* 'be happy'. [deal-2026] (27a). -/
def liloy : NezPerceEmbedder where
  form := "liloy"; gloss := "be happy"
  ctpClass := .commentative
  factive := true
  requiresYoxKeEdge := true

/-- *etqew* 'be sad'. [deal-2026] (27b). -/
def etqew : NezPerceEmbedder where
  form := "'etqew"; gloss := "be sad"
  ctpClass := .commentative
  factive := true
  requiresYoxKeEdge := true

/-- *cicwaay* 'be surprised'. [deal-2026] (27c). -/
def cicwaay : NezPerceEmbedder where
  form := "cicwaay"; gloss := "be surprised"
  ctpClass := .commentative
  factive := true
  requiresYoxKeEdge := true

/-- *eey's* 'be joyful'. [deal-2026] (27e). -/
def eeys : NezPerceEmbedder where
  form := "'eey's"; gloss := "be joyful"
  ctpClass := .commentative
  factive := true
  requiresYoxKeEdge := true

/-- *q'eese* 'be bothered, unhappy'. [deal-2026] (27e). -/
def qeese : NezPerceEmbedder where
  form := "q'eese"; gloss := "be bothered"
  ctpClass := .commentative
  factive := true
  requiresYoxKeEdge := true

/-- *tim'neneki* 'be worried'. [deal-2026] (27e). -/
def timneneki : NezPerceEmbedder where
  form := "tim'neneki"; gloss := "be worried"
  ctpClass := .commentative
  factive := true
  requiresYoxKeEdge := true

/-! ### Cognitive factive

*timiipni* 'remember' is classed by Noonan as `knowledge` (cognitive factive)
but exhibits the same RE morphosyntax as the emotive factives in Nez Perce
([deal-2026] (27d), §3). The CTP class divergence between Nez Perce
*timiipni* and English *remember* (which is also `knowledge`) is a Fragment
fact: whether `knowledge` predicates are RE-takers is a per-language
property. -/

/-- *timiipni* 'remember'. [deal-2026] (27d). -/
def timiipni : NezPerceEmbedder where
  form := "timiipni"; gloss := "remember"
  ctpClass := .knowledge
  factive := true
  requiresYoxKeEdge := true

/-! ### Speech-act particle

*qe'ciyeew'yew* 'thank you' is a non-verbal particle that nonetheless takes
notional complements with the RE morphosyntax ([deal-2026] (42)). It
disallows DP complements (42b), reinforcing Deal's argument that REs are not
DPs. -/

/-- *qe'ciyeew'yew* 'thank you' (particle). [deal-2026] (42). -/
def qeciyeewyew : NezPerceEmbedder where
  form := "qe'ciyeew'yew"; gloss := "thank you"
  ctpClass := .commentative
  factive := true
  requiresYoxKeEdge := true

-- ============================================================================
-- §3. Predicates from [deal-2026] §6 — simplex-only
-- ============================================================================

/-! ### Non-factive cognitive and utterance predicates

These predicates strictly reject the RE morphosyntax — *yox̂ ke* on the
complement edge is ungrammatical for them ([deal-2026] (20), (47)–(48),
(65), (69)–(70)). -/

/-- *neki* 'think'. [deal-2026] (47), (65). Non-factive. -/
def neki : NezPerceEmbedder where
  form := "neki"; gloss := "think"
  ctpClass := .propAttitude
  factive := false
  requiresYoxKeEdge := false

/-- *hi* 'say, tell'. [deal-2026] (47), (65). Non-factive. -/
def hi : NezPerceEmbedder where
  form := "hi"; gloss := "say, tell"
  ctpClass := .utterance
  factive := false
  requiresYoxKeEdge := false

/-! ### Factive cognitive predicate

*cuukwe* 'know' is factive ([deal-2026] §6 (68): projection test
confirms factivity even in conditional antecedent), but typically takes
*simplex* complements (no *yox̂ ke*) — RE morphosyntax is rare and marginal
((66b) is `%`-marked). This is Deal 2026's central dissociation:
factivity ⊥ RE-structure. -/

/-- *cuukwe* 'know'. [deal-2026] (66), (68). Factive but
    typically simplex-embedding — the `requiresYoxKeEdge = false` field
    encodes the headline [deal-2026] dissociation: factivity does not
    force RE morphology in Nez Perce. (66b) shows a marginal `%`-attested
    RE-marked variant; we record the canonical pattern.  -/
def cuukwe : NezPerceEmbedder where
  form := "cuukwe"; gloss := "know"
  ctpClass := .knowledge
  factive := true
  requiresYoxKeEdge := false

-- ============================================================================
-- §4. Inventories
-- ============================================================================

/-- All embedders surveyed in [deal-2026]: 8 RE-canonical + 3
    simplex-canonical. This is the source-of-truth list; the partitions
    `reCanonical` / `simplexCanonical` are derived views on it via the
    Fragment-level observable `requiresYoxKeEdge`. -/
def allEmbedders : List NezPerceEmbedder :=
  [liloy, etqew, cicwaay, eeys, qeese, timneneki, timiipni, qeciyeewyew,
   neki, hi, cuukwe]

/-- The RE-canonical predicates: those whose notional complement
    obligatorily begins with the *yox̂ ke* morpheme pair. Defined as a
    derived view on the Fragment-level observable `requiresYoxKeEdge`
    rather than as a hand-curated list, so that adding/removing the
    edge-marking field on any predicate automatically updates this list. -/
def reCanonical : List NezPerceEmbedder :=
  allEmbedders.filter (·.requiresYoxKeEdge)

/-- The simplex-canonical predicates: those whose notional complement
    is incompatible with *yox̂ ke* on the edge. -/
def simplexCanonical : List NezPerceEmbedder :=
  allEmbedders.filter (! ·.requiresYoxKeEdge)

/-- Drift sentry: `reCanonical` contains exactly the eight predicates
    [deal-2026] §3 (27a–e), (27d), (42) lists. A `decide` failure here
    means either a verb's `requiresYoxKeEdge` field has been edited
    incorrectly, or a verb has been added/removed from `allEmbedders`. -/
theorem reCanonical_membership :
    reCanonical = [liloy, etqew, cicwaay, eeys, qeese, timneneki,
                   timiipni, qeciyeewyew] := by decide

/-- Drift sentry: `simplexCanonical` contains exactly *neki*, *hi*, *cuukwe*. -/
theorem simplexCanonical_membership :
    simplexCanonical = [neki, hi, cuukwe] := by decide

/-- Partition: every embedder is either RE-canonical or simplex-canonical
    (no third category in [deal-2026]'s survey). -/
theorem allEmbedders_partitioned :
    allEmbedders = reCanonical ++ simplexCanonical := by decide

-- ============================================================================
-- §5. Factivity Generalisations (consensus, observation-level)
-- ============================================================================

/-- All RE-canonical predicates are factive. [deal-2026] §3. -/
theorem reCanonical_all_factive :
    reCanonical.all (·.factive) = true := by decide

/-- The factive simplex-canonical predicates: exactly *cuukwe* 'know'.
    Drift sentry rather than aggregate count — pins which verb is the
    factive simplex-taker. -/
theorem factive_simplex_membership :
    simplexCanonical.filter (·.factive) = [cuukwe] := by decide

/-- The non-factive simplex-canonical predicates: exactly *neki* 'think'
    and *hi* 'say/tell'. -/
theorem nonfactive_simplex_membership :
    simplexCanonical.filter (! ·.factive) = [neki, hi] := by decide

/-- Crucially: factivity does NOT predict RE-canonical status.
    *cuukwe* 'know' is factive but simplex-canonical — establishing that
    factivity is necessary but not sufficient for RE morphosyntax in
    Nez Perce. (Deal 2026's central dissociation.) -/
theorem cuukwe_factive_but_simplex :
    cuukwe.factive = true ∧ cuukwe ∈ simplexCanonical := by
  refine ⟨rfl, ?_⟩
  decide

-- ============================================================================
-- §6. Relative Pronoun Paradigm
-- ============================================================================

/-! ### *yox̂/ko* paradigm — [deal-2016a], reproduced as
[deal-2026] Table (22).

Cells are indexed by `Core.UD.Case` (Nom/Erg/Acc) × `Core.UD.Number`
(Sing/Plur) — reusing the universally-shared UD substrate rather than
inventing local enums. -/

/-- A relative-pronoun cell from [deal-2026] Table (22). -/
structure RelativePronoun where
  case : UD.Case
  number : UD.Number
  forms : List String  -- multiple if idiolectal variation
  deriving Repr

/-- A relative pronoun bears its number slot (`HasNumber`). -/
instance : HasNumber RelativePronoun := ⟨fun rp => Number.fromUD rp.number⟩

def rp_nom_sg : RelativePronoun := ⟨.Nom, .Sing, ["yox̂"]⟩
def rp_nom_pl : RelativePronoun := ⟨.Nom, .Plur, ["yox̂me"]⟩
def rp_erg_sg : RelativePronoun := ⟨.Erg, .Sing, ["konim"]⟩
def rp_erg_pl : RelativePronoun := ⟨.Erg, .Plur, ["konmam"]⟩
def rp_acc_sg : RelativePronoun := ⟨.Acc, .Sing, ["konya"]⟩
def rp_acc_pl : RelativePronoun := ⟨.Acc, .Plur, ["konmana", "yox̂mene"]⟩

/-- The full [deal-2016a] paradigm: three cases × two numbers,
    six cells total. -/
def relativePronounParadigm : List RelativePronoun :=
  [rp_nom_sg, rp_nom_pl, rp_erg_sg, rp_erg_pl, rp_acc_sg, rp_acc_pl]

/-- Drift sentry: the paradigm covers exactly the Nom × Sing/Plur,
    Erg × Sing/Plur, Acc × Sing/Plur cells. A failure here means a cell
    has been added, removed, or its (case, number) pair edited. -/
theorem paradigm_membership :
    (relativePronounParadigm.map (λ p => (p.case, p.number))) =
      [(.Nom, .Sing), (.Nom, .Plur), (.Erg, .Sing), (.Erg, .Plur),
       (.Acc, .Sing), (.Acc, .Plur)] := by decide

/-- The accusative-plural cell shows idiolectal variation: two attested forms. -/
theorem acc_pl_variants : rp_acc_pl.forms = ["konmana", "yox̂mene"] := rfl

end NezPerce.ClausalEmbedding
