import Linglib.Fragments.NezPerce.ClausalEmbedding
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine

/-! # Deal (2026): Clausal complementation as relativization, revisited

[deal-2026] argues that the relative-like notional complement clauses of
Nez Perce ("relative embeddings", REs) are CPs containing an
Ā-dependency launched above TP — not DPs or PPs. Clausal complementation
is therefore not uniformly relativization ([kayne-2008], [kayne-2014],
[arsenijevic-2009]), and factivity, RE-syntax, and nominalization
dissociate cross-linguistically ((79)–(81)), though within Nez Perce all
REs are factive. Formalized here: the CP-external shell inventory and
the (79) shell typology; the per-predicate embedding strategy derived
from the Fragment's *yox̂ ke* edge observable; the factivity
dissociations; and the case-inflection half of the *yox̂*-is-D
diagnostic. The *ke*-agreement analysis ([deal-2015a-nels]
interaction–satisfaction) and the §6 shift/tense semantics
([deal-2025]) await substrate — see the closing section.
-/

namespace Deal2026

open NezPerce.ClausalEmbedding
open Minimalist (Cat ClauseSpine)

/-! ### CP-external shells

The external-syntax axis of [deal-2026]'s (79): what wraps the embedded
CP, innermost first. -/

/-- A wrapping head above the embedded CP: [deal-2026]'s survey exhibits
    D, N, and P shells ((79) and fn. 33). -/
inductive Shell where
  /-- D shell. -/
  | d
  /-- N shell (between D and CP). -/
  | n
  /-- P shell. -/
  | p
  deriving DecidableEq, Repr

/-- The external wrapping above a CP, innermost first: `[]` = bare CP,
`[.n, .d]` = D over N over CP, `[.d, .p]` = P over D over CP. -/
abbrev ShellInventory := List Shell

namespace ShellInventory

/-- The bare-CP row of (79) (Nez Perce; English *think*). -/
def bareCP : ShellInventory := []

/-- V D CP: not a row of (79) — [deal-2026] fn. 33 notes the structure
    as "defended in the literature" for Washo ([bochnak-hanink-2021]),
    with no known RE instance. -/
def dCP : ShellInventory := [.d]

/-- The V D N CP row of (79) (Adyghe, [caponigro-polinsky-2011];
    English N complementation, [hankamer-mikkelsen-2021]). -/
def dnCP : ShellInventory := [.n, .d]

/-- The V P D CP row of (79) (Bulgarian, [krapova-2010]; Ndebele,
    [pietraszko-2019]). -/
def pdCP : ShellInventory := [.d, .p]

end ShellInventory

open ShellInventory

/-! ### Notional-complement shapes -/

/-- The full Deal-2026 description of a notional complement clause:
    internal spine + external shell + presence of an internal
    Ā-dependency. Bundled here rather than in substrate to keep the
    per-axis substrate primitive (`ClauseSpine`) reusable for non-Deal
    accounts; the shell axis is Deal-specific and lives above. -/
structure NotionalComplementShape where
  /-- Internal spine of the embedded clause (typically `ClauseSpine.cP`). -/
  internal : ClauseSpine
  /-- External wrapping shells from C outward (`bareCP / dCP / dnCP / pdCP`). -/
  external : ShellInventory
  /-- Whether the embedded CP contains an internal Ā-dependency. -/
  hasInternalAbar : Bool
  deriving Repr

/-- The Nez Perce shape of a given embedder, derived from the Fragment's
    edge observable: a bare CP whose internal Ā-dependency is Deal's
    interpretation of obligatory *yox̂ ke* edge morphology. -/
def nezPerceShape (v : NezPerceEmbedder) : NotionalComplementShape :=
  ⟨ClauseSpine.cP, bareCP, v.yoxKeEdge == .obligatory⟩

/-- The Nez Perce RE shape ([deal-2026] §3, §5). -/
def nezPerceREShape : NotionalComplementShape := nezPerceShape liloy

/-- The Nez Perce simplex shape ([deal-2026] §6). -/
def nezPerceSimplexShape : NotionalComplementShape := nezPerceShape neki

/-- The Adyghe RE shape from [caponigro-polinsky-2011], exhibited at
    [deal-2026] §4 (43): V D N CP with internal Ā. Deal cites Caponigro
    & Polinsky as theoretical kin on the high origin of the operator
    while diverging on the external shell. -/
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
    [hanink-bochnak-2017]: V D CP, no Ā ([deal-2026] fn. 33). -/
def washoShape : NotionalComplementShape :=
  ⟨ClauseSpine.cP, dCP, false⟩

/-- The English N-complementation shape of (79)'s V D N CP / no-Ā cell
    (*the fact that S*) — the DP shell with an N co-argument envisioned
    by [hankamer-mikkelsen-2021], as Deal notes in §7. -/
def englishNComplementationShape : NotionalComplementShape :=
  ⟨ClauseSpine.cP, dnCP, false⟩

/-! ### The cross-linguistic shell typology -/

/-- An entry in [deal-2026]'s (79): a language × construction with its
    NotionalComplementShape. -/
structure ShellTypologyCell where
  language : String
  construction : String
  shape : NotionalComplementShape
  deriving Repr

/-- The rows of [deal-2026]'s (79) — all six cells of the 3×2 table are
    filled, with V CP / no-Ā doubly witnessed — plus the Washo V D CP
    structure from footnote 33 per [bochnak-hanink-2021]. -/
def shellTypology : List ShellTypologyCell := [
  ⟨"Nez Perce", "RE",                nezPerceREShape⟩,
  ⟨"Nez Perce", "simplex",           nezPerceSimplexShape⟩,
  ⟨"English",   "think-complement",  nezPerceSimplexShape⟩,  -- bareCP, no Ā
  ⟨"Adyghe",    "RE",                adygheREShape⟩,
  ⟨"English",   "N-complementation", englishNComplementationShape⟩,
  ⟨"Bulgarian", "RE",                bulgarianREShape⟩,
  ⟨"Ndebele",   "embedding",         ndebeleShape⟩,
  ⟨"Washo",     "factive",           washoShape⟩
]

/-- Not every row of (79) carries an internal Ā-dependency: the
    universalist position that all clausal complementation is
    relativization ([kayne-2008], [arsenijevic-2009]) fails on the no-Ā
    rows (Nez Perce simplex, English *think*, Ndebele, Washo). -/
theorem not_all_rows_abar :
    ¬ ∀ c ∈ shellTypology, c.shape.hasInternalAbar = true := by decide

/-- Bare CPs occur with and without an internal Ā-dependency: REs are
    real, and not all complementation is relativization. -/
theorem bareCP_abar_dissociates :
    (∃ c ∈ shellTypology,
      c.shape.external = bareCP ∧ c.shape.hasInternalAbar = true) ∧
    (∃ c ∈ shellTypology,
      c.shape.external = bareCP ∧ c.shape.hasInternalAbar = false) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- REs vary in nominal superstructure: some carry their Ā-dependency
    inside a D shell (Adyghe V D N CP, Bulgarian V P D CP). -/
theorem shelled_RE_attested :
    ∃ c ∈ shellTypology, Shell.d ∈ c.shape.external ∧
      c.shape.hasInternalAbar = true := by decide

/-! ### Embedding strategy from the *yox̂ ke* edge

The Fragment carries the morphological observable (`yoxKeEdge`); Deal's
analytical commitments — the RE-vs-simplex classification and the
selectional profile — are derived from it. -/

/-- The two embedding strategies [deal-2026] distinguishes. -/
inductive EmbeddingStrategy where
  | re       -- relative embedding (yox̂ + ke + Ā-dep above TP)
  | simplex  -- bare CP, no Ā-dep
  deriving DecidableEq, Repr

/-- Deal's per-predicate embedding-strategy classification, derived from
    the Fragment observable: obligatory *yox̂ ke* on the complement edge
    ↔ syntactic Ā-dependency above TP. -/
def nezPerceEmbedStrategy (v : NezPerceEmbedder) : EmbeddingStrategy :=
  if v.yoxKeEdge = .obligatory then .re else .simplex

/-- A predicate is RE-canonical in Deal's analysis iff its complement
    obligatorily carries the *yox̂ ke* edge morphology. -/
theorem strategy_iff_yoxKe (v : NezPerceEmbedder) :
    nezPerceEmbedStrategy v = .re ↔ v.yoxKeEdge = .obligatory := by
  simp [nezPerceEmbedStrategy]

theorem reCanonical_strategy :
    ∀ v ∈ reCanonical, nezPerceEmbedStrategy v = .re := by decide

theorem simplexCanonical_strategy :
    ∀ v ∈ simplexCanonical, nezPerceEmbedStrategy v = .simplex := by decide

/-- Deal's selectional commitment for a Nez Perce embedder: the verb
    c-selects a CP and (for RE-takers) requires that CP to contain an
    internal Ā-dependency. This is not standard c-selection: c-selection
    sees only the outer category, which is uniformly `.C`; the
    RE-vs-simplex distinction is in the internal structure of the
    selected CP — whether its head bears the [+Ā] feature triggering
    operator movement above TP. -/
structure DealSelectionalProfile where
  /-- Outer category the verb c-selects for (always `.C` for embedders). -/
  outerCat : Cat
  /-- Whether the selected CP must contain an internal Ā-dependency. -/
  requiresInternalAbar : Bool
  deriving DecidableEq, Repr

/-- Deal's selectional analysis, derived from the Fragment observable. -/
def dealSelectionalProfile (v : NezPerceEmbedder) : DealSelectionalProfile :=
  { outerCat := .C, requiresInternalAbar := v.yoxKeEdge == .obligatory }

/-- The selected CP requires an internal Ā-dependency iff *yox̂ ke* is
    obligatory on the edge. -/
theorem requiresInternalAbar_iff_yoxKe (v : NezPerceEmbedder) :
    (dealSelectionalProfile v).requiresInternalAbar =
      (v.yoxKeEdge == .obligatory) := rfl

/-- Every Nez Perce embedder uniformly c-selects `.C`: the RE-vs-simplex
    contrast is not a c-selectional difference. -/
theorem all_embedders_select_C (v : NezPerceEmbedder) :
    (dealSelectionalProfile v).outerCat = .C := rfl

/-! ### Factivity and RE-syntax vary independently

[deal-2026] (80): factivity and RE-syntax dissociate — cross-
linguistically the axes vary "independently to at least some extent",
while within Nez Perce the entailment holds one way only (all REs are
factive, `reCanonical_all_factive`; not all factives are REs). The
fourth cell (non-factive + Ā) is Adyghe: Deal reports from
[caponigro-polinsky-2011] p. 115 that Adyghe uses the RE strategy for
all notional complementation regardless of factivity, so RE syntax does
not ensure factivity. -/

/-- Factivity does not coincide with RE-syntax across the Fragment
    inventory. -/
theorem factivity_not_abar :
    ¬ ∀ v ∈ allEmbedders,
      v.factive = (nezPerceShape v).hasInternalAbar := by decide

/-- The dissociating witness: a factive predicate whose shape carries no
    internal Ā-dependency (*cuukwe* 'know'). -/
theorem factive_simplex_attested :
    ∃ v ∈ allEmbedders,
      v.factive = true ∧ (nezPerceShape v).hasInternalAbar = false := by
  decide

/-- The co-occurring cell: a factive RE-taker (*lilooy* 'be happy'). -/
theorem factive_re_attested :
    ∃ v ∈ allEmbedders,
      v.factive = true ∧ (nezPerceShape v).hasInternalAbar = true := by
  decide

/-! ### Projection does not distinguish RE from simplex

Deal's factivity trials assess projection only — "in claiming that RE
verbs are factive, what I claim is that their complement clause content
is projective" (§3), in the [tonhauser-beaver-roberts-simons-2013]
sense. On that dimension *cuukwe* and *lilooy* are indistinguishable;
the RE-vs-simplex split lives at the embedding-strategy layer. -/

/-- The projection dimension does not distinguish *cuukwe* from
    *lilooy*: both are factive. -/
theorem projective_cuukwe_eq_liloy : cuukwe.factive = liloy.factive := rfl

/-- The embedding-strategy layer does distinguish them. -/
theorem strategy_cuukwe_ne_liloy :
    nezPerceEmbedStrategy cuukwe ≠ nezPerceEmbedStrategy liloy := by decide

/-! ### The D-inflection diagnostic -/

/-- The relative pronoun *yox̂/ko* inflects for case: cells with distinct
    cases share no forms. This is the case-inflection half of
    [deal-2026] §2's diagnostic ((21)) that *yox̂/ko* is a D while
    invariant *ke* is a C — the D half of the *yox̂ ke* edge whose
    obligatoriness `yoxKeEdge` records. -/
theorem paradigm_case_discriminates :
    ∀ p ∈ relativePronounParadigm, ∀ q ∈ relativePronounParadigm,
      p.case ≠ q.case → ∀ f ∈ p.forms, f ∉ q.forms := by decide

/-! ### Awaiting substrate

Two of the paper's core arguments are stated here only as deferrals.
The *ke*-agreement analysis ([deal-2026] §2, following
[deal-2015a-nels]): *ke*'s φ-probe interacts with all φ-features,
probing from the subject downward until the feature [addr] (second
person) is encountered, with 1st/2nd — but not 3rd — person agreement
overt. Expressing this needs value-sensitive satisfaction (the current
`Minimalist.SatisfactionCond` matches feature *types* only) and
ordered-goal sequential probing. The §6 contrasts — REs block indexical
shift and take matrix-matching tense as temporal de re, simplex
embeddings allow shift and relative tense — rest on [deal-2025]'s
semantics for the two clause types (world-set vs perspectival-tuple
denotations), which linglib does not yet implement. -/

end Deal2026
