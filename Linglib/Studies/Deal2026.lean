import Linglib.Fragments.NezPerce.ClausalEmbedding
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine

/-! # Deal (2026): Clausal complementation as relativization, revisited

[deal-2026] argues that the relative-like notional complement clauses of
Nez Perce ("relative embeddings", REs) are CPs containing an
Ā-dependency launched above TP — not DPs or PPs. Clausal complementation
is therefore not uniformly relativization ([kayne-2008], [kayne-2014],
[arsenijevic-2009]), and factivity, RE-syntax, and nominalization
dissociate cross-linguistically ((79)–(81)), though within Nez Perce all
REs are factive. Formalized here: the (79) typology as extended clause
spines (`Minimalist.ClauseSpine`), with shell superstructure, bare-CP
status, nominal-shell status, and the selected category all *derived*
from each row's spine; the per-predicate embedding strategy derived from
the Fragment's *yox̂ ke* edge observable; the factivity dissociations;
and the case-inflection half of the *yox̂*-is-D diagnostic. Deal's
c-selection point — RE-takers and simplex-takers alike select a CP, the
contrast being CP-internal — awaits LI-level Nez Perce entries
(`Minimalist.SimpleLI` selection stacks).

## TODO

* *ke*-agreement ([deal-2026] §2, after [deal-2015a-nels]): the φ-probe
  on C interacts with all φ-features, probing from the subject downward
  until [addr] (second person) satisfies it; 1st/2nd but not 3rd person
  agreement is overt. Needs value-sensitive satisfaction and
  ordered-goal probing — `Minimalist.SatisfactionCond` matches feature
  types only.
* §6 shift/tense: REs block indexical shift and take matrix-matching
  tense as temporal de re; simplex embeddings allow shift and relative
  tense. Rests on [deal-2025]'s clause-type semantics (world-set vs
  perspectival-tuple denotations), not yet implemented.
-/

namespace Deal2026

open NezPerce.ClausalEmbedding
open Minimalist (Cat ClauseSpine catFeatures)

/-! ### Embedding strategy from the *yox̂ ke* edge

The Fragment carries the morphological observable (`yoxKeEdge`); Deal's
analytical classification is derived from it: obligatory *yox̂ ke* on
the complement edge ↔ a syntactic Ā-dependency above TP inside the
embedded CP. Both classes c-select a CP — the RE-vs-simplex contrast is
internal to the selected clause, not a c-selectional difference. -/

/-- The two embedding strategies [deal-2026] distinguishes. -/
inductive EmbeddingStrategy where
  | re       -- relative embedding (yox̂ + ke + Ā-dep above TP)
  | simplex  -- bare CP, no Ā-dep
  deriving DecidableEq, Repr

/-- Deal's per-predicate embedding-strategy classification, derived from
    the Fragment observable. -/
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

/-! ### The cross-linguistic shell typology

[deal-2026]'s (79) describes each notional complement by its extended
spine — the projected heads from V upward, *including* any nominal or
adpositional superstructure over C. The shell vocabulary is derived:
the shells are `spine.above .C`, bare-CP-hood is `highestHead = .C`, a
nominal shell is a [+N] head above C ([chomsky-1970] features via
`catFeatures`), and the category the matrix predicate selects is the
spine's highest head. The internal-Ā axis remains a recorded datum
(probe-bearing structure is not yet represented). -/

/-- A row of [deal-2026]'s (79): a language × construction with its
    extended spine and internal-Ā status. -/
structure ShellTypologyCell where
  language : String
  construction : String
  /-- Projected heads of the notional complement, V up through any
      CP-external shells. -/
  spine : ClauseSpine
  /-- Whether the embedded CP contains an internal Ā-dependency. -/
  hasInternalAbar : Bool
  deriving Repr

/-- Nothing projects above C ((79)'s V CP row). -/
def ShellTypologyCell.IsBareCP (c : ShellTypologyCell) : Prop :=
  c.spine.highestHead = .C

instance (c : ShellTypologyCell) : Decidable c.IsBareCP :=
  inferInstanceAs (Decidable (_ = _))

/-- The clause complex is wrapped in a nominal projection: some head
    above C is [+N]. -/
def ShellTypologyCell.HasNominalShell (c : ShellTypologyCell) : Prop :=
  ∃ h ∈ c.spine.above .C, (catFeatures h).plusN = true

instance (c : ShellTypologyCell) : Decidable c.HasNominalShell :=
  inferInstanceAs (Decidable (∃ h ∈ c.spine.above .C, _))

/-- A Nez Perce row, derived from the Fragment's edge observable: a bare
    finite CP whose internal Ā-dependency is Deal's interpretation of
    obligatory *yox̂ ke* edge morphology. -/
def nezPerceCell (construction : String) (v : NezPerceEmbedder) :
    ShellTypologyCell :=
  ⟨"Nez Perce", construction, ClauseSpine.cP, v.yoxKeEdge == .obligatory⟩

/-- The Nez Perce RE row ([deal-2026] §3, §5). -/
def nezPerceRE : ShellTypologyCell := nezPerceCell "RE" liloy

/-- The Nez Perce simplex row ([deal-2026] §6). -/
def nezPerceSimplex : ShellTypologyCell := nezPerceCell "simplex" neki

/-- English simplex V complementation (*think*): bare CP, no Ā
    ((79)'s V CP row). -/
def englishThink : ShellTypologyCell :=
  ⟨"English", "think-complement", ClauseSpine.cP, false⟩

/-- The Adyghe RE row from [caponigro-polinsky-2011], exhibited at
    [deal-2026] §4 (43): V D N CP with internal Ā. Deal cites Caponigro
    & Polinsky as theoretical kin on the high origin of the operator
    while diverging on the external shell. -/
def adygheRE : ShellTypologyCell :=
  ⟨"Adyghe", "RE", ClauseSpine.cP.extend [.N, .D], true⟩

/-- The English N-complementation row of (79)'s V D N CP / no-Ā cell
    (*the fact that S*) — the DP shell with an N co-argument envisioned
    by [hankamer-mikkelsen-2021], as Deal notes in §7. -/
def englishNComplementation : ShellTypologyCell :=
  ⟨"English", "N-complementation", ClauseSpine.cP.extend [.N, .D], false⟩

/-- The Bulgarian RE row from [krapova-2010], exhibited at
    [deal-2026] §4 (49): V P D CP with internal Ā. -/
def bulgarianRE : ShellTypologyCell :=
  ⟨"Bulgarian", "RE", ClauseSpine.cP.extend [.D, .P], true⟩

/-- The Ndebele row from [pietraszko-2019], exhibited at [deal-2026]
    §7 (78): V P D CP with no Ā-dependency. -/
def ndebeleEmbedding : ShellTypologyCell :=
  ⟨"Ndebele", "embedding", ClauseSpine.cP.extend [.D, .P], false⟩

/-- The Washo factive row from [bochnak-hanink-2021],
    [hanink-bochnak-2017]: V D CP, no Ā — not a row of (79);
    [deal-2026] fn. 33 notes the structure as "defended in the
    literature" for Washo, with no known RE instance. -/
def washoFactive : ShellTypologyCell :=
  ⟨"Washo", "factive", ClauseSpine.cP.extend [.D], false⟩

/-- The rows of [deal-2026]'s (79) — all six cells of the 3×2 table are
    filled, with V CP / no-Ā doubly witnessed — plus the Washo V D CP
    structure from footnote 33. -/
def shellTypology : List ShellTypologyCell := [
  nezPerceRE, nezPerceSimplex, englishThink, adygheRE,
  englishNComplementation, bulgarianRE, ndebeleEmbedding, washoFactive
]

/-- Not every row of (79) carries an internal Ā-dependency: the
    universalist position that all clausal complementation is
    relativization ([kayne-2008], [arsenijevic-2009]) fails on the no-Ā
    rows (Nez Perce simplex, English *think*, Ndebele, Washo). -/
theorem not_all_rows_abar :
    ¬ ∀ c ∈ shellTypology, c.hasInternalAbar = true := by decide

/-- Bare CPs occur with and without an internal Ā-dependency: REs are
    real, and not all complementation is relativization. -/
theorem bareCP_abar_dissociates :
    (∃ c ∈ shellTypology, c.IsBareCP ∧ c.hasInternalAbar = true) ∧
    (∃ c ∈ shellTypology, c.IsBareCP ∧ c.hasInternalAbar = false) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- REs vary in nominal superstructure: some carry their Ā-dependency
    inside a nominal shell (Adyghe V D N CP, Bulgarian V P D CP). -/
theorem shelled_RE_attested :
    ∃ c ∈ shellTypology, c.HasNominalShell ∧
      c.hasInternalAbar = true := by decide

/-- Every row's spine extends the same finite-CP core: the rows differ
    only above C. -/
theorem shared_cP_core :
    ∀ c ∈ shellTypology,
      ClauseSpine.cP.projectedHeads <+: c.spine.projectedHeads := by decide

/-- The category the matrix predicate selects — the spine's highest
    head — nonetheless varies across the rows: C, D, and P are all
    attested. With `shared_cP_core`, this derives [deal-2026] §7's
    moral: the internal syntax of a clause does not predict its
    external syntax. -/
theorem selected_category_varies :
    ∃ c₁ ∈ shellTypology, ∃ c₂ ∈ shellTypology, ∃ c₃ ∈ shellTypology,
      c₁.spine.highestHead = .C ∧ c₂.spine.highestHead = .D ∧
      c₃.spine.highestHead = .P := by decide

/-! ### Factivity and RE-syntax vary independently

[deal-2026] (80): factivity and RE-syntax dissociate — cross-
linguistically the axes vary "independently to at least some extent",
while within Nez Perce the entailment holds one way only (all REs are
factive, `reCanonical_all_factive`; not all factives are REs). The
fourth cell (non-factive + Ā) is Adyghe: Deal reports from
[caponigro-polinsky-2011] p. 115 that Adyghe uses the RE strategy for
all notional complementation regardless of factivity, so RE syntax does
not ensure factivity. -/

/-- Factivity does not coincide with the embedding strategy across the
    Fragment inventory. -/
theorem factivity_not_strategy :
    ¬ ∀ v ∈ allEmbedders,
      (v.factive = true ↔ nezPerceEmbedStrategy v = .re) := by decide

/-- The dissociating witness: a factive simplex-taker (*cuukwe*
    'know'). -/
theorem factive_simplex_attested :
    ∃ v ∈ allEmbedders,
      v.factive = true ∧ nezPerceEmbedStrategy v = .simplex := by decide

/-- The co-occurring cell: a factive RE-taker (*lilooy* 'be happy'). -/
theorem factive_re_attested :
    ∃ v ∈ allEmbedders,
      v.factive = true ∧ nezPerceEmbedStrategy v = .re := by decide

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

end Deal2026
