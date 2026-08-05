import Linglib.Fragments.Adyghe.Clause
import Linglib.Fragments.Bulgarian.Clause
import Linglib.Fragments.Ndebele.Clause
import Linglib.Fragments.NezPerce.Clause
import Linglib.Fragments.Washo.Clause
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine

/-! # Deal (2026): Clausal complementation as relativization, revisited

[deal-2026] argues that the relative-like notional complement clauses of
Nez Perce ("relative embeddings") are CPs containing an
Ā-dependency launched above TP — not DPs or PPs. Clausal complementation
is therefore not uniformly relativization ([kayne-2008], [kayne-2014],
[arsenijevic-2009]), and factivity, relative-embedding syntax, and nominalization
dissociate cross-linguistically ((79)–(81)), though within Nez Perce all
relative embeddings are factive. Formalized here: the (79) typology as extended clause
spines (`Minimalist.ClauseSpine`), with shell superstructure, bare-CP
status, nominal-shell status, and the selected category all *derived*
from each row's spine; the per-predicate embedding strategy derived from
the Fragment's *yox̂ ke* edge observable; the factivity dissociations;
and the case-inflection half of the *yox̂*-is-D diagnostic. Deal's
c-selection point — relative-embedding takers and simplex-takers alike select a CP, the
contrast being CP-internal — awaits LI-level Nez Perce entries
(`Minimalist.SimpleLI` selection stacks).

## TODO

* *ke*-agreement ([deal-2026] §2, after [deal-2015a-nels]): the φ-probe
  on C interacts with all φ-features, probing from the subject downward
  until [addr] (second person) satisfies it; 1st/2nd but not 3rd person
  agreement is overt. Needs value-sensitive satisfaction and
  ordered-goal probing — `Minimalist.SatisfactionCond` matches feature
  types only.
* §6 shift/tense: relative embeddings block indexical shift and take matrix-matching
  tense as temporal de re; simplex embeddings allow shift and relative
  tense. Rests on [deal-2025]'s clause-type semantics (world-set vs
  perspectival-tuple denotations), not yet implemented.
-/

namespace Deal2026

open NezPerce.Clause
open Minimalist (Cat ClauseSpine catFeatures)

/-! ### Embedding strategy from the *yox̂ ke* edge

The Fragment carries the morphological observable (`yoxKeEdge`); Deal's
analytical classification is derived from it: obligatory *yox̂ ke* on
the complement edge ↔ a syntactic Ā-dependency above TP inside the
embedded CP. Both classes c-select a CP — the relative-vs-simplex contrast is
internal to the selected clause, not a c-selectional difference. -/

/-- The two embedding strategies [deal-2026] distinguishes. -/
inductive EmbeddingStrategy where
  | relative -- relative embedding (yox̂ + ke + Ā-dep above TP)
  | simplex  -- bare CP, no Ā-dep
  deriving DecidableEq, Repr

/-- Deal's per-predicate embedding-strategy classification, derived from
    the Fragment observable. -/
def nezPerceEmbedStrategy (v : NezPerceEmbedder) : EmbeddingStrategy :=
  if v.yoxKeEdge = .obligatory then .relative else .simplex

/-- A predicate is relative-canonical in Deal's analysis iff its complement
    obligatorily carries the *yox̂ ke* edge morphology. -/
theorem strategy_iff_yoxKe (v : NezPerceEmbedder) :
    nezPerceEmbedStrategy v = .relative ↔ v.yoxKeEdge = .obligatory := by
  simp [nezPerceEmbedStrategy]

theorem relativeCanonical_strategy :
    ∀ v ∈ relativeCanonical, nezPerceEmbedStrategy v = .relative := by decide

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

/-- The Nez Perce relative-embedding row ([deal-2026] §3, §5). -/
def nezPerceRelative : ShellTypologyCell := nezPerceCell "relative embedding" liloy

/-- The Nez Perce simplex row ([deal-2026] §6). -/
def nezPerceSimplex : ShellTypologyCell := nezPerceCell "simplex" neki

/-- English simplex V complementation (*think*): bare CP, no Ā
    ((79)'s V CP row). -/
def englishThink : ShellTypologyCell :=
  ⟨"English", "think-complement", ClauseSpine.cP, false⟩

/-- The Adyghe relative-embedding row from [caponigro-polinsky-2011],
    exhibited at [deal-2026] §4 (43): V D N CP with internal Ā. The
    Ā-flag is derived from the Fragment observable — 'think' requires
    the relativizer + high-applicative *ze-re-* on its tensed
    complement. Deal cites Caponigro & Polinsky as theoretical kin on
    the high origin of the operator while diverging on the external
    shell. -/
def adygheRelative : ShellTypologyCell :=
  ⟨"Adyghe", "relative embedding", ClauseSpine.cP.extend [.N, .D],
    Adyghe.Clause.gwepshesa.highApplicative == .required⟩

/-- The English N-complementation row of (79)'s V D N CP / no-Ā cell
    (*the fact that S*) — the DP shell with an N co-argument envisioned
    by [hankamer-mikkelsen-2021], as Deal notes in §7. -/
def englishNComplementation : ShellTypologyCell :=
  ⟨"English", "N-complementation", ClauseSpine.cP.extend [.N, .D], false⟩

/-- The Bulgarian relative-embedding row from [krapova-2010], exhibited
    at [deal-2026] §4 (49): V P D CP (*za* over demonstrative *tova*
    over the *deto*-CP; both heads can be null) with internal Ā. The
    Ā-flag is derived from the Fragment observable — *săžaljavam*
    'regret' takes the *deto*-complement Krapova analyzes as a hidden
    relative. -/
def bulgarianRelative : ShellTypologyCell :=
  ⟨"Bulgarian", "relative embedding", ClauseSpine.cP.extend [.D, .P],
    Bulgarian.Clause.sazhaljavam.deto == .alternating⟩

/-- The Ndebele row, exhibited at [deal-2026] §7 (78): V P D CP with no
    Ā-dependency. [pietraszko-2019]'s general claim is a *direct* DP
    shell over the CP (class-15 augment = D over *kuthi*); the P here
    is the independent preposition *nga* 'about' of the (78) exhibit
    (her (20b), *khuluma nga*), so this row records the attested
    P-over-DP combination, not the language's only shape. -/
def ndebeleEmbedding : ShellTypologyCell :=
  ⟨"Ndebele", "embedding", ClauseSpine.cP.extend [.D, .P], false⟩

/-- The Washo factive row from [bochnak-hanink-2021],
    [hanink-bochnak-2017]: V D CP, no Ā — not a row of (79);
    [deal-2026] fn. 33 notes the structure as "defended in the
    literature" for Washo, with no known relative-embedding instance.
    The D is silent, with the nominalizer *-gi ~ -ge* spelling out a
    separate idx head, and no intervening N ('fact'-nouns are
    unattested in the language); the Fragment observable
    (`Washo.Clause.hamupay.edge = .nominalized`) records the
    nominalization this cell rests on. -/
def washoFactive : ShellTypologyCell :=
  ⟨"Washo", "factive", ClauseSpine.cP.extend [.D], false⟩

/-- The rows of [deal-2026]'s (79) — all six cells of the 3×2 table are
    filled, with V CP / no-Ā doubly witnessed — plus the Washo V D CP
    structure from footnote 33. -/
def shellTypology : List ShellTypologyCell := [
  nezPerceRelative, nezPerceSimplex, englishThink, adygheRelative,
  englishNComplementation, bulgarianRelative, ndebeleEmbedding, washoFactive
]

/-- Not every row of (79) carries an internal Ā-dependency: the
    universalist position that all clausal complementation is
    relativization ([kayne-2008], [arsenijevic-2009]) fails on the no-Ā
    rows (Nez Perce simplex, English *think*, Ndebele, Washo). -/
theorem not_all_rows_abar :
    ¬ ∀ c ∈ shellTypology, c.hasInternalAbar = true := by decide

/-- Bare CPs occur with and without an internal Ā-dependency: relative embeddings are
    real, and not all complementation is relativization. -/
theorem bareCP_abar_dissociates :
    (∃ c ∈ shellTypology, c.IsBareCP ∧ c.hasInternalAbar = true) ∧
    (∃ c ∈ shellTypology, c.IsBareCP ∧ c.hasInternalAbar = false) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- relative embeddings vary in nominal superstructure: some carry their Ā-dependency
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

/-! ### Factivity and relative-embedding syntax vary independently

[deal-2026] (80): factivity and relative-embedding syntax dissociate —
cross-linguistically the axes vary "independently to at least some
extent", while within Nez Perce the entailment holds one way only (all
relative embeddings are factive, `relativeCanonical_all_factive`; not
all factives are relative embeddings). The fourth cell (non-factive +
Ā) is Adyghe, where the relative strategy is required for all *tensed*
notional complementation regardless of factivity
([caponigro-polinsky-2011] §6.5, as Deal reports) — now witnessed from
Fragment data (`nonfactive_relative_attested`). Bulgarian dissociates
in the same direction as Nez Perce:
`Bulgarian.Clause.factivity_not_sufficient_for_deto`. -/

/-- Factivity does not coincide with the embedding strategy across the
    Fragment inventory. -/
theorem factivity_not_strategy :
    ¬ ∀ v ∈ allEmbedders,
      (v.factive = true ↔ nezPerceEmbedStrategy v = .relative) := by decide

/-- The dissociating witness: a factive simplex-taker (*cuukwe*
    'know'). -/
theorem factive_simplex_attested :
    ∃ v ∈ allEmbedders,
      v.factive = true ∧ nezPerceEmbedStrategy v = .simplex := by decide

/-- The co-occurring cell: a factive relative-embedding taker
    (*lilooy* 'be happy'). -/
theorem factive_relative_attested :
    ∃ v ∈ allEmbedders,
      v.factive = true ∧ nezPerceEmbedStrategy v = .relative := by decide

/-- The fourth cell of (80) — non-factive + Ā — witnessed from Fragment
    data: Adyghe 'think' is consensus-non-factive and requires *ze-re-*
    on its tensed complement ([caponigro-polinsky-2011] (96) vs
    (98)). -/
theorem nonfactive_relative_attested :
    ∃ v ∈ Adyghe.Clause.relativeTakers, v.factive = some false := by
  decide

/-! ### Projection does not distinguish relative from simplex

Deal's factivity trials assess projection only — "in claiming that RE
verbs are factive, what I claim is that their complement clause content
is projective" (§3), in the [tonhauser-beaver-roberts-simons-2013]
sense. On that dimension *cuukwe* and *lilooy* are indistinguishable;
the relative-vs-simplex split lives at the embedding-strategy layer. -/

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
