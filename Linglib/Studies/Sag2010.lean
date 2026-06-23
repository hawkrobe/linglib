/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Construction
import Linglib.Studies.Ross1967
import Linglib.Studies.SagWasowBender2003
import Linglib.Features.ClauseForm

set_option autoImplicit false

/-!
# English Filler-Gap Constructions
[sag-2010]

Parametric variation across the five types of English filler-gap (F-G) clause,
following [sag-2010]. The clauses share a common filler-head structure but
differ systematically along the seven parameters of variation listed in the
paper, and they cross-classify with clause-type supertypes from which their
semantics is inherited.

## The five F-G clause types

1. Wh-interrogative: "How foolish is he?" / "I wonder how foolish he is."
2. Wh-exclamative: "What a fool he is!" / "It's amazing how odd it is."
3. Topicalized: "The bagels, I like."
4. Wh-relative: "the person who they nominated"
5. The-clause: "The more people I met, the happier I became."

## What is modeled

This file formalizes the *descriptive parameter table* of [sag-2010] §2.1 plus
the inheritance skeleton of the Sign-Based Construction Grammar analysis:

* a `FGConstruction` constraint bundle for each clause type, one field per
  parameter of variation;
* a cross-classifying `clauseType` supertype that *determines* the semantic
  type — so semantics is inherited, not stipulated per construction;
* the `filler-head-cxt` filler constraint (`[CAT nonverbal]`) stated once and
  proved inherited by all five constructions, rather than re-stipulated.

The full SBCG feature-structure unification engine (signs, MTR/DTRS feature
geometry, multiple-inheritance lattice) is out of scope for a study file; it
would live in the HPSG theory layer.

## Bridges (true by construction, not by prose)

* islands reground on the canonical RSRL signature (`Syntax/HPSG/Construction`):
  islandhood is a `Models` fact — a topicalized/exclamative construct rejects a
  second, undischarged gap (`[GAP ⟨⟩]` plus amalgamation), not a boolean stipulation;
* agreement with [sag-wasow-bender-2003]'s SLASH model on the topicalization
  island;
* divergence from [ross-1967]'s configurational Complex-NP Constraint on
  wh-relatives, which [sag-2010] re-attributes to processing
  ([hofmeister-sag-2010]);
* the surface-form correspondents map to `Features.ClauseForm`.
-/

namespace Sag2010

open Features (ClauseForm)
open HPSG

/-! ### Syntactic categories -/

/-- Syntactic categories relevant to F-G filler and head daughters. Nonverbal
categories (`NP`, `PP`, `AP`, `AdvP`) appear as fillers; verbal projections
(`S`, `CP`, `VP`) appear in the head daughter. -/
inductive SynCat
  | NP | PP | AP | AdvP | S | CP | VP
  deriving DecidableEq, Repr

/-- A category is *nonverbal* when it is not a verbal projection. [sag-2010]'s
filler-head construction constrains every filler daughter to be `[CAT nonverbal]`
((25)). -/
def SynCat.IsNonverbal (c : SynCat) : Prop :=
  c = .NP ∨ c = .PP ∨ c = .AP ∨ c = .AdvP

instance : DecidablePred SynCat.IsNonverbal :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-! ### Parameters of variation ((6)) -/

/-- The distinguished wh-element a construction requires in its filler daughter
((6a), (7)). -/
inductive FillerWh
  | noWh           -- topicalization
  | interrogative
  | exclamative
  | relative
  | degreeThe      -- the definite degree marker `the` (the-clause)
  deriving DecidableEq, Repr

/-- Inversion policy on the head daughter ((28)). Wh-interrogatives invert *iff*
the clause is independent — the IC/INV identity constraint of construction (80),
not an unconditional requirement. -/
inductive InversionPolicy
  | iffIndependent   -- INV = IC: inverted exactly when independent ((28a), (84))
  | prohibited       -- never inverted ((28b))
  | optional         -- noninitial the-clause ((28c))
  deriving DecidableEq, Repr

/-- Whether the head daughter may be infinitival ((29)). -/
inductive Finiteness
  | finiteOnly           -- always finite ((29a))
  | infinitivalPossible  -- infinitival head daughter possible ((29b))
  deriving DecidableEq, Repr

/-- Syntactic category of the head daughter ((6c), (27)). -/
inductive HeadCat
  | s        -- S
  | sOrCP    -- S or CP (the-clause, (27b))
  deriving DecidableEq, Repr

/-- The `[IC ±]` (independent-clause) status a construction imposes, with its
embedding profile ((31); §5.1, §5.3). -/
inductive ICStatus
  | mainClause     -- [IC +]: root, or embedded where main-clause phenomena are licensed
  | embeddedOnly   -- [IC −]: must be embedded (wh-relative, (91))
  | unconstrained  -- IC value free (exclamative (70), interrogative (80), the-clause)
  deriving DecidableEq, Repr

/-! ### Clause-type supertype and inherited semantics ((30)) -/

/-- The clause-type supertype an F-G construction cross-classifies with in
[sag-2010]'s type hierarchy (§3, Appendix B). A nonsubject wh-interrogative
construct is *simultaneously* a `filler-head-cxt` and an `interrogative-cl`; its
semantic type is inherited from the latter and shared with non-F-G clauses of
the same type. -/
inductive ClauseType
  | interrogativeCl
  | relativeCl
  | exclamativeCl
  | declarativeCl
  deriving DecidableEq, Repr

/-- Semantic type of a clause ((30), following [ginzburg-sag-2000]'s Vendlerian
typology of facts, propositions, questions, and outcomes). -/
inductive SemType
  | question     -- (30a) wh-interrogative
  | proposition  -- (30b) wh-relative
  | fact         -- (30c) wh-exclamative
  | austinean    -- (30d), (30e) the-clause and topicalization (proposition or outcome)
  deriving DecidableEq, Repr

/-- The semantic type is a property of the clause-type *supertype* ((30)): it is
determined by the clause type, not stipulated per construction. -/
def ClauseType.semType : ClauseType → SemType
  | interrogativeCl => .question
  | relativeCl      => .proposition
  | exclamativeCl   => .fact
  | declarativeCl   => .austinean

/-- The compositional contribution of a construction, kept distinct from the
clause's semantic type. The wh-relative clause denotes a *proposition* ((30b)),
but the wh-relative *construction* contributes a common-noun-phrase modifier
`λPλx[…]` ((90)) — two things [sag-2010] keeps separate. -/
inductive Composition
  | clausal      -- the clause's own denotation
  | cnpModifier  -- modifies a common-noun phrase (wh-relative, (90))
  deriving DecidableEq, Repr

/-! ### The construction bundle -/

/-- The constraints a filler-gap construction imposes, indexed by [sag-2010]'s
parameters of variation ((6)). Models the descriptive parameter table of §2.1;
`clauseType` records the cross-classifying supertype from which the semantic type
is inherited. The (6f) island parameter is *not* a field here — islandhood is a
`Models` fact about the construction's RSRL sort (`FGClauseType.IsIsland`), derived
from the `[GAP ⟨⟩]` principle plus amalgamation, not stored as a tag. -/
structure FGConstruction where
  /-- (6b) Allowed syntactic categories of the filler daughter ((25)). -/
  fillerCategories : List SynCat
  /-- (6a) The distinguished wh-element in the filler ((6a), (7)). -/
  fillerWh : FillerWh
  /-- (6c) Syntactic category of the head daughter ((27)). -/
  headCategory : HeadCat
  /-- (6d) Inversion policy on the head daughter ((28)). -/
  headInversion : InversionPolicy
  /-- (6d) Whether the head daughter may be infinitival ((29)). -/
  headFiniteness : Finiteness
  /-- (6e) The cross-classifying clause-type supertype, which determines the
  semantic type ((30)). -/
  clauseType : ClauseType
  /-- (6g) The `[IC ±]` status and embedding profile ((31)). -/
  ic : ICStatus
  /-- Compositional contribution; `cnpModifier` for wh-relatives ((90)). -/
  composition : Composition
  deriving Repr

/-- The semantic type of a construction, inherited from its clause supertype. -/
def FGConstruction.semType (k : FGConstruction) : SemType :=
  k.clauseType.semType

/-! ### The five constructions -/

/-- The five types of English filler-gap clause ((1)-(5)). -/
inductive FGClauseType
  | whInterrogative   -- (1) "How foolish is he?" / "I wonder how foolish he is."
  | whExclamative     -- (2) "What a fool he is!" / "It's amazing how odd it is."
  | topicalized       -- (3) "The bagels, I like."
  | whRelative        -- (4) "the person who they nominated"
  | theClause         -- (5) "The more people I met, the happier I became."
  deriving DecidableEq, Repr

/-- The five filler-gap clause types, in canonical order. -/
def allTypes : List FGClauseType :=
  [.whInterrogative, .whExclamative, .topicalized, .whRelative, .theClause]

/-- The parameter bundle of each filler-gap construction, with every value
sourced from [sag-2010] §2.1 and §5. -/
def fgParams : FGClauseType → FGConstruction
  | .whInterrogative =>
      { fillerCategories := [.NP, .PP, .AP, .AdvP]   -- (25a), (86)
        fillerWh := .interrogative
        headCategory := .s                            -- (27a)
        headInversion := .iffIndependent              -- (28a), (84): matrix inverts, embedded does not
        headFiniteness := .infinitivalPossible        -- (29b)
        clauseType := .interrogativeCl                -- (30a) → question
        ic := .unconstrained                          -- (78): matrix or embedded
        composition := .clausal }
  | .whExclamative =>
      { fillerCategories := [.NP, .PP, .AP, .AdvP]   -- (76)
        fillerWh := .exclamative
        headCategory := .s
        headInversion := .prohibited                  -- (28b)
        headFiniteness := .finiteOnly                 -- (29a)
        clauseType := .exclamativeCl                  -- (30c) → fact
        ic := .unconstrained                          -- (71): independent or embedded
        composition := .clausal }
  | .topicalized =>
      { fillerCategories := [.NP, .PP, .AP, .AdvP]   -- (25a), (63)
        fillerWh := .noWh
        headCategory := .s
        headInversion := .prohibited                  -- (28b)
        headFiniteness := .finiteOnly                 -- (29a)
        clauseType := .declarativeCl                  -- (30e) → austinean
        ic := .mainClause                             -- (61): [IC +], embeddable in MCP contexts
        composition := .clausal }
  | .whRelative =>
      { fillerCategories := [.NP, .PP]               -- (25b): finite relative NP/PP
        fillerWh := .relative
        headCategory := .s
        headInversion := .prohibited                  -- (28b)
        headFiniteness := .infinitivalPossible        -- (29b), (97)
        clauseType := .relativeCl                     -- (30b) → proposition
        ic := .embeddedOnly                           -- (91): [IC −]
        composition := .cnpModifier }                 -- (90): λPλx[…] modifies a CNP
  | .theClause =>
      { fillerCategories := [.NP, .PP, .AP, .AdvP]   -- (25a)
        fillerWh := .degreeThe
        headCategory := .sOrCP                         -- (27b): S or CP
        headInversion := .optional                    -- (28c)
        headFiniteness := .finiteOnly                 -- (29a)
        clauseType := .declarativeCl                  -- (30d) → austinean
        ic := .unconstrained
        composition := .clausal }

/-! ### Inheritance from the `filler-head-cxt` supertype

[sag-2010] derives the shared properties of filler-gap clauses from constraints
on the superordinate `filler-head-cxt`, inherited by all five subtypes — not
stipulated five times. We state the supertype constraint once and verify every
construction inherits it. -/

/-- The filler-daughter constraint imposed by the `filler-head-cxt` supertype:
the filler is `[CAT nonverbal]` ((25)). -/
def FGConstruction.FillerIsNonverbal (k : FGConstruction) : Prop :=
  ∀ cat ∈ k.fillerCategories, cat.IsNonverbal

instance : DecidablePred FGConstruction.FillerIsNonverbal :=
  fun k => inferInstanceAs (Decidable (∀ cat ∈ k.fillerCategories, cat.IsNonverbal))

/-- Every filler-gap construction inherits the `[CAT nonverbal]` filler
constraint from `filler-head-cxt` — proved once for the whole family, never a
verbal projection ((25)). -/
theorem fg_inherits_nonverbal_filler (c : FGClauseType) :
    (fgParams c).FillerIsNonverbal := by
  cases c <;> decide

/-! ### Cross-classification and inherited semantics ((30)) -/

/-- The semantic type is inherited from the clause-type supertype: it is not an
independent per-construction stipulation. -/
theorem semType_inherited (c : FGClauseType) :
    (fgParams c).semType = (fgParams c).clauseType.semType := rfl

/-- The five constructions realize all four semantic types, with topicalization
and the-clause sharing `austinean` — [sag-2010]'s point that F-G clauses are not
semantically uniform ((30)). -/
theorem semTypes :
    allTypes.map (fun c => (fgParams c).semType)
      = [.question, .fact, .austinean, .proposition, .austinean] := by
  decide

/-- Wh-interrogatives inherit `question` semantics from `interrogative-cl`, the
supertype they share with non-filler-gap (e.g. subject) interrogatives. -/
theorem interrogative_question_via_clauseType :
    (fgParams .whInterrogative).clauseType = .interrogativeCl ∧
      ClauseType.interrogativeCl.semType = .question := ⟨rfl, rfl⟩

/-- Topicalization and the-clause share the `declarative-cl` supertype, hence the
same austinean semantics — one shared fact, not two stipulations ((30d), (30e)).
The `declarative-cl` membership of topicalization follows [sag-2010]'s
Appendix-B hierarchy; construction (61) states only `↑filler-head-cxt` explicitly. -/
theorem topicalized_theClause_share_clauseType :
    (fgParams .topicalized).clauseType = (fgParams .theClause).clauseType := rfl

/-! ### Grounding in the RSRL construct hierarchy ([sag-etal-2020] Figs. 6–7)

The five clause types are sorts in the RSRL construct hierarchy (`Syntax/HPSG/Construction`), where
the filler-head inheritance and the clausal cross-classification above are *theorems about the sort
order* — the model-theoretic substrate ([richter-2000]) under the `fgParams` record. -/

/-- Each filler-gap clause type as a construct sort in the RSRL hierarchy. -/
def fgSort : FGClauseType → Construction.Srt
  | .whInterrogative => .nsWhIntCl
  | .whExclamative => .whExclCl
  | .topicalized => .topCl
  | .whRelative => .whRelCl
  | .theClause => .theCl

/-- Every clause type is a filler-head construct in the RSRL hierarchy, so it inherits
`filler-head-cxt`'s constraints (head verbal, filler↔gap token identity) proved in `Construction.lean`
— the model-theoretic ground of `fg_inherits_nonverbal_filler`. -/
theorem fgSort_filler_head (c : FGClauseType) :
    fgSort c ≤ Construction.Srt.fillerHeadCxt := by cases c <;> decide

/-- The local `ClauseType` as the matching RSRL clausal sort (Fig. 7). -/
def clauseTypeSort : ClauseType → Construction.Srt
  | .interrogativeCl => .interrogativeCl
  | .relativeCl => .relativeCl
  | .exclamativeCl => .exclamativeCl
  | .declarativeCl => .declarativeCl

/-- The RSRL clausal cross-classification agrees with the local `clauseType` assignment: each clause
type's construct sits below the RSRL clausal sort matching `(fgParams c).clauseType`. The
cross-classification of this section is thus the same fact as the RSRL sort order. -/
theorem fgSort_matches_clauseType (c : FGClauseType) :
    fgSort c ≤ clauseTypeSort (fgParams c).clauseType := by cases c <;> decide

/-! ### Inversion ((28)) -/

/-- Inversion policy across the family: only wh-interrogatives covary with
independence (the IC/INV identity of (80)); topicalization, exclamatives, and
relatives never invert ((28b)); noninitial the-clauses invert optionally
((28c)). -/
theorem inversionPolicies :
    allTypes.map (fun c => (fgParams c).headInversion)
      = [.iffIndependent, .prohibited, .prohibited, .prohibited, .optional] := by
  decide

/-! ### Islands as a property of the construction type ([sag-2010] §5.1)

[sag-2010] argues islandhood is a construction-specific `[GAP ⟨⟩]` restriction,
not universal Subjacency. Here islandhood is a **`Models` fact** about the
construction's sort in the canonical RSRL signature (`Syntax/HPSG/Construction`):
a construction is an absolute island iff its construct cannot host a second,
undischarged gap — the `[GAP ⟨⟩]` principle plus amalgamation reject it. -/

/-- A filler-gap construction is an **absolute extraction island** iff its
construct cannot host a second, undischarged gap — a `Models` fact about the RSRL
sort ((67), (73), (74)), derived from the `[GAP ⟨⟩]` principle plus amalgamation,
not stored as a tag. Each case is `¬ Models` of the construction's two-gap RSRL
worked model (`Syntax/HPSG/Construction`): an island rejects the second gap, a
non-island admits it. -/
def FGClauseType.IsIsland : FGClauseType → Prop
  | .whInterrogative => ¬ Construction.nsWhIntSecondGap.Models Construction.grammar
  | .whExclamative   => ¬ Construction.whExclSecondGap.Models Construction.grammar
  | .topicalized     => ¬ Construction.topClSecondGap.Models Construction.grammar
  | .whRelative      => ¬ Construction.whRelSecondGap.Models Construction.grammar
  | .theClause       => ¬ Construction.theClSecondGap.Models Construction.grammar

instance : DecidablePred FGClauseType.IsIsland
  | .whInterrogative =>
      inferInstanceAs (Decidable (¬ Construction.nsWhIntSecondGap.Models Construction.grammar))
  | .whExclamative =>
      inferInstanceAs (Decidable (¬ Construction.whExclSecondGap.Models Construction.grammar))
  | .topicalized =>
      inferInstanceAs (Decidable (¬ Construction.topClSecondGap.Models Construction.grammar))
  | .whRelative =>
      inferInstanceAs (Decidable (¬ Construction.whRelSecondGap.Models Construction.grammar))
  | .theClause =>
      inferInstanceAs (Decidable (¬ Construction.theClSecondGap.Models Construction.grammar))

/-- Topicalization is an absolute island ((67)): a topicalized construct with a
second gap is rejected by the `[GAP ⟨⟩]` principle. -/
theorem topicalized_isIsland : FGClauseType.topicalized.IsIsland := by decide

/-- Wh-exclamatives are absolute islands ((74)). -/
theorem exclamative_isIsland : FGClauseType.whExclamative.IsIsland := by decide

/-- Wh-interrogatives, wh-relatives, and the-clauses are not constructional
islands: a second gap amalgamates freely (no `[GAP ⟨⟩]`). For wh-relatives this
diverges from the classic Complex-NP Constraint — [sag-2010] re-attributes the
residual degradation to processing ([hofmeister-sag-2010]), not grammar. -/
theorem interrogative_relative_theClause_not_islands :
    ¬ FGClauseType.whInterrogative.IsIsland ∧
      ¬ FGClauseType.whRelative.IsIsland ∧
      ¬ FGClauseType.theClause.IsIsland := by
  decide

/-- The filler-gap constructions that are absolute extraction islands — exactly
those whose construct rejects a second gap ((67), (73), (74)). Computed from the
RSRL `Models` verdict, not stipulated. -/
def islandConstructions : List FGClauseType :=
  allTypes.filter (fun c => decide c.IsIsland)

/-- Exactly wh-exclamatives and topicalization are filler-gap islands. -/
theorem islandConstructions_eq :
    islandConstructions = [.whExclamative, .topicalized] := by
  decide

/-! ### Reconciliation with the Ross taxonomy and the HPSG mechanism

[sag-2010]'s construction-typed islands classify *whole construction types*,
orthogonal to [ross-1967]'s configurational island *domains*. The
chronologically-later account (Sag) draws the comparison. -/

/-- The construction-typed `IsIsland` verdicts are grounded in the same RSRL gap mechanism as the SLASH
analysis: the model-theoretic content of an absolute island is `[GAP ⟨⟩]` plus amalgamation blocking a
second gap. Derived from [sag-wasow-bender-2003]'s authoritative `islands_rsrl_grounded` (over the
canonical `Syntax/HPSG/Construction` signature), not re-stated — the construction-tag level and the
gap-list mechanism agree. -/
theorem island_grounded_in_rsrl :
    ¬ Construction.islandTwoGap.Models Construction.grammar :=
  SagWasowBender2003.islands_rsrl_grounded.2.1

/-- Agreement with [sag-wasow-bender-2003]: the topicalization island is the same
datum in two analyses — Sag's `[GAP ⟨⟩]` topicalization construct and the generic
HPSG SLASH model both block a second gap. -/
theorem topicalized_island_agrees_swb :
    FGClauseType.topicalized.IsIsland ∧
      ¬ Construction.islandTwoGap.Models Construction.grammar :=
  ⟨by decide, SagWasowBender2003.islands_rsrl_grounded.2.1⟩

/-- The sharpest divergence from [ross-1967]: the relative clause is Ross's
paradigm Complex-NP-Constraint island, yet [sag-2010]'s wh-relative construction
is no grammatical island — its construct *admits* a second gap, whereas a
configurational island (Ross's CNPC domain, modeled as a generic absolute island)
blocks it. The residual effect is processing, not grammar ([hofmeister-sag-2010]). -/
theorem relative_diverges_from_cnpc :
    Construction.whRelSecondGap.Models Construction.grammar ∧
      ¬ Construction.islandTwoGap.Models Construction.grammar :=
  ⟨by decide, SagWasowBender2003.islands_rsrl_grounded.2.1⟩

/-! ### Surface clause form (bridge to `Features.ClauseForm`) -/

/-- Surface clause form, where a construction has a direct correspondent in
`Features.ClauseForm`. Wh-interrogatives map to the independent (matrix) form;
topicalization and the-clause are declarative; exclamatives and relatives have no
`ClauseForm` correspondent. -/
def clauseForm : FGClauseType → Option ClauseForm
  | .whInterrogative => some .matrixQuestion
  | .topicalized     => some .declarative
  | .theClause       => some .declarative
  | .whExclamative   => none
  | .whRelative      => none

/-- Topicalization corresponds to a declarative surface form. -/
theorem topicalized_is_declarative_form :
    clauseForm .topicalized = some .declarative := rfl

/-- Wh-interrogatives correspond to the matrix-question surface form. -/
theorem interrogative_is_question_form :
    clauseForm .whInterrogative = some .matrixQuestion := rfl

/-! ### Wh-word inventory (Table 1)

[sag-2010]'s Table 1 classifies each wh-form *by syntactic category* with a
three-valued judgment (`+` full, `%` for some speakers, `-` excluded) across the
three wh-construction types. The category splits carry Sag's central claim that
'wh-expression' is not a unitary category (§2.1). Where Table 1 and the worked
examples diverge (e.g. `what`·NP relative is `-` in the table but `%` at (11c)),
this transcribes the printed table. -/

/-- A three-valued participation judgment (Table 1: `+`, `%`, `-`). -/
inductive WhStatus
  | full          -- +
  | someSpeakers  -- %
  | excluded      -- -
  deriving DecidableEq, Repr

/-- The wh-forms of Table 1. -/
inductive WhForm
  | who | whose | what | whatA | which | how | when | whereWh | why
  deriving DecidableEq, Repr

/-- The syntactic categories a wh-form bears in Table 1. -/
inductive WhCategory
  | np | det | detSing | detPl | degree | advpManner | ap | ppTime | ppPlace | ppReason
  deriving DecidableEq, Repr

/-- One row of Table 1: a wh-form in a given category, with its participation in
each of the three wh-construction types. -/
structure WhWordProfile where
  form : WhForm
  category : WhCategory
  interrogative : WhStatus
  exclamative : WhStatus
  relative : WhStatus
  deriving DecidableEq, Repr

/-- [sag-2010] Table 1, faithful to its category splits and three-valued
judgments. -/
def whWordProfiles : List WhWordProfile :=
  [ { form := .who,     category := .np,         interrogative := .full,     exclamative := .excluded,     relative := .full }
  , { form := .whose,   category := .det,        interrogative := .full,     exclamative := .excluded,     relative := .full }
  , { form := .what,    category := .np,         interrogative := .full,     exclamative := .excluded,     relative := .excluded }
  , { form := .what,    category := .detSing,    interrogative := .full,     exclamative := .someSpeakers, relative := .excluded }
  , { form := .what,    category := .detPl,      interrogative := .full,     exclamative := .full,         relative := .excluded }
  , { form := .what,    category := .degree,     interrogative := .full,     exclamative := .full,         relative := .excluded }
  , { form := .whatA,   category := .detSing,    interrogative := .excluded, exclamative := .full,         relative := .excluded }
  , { form := .which,   category := .np,         interrogative := .excluded, exclamative := .excluded,     relative := .full }
  , { form := .which,   category := .det,        interrogative := .full,     exclamative := .excluded,     relative := .someSpeakers }
  , { form := .how,     category := .advpManner, interrogative := .full,     exclamative := .full,         relative := .someSpeakers }
  , { form := .how,     category := .ap,         interrogative := .full,     exclamative := .excluded,     relative := .excluded }
  , { form := .how,     category := .degree,     interrogative := .full,     exclamative := .full,         relative := .excluded }
  , { form := .when,    category := .ppTime,     interrogative := .full,     exclamative := .excluded,     relative := .full }
  , { form := .whereWh, category := .ppPlace,    interrogative := .full,     exclamative := .excluded,     relative := .full }
  , { form := .why,     category := .ppReason,   interrogative := .full,     exclamative := .excluded,     relative := .full }
  ]

/-- No wh-form/category row is a `full` participant in all three construction
types — [sag-2010]'s point that 'wh-expression' is not a unitary category
(§2.1). The closest cases (e.g. manner `how`) are only `%` in the relative
column. -/
theorem no_universal_wh_word :
    ∀ w ∈ whWordProfiles,
      ¬ (w.interrogative = .full ∧ w.exclamative = .full ∧ w.relative = .full) := by
  decide

/-- The manner wh-word `how` participates fully in both interrogatives and
exclamatives — one of the few wh-forms crossing that boundary ((18)-(20)). -/
theorem how_crosses_interrogative_exclamative :
    ∃ w ∈ whWordProfiles,
      w.form = .how ∧ w.interrogative = .full ∧ w.exclamative = .full := by
  decide

end Sag2010
