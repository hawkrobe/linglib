import Mathlib.Data.Finset.Basic
import Linglib.Features.Acceptability
import Linglib.Fragments.Japanese.Case
import Linglib.Theories.Syntax.Case.Dependent
import Linglib.Core.Case.Grammaticalization
/-!
# Sadakane & Koizumi 1995 @cite{sadakane-koizumi-1995} @cite{martin-1975}

*On the nature of the "dative" particle ni in Japanese*. Linguistics 33(1):5–33.

## Headline claim

The apparent ambiguity of Japanese particle *ni* between case marker and
postposition is **illusory** (Conclusion, p. 23). What looks like a
single particle with mixed properties is actually four homophonous
lexemes:

1. **Dative case marker *ni*** (Martin (1975) categories A, O1)
2. **Postposition *ni*** (categories B, C1–C3, E, F, G, H1–H3, I, K, L1, M, O2, R, T, U)
3. ***ni* of *ni*-insertion** (J1, J2, L2; Takezawa 1987's Japanese analogue
   of English *of*-insertion — a last-resort default for caseless arguments)
4. **Copula *ni*** (P1, P2, Q, S, V; a form of the copula *da/de aru*)

Plus an **ambiguous** bucket (D, N1, N2) where speakers disagree on
whether *ni* is a case marker or a postposition; encoded as
`Classification.classify _ = none`.

S&K SUPPORT @cite{kuno-1987}'s and Miyagawa (1989)'s case-marker /
postposition dichotomy — once the four homophones are split apart, the
remainder respects the binary partition. This is in contrast to the
"third-type" view (a single *ni* with both case-marker and postposition
properties) widely held in Japanese linguistics.

## Three operational tests (§2)

S&K distinguish the four types by three syntactic diagnostics, summarised
in tables 14, 27, 29, and 32:

| Type                | Floating NQ | Cleft + particle | Cleft − particle |
|---------------------|-------------|------------------|------------------|
| Dative case marker  | OK          | */??              | OK               |
| Postposition        | *           | OK               | */?/OK           |
| Ambiguous (D,N1,N2) | OK          | OK               | OK               |
| *ni*-insertion      | *           | */??              | OK               |
| Copula *ni*         | */N.A.      | */??              | */??             |

The diagnostic acceptability scores are encoded in `Features.Acceptability`
(the project canon): `*/??` reduces to `unacceptable`; `*/?/OK` to
`variable` (genuine speaker variation); `*/N.A.` to `unacceptable` (per
S&K fn. 10, the test fails for an independent non-referentiality reason
PLUS a second structural reason — both yield `*`).

## Affectedness criterion (§4, p. 18)

> "The case marker *ni* is attached to an NP whose referent is relatively
> more affected by the action denoted by the verb (predicate/sentence),
> and the postposition *ni* is attached to an NP whose referent is less
> affected." (p. 18)

Hierarchy (figure 45, p. 22) carries TWO orthogonal dimensions: a 4-rank
position scale (NP-in-PP < dative NP < upper accusative NP < lower
accusative NP) and an `AffectedKind` distinction (phenomenally vs.
structurally affected). Examples 42–43: *Tom-o korosita* "killed Tom"
structurally affects Tom (he ceases to exist as such); *Bill-o hometa*
"praised Bill" only phenomenally affects Bill's psychological state.

## Acquisition prediction (§5, pp. 23–24)

If S&K's analysis is correct (case-marker and postposition *ni* are
distinct lexemes), Japanese-learning children should acquire them
independently. Morii (1993) confirms: case-marker *ni* (categories A, O1)
is acquired between 2;0 and 2;11; postposition *ni* (categories B–U) is
acquired only after 3;0.

## Heine 2009 grammaticalization

The four S&K classifications align partially with Heine's case
grammaticalization cline (`Core.CaseGramStage`: lexical → adposition →
caseAffix → lost). Both case-marker *ni* and postposition *ni* are at
`.adposition` stage in modern Japanese (morphologically free), but
case-marker *ni* is more grammaticalized within that stage (no inherent
meaning, omissible in casual speech). The cline doesn't capture
intra-adposition gradience; the projection `Classification.gramStage` is
correspondingly coarse.

## Layered grounding to linglib

- Diagnostic acceptability scores use `Features.Acceptability` (the
  project canon), not a per-paper Grammaticality enum.
- `Classification.marantz` aligns S&K's 4-way with @cite{baker-2015}'s
  `Syntax.Case.CaseSource` from `Theories.Syntax.Case.Dependent`. The map
  is partial: copula *ni* lies outside Marantz's case-assignment domain.
  Note: `.niInsertion → .unmarked` (Marantz/Schütze's "default-case"
  fallback) rather than `.agree` — Takezawa's salvage operation is what
  happens *when Agree fails*, not Agree itself.
- `MartinCategory.InFragmentNi` is **derived** as a `Finset` intersection
  of the per-category `fragmentCases` footprint with the Fragment's
  `Fragments.Japanese.Case.ni.cases = {.dat, .loc, .all, .Tem}`. The
  conflation theorem `fragment_ni_predicts_inconsistent_signatures`
  derives the Tsujimura/Fragment vs. S&K granularity disagreement as a
  real claim about set intersection plus diagnostic-signature mismatch.

## Dialect parameter

S&K's footnote 9 (p. 30) flags that judgments throughout the paper are
from the **innovating** dialect (per @cite{kuno-1987}, Miyagawa 1989).
The **conservative** dialect (Shibatani 1977) gives different judgments
for some categories (notably K, *Ohaio Ginkoo-ni* 'work for Ohio Bank').
This Studies file's `Classification.signature` reflects the innovating
dialect; a future `Phenomena/Case/Studies/Shibatani1977.lean` could
formalise the conservative judgments and surface where they diverge.
The `Dialect` enum is intentionally NOT introduced here (was dead code
in the previous version) — it earns its keep when the conservative file
lands.

## Korean parallel (Sells 1995, not yet in linglib)

Sells (1995, *Journal of East Asian Linguistics*) documents the parallel
case-particle/postposition split for Korean *-i*/*-eseo* but does not
engage S&K's homophony move for Korean equivalents of *ni*. This gap
cannot be Lean-formalised until `Fragments/Korean/Case.lean` adopts
Pattern B (rich marker structure); currently it's a `Finset Core.Case`
stipulation only. Documented here as future work.
-/

namespace Phenomena.Case.Studies.SadakaneKoizumi1995

open Features (Acceptability)

/-! ## §1 Classification — S&K's four homophonous *ni* lexemes -/

/-- S&K's classification of *ni* into four distinct homophonous lexemes
    (§4 Discussion, summarised in Conclusion §5). The "ambiguous" cases
    (D, N1, N2) are encoded as `none` via `Option Classification` rather
    than a separate constructor — speakers genuinely vary on which of
    `.dativeCaseMarker` or `.postposition` these belong to. -/
inductive Classification where
  /-- Categories A (goal indirect object) and O1 (change of position
      with intransitive verb). Behaves like accusative *o* and nominative
      *ga*: omissible in casual speech, no inherent meaning. -/
  | dativeCaseMarker
  /-- The 18 categories B, C1–C3, E, F, G, H1–H3, I, K, L1, M, O2, R, T, U.
      Bears inherent meaning; non-omissible. -/
  | postposition
  /-- Categories J1, J2, L2. Per Takezawa 1987, *ni* is inserted onto
      caseless arguments of certain predicates (causativised verbs) as a
      last-resort default; the Japanese analogue of English *of*-insertion. -/
  | niInsertion
  /-- Categories P1, P2, Q, S, V. *ni* attached to a "predicate" of
      some sort, related to copula *da/de aru* constructions. -/
  | copula
  deriving DecidableEq, Repr, Fintype

/-! ## §2 Martin (1975) usage categories — 31 letter codes

The 31 categories follow @cite{martin-1975}'s reference grammar; S&K adopt
his classification with minor modifications (see §2 fn. 3). Each category
in the appendix (pp. 23–33) is exemplified by one or more verbs.
-/

/-- The 31 usage categories of Japanese *ni* per @cite{martin-1975}, as
    reported in S&K's Appendix (pp. 23–33). Letter codes are S&K's. -/
inductive MartinCategory where
  | A | B | C1 | C2 | C3 | D | E | F | G
  | H1 | H2 | H3 | I | J1 | J2 | K | L1 | L2
  | M | N1 | N2 | O1 | O2 | P1 | P2 | Q | R | S | T | U | V
  deriving DecidableEq, Repr, Fintype

namespace MartinCategory

/-- Ascription of each Martin category to one of S&K's four classification
    types. The "ambiguous" categories (D, N1, N2) return `none`; speakers
    differ on whether the *ni* in these contexts is a case marker or a
    postposition. -/
def classify : MartinCategory → Option Classification
  | .A | .O1                                 => some .dativeCaseMarker
  | .D | .N1 | .N2                           => none  -- ambiguous
  | .J1 | .J2 | .L2                          => some .niInsertion
  | .P1 | .P2 | .Q  | .S  | .V               => some .copula
  | .B  | .C1 | .C2 | .C3 | .E  | .F  | .G
  | .H1 | .H2 | .H3 | .I  | .K  | .L1 | .M
  | .O2 | .R  | .T  | .U                     => some .postposition

/-- Per-category footprint on the `Core.Case` lattice — what UD case
    feature(s) the *ni*-use of this Martin category corresponds to most
    directly. Categories whose *ni*-use does NOT fit any UD case feature
    Tsujimura's Fragment recognises (`Fragments.Japanese.Case.ni.cases =
    {.dat, .loc, .all, .Tem}`) map to `∅`. This is study-internal
    stipulation (the lin agent verified F's mapping is empty per the
    *GB riron-ni motozuiteiru* example). -/
def fragmentCases : MartinCategory → Finset Core.Case
  | .A                  => {.dat}            -- goal indirect object
  | .O1                 => {.dat, .all}      -- change of position (riding ON something)
  | .L1                 => {.loc}            -- locative-of-existence
  | .N1 | .N2           => {.dat, .all}      -- dative of direction (S&K-ambiguous)
  | .M                  => {.Tem}            -- specific time
  | _                   => ∅                 -- not in Fragment.ni.cases coverage

/-- Whether the Fragment's single `ni : CaseMarker` (with
    `cases = {.dat, .loc, .all, .Tem}`) covers the *ni* uses of a given
    Martin category. Derived as the non-emptiness of the intersection
    between the category's `fragmentCases` footprint and the Fragment's
    `ni.cases` — a real `Finset` operation rather than a stipulated
    lookup table. -/
def InFragmentNi (c : MartinCategory) : Prop :=
  (c.fragmentCases ∩ Fragments.Japanese.Case.ni.cases).Nonempty

instance (c : MartinCategory) : Decidable c.InFragmentNi := by
  unfold InFragmentNi; infer_instance

end MartinCategory

/-! ## §3 Operational tests + diagnostic signature

Per S&K §2 (pp. 8–11), three syntactic tests distinguish the four types.
The signatures in tables 14, 29, 32 are encoded as `Classification.signature`.
Split judgments in the source (e.g., `*/??`, `*/?/OK`) are reduced to
`Acceptability` per the convention: `*/??` → `unacceptable` (split with `*`
floor); `*/?/OK` → `variable` (genuinely speaker-dependent); `*/N.A.` →
`unacceptable` (per fn 10, S&K's two-reason analysis: non-referentiality
PLUS structural blocking, both yielding `*`).
-/

/-- The three operational diagnostics S&K apply to each Martin category. -/
inductive OperationalTest where
  /-- Floating numeral quantifier construction (§2, p. 8): the c-command
      requirement between numeral and host NP is blocked by an intervening
      PP node. Case markers permit FNQ; postpositions block it. -/
  | floatingNQ
  /-- Clefting with the particle in focus position (§2, p. 9): PPs may
      occupy focus position; NPs with case markers may not. -/
  | cleftWithParticle
  /-- Clefting without the particle (§2, p. 10): a Hoji-1987 / Inoue-1976
      "aboutness" cleft variant. Behaviour distinguishes copula *ni* from
      the others. -/
  | cleftWithoutParticle
  deriving DecidableEq, Repr, Fintype

namespace Classification

/-- The acceptability signature S&K predict for each `Classification` ×
    `OperationalTest` pair (tables 14, 29, 32). -/
def signature : Classification → OperationalTest → Acceptability
  -- Dative case marker (table 14, top row): OK | */?? | OK
  | .dativeCaseMarker, .floatingNQ           => .ok
  | .dativeCaseMarker, .cleftWithParticle    => .unacceptable
  | .dativeCaseMarker, .cleftWithoutParticle => .ok
  -- Postposition (table 14, bottom row): * | OK | */?/OK
  | .postposition,     .floatingNQ           => .unacceptable
  | .postposition,     .cleftWithParticle    => .ok
  | .postposition,     .cleftWithoutParticle => .variable
  -- ni-of-ni-insertion (table 29): * | */?? | OK
  | .niInsertion,      .floatingNQ           => .unacceptable
  | .niInsertion,      .cleftWithParticle    => .unacceptable
  | .niInsertion,      .cleftWithoutParticle => .ok
  -- Copula ni (table 32): */N.A. | */?? | */??
  | .copula,           .floatingNQ           => .unacceptable
  | .copula,           .cleftWithParticle    => .unacceptable
  | .copula,           .cleftWithoutParticle => .unacceptable

end Classification

/-! ## §4 Cardinality theorems — Finset.card decomposition

The audit-promised "test the data, not the constructor" theorems —
verifying that S&K's distribution of 31 Martin categories into 4 types
+ 3 ambiguous matches the paper's own count.
-/

/-- Number of Martin categories classified as `dativeCaseMarker` (§3, p. 11:
    "two categories of *ni* … behave purely as case markers"). -/
theorem card_dativeCaseMarker :
    (Finset.univ.filter (fun c : MartinCategory => c.classify = some .dativeCaseMarker)).card = 2 := by
  decide

/-- Number of Martin categories classified as `postposition` (§3, p. 12:
    "Eighteen categories of *ni* in our list turned out to be postpositions"). -/
theorem card_postposition :
    (Finset.univ.filter (fun c : MartinCategory => c.classify = some .postposition)).card = 18 := by
  decide

/-- Number of categories where speakers vary (S&K's "ambiguous" bucket;
    §3, p. 14: D, N1, N2 — the three categories listed in (23)). -/
theorem card_ambiguous :
    (Finset.univ.filter (fun c : MartinCategory => c.classify = none)).card = 3 := by
  decide

/-- Number of *ni*-of-*ni*-insertion categories (§3, p. 16: J1, J2, L2). -/
theorem card_niInsertion :
    (Finset.univ.filter (fun c : MartinCategory => c.classify = some .niInsertion)).card = 3 := by
  decide

/-- Number of copula *ni* categories (§3, p. 17: P1, P2, Q, S, V). -/
theorem card_copula :
    (Finset.univ.filter (fun c : MartinCategory => c.classify = some .copula)).card = 5 := by
  decide

/-- The five sub-counts decompose the universe of 31 Martin categories. -/
theorem card_decomposition :
    (Finset.univ : Finset MartinCategory).card = 31 := by decide

/-! ## §5 Conflation: Fragment's `ni` collapses S&K types

`Fragments/Japanese/Case.lean` exposes a single `ni : CaseMarker` entry
(consistent with @cite{tsujimura-2014}'s textbook presentation). S&K's
4-way analysis would split this entry into multiple lexemes. The
following theorems make the granularity disagreement Lean-visible: the
Fragment's `ni` covers Martin categories with INCONSISTENT diagnostic
signatures, refuting the unitary-`ni` treatment.
-/

/-- The Fragment's `ni` covers Martin categories from at least two
    distinct S&K classifications — *.dativeCaseMarker* (witnessed by A)
    and *.postposition* (witnessed by L1). -/
theorem fragment_ni_covers_two_sk_types :
    ∃ c1 c2 : MartinCategory,
      c1.InFragmentNi ∧ c2.InFragmentNi ∧
      c1.classify ≠ c2.classify :=
  ⟨MartinCategory.A, MartinCategory.L1, by decide, by decide, by decide⟩

/-- Stronger statement: the Fragment's `ni` straddles three S&K cells —
    case marker (A), postposition (L1), and ambiguous (N1). -/
theorem fragment_ni_conflates_three_sk_cells :
    (∃ c : MartinCategory, c.InFragmentNi ∧ c.classify = some .dativeCaseMarker) ∧
    (∃ c : MartinCategory, c.InFragmentNi ∧ c.classify = some .postposition) ∧
    (∃ c : MartinCategory, c.InFragmentNi ∧ c.classify = none) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨MartinCategory.A, by decide, by decide⟩
  · exact ⟨MartinCategory.L1, by decide, by decide⟩
  · exact ⟨MartinCategory.N1, by decide, by decide⟩

/-- The empirical bite of the homophony argument: the Fragment's single
    `ni` covers Martin categories whose S&K-predicted diagnostic
    signatures DISAGREE on at least one operational test. A unitary `ni`
    lexeme entails one verdict per test, but the data show two. The
    Fragment's lexicon is empirically inadequate as encoded. -/
theorem fragment_ni_predicts_inconsistent_signatures :
    ∃ c1 c2 : MartinCategory, ∃ cl1 cl2 : Classification, ∃ t : OperationalTest,
      c1.InFragmentNi ∧ c2.InFragmentNi ∧
      c1.classify = some cl1 ∧ c2.classify = some cl2 ∧
      Classification.signature cl1 t ≠ Classification.signature cl2 t := by
  refine ⟨MartinCategory.A, MartinCategory.L1,
          .dativeCaseMarker, .postposition, .floatingNQ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §6 Alignment with Marantz dependent case

S&K's 4-way classification partially aligns with Marantz/Baker's
`CaseSource` (`lexical | dependent | unmarked | agree`), encoded in
`Theories.Syntax.Case.Dependent`. Per the cross-framework reasoning:

- Dative case marker *ni* — assigned by structural configuration → `dependent`
- Postposition *ni* — bears inherent meaning, attached to NP via P head → `lexical`
- *ni*-of-*ni*-insertion — Takezawa 1987's last-resort salvage on caseless
  arguments → `unmarked` (Marantz/Schütze 2001 default-case fallback);
  NOT `agree` (which is T/D-driven probing, distinct from the salvage
  operation S&K formalise via Takezawa)
- Copula *ni* — outside Marantz's case-assignment domain (it's a copular
  construction, not case marking) → `none`
-/

open Syntax.Case (CaseSource)

namespace Classification

/-- Partial map from S&K's 4-way *ni* taxonomy to Marantz/Baker's
    `CaseSource`. Copula *ni* maps to `none` (outside Marantz's domain). -/
def marantz : Classification → Option CaseSource
  | .dativeCaseMarker => some .dependent
  | .postposition     => some .lexical
  | .niInsertion      => some .unmarked
  | .copula           => none

end Classification

/-- The Takezawa-vs-Chomsky alignment for *ni*-insertion is genuinely
    underdetermined: Schütze 2001-style default case (`.unmarked`) is the
    closer fit to Takezawa 1987's "salvage on caseless argument", but a
    Chomsky 2000-style functional-head Agree analysis would assign
    `.agree`. The two readings make different predictions for whether
    *ni*-inserted NPs are visible to T-Agree. This Studies file picks
    `.unmarked`; the disagreement is recorded explicitly. -/
theorem niInsertion_alignment_underdetermined :
    Classification.marantz .niInsertion = some .unmarked ∧
    (some CaseSource.agree : Option CaseSource) ≠ some .unmarked := by
  refine ⟨rfl, ?_⟩; decide

/-! ## §7 Affectedness hierarchy (§4, figure 45)

S&K's semantic correlate for the case-marker/postposition split: case
markers attach to MORE-affected NPs, postpositions to LESS-affected ones.
The hierarchy spans 4 syntactic positions on a rank dimension PLUS a
phenomenally-vs-structurally split on an affectedness-kind dimension —
two orthogonal axes per figure 45.
-/

/-- The four syntactic positions in S&K's affectedness hierarchy
    (figure 45, p. 22). Ordered from least to most affected on the
    rank dimension. -/
inductive SyntacticPosition where
  /-- NP inside a PP (least affected). -/
  | npInPP
  /-- Dative NP (indirect object). Phenomenally affected. -/
  | dativeNP
  /-- Upper accusative NP (e.g., direct object of *praise*). Phenomenally
      affected (psychological state altered). -/
  | upperAccusativeNP
  /-- Lower accusative NP (e.g., direct object of *kill*). Structurally
      affected (referent's existence/identity altered). -/
  | lowerAccusativeNP
  deriving DecidableEq, Repr, Fintype

/-- The kind of affectedness, orthogonal to rank (§4, examples 42–43,
    p. 21–22). Phenomenal = referent's psychological/relational state
    altered (*hometa* "praised", *nagutta* "hit" — only part of body).
    Structural = referent's existence or identity altered (*korosita*
    "killed", *tabeta* "ate"). -/
inductive AffectedKind where
  | phenomenal
  | structural
  deriving DecidableEq, Repr, Fintype

namespace SyntacticPosition

/-- Affectedness rank: higher = more affected. -/
def affectednessRank : SyntacticPosition → Nat
  | .npInPP             => 0
  | .dativeNP           => 1
  | .upperAccusativeNP  => 2
  | .lowerAccusativeNP  => 3

/-- The kind of affectedness associated with each position: phenomenal
    for dative and upper-accusative; structural for lower-accusative;
    none for NP-in-PP (unaffected). -/
def kindOf : SyntacticPosition → Option AffectedKind
  | .npInPP             => none           -- unaffected
  | .dativeNP           => some .phenomenal
  | .upperAccusativeNP  => some .phenomenal
  | .lowerAccusativeNP  => some .structural

theorem npInPP_least_affected (p : SyntacticPosition) :
    npInPP.affectednessRank ≤ p.affectednessRank := by cases p <;> decide

theorem lowerAcc_most_affected (p : SyntacticPosition) :
    p.affectednessRank ≤ lowerAccusativeNP.affectednessRank := by cases p <;> decide

/-- Dative NPs are MORE affected than NPs in PPs (the case-marker /
    postposition affectedness contrast, p. 18). -/
theorem dative_more_than_pp :
    npInPP.affectednessRank < dativeNP.affectednessRank := by decide

/-- Accusative NPs are more affected than dative NPs (p. 21 caveat). -/
theorem accusative_more_than_dative :
    dativeNP.affectednessRank < upperAccusativeNP.affectednessRank := by decide

/-- Lower-accusative is the unique structurally-affected position. -/
theorem lowerAcc_unique_structural :
    ∀ p : SyntacticPosition, p.kindOf = some .structural → p = .lowerAccusativeNP := by
  intro p hp; cases p <;> simp_all [kindOf]

end SyntacticPosition

/-! ## §8 Acquisition prediction (Morii 1993, cited at §5 p. 23–24)

S&K's homophony analysis predicts that case-marker *ni* and postposition
*ni* are independent lexical items, hence acquired independently. Morii
1993 confirms: case-marker categories (A, O1) are acquired between ages
2;0 and 2;11; postposition categories (B–U) are acquired only after 3;0.

Encoded as a discrete acquisition order rather than absolute ages —
the substantive prediction is the strict ordering, not the precise ages.
-/

namespace Classification

/-- Acquisition order per Morii 1993: lower number = acquired earlier.
    Only the dative-case-marker / postposition contrast is reported by
    Morii; the other two types' acquisition orders are not specified. -/
def acquisitionOrder : Classification → Option Nat
  | .dativeCaseMarker => some 0  -- 2;0–2;11
  | .postposition     => some 1  -- after 3;0
  | .niInsertion      => none    -- not addressed by Morii 1993
  | .copula           => none    -- not addressed by Morii 1993

end Classification

/-- Case-marker *ni* is acquired strictly before postposition *ni*
    (Morii 1993, vindicating S&K's homophony analysis). Universally
    quantified form: every concrete acquisition-order witness for the
    case-marker class precedes every witness for the postposition class. -/
theorem case_marker_acquired_before_postposition :
    ∀ a b : Nat,
      Classification.acquisitionOrder .dativeCaseMarker = some a →
      Classification.acquisitionOrder .postposition     = some b →
      a < b := by
  intro a b ha hb
  simp only [Classification.acquisitionOrder, Option.some.injEq] at ha hb
  omega

/-! ## §9 Heine grammaticalization stage projection

Connects S&K's classification to `Core.CaseGramStage` (Heine 2009's
case grammaticalization cline: lexical → adposition → caseAffix → lost).
Both case-marker *ni* and postposition *ni* are at `.adposition` stage
in modern Japanese (morphologically free); the cline doesn't capture
intra-adposition gradience, so the projection is correspondingly coarse.
The diachronic prediction (case-marker *ni* should be CLOSER to
`.caseAffix` than postposition *ni*) is documented in prose pending a
finer-grained stage type.
-/

namespace Classification

/-- Heine grammaticalization stage projection. Both case-marker and
    postposition *ni* are at `.adposition` in modern Japanese; copula *ni*
    is outside the case cline (`none`). -/
def gramStage : Classification → Option Core.CaseGramStage
  | .dativeCaseMarker => some .adposition
  | .postposition     => some .adposition
  | .niInsertion      => some .adposition
  | .copula           => none

end Classification

/-- All case-relevant *ni* lexemes are at the `.adposition` stage on
    Heine's cline. The diachronic prediction that case-marker *ni* is
    MORE grammaticalized (closer to `.caseAffix`) than postposition *ni*
    is currently invisible at this granularity — `CaseGramStage` lacks
    intra-stage gradience. -/
theorem case_ni_lexemes_all_adposition :
    Classification.gramStage .dativeCaseMarker = some .adposition ∧
    Classification.gramStage .postposition     = some .adposition ∧
    Classification.gramStage .niInsertion      = some .adposition := by
  refine ⟨rfl, rfl, rfl⟩

end Phenomena.Case.Studies.SadakaneKoizumi1995
