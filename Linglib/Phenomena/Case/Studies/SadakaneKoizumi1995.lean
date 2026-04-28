import Linglib.Features.Acceptability
import Linglib.Fragments.Japanese.Case
import Linglib.Theories.Syntax.Case.Dependent
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
   of English *of*-insertion)
4. **Copula *ni*** (P1, P2, Q, S, V; a form of the copula *da/de aru*)

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

## Affectedness criterion (§4, p. 18)

> "The case marker *ni* is attached to an NP whose referent is relatively
> more affected by the action denoted by the verb (predicate/sentence),
> and the postposition *ni* is attached to an NP whose referent is less
> affected." (p. 18)

Hierarchy (figure 45, p. 22): NP-in-PP < dative NP < upper accusative NP <
lower accusative NP, with phenomenally-affected vs. structurally-affected
as the metric distinguishing dative from accusative.

## Acquisition prediction (§5, pp. 23–24)

If S&K's analysis is correct (case-marker and postposition *ni* are
distinct lexemes), Japanese-learning children should acquire them
independently. Morii (1993) confirms: case-marker *ni* (categories A, O1)
is acquired between 2;0 and 2;11; postposition *ni* (categories B–U) is
acquired only after 3;0.

## Layered grounding to linglib

- Diagnostic acceptability scores use `Features.Acceptability` (the
  project canon), not a per-paper Grammaticality enum.
- `Classification.toMarantz` aligns S&K's 4-way with
  @cite{baker-2015}'s `Syntax.Case.CaseSource` from
  `Theories.Syntax.Case.Dependent`. The map is partial: copula *ni* lies
  outside Marantz's case-assignment domain.
- `MartinCategory.inFragmentNi` identifies which of the 31 Martin
  categories the Fragment's single `Fragments.Japanese.Case.ni` entry
  collapses; the conflation theorem `fragment_ni_conflates_sk_types`
  derives the Tsujimura/Fragment vs. S&K granularity disagreement as a
  Lean theorem (currently rotting as docstring promise in
  `Fragments/Japanese/Case.lean`).

## Dialect parameter

S&K's footnote 9 (p. 30) notes judgments are from the **innovating**
dialect (Miyagawa 1989); the **conservative** dialect (Shibatani 1977)
gives different judgments for some categories. This Fragment encodes
the innovating data; the `Dialect` enum is provided for future
specialisation.
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
      caseless arguments of certain predicates (causativised verbs);
      the Japanese analogue of English *of*-insertion. -/
  | niInsertion
  /-- Categories P1, P2, Q, S, V. *ni* attached to a "predicate" of
      some sort, related to copula *da/de aru* constructions. -/
  | copula
  deriving DecidableEq, Repr

namespace Classification

/-- Short label for documentation/error messages. -/
def label : Classification → String
  | .dativeCaseMarker => "dative case marker"
  | .postposition     => "postposition"
  | .niInsertion      => "ni-of-ni-insertion"
  | .copula           => "copula ni"

end Classification

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
  deriving DecidableEq, Repr

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

/-- Short prose label per @cite{martin-1975}'s classification, as reported
    in S&K's Appendix (pp. 23–33). Used for documentation; not consumed
    by any theorem. -/
def label : MartinCategory → String
  | .A  => "Goal indirect object"
  | .B  => "Benefactive"
  | .C1 => "Dative of confrontation with adjectival predicate"
  | .C2 => "Dative of confrontation with adjectival nominal predicate"
  | .C3 => "Dative of confrontation with verbal predicate"
  | .D  => "Pseudo-reciprocal use of dative confrontation"
  | .E  => "Objective stimulus"
  | .F  => "Dependent etc. on"
  | .G  => "From/by agent"
  | .H1 => "Underlying agent of direct passive"
  | .H2 => "Underlying agent of indirect passive (intransitive)"
  | .H3 => "Underlying agent of indirect passive (transitive)"
  | .I  => "Instigator of passivized causative"
  | .J1 => "Underlying agent of causativised intransitive"
  | .J2 => "Underlying agent of causativised transitive"
  | .K  => "Pseudo-agent by/at"
  | .L1 => "Indirect subject — possessor"
  | .L2 => "Indirect subject — possessor (insertion variant)"
  | .M  => "Specific time"
  | .N1 => "Dative of direction with intransitive"
  | .N2 => "Dative of direction with transitive"
  | .O1 => "Change of position with intransitive"
  | .O2 => "Change of position with transitive"
  | .P1 => "Change of state with intransitive"
  | .P2 => "Change of state with transitive"
  | .Q  => "Evaluative"
  | .R  => "Purpose"
  | .S  => "Appearing to be"
  | .T  => "Manner"
  | .U  => "Reference"
  | .V  => "Correlational mutative"

/-- The complete enumeration of all 31 Martin categories. -/
def all : List MartinCategory :=
  [.A, .B, .C1, .C2, .C3, .D, .E, .F, .G, .H1, .H2, .H3, .I, .J1, .J2,
   .K, .L1, .L2, .M, .N1, .N2, .O1, .O2, .P1, .P2, .Q, .R, .S, .T, .U, .V]

theorem all_length : all.length = 31 := by decide

end MartinCategory

/-! ## §3 Operational tests + diagnostic signature

Per S&K §2 (pp. 8–11), three syntactic tests distinguish the four types.
The signatures in tables 14 (case marker / postposition), 27 (ambiguous),
29 (*ni*-insertion), and 32 (copula) are encoded as `predictedSignature`.
Split judgments in the source (e.g., `*/??`, `*/?/OK`) are reduced to
`Acceptability` per the convention: split with `*` floor → `unacceptable`
unless genuinely speaker-dependent (in which case `variable`); `*/N.A.`
(test inapplicable for an independent reason) → `anomalous`.
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
  deriving DecidableEq, Repr

/-- The acceptability signature S&K predict for each `Classification` ×
    `OperationalTest` pair. Encodes tables 14, 29, 32 (and the ambiguous
    cases at 27 — but `Classification` does not include an ambiguous
    constructor; ambiguous Martin categories return `none` from
    `classify` and have no predicted signature). -/
def predictedSignature : Classification → OperationalTest → Acceptability
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
  | .copula,           .floatingNQ           => .anomalous
  | .copula,           .cleftWithParticle    => .unacceptable
  | .copula,           .cleftWithoutParticle => .unacceptable

/-! ## §4 Cardinality theorems

The audit-promised "test the data, not the constructor" theorems —
verifying that S&K's distribution of 31 Martin categories into 4 types
+ 3 ambiguous matches the paper's own count.
-/

/-- Number of Martin categories classified as `dativeCaseMarker` (§3, p. 11:
    "two categories of *ni* … behave purely as case markers"). -/
theorem card_dativeCaseMarker :
    (MartinCategory.all.filter (fun c => c.classify = some .dativeCaseMarker)).length = 2 := by
  decide

/-- Number of Martin categories classified as `postposition` (§3, p. 12:
    "Eighteen categories of *ni* in our list turned out to be postpositions"). -/
theorem card_postposition :
    (MartinCategory.all.filter (fun c => c.classify = some .postposition)).length = 18 := by
  decide

/-- Number of categories where speakers vary (S&K's "ambiguous" bucket;
    §3, p. 14: D, N1, N2 — the three categories listed in (23)). -/
theorem card_ambiguous :
    (MartinCategory.all.filter (fun c => c.classify = none)).length = 3 := by
  decide

/-- Number of *ni*-of-*ni*-insertion categories (§3, p. 16: J1, J2, L2). -/
theorem card_niInsertion :
    (MartinCategory.all.filter (fun c => c.classify = some .niInsertion)).length = 3 := by
  decide

/-- Number of copula *ni* categories (§3, p. 17: P1, P2, Q, S, V). -/
theorem card_copula :
    (MartinCategory.all.filter (fun c => c.classify = some .copula)).length = 5 := by
  decide

/-- The five sub-counts sum to the total of 31. -/
theorem cards_sum_to_31 : 2 + 18 + 3 + 3 + 5 = 31 := by decide

/-! ## §5 Conflation: Fragment's `ni` collapses S&K types

`Fragments/Japanese/Case.lean` exposes a single `ni : CaseMarker` entry
(consistent with @cite{tsujimura-2014}'s textbook presentation). S&K's
4-way analysis would split this entry into multiple lexemes. The
following theorem makes the granularity disagreement Lean-visible.
-/

/-- Whether the Fragment's single `ni : CaseMarker` (with
    `cases = {.dat, .loc, .all, .Tem}`) covers the *ni* uses of a given
    Martin category, on the most generous reading. The mapping reflects
    Tsujimura's textbook coverage: dative recipient (A), locative-of-
    existence (L1, F), allative motion-toward (N1, N2), and temporal-on
    (M). The remaining categories use *ni* in ways the Fragment doesn't
    explicitly model (passive agents, causative causees, copula). -/
def MartinCategory.inFragmentNi : MartinCategory → Bool
  | .A | .O1                  => true   -- dative recipient + change of position
  | .L1 | .F                  => true   -- locative-of-existence + dependent-on
  | .N1 | .N2                 => true   -- allative direction (ambiguous in S&K)
  | .M                        => true   -- temporal-at
  | _                         => false

/-- The Fragment's `ni` covers Martin categories from at least two
    distinct S&K classifications — *.dativeCaseMarker* (witnessed by A)
    and *.postposition* (witnessed by L1). This refutes the
    Tsujimura/Fragment treatment of *ni* as a unitary case-particle. -/
theorem refutes_tsujimura_unitary_ni :
    ∃ c1 c2 : MartinCategory,
      c1.inFragmentNi = true ∧ c2.inFragmentNi = true ∧
      c1.classify ≠ c2.classify :=
  ⟨MartinCategory.A, MartinCategory.L1, by decide, by decide, by decide⟩

/-- Stronger statement: the Fragment's `ni` straddles three S&K cells —
    case marker (A), postposition (L1), and ambiguous (N1). -/
theorem fragment_ni_conflates_three_sk_cells :
    (∃ c : MartinCategory, c.inFragmentNi = true ∧ c.classify = some .dativeCaseMarker) ∧
    (∃ c : MartinCategory, c.inFragmentNi = true ∧ c.classify = some .postposition) ∧
    (∃ c : MartinCategory, c.inFragmentNi = true ∧ c.classify = none) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨MartinCategory.A, by decide, by decide⟩
  · exact ⟨MartinCategory.L1, by decide, by decide⟩
  · exact ⟨MartinCategory.N1, by decide, by decide⟩

/-! ## §6 Alignment with Marantz dependent case

S&K's 4-way classification partially aligns with Marantz/Baker's
`CaseSource` (`lexical | dependent | unmarked | agree`), encoded in
`Theories.Syntax.Case.Dependent`. Per the cross-framework reasoning:

- Dative case marker *ni* — assigned by structural configuration → `dependent`
- Postposition *ni* — bears inherent meaning, attached to NP via P head → `lexical`
- *ni*-of-*ni*-insertion — Takezawa 1987 analyses as a salvage operation
  on caseless arguments; functionally agrees with a functional head → `agree`
- Copula *ni* — outside Marantz's case-assignment domain (it's a copular
  construction, not case marking) → `none`
-/

open Syntax.Case (CaseSource)

/-- Partial map from S&K's 4-way *ni* taxonomy to Marantz/Baker's
    `CaseSource`. Copula *ni* maps to `none` (outside Marantz's domain). -/
def Classification.toMarantz : Classification → Option CaseSource
  | .dativeCaseMarker => some .dependent
  | .postposition     => some .lexical
  | .niInsertion      => some .agree
  | .copula           => none

theorem dat_aligns_dependent :
    Classification.toMarantz .dativeCaseMarker = some .dependent := rfl

theorem postp_aligns_lexical :
    Classification.toMarantz .postposition = some .lexical := rfl

theorem niInsertion_aligns_agree :
    Classification.toMarantz .niInsertion = some .agree := rfl

theorem copula_outside_marantz :
    Classification.toMarantz .copula = none := rfl

/-! ## §7 Affectedness hierarchy (§4, figure 45)

S&K's semantic correlate for the case-marker/postposition split: case
markers attach to MORE-affected NPs, postpositions to LESS-affected ones.
The hierarchy spans 4 syntactic positions, with phenomenally vs.
structurally affected as the metric distinguishing dative from accusative.
-/

/-- The four syntactic positions in S&K's affectedness hierarchy
    (figure 45, p. 22). Ordered from least to most affected. -/
inductive SyntacticPosition where
  /-- NP inside a PP (least affected). -/
  | npInPP
  /-- Dative NP (indirect object). Phenomenally affected. -/
  | dativeNP
  /-- Upper accusative NP (e.g., direct object of *praise*). Less
      structurally affected than lower-accusative. -/
  | upperAccusativeNP
  /-- Lower accusative NP (e.g., direct object of *kill*). Structurally
      affected (referent's existence/identity altered). -/
  | lowerAccusativeNP
  deriving DecidableEq, Repr

namespace SyntacticPosition

/-- Affectedness rank: higher = more affected. Used to compare positions
    rather than to assign absolute values. -/
def affectednessRank : SyntacticPosition → Nat
  | .npInPP             => 0
  | .dativeNP           => 1
  | .upperAccusativeNP  => 2
  | .lowerAccusativeNP  => 3

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

end SyntacticPosition

/-! ## §8 Acquisition prediction (Morii 1993, cited at §5 p. 23–24)

S&K's homophony analysis predicts that case-marker *ni* and postposition
*ni* are independent lexical items, hence acquired independently. Morii
1993 confirms: case-marker categories (A, O1) are acquired between ages
2;0 and 2;11; postposition categories (B–U) are acquired only after 3;0.

Encoded as a discrete acquisition order rather than absolute ages —
the substantive prediction is the strict ordering, not the precise ages.
-/

/-- Acquisition order per Morii 1993: lower number = acquired earlier.
    Only the dative-case-marker / postposition contrast is reported by
    Morii; the other two types' acquisition orders are not specified. -/
def Classification.acquisitionOrder : Classification → Option Nat
  | .dativeCaseMarker => some 0  -- 2;0–2;11
  | .postposition     => some 1  -- after 3;0
  | .niInsertion      => none    -- not addressed by Morii 1993
  | .copula           => none    -- not addressed by Morii 1993

/-- Case-marker *ni* is acquired strictly before postposition *ni*
    (Morii 1993, vindicating S&K's homophony analysis). Witnessed by the
    concrete acquisition orders 0 (case marker, age 2;0–2;11) vs. 1
    (postposition, after 3;0). -/
theorem case_marker_acquired_before_postposition :
    ∃ a b : Nat,
      Classification.acquisitionOrder .dativeCaseMarker = some a ∧
      Classification.acquisitionOrder .postposition     = some b ∧
      a < b :=
  ⟨0, 1, rfl, rfl, by decide⟩

/-! ## §9 Dialect parameter

S&K footnote 9 (p. 30) flags that judgments throughout the paper are from
the **innovating** dialect (per @cite{kuno-1987}, Miyagawa 1989). The
**conservative** dialect (Shibatani 1977) gives different judgments for
some categories. This Fragment's `predictedSignature` reflects the
innovating dialect; the `Dialect` enum is provided for future
specialisation (e.g., a `Phenomena/Case/Studies/Shibatani1977.lean`
formalising the conservative judgments and proving where they diverge).
-/

/-- The two dialects that S&K's footnote 9 distinguishes. -/
inductive Dialect where
  /-- Modern/innovating dialect; S&K and Miyagawa (1989) report this. -/
  | innovating
  /-- Conservative dialect; Shibatani (1977) reports this; not yet
      formalised in linglib. -/
  | conservative
  deriving DecidableEq, Repr

/-- The dialect this Studies file's `predictedSignature` encodes. -/
def encodedDialect : Dialect := .innovating

/-! ## §10 Sells 1995 absence (cross-linguistic gap)

@cite{sells-1995} (not yet in linglib bib) documents the parallel
case-particle/postposition split for Korean *-i*/*-eseo* but does not
engage S&K's homophony move for Korean equivalents of *ni*. Whether
Korean *-eseo* (locative postposition) and *-ege* (dative case marker)
exhibit the same homophony pattern S&K identify for Japanese *ni*
remains open and unformalised in linglib. A future
`Fragments/Korean/Case.lean` upgrade to Pattern B (rich marker structure)
would be the natural place to formalise the parallel.
-/

end Phenomena.Case.Studies.SadakaneKoizumi1995
