import Linglib.Semantics.Dynamic.PPCDRT.Anaphora

/-!
# Reciprocal Semantics: Anaphoric Relations and Scope
[dalrymple-haug-2024] [dalrymple-et-al-1998]
[haug-dalrymple-2020]

Two competing analyses of reciprocal expressions like *each other*:

1. **Quantificational** ([heim-lasnik-may-1991]): the reciprocal is
   (or contains) a quantifier that can raise to the matrix clause,
   yielding a wide-scope (I-)reading. The local antecedent is bound by
   the raised quantifier part.

2. **Relational** ([dalrymple-haug-2024], [sternefeld-1998],
   [beck-2001], [dotlacil-2013], [haug-dalrymple-2020]):
   the reciprocal is a pronoun bearing an anaphoric relation to its
   antecedent. The narrow/wide scope ambiguity reduces to the choice of
   anaphoric relation: group identity (∪) for narrow scope vs. binding
   (=) for wide scope.

## Three Anaphoric Relations

Following [higginbotham-1985] and [williams-1991], anaphoric
dependencies between a pronoun and its antecedent come in three types:

- **Binding (=)**: the pronoun is a bound variable; the antecedent denotes
  an individual. Requires c-command.
- **Group identity (∪)**: the pronoun denotes the same plurality as its
  antecedent. No c-command required.
- **Reciprocity (R)**: cumulative identity across situations (the group
  picked out is the same) but distinctness within each situation (each
  pair involves different individuals). This is the core contribution
  of the reciprocal.

The formal semantics of these relations is defined over plural information
states in `Semantics/Dynamic/PPCDRT/Anaphora.lean`. This file
holds the *enum-level* classification — the abstract relation labels, the
scope readings, the antecedent property bundle, and the prediction
functions used by the Dalrymple–Haug 2024 cross-construction survey.

## Two-parameter scope classification

[haug-dalrymple-2020] §3.3 (p. 24) makes the reciprocal-scope
classification two-dimensional: the locus of the reciprocal in the matrix
Update (high or low) crossed with the type of anaphoric relation between the
matrix subject and the embedded local antecedent (binding or group
identity). Three of the four cells are attested; the (low, bound) cell is
empty (paper p. 24: "the bound reading of the reciprocal's antecedent
cannot cooccur with a low locus for the reciprocal, because it does not
make available the plurality that the reciprocal needs").

The `RecipReading` structure exposes locus alongside the two anaphoric
relations so that consumers can witness the three cells distinctly.

## Key Prediction

The two analyses diverge on whether properties of the **local antecedent**
(the embedded-clause pronoun coreferent with the matrix subject) can
constrain reciprocal scope. The relational analysis predicts they can;
the quantificational analysis predicts they cannot for cases involving
distributive operators (§5) and logophoric antecedents (§6) — see
[dalrymple-haug-2024] for the empirical contrast.
-/

namespace Semantics.Reference.Reciprocals

open PPCDRT

-- ════════════════════════════════════════════════════════════════
-- § 1: Anaphoric Relations ([higginbotham-1985], [williams-1991])
-- ════════════════════════════════════════════════════════════════

/-- The three types of anaphoric relation between a pronoun and its
    antecedent. Properties of the *resolution*, not the expression: the
    same pronoun (e.g., *they*) can participate in binding or group
    identity depending on context. -/
inductive AnaphoricRelation where
  /-- Bound variable: pronoun gets its value from a c-commanding binder.
      The antecedent denotes an individual. -/
  | binding
  /-- Group identity: pronoun denotes the same plurality as its antecedent.
      Cumulative identity across all contexts. -/
  | groupIdentity
  /-- Reciprocity: cumulative identity across situations (same group) but
      per-situation distinctness (different individuals in each pair). -/
  | reciprocity
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Reciprocal Locus and Scope Readings
-- ([haug-dalrymple-2020] §3, §3.3)
-- ════════════════════════════════════════════════════════════════

/-- Locus of the reciprocal in the matrix Update. [haug-dalrymple-2020]
    §3.3 (p. 24): the reciprocal is either interpreted in-situ inside the
    embedded clause (`low` locus) or lifted to the matrix Update (`high`
    locus). The locus is one of the two parameters in the §3.3
    classification of reciprocal readings. -/
inductive RecipLocus where
  /-- High locus: reciprocal lifted to matrix Update. Required for
      wide scope and for the crossed reading. -/
  | high
  /-- Low locus: reciprocal interpreted in-situ inside the embedded
      clause. Required for narrow scope. -/
  | low
  deriving DecidableEq, Repr

/-- Scope reading of a reciprocal in a complex sentence.

    - *narrow* (we-reading): "Tracy and Chris each thought 'We saw each other.'"
      The reciprocal is interpreted inside the embedded clause.
    - *wide* (I-reading): "Tracy thought 'I saw Chris' and Chris thought 'I saw Tracy.'"
      The reciprocal's semantic contribution is in the matrix clause. -/
inductive RecipScope where
  | narrow
  | wide
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 3: Two Analyses
-- ════════════════════════════════════════════════════════════════

/-- The two families of reciprocal analysis. -/
inductive RecipAnalysis where
  /-- Reciprocal is/contains a quantifier that can QR to the matrix clause.
      [heim-lasnik-may-1991]. -/
  | quantificational
  /-- Reciprocal is a pronoun bearing an anaphoric relation on its
      antecedent. [sternefeld-1998], [beck-2001],
      [dotlacil-2013], [haug-dalrymple-2020]. -/
  | relational
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 4: Properties of the Local Antecedent
-- ════════════════════════════════════════════════════════════════

/-- Properties of the local antecedent of the reciprocal (the
    embedded-clause pronoun coreferent with the matrix subject) that
    affect scopal possibilities. [dalrymple-haug-2024]. -/
structure AntecedentProperties where
  /-- Whether the local antecedent is syntactically bound (=) by the
      matrix subject. -/
  isBound : Bool
  /-- Whether the embedded predicate is conjoined with a necessarily
      collective predicate. -/
  hasCollectiveConjunct : Bool
  /-- Whether the construction involves exhaustive control vs. partial
      control. -/
  isExhaustiveControl : Bool
  /-- Whether the controller is interpreted collectively. -/
  controllerIsCollective : Bool
  /-- Whether the pronoun type forces group identity (∪), excluding the
      binding (=) option. Japanese *zibun-tati* (plural reflexive),
      [nishigauchi-1992]. -/
  forcesGroupIdentity : Bool
  /-- Whether the antecedent is a logophoric pronoun. -/
  isLogophoric : Bool
  /-- Whether a distributive operator (*each*, *each of them*) is present
      in the matrix clause. -/
  hasDistributiveOperator : Bool
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 5: Scope Predictions ([dalrymple-haug-2024])
-- ════════════════════════════════════════════════════════════════

/-- Scope readings predicted by the relational analysis.

    Distributive operators are orthogonal on the relational analysis:
    *each other* is a pronoun, not a quantified NP, so distribution is
    orthogonal — both readings remain available. Logophoric antecedents
    restrict to narrow only. -/
def relationalPrediction (props : AntecedentProperties) : List RecipScope :=
  if props.isLogophoric then [.narrow]
  else if props.hasCollectiveConjunct then [.narrow]
  else if props.forcesGroupIdentity then [.narrow]
  else if props.isExhaustiveControl && !props.controllerIsCollective then [.wide]
  else if props.isExhaustiveControl && props.controllerIsCollective then [.narrow]
  else if props.isBound then [.wide]
  else [.narrow, .wide]

/-- Scope readings predicted by the quantificational analysis.

    Diverges from `relationalPrediction` on:
    - **Distributive operators**: predicts narrow only (incorrect; both attested).
    - **Logophoric antecedents**: predicts both (incorrect; only narrow attested). -/
def quantificationalPrediction (props : AntecedentProperties) : List RecipScope :=
  if props.hasDistributiveOperator then [.narrow]
  else if props.hasCollectiveConjunct then [.narrow]
  else if props.forcesGroupIdentity then [.narrow]
  else if props.isExhaustiveControl && !props.controllerIsCollective then [.wide]
  else if props.isExhaustiveControl && props.controllerIsCollective then [.narrow]
  else if props.isBound then [.wide]
  else [.narrow, .wide]

/-- A *synthetic* Strongest Meaning Hypothesis at the scope-ambiguity
    layer ([dalrymple-et-al-1998]'s SMH idea, applied to the choice
    between narrow and wide scope): when both readings are available,
    pick the logically stronger one. Narrow scope is stronger than wide
    in the sense that the narrow-scope reciprocity reading is more
    restrictive on doxastic alternatives.

    **Caveat.** This is NOT what [haug-dalrymple-2020] §6.1 actually
    argues against. The paper's §6.1 contrast (eq 132–133) is about
    SMH applied to **reciprocal-reading STRENGTH** (Strong vs Weak
    Reciprocity) under downward-entailing contexts — a different
    dimension from scope. Properly formalising the §6.1 argument would
    require a Strong/Weak Reciprocity gradation in the substrate, which
    PPCDRT does not currently expose. The `SMH_diverges_from_relational`
    theorem below is *synthetic divergence at the scope layer* — a Lean
    fact, not a paper-faithful refutation. -/
def strongestMeaningPrediction (props : AntecedentProperties) : List RecipScope :=
  match relationalPrediction props with
  | [.narrow, .wide] => [.narrow]   -- both available: narrow is stronger, SMH commits
  | other            => other        -- otherwise: trivially strongest

/-- Synthetic SMH-vs-relational divergence at the scope layer. On the
    default property bundle, the relational analysis leaves both
    readings available; the synthetic SMH commits to narrow only. See
    the `caveat` on `strongestMeaningPrediction` — this is not the
    paper's §6.1 argument, which is about Strong/Weak Reciprocity not
    formalised here. -/
theorem SMH_diverges_from_relational :
    ∃ props : AntecedentProperties,
      strongestMeaningPrediction props ≠ relationalPrediction props := by
  refine ⟨{
    isBound := false, hasCollectiveConjunct := false,
    isExhaustiveControl := false, controllerIsCollective := false,
    forcesGroupIdentity := false, isLogophoric := false,
    hasDistributiveOperator := false }, ?_⟩
  decide

-- ════════════════════════════════════════════════════════════════
-- § 6: Reciprocal Reading — Locus + Two Anaphoric Relations
-- ([haug-dalrymple-2020] §3, §3.3)
-- ════════════════════════════════════════════════════════════════

/-- A reciprocal reading per the [haug-dalrymple-2020] two-parameter
    classification: locus of the reciprocal × type of antecedent relation
    × type of reciprocal-to-antecedent relation. The three valid cells
    are exhibited by `narrowScopeReading`, `wideScopeReading`,
    `crossedReading`; the fourth cell (low locus + bound antecedent) is
    empirically empty per paper p. 24. -/
structure RecipReading where
  /-- Locus of the reciprocal in the matrix Update. -/
  locus : RecipLocus
  /-- Anaphoric relation between the matrix subject and the embedded
      local antecedent. -/
  antecedentRel : AnaphoricRelation
  /-- Anaphoric relation between the embedded local antecedent and the
      reciprocal pronoun itself. -/
  reciprocalRel : AnaphoricRelation
  deriving DecidableEq, Repr

/-- Narrow-scope reading (we-reading): low locus, group-identity
    antecedent, in-situ reciprocity. [haug-dalrymple-2020] eq 52. -/
def narrowScopeReading : RecipReading :=
  { locus := .low, antecedentRel := .groupIdentity, reciprocalRel := .reciprocity }

/-- Wide-scope reading (I-reading): high locus, bound antecedent,
    matrix-clause reciprocity. [haug-dalrymple-2020] eq 54. -/
def wideScopeReading : RecipReading :=
  { locus := .high, antecedentRel := .binding, reciprocalRel := .reciprocity }

/-- Crossed reading (paper §3.3, eq 56): high locus, group-identity
    antecedent, group-identity reciprocal slot — reciprocity is contributed
    by the Update distinctness presupposition `∂(u₃ ≠ u₂)`, not by an
    anaphoric reciprocity relation. -/
def crossedReading : RecipReading :=
  { locus := .high, antecedentRel := .groupIdentity, reciprocalRel := .groupIdentity }

/-- The three attested cells. The empirically-empty fourth cell
    (`{low, bound, _}`) is not listed. -/
def recipReadings : List RecipReading :=
  [narrowScopeReading, wideScopeReading, crossedReading]

/-- The three readings are pairwise distinct as `RecipReading` records.
    Sanity check that the four-cell classification produces three
    *different* cells (not three name-aliases for the same cell). -/
theorem readings_pairwise_distinct :
    narrowScopeReading ≠ wideScopeReading ∧
    crossedReading ≠ narrowScopeReading ∧
    crossedReading ≠ wideScopeReading := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Semantics.Reference.Reciprocals
