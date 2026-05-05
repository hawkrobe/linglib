import Linglib.Theories.Semantics.Dynamic.PPCDRT.Anaphora

/-!
# Reciprocal Semantics: Anaphoric Relations and Scope
@cite{dalrymple-haug-2024} @cite{dalrymple-et-al-1998}
@cite{haug-dalrymple-2020}

Two competing analyses of reciprocal expressions like *each other*:

1. **Quantificational** (@cite{heim-lasnik-may-1991}): the reciprocal is
   (or contains) a quantifier that can raise to the matrix clause,
   yielding a wide-scope (I-)reading. The local antecedent is bound by
   the raised quantifier part.

2. **Relational** (@cite{dalrymple-haug-2024}, @cite{sternefeld-1998},
   @cite{beck-2001}, @cite{dotlacil-2013}, @cite{haug-dalrymple-2020}):
   the reciprocal is a pronoun bearing an anaphoric relation to its
   antecedent. The narrow/wide scope ambiguity reduces to the choice of
   anaphoric relation: group identity (∪) for narrow scope vs. binding
   (=) for wide scope.

## Three Anaphoric Relations

Following @cite{higginbotham-1985} and @cite{williams-1991}, anaphoric
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
states in `Theories/Semantics/Dynamic/PPCDRT/Anaphora.lean`. This file
holds the *enum-level* classification — the abstract relation labels, the
scope readings, the antecedent property bundle, and the prediction
functions used by the Dalrymple–Haug 2024 cross-construction survey.

## Two-parameter scope classification

@cite{haug-dalrymple-2020} §3.3 (p. 24) makes the reciprocal-scope
classification two-dimensional: the locus of the reciprocal in the matrix
DRS (high or low) crossed with the type of anaphoric relation between the
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
@cite{dalrymple-haug-2024} for the empirical contrast.
-/

namespace Semantics.Reference.Reciprocals

open Theories.Semantics.Dynamic.PPCDRT

-- ════════════════════════════════════════════════════════════════
-- § 1: Anaphoric Relations (@cite{higginbotham-1985}, @cite{williams-1991})
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
-- (@cite{haug-dalrymple-2020} §3, §3.3)
-- ════════════════════════════════════════════════════════════════

/-- Locus of the reciprocal in the matrix DRS. @cite{haug-dalrymple-2020}
    §3.3 (p. 24): the reciprocal is either interpreted in-situ inside the
    embedded clause (`low` locus) or lifted to the matrix DRS (`high`
    locus). The locus is one of the two parameters in the §3.3
    classification of reciprocal readings. -/
inductive RecipLocus where
  /-- High locus: reciprocal lifted to matrix DRS. Required for
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
      @cite{heim-lasnik-may-1991}. -/
  | quantificational
  /-- Reciprocal is a pronoun bearing an anaphoric relation on its
      antecedent. @cite{sternefeld-1998}, @cite{beck-2001},
      @cite{dotlacil-2013}, @cite{haug-dalrymple-2020}. -/
  | relational
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 4: Properties of the Local Antecedent
-- ════════════════════════════════════════════════════════════════

/-- Properties of the local antecedent of the reciprocal (the
    embedded-clause pronoun coreferent with the matrix subject) that
    affect scopal possibilities. @cite{dalrymple-haug-2024}. -/
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
      @cite{nishigauchi-1992}. -/
  forcesGroupIdentity : Bool
  /-- Whether the antecedent is a logophoric pronoun. -/
  isLogophoric : Bool
  /-- Whether a distributive operator (*each*, *each of them*) is present
      in the matrix clause. -/
  hasDistributiveOperator : Bool
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 5: Scope Predictions (@cite{dalrymple-haug-2024})
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

-- ════════════════════════════════════════════════════════════════
-- § 6: Reciprocal Reading — Locus + Two Anaphoric Relations
-- (@cite{haug-dalrymple-2020} §3, §3.3)
-- ════════════════════════════════════════════════════════════════

/-- A reciprocal reading per the @cite{haug-dalrymple-2020} two-parameter
    classification: locus of the reciprocal × type of antecedent relation
    × type of reciprocal-to-antecedent relation. The three valid cells
    are exhibited by `narrowScopeReading`, `wideScopeReading`,
    `crossedReading`; the fourth cell (low locus + bound antecedent) is
    empirically empty per paper p. 24. -/
structure RecipReading where
  /-- Locus of the reciprocal in the matrix DRS. -/
  locus : RecipLocus
  /-- Anaphoric relation between the matrix subject and the embedded
      local antecedent. -/
  antecedentRel : AnaphoricRelation
  /-- Anaphoric relation between the embedded local antecedent and the
      reciprocal pronoun itself. -/
  reciprocalRel : AnaphoricRelation
  deriving DecidableEq, Repr

/-- Narrow-scope reading (we-reading): low locus, group-identity
    antecedent, in-situ reciprocity. @cite{haug-dalrymple-2020} eq 52. -/
def narrowScopeReading : RecipReading :=
  { locus := .low, antecedentRel := .groupIdentity, reciprocalRel := .reciprocity }

/-- Wide-scope reading (I-reading): high locus, bound antecedent,
    matrix-clause reciprocity. @cite{haug-dalrymple-2020} eq 54. -/
def wideScopeReading : RecipReading :=
  { locus := .high, antecedentRel := .binding, reciprocalRel := .reciprocity }

/-- Crossed reading (paper §3.3, eq 56): high locus, group-identity
    antecedent, group-identity reciprocal slot — reciprocity is contributed
    by the DRS distinctness presupposition `∂(u₃ ≠ u₂)`, not by an
    anaphoric reciprocity relation. -/
def crossedReading : RecipReading :=
  { locus := .high, antecedentRel := .groupIdentity, reciprocalRel := .groupIdentity }

/-- The three attested cells. The empirically-empty fourth cell
    (`{low, bound, _}`) is not listed. -/
def recipReadings : List RecipReading :=
  [narrowScopeReading, wideScopeReading, crossedReading]

/-- Narrow and wide scope are distinct (different locus, different
    antecedent relation). -/
theorem narrow_ne_wide : narrowScopeReading ≠ wideScopeReading := by decide

/-- Crossed reading is distinct from both narrow and wide. -/
theorem crossed_ne_narrow_and_wide :
    crossedReading ≠ narrowScopeReading ∧
    crossedReading ≠ wideScopeReading := by decide

/-- Narrow scope has low locus; wide scope and crossed reading have high
    locus. The locus distinguishes narrow from {wide, crossed}. -/
theorem narrow_low_others_high :
    narrowScopeReading.locus = .low ∧
    wideScopeReading.locus = .high ∧
    crossedReading.locus = .high := ⟨rfl, rfl, rfl⟩

/-- Wide scope is the only reading using `.binding` for the antecedent
    relation. Narrow and crossed both use group identity for the
    antecedent relation. -/
theorem only_wide_uses_binding :
    narrowScopeReading.antecedentRel = .groupIdentity ∧
    wideScopeReading.antecedentRel = .binding ∧
    crossedReading.antecedentRel = .groupIdentity := ⟨rfl, rfl, rfl⟩

/-- Crossed is the only reading using `.groupIdentity` for the reciprocal
    slot — narrow and wide both use `.reciprocity` there. -/
theorem only_crossed_uses_groupIdentity_recipSlot :
    narrowScopeReading.reciprocalRel = .reciprocity ∧
    wideScopeReading.reciprocalRel = .reciprocity ∧
    crossedReading.reciprocalRel = .groupIdentity := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 7: Anaphoric-Relation Dispatch over PPCDRT
-- ════════════════════════════════════════════════════════════════

/-- Maps each `AnaphoricRelation` constructor to its formal semantics in
    the PPCDRT substrate (`Theories/Semantics/Dynamic/PPCDRT/Anaphora.lean`).
    The three relations are distinguished propositions on plural
    information states `PluralAssign E`, parameterised by anaphor and
    antecedent dref indices. -/
def AnaphoricRelation.denotes (r : AnaphoricRelation) {E : Type}
    (uAnaph uAnt : Nat) : PPDRSCond E :=
  match r with
  | .binding       => bindingCond uAnaph uAnt
  | .groupIdentity => groupIdentityCond uAnaph uAnt
  | .reciprocity   => reciprocityCond uAnaph uAnt

/-- The narrow-scope antecedent relation denotes group identity. -/
theorem narrow_antecedent_denotes {E : Type} (uAnaph uAnt : Nat) :
    narrowScopeReading.antecedentRel.denotes (E := E) uAnaph uAnt =
    groupIdentityCond uAnaph uAnt := rfl

/-- The wide-scope antecedent relation denotes binding. -/
theorem wide_antecedent_denotes {E : Type} (uAnaph uAnt : Nat) :
    wideScopeReading.antecedentRel.denotes (E := E) uAnaph uAnt =
    bindingCond uAnaph uAnt := rfl

/-- The crossed-reading antecedent relation denotes group identity. -/
theorem crossed_antecedent_denotes {E : Type} (uAnaph uAnt : Nat) :
    crossedReading.antecedentRel.denotes (E := E) uAnaph uAnt =
    groupIdentityCond uAnaph uAnt := rfl

end Semantics.Reference.Reciprocals
