import Linglib.Theories.Semantics.Composition.Scope
import Linglib.Core.Discourse.Logophoricity

/-!
# Reciprocal Semantics: Anaphoric Relations and Scope
@cite{dalrymple-haug-2024} @cite{dalrymple-et-al-1998}

Two competing analyses of reciprocal expressions like *each other*:

1. **Quantificational** (@cite{heim-lasnik-may-1991}): the reciprocal is (or
   contains) a quantifier that can raise to the matrix clause, yielding a
   wide-scope (I-)reading. The local antecedent is bound by the raised
   quantifier part.

2. **Relational** (@cite{dalrymple-haug-2024}, Sternenfeld 1998, Beck 2001,
   Dotlačil 2013, @cite{haug-dalrymple-2020}): the reciprocal is a pronoun
   bearing an anaphoric relation to its antecedent. The narrow/wide scope
   ambiguity reduces to the choice of anaphoric relation: group identity (∪)
   for narrow scope vs. binding (=) for wide scope.

## Three Anaphoric Relations

Following Higginbotham (1985) and Williams (1991), anaphoric dependencies
between a pronoun and its antecedent come in three types:

- **Binding (=)**: the pronoun is a bound variable; the antecedent denotes
  an individual. Requires c-command.
- **Group identity (∪)**: the pronoun denotes the same plurality as its
  antecedent. No c-command required.
- **Reciprocity (R)**: cumulative identity across situations (the group
  picked out is the same) but distinctness within each situation (each
  pair involves different individuals). This is the core contribution
  of the reciprocal.

## Key Prediction

The two analyses diverge on whether properties of the **local antecedent**
(the embedded-clause pronoun coreferent with the matrix subject) can
constrain reciprocal scope. The relational analysis predicts they can,
because the local antecedent participates directly in the anaphoric
relation. The quantificational analysis predicts they cannot for cases
involving distributive operators (§5) and logophoric antecedents (§6),
because the quantifier part of the reciprocal scopes independently of
the local antecedent.
-/

namespace Semantics.Reference.Reciprocals

-- ════════════════════════════════════════════════════════════════
-- § 1: Anaphoric Relations (Higginbotham 1985, Williams 1991)
-- ════════════════════════════════════════════════════════════════

/-- The three types of anaphoric relation between a pronoun and its
    antecedent. These are properties of the *resolution*, not the
    expression: the same pronoun (e.g., *they*) can participate in
    binding or group identity depending on context. -/
inductive AnaphoricRelation where
  /-- Bound variable: pronoun gets its value from a c-commanding binder.
      The antecedent denotes an individual. -/
  | binding
  /-- Group identity: pronoun denotes the same plurality as its antecedent.
      Cumulative identity across all contexts. -/
  | groupIdentity
  /-- Reciprocity: cumulative identity across situations (same group) but
      per-situation distinctness (different individuals in each pair).
      This is the semantic core of reciprocal *each other*. -/
  | reciprocity
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Reciprocal Scope Readings
-- ════════════════════════════════════════════════════════════════

/-- Scope reading of a reciprocal in a complex sentence.

    - *narrow* (we-reading): "Tracy and Chris each thought 'We saw each other.'"
      The reciprocal is interpreted inside the embedded clause.
    - *wide* (I-reading): "Tracy thought 'I saw Chris' and Chris thought 'I saw Tracy.'"
      The reciprocal's semantic contribution is in the matrix clause. -/
inductive RecipScope where
  | narrow  -- we-reading: reciprocity inside embedded clause
  | wide    -- I-reading: reciprocity in matrix clause
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 3: Two Analyses
-- ════════════════════════════════════════════════════════════════

/-- The two families of reciprocal analysis. -/
inductive RecipAnalysis where
  /-- Reciprocal is/contains a quantifier that can QR to the matrix clause.
      @cite{heim-lasnik-may-1991}, Sigurðsson et al. 2022, Atlamaz & Öztürk
      2023, Paparounas & Salzmann 2023. -/
  | quantificational
  /-- Reciprocal is a pronoun bearing an anaphoric relation on its
      antecedent. Scope ambiguity reduces to binding (=) vs. group
      identity (∪). Sternenfeld 1998, Beck 2001, Dotlačil 2013,
      @cite{haug-dalrymple-2020}. -/
  | relational
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 4: Properties of the Local Antecedent
-- ════════════════════════════════════════════════════════════════

/-- Properties of the local antecedent of the reciprocal (the
    embedded-clause pronoun coreferent with the matrix subject)
    that affect scopal possibilities. -/
structure AntecedentProperties where
  /-- Whether the local antecedent is syntactically bound (=) by the
      matrix subject. If true, the antecedent denotes an individual,
      forcing wide scope. If false (group identity ∪), narrow scope. -/
  isBound : Bool
  /-- Whether the embedded predicate is conjoined with a necessarily
      collective predicate. Collective predicates require a plurality
      argument, which wide scope (individual denotation) cannot provide. -/
  hasCollectiveConjunct : Bool
  /-- Whether the construction involves exhaustive control (PRO has
      same reference as controller) vs. partial control (PRO can denote
      a superset). -/
  isExhaustiveControl : Bool
  /-- Whether the controller is interpreted collectively. -/
  controllerIsCollective : Bool
  /-- Whether the antecedent is a logophoric pronoun. Logophoric pronouns
      are interpreted inside the report context, and the reciprocal cannot
      "drag" them out to the matrix clause. -/
  isLogophoric : Bool
  /-- Whether a distributive operator (*each*, *each of them*) is present
      in the matrix clause. On the quantificational analysis, this should
      block wide scope (can't distribute over an already-distributed NP).
      On the relational analysis, distributors are orthogonal to reciprocal
      scope: *each other* is a pronoun, not a quantifier, so there is no
      double-distribution problem. @cite{dalrymple-haug-2024} §5. -/
  hasDistributiveOperator : Bool
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 5: Scope Predictions
-- ════════════════════════════════════════════════════════════════

/-- Scope readings predicted by the relational analysis.

    The relational analysis predicts scope from the anaphoric relation
    between the local antecedent and the matrix subject:
    - Group identity (∪) → narrow scope
    - Binding (=) → wide scope

    Key constraints:
    1. Logophoric antecedent → only narrow scope (logophor confined to
       report context)
    2. Collective conjunct → only narrow scope (wide gives individual,
       can't satisfy collectivity)
    3. Exhaustive control + non-collective → wide only
    4. Exhaustive control + collective → narrow only
    5. Bound antecedent → only wide scope (binding forces individual)
    6. Distributive operator → BOTH readings (no constraint; *each other*
       is a pronoun, not a quantified NP, so distribution is orthogonal) -/
def relationalPrediction (props : AntecedentProperties) : List RecipScope :=
  if props.isLogophoric then [.narrow]
  else if props.hasCollectiveConjunct then [.narrow]
  else if props.isExhaustiveControl && !props.controllerIsCollective then [.wide]
  else if props.isExhaustiveControl && props.controllerIsCollective then [.narrow]
  else if props.isBound then [.wide]
  -- Distributive operators are orthogonal on the relational analysis:
  -- *each other* is a pronoun, and *each* distributes over the group
  -- denoted by the antecedent, which the reciprocal can still access.
  else [.narrow, .wide]

/-- Scope readings predicted by the quantificational analysis.

    The quantificational analysis derives scope from QR of the quantifier
    part of the reciprocal. It makes the same predictions as the relational
    analysis for §§2–4, but diverges on:

    - **Distributive operators (§5)**: predicts only narrow scope when a
      distributor is present, because a distributive operator cannot apply
      to an already-distributed NP (*each* in the quantificational analysis
      of *each other*). @cite{heim-lasnik-may-1991} claim (18b) "*They each
      examined each other" is ungrammatical — but corpus evidence refutes
      this. The relational analysis correctly allows both readings.

    - **Logophoric antecedents (§6)**: predicts both readings should be
      available (the quantifier scopes independently of logophoricity).
      The relational analysis correctly restricts to narrow only. -/
def quantificationalPrediction (props : AntecedentProperties) : List RecipScope :=
  if props.hasDistributiveOperator then [.narrow]
  else if props.hasCollectiveConjunct then [.narrow]
  else if props.isExhaustiveControl && !props.controllerIsCollective then [.wide]
  else if props.isExhaustiveControl && props.controllerIsCollective then [.narrow]
  else if props.isBound then [.wide]
  -- Logophoricity is invisible to the quantificational analysis:
  -- the quantifier part of the reciprocal scopes independently.
  else [.narrow, .wide]

-- ════════════════════════════════════════════════════════════════
-- § 6: Scope from Anaphoric Relation
-- ════════════════════════════════════════════════════════════════

/-- On the relational analysis, narrow scope reciprocity decomposes into
    group identity (∪) between the local antecedent and the matrix subject,
    plus in-situ reciprocity (R) between the local antecedent and the
    reciprocal pronoun. -/
def narrowScopeRelations : AnaphoricRelation × AnaphoricRelation :=
  (.groupIdentity, .reciprocity)

/-- Wide scope reciprocity decomposes into binding (=) of the local
    antecedent by the matrix subject, plus reciprocity (R) in the
    matrix clause between the matrix subject and the reciprocal. -/
def wideScopeRelations : AnaphoricRelation × AnaphoricRelation :=
  (.binding, .reciprocity)

/-- Both scope readings require exactly two anaphoric relations:
    one between matrix subject and local antecedent, one involving
    the reciprocal. -/
theorem both_readings_binary :
    narrowScopeRelations.1 ≠ narrowScopeRelations.2 ∧
    wideScopeRelations.1 ≠ wideScopeRelations.2 := by
  constructor <;> decide

/-- The two readings differ in whether the local antecedent is bound
    or group-identical with the matrix subject. -/
theorem readings_differ_on_antecedent_relation :
    narrowScopeRelations.1 ≠ wideScopeRelations.1 := by decide

/-- Both readings share the reciprocity relation. -/
theorem both_use_reciprocity :
    narrowScopeRelations.2 = .reciprocity ∧
    wideScopeRelations.2 = .reciprocity := ⟨rfl, rfl⟩

end Semantics.Reference.Reciprocals
