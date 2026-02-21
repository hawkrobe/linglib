import Linglib.Core.Intension
import Linglib.Core.Tense

/-!
# Percus (2000): Constraints on Situation Variables in Syntax @cite{percus-2000}

Formalizes Percus's theory of situation pronouns in LF. Every predicate
takes a situation argument, every clause introduces a λs binder, and
**Generalization X** constrains which binder can bind which variable.

## Generalization X

> The situation pronoun that a predicate is associated with must be
> bound by the minimal c-commanding situation binder.

This is a *syntactic* well-formedness constraint that predicts:
- Main predicates in attitude complements are obligatorily de dicto
  (evaluated in belief situations, not the actual situation)
- NP restrictors can be de re (their situation variable can be
  bound by a higher λs)
- "Mixed" readings where the main predicate is de re but the NP is
  de dicto are impossible

## Situation Assignment Infrastructure

Situation assignments specialize `Core.VarAssignment` from `D = Time`
(Partee's temporal variables) to `D = Situation W Time` (Percus's
situation variables). The algebraic structure is identical:

| Partee (1973)           | Percus (2000)                    |
|-------------------------|----------------------------------|
| `TemporalAssignment`    | `SituationAssignment`            |
| `interpTense n g`       | `interpSitVar n g`               |
| `updateTemporal g n t`  | `updateSitVar g n s`             |
| `temporalLambdaAbs`     | `sitLambdaAbs`                   |

This parallel is Partee's structural analogy taken to its logical
conclusion: the SAME referential mechanism (variable assignment)
operates over worlds, times, and situations.

## References

- Percus, O. (2000). Constraints on some other variables in syntax.
  *Natural Language Semantics* 8(3): 173–229.
- Partee, B. (1973). Some structural analogies between tenses and pronouns.
- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
-/

namespace Semantics.Intensional.Situations.Percus

open Core (Situation)
open Core.VarAssignment (VarAssignment updateVar lookupVar varLambdaAbs
  update_lookup_same update_lookup_other)


-- ════════════════════════════════════════════════════════════════
-- § Situation Assignment
-- ════════════════════════════════════════════════════════════════

/-- Situation assignment function: maps variable indices to situations.
    The situation-level analogue of Partee's `TemporalAssignment`
    and H&K's entity assignment `Assignment`. -/
abbrev SituationAssignment (W Time : Type*) := VarAssignment (Situation W Time)

/-- Situation variable denotation: ⟦sₙ⟧^g = g(n).
    Specializes `Core.VarAssignment.lookupVar`. -/
abbrev interpSitVar {W Time : Type*} (n : ℕ) (g : SituationAssignment W Time) :
    Situation W Time :=
  lookupVar n g

/-- Modified situation assignment g[n ↦ s].
    Specializes `Core.VarAssignment.updateVar`. -/
abbrev updateSitVar {W Time : Type*} (g : SituationAssignment W Time)
    (n : ℕ) (s : Situation W Time) : SituationAssignment W Time :=
  updateVar g n s

/-- Situation lambda abstraction: bind a situation variable.
    Specializes `Core.VarAssignment.varLambdaAbs`.

    Every clause boundary introduces a λsₙ binder in Percus's system.
    Under attitude verbs, the binder's value is filled by quantification
    over doxastic alternatives. -/
abbrev sitLambdaAbs {W Time α : Type*} (n : ℕ)
    (body : SituationAssignment W Time → α) :
    SituationAssignment W Time → Situation W Time → α :=
  varLambdaAbs n body


-- ════════════════════════════════════════════════════════════════
-- § Generalization X
-- ════════════════════════════════════════════════════════════════

/-- A predicate binding record: which situation variable a predicate
    uses and which binder (by index) should bind it.

    In Percus's LF, a sentence like:
      [λs₁ Mary believes_s₁ [λs₂ John isCanadian_s₂]]
    has the predicate "isCanadian" bound by λs₂ (index 2).
    Generalization X says this binding is the ONLY well-formed option:
    the predicate must use the closest c-commanding binder. -/
structure PredicateBinding where
  /-- The situation variable index the predicate uses -/
  sitVarIndex : ℕ
  /-- The index of the closest c-commanding λs binder -/
  closestBinderIndex : ℕ

/-- Generalization X (Percus 2000, p. 183):

    > The situation pronoun that a verb/predicate is associated with
    > must be bound by the minimal c-commanding situation binder.

    A predicate's binding is Gen-X-compliant iff its situation variable
    is bound by the closest binder. -/
def PredicateBinding.genXCompliant (b : PredicateBinding) : Bool :=
  b.sitVarIndex == b.closestBinderIndex

/-- An LF reading is well-formed under Generalization X iff ALL
    predicate bindings use their closest c-commanding binder. -/
def genXWellFormed (bindings : List PredicateBinding) : Bool :=
  bindings.all PredicateBinding.genXCompliant

/-- Generalization Y (Percus 2000, p. 204, example 39):

    > The situation pronoun that an adverbial quantifier selects for
    > must be coindexed with the nearest λ above it.

    Gen Y is a *parallel* constraint to Gen X, but for **adverbial
    quantifiers** ("always", "usually", "never") rather than
    predicates (verbs, adjectives).

    The situation pronoun ssh that a quantifier like "always" uses to
    determine its domain must be bound by the nearest c-commanding λs.
    This prevents "always" from reaching past an attitude verb to
    quantify over actual-world situations rather than belief-world
    situations.

    The `PredicateBinding` structure is reused: it records which
    situation variable the quantifier uses and which binder is closest. -/
def genYWellFormed (quantifierBindings : List PredicateBinding) : Bool :=
  quantifierBindings.all PredicateBinding.genXCompliant

/-- Combined well-formedness: both Gen X (predicates) and Gen Y
    (adverbial quantifiers) must use their closest binder. -/
def genXYWellFormed (predicateBindings quantifierBindings : List PredicateBinding) : Bool :=
  genXWellFormed predicateBindings && genYWellFormed quantifierBindings


-- ════════════════════════════════════════════════════════════════
-- § Attitude Semantics with Situation Binding
-- ════════════════════════════════════════════════════════════════

/-- Doxastic alternatives as situations.
    `dox agent s` returns the situations compatible with what `agent`
    believes at situation `s`. Generalizes Hintikka's `Dox_x(w)` from
    worlds to world–time pairs. -/
abbrev DoxSit (W Time E : Type*) := E → Situation W Time → List (Situation W Time)

/-- Attitude verb semantics with situation binding.

    ⟦x believes [λsₙ. φ]⟧^g(s) = ∀s' ∈ Dox_x(s). φ^(g[n ↦ s'])

    The attitude verb quantifies universally over doxastic alternatives.
    Each alternative s' is bound to situation variable n in the complement.
    Predicates inside the complement that reference sₙ are thereby
    evaluated in belief situations — this is the de dicto reading.

    Predicates that reference a DIFFERENT variable (e.g., s_m where m ≠ n)
    escape the binding and are evaluated at whatever s_m is set to by the
    outer binder — this would be a de re reading. Generalization X blocks
    this for main predicates but allows it for NP restrictors. -/
def believeSit {W Time E : Type*}
    (dox : DoxSit W Time E) (agent : E) (n : ℕ)
    (complement : SituationAssignment W Time → Bool)
    (g : SituationAssignment W Time) (s : Situation W Time) : Bool :=
  (dox agent s).all λ s' => complement (updateSitVar g n s')


/-- Adverbial quantifier "always" with situation binding.

    ⟦always_ssh [λsₙ. φ]⟧^g = ∀s' ∈ domain(ssh). φ^(g[n ↦ s'])

    The quantifier introduces a binder λsₙ over its nuclear scope.
    Its domain is determined by the situation pronoun ssh: the set
    of relevant situations (game rounds, time points, etc.) at the
    world of ssh.

    Generalization Y constrains ssh: it must be bound by the nearest
    c-commanding λ — typically the one introduced by an attitude verb
    when "always" is embedded under an attitude. -/
def alwaysAt {W Time : Type*}
    (domain : Situation W Time → List (Situation W Time))
    (ssh : Situation W Time) (n : ℕ)
    (scope : SituationAssignment W Time → Bool)
    (g : SituationAssignment W Time) : Bool :=
  (domain ssh).all λ s' => scope (updateSitVar g n s')


-- ════════════════════════════════════════════════════════════════
-- § Key Properties
-- ════════════════════════════════════════════════════════════════

/-- Bound situation variable receives the binder's value.
    Parallel to `zeroTense_receives_binder_time` in `Core/Tense.lean`. -/
theorem sitVar_receives_binder_value {W Time : Type*}
    (g : SituationAssignment W Time) (n : ℕ) (s : Situation W Time) :
    interpSitVar n (updateSitVar g n s) = s :=
  update_lookup_same g n s

/-- Non-target variables are unaffected by binding. -/
theorem sitVar_other_unaffected {W Time : Type*}
    (g : SituationAssignment W Time) (n i : ℕ) (s : Situation W Time)
    (h : i ≠ n) :
    interpSitVar i (updateSitVar g n s) = interpSitVar i g :=
  update_lookup_other g n i s h


-- ════════════════════════════════════════════════════════════════
-- § Bridge: Temporal ↔ Situational
-- ════════════════════════════════════════════════════════════════

/-- Project a situation assignment to a temporal assignment.
    This is `Core.Tense.situationToTemporal` with a transparent
    definition: we extract the temporal coordinate from each situation
    (Kratzer 1998, formula 38: `time(e)` on eventualities/situations). -/
def toTemporalAssignment {W Time : Type*}
    (g : SituationAssignment W Time) : Core.Tense.TemporalAssignment Time :=
  λ n => (g n).time

/-- Situation assignment projects to temporal assignment coherently:
    the temporal variable at index n equals the time of the situation
    at index n. -/
theorem temporal_projection_commutes {W Time : Type*}
    (g : SituationAssignment W Time) (n : ℕ) :
    Core.Tense.interpTense n (toTemporalAssignment g) = (interpSitVar n g).time :=
  rfl


end Semantics.Intensional.Situations.Percus
