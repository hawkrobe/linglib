import Linglib.Theories.Semantics.Dynamic.IntensionalCDRT.Basic

/-!
# Plural Intensional Presuppositional Predicate Calculus (PIP)

@cite{keshet-abney-2024} @cite{brasoveanu-2010} @cite{stone-1997}Core types for @cite{keshet-abney-2024}'s PIP system, which extends
first-order predicate calculus with set abstraction, plural assignments,
formula labels, and world-subscripted predicates to handle intensional
anaphora uniformly.

## The Core Innovation

Pronouns carry **descriptive content** (the formula that introduced their
antecedent), not stored entity values. This enables anaphora to entities
introduced under modal operators, where no actual entity exists in the
evaluation world.

## Encoding Strategy

PIP is natively a **static, truth-conditional** system: formulas denote
truth values relative to a model, plural assignment set G, and evaluation
world w*. Our formalization encodes PIP as a dynamic update system over
IntensionalCDRT's `IContext W E`, which is a legitimate approach:
@cite{brasoveanu-2010} shows the equivalence between plural predicate calculi
and dynamic plural logics. The key properties (label monotonicity,
external/local variable distinction) are faithfully preserved.

## PIP's Five Constructs (paper item 17)

1. **Unselective closure** with bracketed [x] (local) vs unbracketed x (external)
2. **Summation** Σxφ: set-forming over individuals
3. **Formula labels** X ≡ φ: tautological abbreviatory definitions
4. **World subscripts** P_w(x): predicates evaluated at specific worlds
5. **Presuppositions** φ|ψ: assert φ, presuppose ψ

## Key Types

| Type | Description |
|------|-------------|
| `FLabel` | Formula label index (paper's X in X ≡ φ) |
| `Description W E` | Descriptive content associated with a label |
| `Discourse W E` | Information state + label registry |
| `PUpdate W E` | Discourse-level update (dynamic encoding of PIP formulas) |

-/

namespace Semantics.PIP

open Semantics.Dynamic.Core
open Semantics.Dynamic.IntensionalCDRT


-- ============================================================
-- Formula Labels
-- ============================================================

/--
Formula label: an index for tracking descriptive content.

In PIP, X ≡ φ defines X as an abbreviation for formula φ. This definition
is a **tautology** (always true) and can be "floated" to the top of any
discourse. Our encoding models this as a registry entry that persists
monotonically through all operators.
-/
structure FLabel where
  idx : Nat
  deriving DecidableEq, Repr, Hashable

/--
A description: the descriptive content associated with a formula label.

Records which variable is being described and the predicate that
constrains it. When a pronoun carries label α, retrieval evaluates
the description's predicate to find the intended referent.
-/
structure Description (W : Type*) (E : Type*) where
  /-- The variable being described -/
  var : IVar
  /-- The constraining predicate (per assignment and world) -/
  predicate : ICDRTAssignment W E → W → Bool


-- ============================================================
-- Label Store
-- ============================================================

/--
A label store maps formula labels to their descriptive content.

Labels accumulate monotonically as discourse proceeds — they are never
retracted by negation, modals, or other operators. This monotonicity
is what enables cross-modal and cross-negation anaphora.
-/
def LabelStore (W : Type*) (E : Type*) := FLabel → Option (Description W E)

namespace LabelStore

variable {W E : Type*}

/-- Empty label store: no labels registered. -/
def empty : LabelStore W E := λ _ => none

/-- Register a label with its description. -/
def register (s : LabelStore W E) (α : FLabel) (d : Description W E) : LabelStore W E :=
  λ β => if β = α then some d else s β

/-- Look up a label. -/
def lookup (s : LabelStore W E) (α : FLabel) : Option (Description W E) := s α

/-- A label is registered iff its lookup is not none. -/
def registered (s : LabelStore W E) (α : FLabel) : Bool :=
  (s α).isSome

/-- Registration is monotonic: registering a new label preserves old ones. -/
theorem register_preserves (s : LabelStore W E) (α β : FLabel) (d : Description W E)
    (hne : β ≠ α) :
    (s.register α d) β = s β := by
  simp [register, hne]

end LabelStore


-- ============================================================
-- Discourse State
-- ============================================================

/--
A PIP discourse state: information state + label registry.

The discourse state separates two orthogonal concerns:
1. **Info**: the set of live assignment-world pairs (epistemic state)
2. **Labels**: the accumulated descriptive content registry

This separation is key: negation and modals affect `info` but not
`labels`, which is why labels survive these operators and enable
cross-boundary anaphora.
-/
structure Discourse (W : Type*) (E : Type*) where
  /-- The information state (set of assignment-world pairs) -/
  info : IContext W E
  /-- The label registry (monotonically accumulated) -/
  labels : LabelStore W E

namespace Discourse

variable {W E : Type*}

/-- Initial discourse: all possibilities, no labels. -/
def initial : Discourse W E where
  info := IContext.univ
  labels := LabelStore.empty

/-- Empty discourse: contradiction. -/
def empty : Discourse W E where
  info := ∅
  labels := LabelStore.empty

/-- Is the discourse consistent (non-empty info state)? -/
def consistent (d : Discourse W E) : Prop := d.info.Nonempty

/-- Update only the info state, preserving labels. -/
def mapInfo (d : Discourse W E) (f : IContext W E → IContext W E) : Discourse W E :=
  { d with info := f d.info }

/-- Register a new label, preserving info state. -/
def addLabel (d : Discourse W E) (α : FLabel) (desc : Description W E) : Discourse W E :=
  { d with labels := d.labels.register α desc }

end Discourse


-- ============================================================
-- PIP Updates
-- ============================================================

/--
A PIP update: discourse-to-discourse transformer.

In PIP's native formulation, formulas are truth-conditional (not updates).
Our dynamic encoding represents PIP formulas as discourse transformers,
following the @cite{brasoveanu-2010} equivalence. The key invariant: labels
are monotonically accumulated (never retracted), mirroring PIP's property
that formula-label definitions X ≡ φ are tautologies that float freely.
-/
def PUpdate (W : Type*) (E : Type*) := Discourse W E → Discourse W E


-- ============================================================
-- Presupposition
-- ============================================================

/--
Presupposition operator ∂: a definedness condition.

⟦∂φ⟧ filters the information state to pairs where φ holds.
If the result is empty, the utterance is undefined (presupposition failure).

In PIP, presuppositions are used for:
1. Definite descriptions (DEF_α presupposes α is registered)
2. Pronominal anaphora (presupposes antecedent is accessible)
-/
def presuppose {W E : Type*}
    (pred : ICDRTAssignment W E → W → Bool) : PUpdate W E :=
  λ d => d.mapInfo (λ c => { gw ∈ c | pred gw.1 gw.2 })


-- ============================================================
-- Description-Based Retrieval
-- ============================================================

/--
DEF_α: retrieve the entity satisfying the description labeled α.

Given label α and the current discourse state:
1. Look up α's description (variable v, predicate P)
2. Filter to assignments where g(v) is a real entity (not ⋆)
3. Filter to assignments where P(g, w) holds

The presupposition is that α is registered and yields a real entity.
This is the mechanism by which pronouns get their reference: the pronoun
carries label α, and DEF_α retrieves "the x such that P(x)" from the
label store.
-/
def retrieveDef {W E : Type*} (α : FLabel) : PUpdate W E :=
  λ d =>
    match d.labels.lookup α with
    | none => { d with info := ∅ }  -- Presupposition failure: α not registered
    | some desc =>
      d.mapInfo (λ c =>
        { gw ∈ c | (gw.1.indiv desc.var gw.2).isSome ∧ desc.predicate gw.1 gw.2 })


-- ============================================================
-- Plural Truth
-- ============================================================

/--
PIP truth relative to a world and a plural context.

A predicate P holds at world w in context c iff P(g, w) = true
for ALL assignments g paired with w in c.

This "plural" evaluation is what gives PIP its power: different
assignments may bind different entities to the same variable, and
truth requires the predicate to hold across all of them.
-/
def pluralTruth {W E : Type*}
    (c : IContext W E) (w : W) (pred : ICDRTAssignment W E → W → Bool) : Prop :=
  ∀ g, (g, w) ∈ c → pred g w


-- ============================================================
-- External vs. Local Variables
-- ============================================================

/--
Variable binding mode: how a variable was introduced.

- **Local**: Bound by a quantifier in the same clause. Both the individual
  variable and its restrictor are in scope.
- **External**: Bound from an enclosing scope. In modal contexts,
  the world variable is external (introduced by the modal operator).

This distinction falls out naturally from PIP's semantics without
stipulation: under quantifiers, the bound variable is local; under
modals, the world variable is external because it's quantified by
the modal from outside the scope of any indefinites.
-/
inductive BindingMode where
  | local    -- Bound within the current scope
  | external -- Bound from an enclosing scope
  deriving DecidableEq, Repr

/-- A bound variable record: tracks how a variable was introduced. -/
structure BoundVar where
  /-- The variable index -/
  var : IVar
  /-- How it was bound -/
  mode : BindingMode
  /-- The label of the introducing formula (if labeled) -/
  label : Option FLabel
  deriving Repr


-- ============================================================
-- Summation (paper §2.2, items 25–27)
-- ============================================================

/--
Summation: Σxφ = ⋃{g(x) : g ∈ G, ⟦φ⟧^{M,{g},w*} = 1}

Collects entity values across assignments satisfying a predicate.
For "Every farmer bought a donkey. They paid a lot for them.",
"them" = Σx(donkey(x)).

This is a core PIP operation (paper items 25–27), not study-specific.
GQ arguments in PIP take two summation terms: restrictor and scope.
-/
def summationFiltered {W E : Type*} (c : IContext W E) (v : IVar)
    (φ : ICDRTAssignment W E → W → Bool) : Set (Entity E) :=
  { e | ∃ g w, (g, w) ∈ c ∧ φ g w = true ∧ g.indiv v w = e }

/-- Summation without filtering: collects all values of variable v. -/
def summationValues {W E : Type*} (c : IContext W E) (v : IVar) : Set (Entity E) :=
  { e | ∃ g w, (g, w) ∈ c ∧ g.indiv v w = e }

/-- Unfiltered summation equals trivially filtered summation. -/
theorem summationValues_eq_trivial_filter {W E : Type*}
    (c : IContext W E) (v : IVar) :
    summationValues c v = summationFiltered c v (λ _ _ => true) := by
  ext e; simp [summationValues, summationFiltered]

/-- Any assignment in a non-empty context contributes to summation. -/
theorem summation_nonempty {W E : Type*}
    (c : IContext W E) (v : IVar)
    (gw : ICDRTAssignment W E × W)
    (h : gw ∈ c) :
    gw.1.indiv v gw.2 ∈ summationValues c v :=
  ⟨gw.1, gw.2, h, rfl⟩


end Semantics.PIP
