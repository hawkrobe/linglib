import Linglib.Theories.Semantics.Dynamic.Core.CCP

/-!
# Dynamic Semantics for Generics
@cite{kirkpatrick-2024}

James Ravi Kirkpatrick, "The Dynamics of Generics."
*Journal of Semantics* 40(4), 2024. 523–548.

## Core idea

Generics expand a "modal horizon" — the set of salient individuals — as a
side effect of assertion. When processing a generic `Gen[φ][ψ]`:

1. Check whether the horizon already contains restrictor-satisfying individuals
2. If not, **expand** the horizon to include normal restrictor-satisfying ones
3. Evaluate truth: all restrictor-satisfying individuals on the expanded
   horizon must satisfy the scope

This monotonic expansion explains why generic Sobel sequences
("Ravens are black; but albino ravens aren't") are consistent while their
reverses ("#Albino ravens aren't black; but ravens are") are not: the
evaluation order determines which individuals are salient.

## Formal components

- `GenericSentence E`: restrictor + scope + normal instances
- `evalGeneric`: computable single-generic evaluation
- `evalSequence`: computable sequence evaluation
- `horizonExpansionCCP`: abstract CCP connecting to `IsExpansive`

## Connection to existing infrastructure

- `IsExpansive` (`Core/CCP.lean`): horizon expansion is the dual of
  eliminative assertion — it grows rather than shrinks the context
- `NormalityOrder.optimal` (`Core/Order/Normality.lean`): determines
  which individuals count as "normal" for the restrictor class
- `traditionalGEN` (`Lexical/Noun/Kind/Generics.lean`): the static
  normality-based truth conditions that this theory dynamicizes

## What's not here

This formalizes the single-world case of Kirkpatrick's theory. The full
multi-world version (definition 24, with dispositional orbits `DO(w)` and
per-world modal horizons `σ : W → ℘(W × Eⁿ)`) quantifies over accessible
worlds. The single-world simplification suffices for all the paper's
examples about Sobel sequences.
-/

namespace Semantics.Dynamic.Generics

open Semantics.Dynamic.Core (CCP IsExpansive IsEliminative)

-- ═══ Computable Model ═══

/-- A generic sentence: restrictor, scope, and normal instances.

The `normalInstances` field packages the output of applying a normality
restriction to the restrictor class. In a full implementation these would
be computed from a `NormalityOrder` via `optimal`; here they are provided
directly to keep the model computable and the theorems decidable.

Kirkpatrick's contextual variable C (the set of alternatives to the
matrix-clause property) is incorporated into the restrictor: the full
restrictor is `kind(x) ∧ C(x)`. Different generics about the same kind
can have different C values, yielding different restrictors. This is how
mixed generic sequences ("Lions have manes and lions give birth") avoid
mutual interference (§5.3). -/
structure GenericSentence (E : Type) where
  restrictor : E → Bool
  scope : E → Bool
  normalInstances : List E

variable {E : Type} [DecidableEq E]

/-- Process a single generic against a horizon.

**Expansion rule** (definition 24a): if no restrictor-satisfying
individual is currently salient, expand the horizon to include
the normal restrictor-satisfying individuals.

**Truth rule** (definition 24b): all restrictor-satisfying individuals
on the (possibly expanded) horizon must satisfy the scope. -/
def evalGeneric (horizon : List E) (g : GenericSentence E) :
    List E × Bool :=
  let hasRestrictor := horizon.any g.restrictor
  let horizon' := if hasRestrictor then horizon
                  else horizon ++ g.normalInstances
  let truth := (horizon'.filter g.restrictor).all g.scope
  (horizon', truth)

/-- Process a sequence of generics left-to-right, threading the horizon.
    Returns the list of truth values in order. -/
def evalSequence (gs : List (GenericSentence E)) : List Bool :=
  go [] gs []
where
  go (horizon : List E) : List (GenericSentence E) → List Bool → List Bool
    | [], acc => acc.reverse
    | g :: gs, acc =>
      let r := evalGeneric horizon g
      go r.1 gs (r.2 :: acc)

/-- A generic sequence is consistent iff every generic evaluates to true. -/
def isConsistent (gs : List (GenericSentence E)) : Bool :=
  (evalSequence gs).all id


-- ═══ Structural Properties ═══

omit [DecidableEq E] in
/-- Horizon expansion is monotone: every individual on the input horizon
    remains on the output horizon. -/
theorem evalGeneric_horizon_superset (horizon : List E)
    (g : GenericSentence E) (e : E) (he : e ∈ horizon) :
    e ∈ (evalGeneric horizon g).1 := by
  simp only [evalGeneric]
  split
  · exact he
  · exact List.mem_append_left _ he


-- ═══ Abstract CCP Bridge ═══

open Classical in
/-- The horizon expansion step as an abstract CCP on sets of entities.

This connects the computable model above to the CCP infrastructure in
`Core/CCP.lean`. The CCP adds `normalInstances` to the horizon when
no restrictor-satisfying individual is present — an expansive update. -/
noncomputable def horizonExpansionCCP {E : Type*} (restrictor : E → Prop)
    (normalInstances : Set E) : CCP E :=
  λ s => if (∃ e ∈ s, restrictor e) then s else s ∪ normalInstances

open Classical in
/-- Horizon expansion is expansive: the output is always a superset
    of the input. This is `IsExpansive` from `Core/CCP.lean`. -/
theorem horizonExpansion_expansive {E : Type*} (restrictor : E → Prop)
    (normalInstances : Set E) :
    IsExpansive (horizonExpansionCCP restrictor normalInstances) := by
  intro s e he
  unfold horizonExpansionCCP
  split
  · exact he
  · exact Set.mem_union_left _ he

open Classical in
/-- Horizon expansion is NOT eliminative (in general): when expansion
    occurs, new individuals are added.

    Witness: empty horizon with nonempty `normalInstances`. -/
theorem horizonExpansion_not_eliminative {E : Type*}
    (restrictor : E → Prop) (e₀ : E) :
    ¬IsEliminative (horizonExpansionCCP restrictor ({e₀} : Set E)) := by
  intro helim
  have hmem : e₀ ∈ horizonExpansionCCP restrictor {e₀} ∅ := by
    unfold horizonExpansionCCP
    have hno : ¬∃ e ∈ (∅ : Set E), restrictor e := by
      intro ⟨_, he, _⟩; exact he
    rw [if_neg hno]
    exact Set.mem_union_right _ rfl
  exact helim ∅ hmem

end Semantics.Dynamic.Generics
