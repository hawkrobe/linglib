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


-- ═══ General Sobel Sequence Theorems ═══

-- The paper's core contribution (§5.1–5.2) is a GENERAL argument that
-- any generic Sobel sequence is consistent and its reversal is inconsistent.
-- The argument depends on a structural relationship between the two generics:
-- the exception's restrictor is a subset of the general's restrictor.

omit [DecidableEq E] in
/-- Helper: `List.all` over a filtered list follows from the filter source. -/
private theorem all_filter_of_forall {l : List E} {p q : E → Bool}
    (h : ∀ e ∈ l, p e = true → q e = true) :
    (l.filter p).all q = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [List.mem_filter] at hx
  exact h x hx.1 hx.2

omit [DecidableEq E] in
/-- Helper: `List.any` is false when no element satisfies the predicate. -/
private theorem any_eq_false_of_forall {l : List E} {p : E → Bool}
    (h : ∀ e ∈ l, p e = false) : l.any p = false := by
  cases hc : l.any p
  · rfl
  · rw [List.any_eq_true] at hc
    obtain ⟨x, hx, hp⟩ := hc
    exact absurd hp (by rw [h x hx]; exact Bool.false_ne_true)

omit [DecidableEq E] in
/-- Helper: `List.any` is true when there exists a satisfying element. -/
private theorem any_eq_true_of_mem {l : List E} {p : E → Bool}
    {e : E} (he : e ∈ l) (hp : p e = true) : l.any p = true := by
  rw [List.any_eq_true]; exact ⟨e, he, hp⟩

omit [DecidableEq E] in
/-- Helper: filter of concatenation where first part is excluded, second included. -/
private theorem filter_append_eq {l₁ l₂ : List E} {p : E → Bool}
    (h₁ : ∀ e ∈ l₁, p e = false) (h₂ : ∀ e ∈ l₂, p e = true) :
    (l₁ ++ l₂).filter p = l₂ := by
  rw [List.filter_append]
  have heq₁ : l₁.filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx; simp [h₁ x hx]
  have heq₂ : l₂.filter p = l₂ := by
    rw [List.filter_eq_self]
    exact h₂
  simp [heq₁, heq₂]

omit [DecidableEq E] in
/-- Helper: `List.all` is false when a member fails. -/
private theorem all_eq_false_of_mem {l : List E} {p : E → Bool}
    {e : E} (he : e ∈ l) (hp : p e = false) : l.all p = false := by
  cases hc : l.all p
  · rfl
  · rw [List.all_eq_true] at hc
    exact absurd (hc e he) (by rw [hp]; exact Bool.false_ne_true)

omit [DecidableEq E] in
/-- General Sobel sequence consistency (§5.1).

    If two generics form a Sobel pair — the general's normal instances
    satisfy its own restrictor and scope, the exception's normal instances
    satisfy their restrictor and scope, and the general's normal instances
    are disjoint from the exception's restrictor — then the Sobel sequence
    [general, exception] is consistent. -/
theorem sobel_pair_consistent
    (general exception : GenericSentence E)
    (hgr : ∀ e ∈ general.normalInstances, general.restrictor e = true)
    (hgs : ∀ e ∈ general.normalInstances, general.scope e = true)
    (hdis : ∀ e ∈ general.normalInstances, exception.restrictor e = false)
    (her : ∀ e ∈ exception.normalInstances, exception.restrictor e = true)
    (hes : ∀ e ∈ exception.normalInstances, exception.scope e = true) :
    isConsistent [general, exception] = true := by
  -- TODO: structured proof using all_filter_of_forall and filter_append_eq
  -- Proof sketch: Step 1 (general against ∅) expands with normal instances, all
  -- satisfy scope → true. Step 2 (exception against normalInstances) finds no
  -- exception-restrictor elements (disjoint), expands, all satisfy scope → true.
  sorry

omit [DecidableEq E] in
/-- General reverse Sobel inconsistency (§5.2).

    If exception normal instances satisfy the exception restrictor and scope,
    the exception restrictor implies the general restrictor (subset),
    all exception normal instances violate the general scope (genuine
    counterexamples), and the exception class is nonempty, then the
    reverse sequence [exception, general] is inconsistent.

    This is the paper's key novel prediction: the dynamic theory explains
    why reverse Sobel sequences are infelicitous, which static theories
    cannot account for. -/
theorem reverse_sobel_pair_inconsistent
    (general exception : GenericSentence E)
    (her : ∀ e ∈ exception.normalInstances, exception.restrictor e = true)
    (hes : ∀ e ∈ exception.normalInstances, exception.scope e = true)
    (hsub : ∀ e, exception.restrictor e = true → general.restrictor e = true)
    (hcounter : ∀ e ∈ exception.normalInstances, general.scope e = false)
    (hne : exception.normalInstances ≠ []) :
    isConsistent [exception, general] = false := by
  -- Unfold the two-step evaluation
  simp only [isConsistent, evalSequence, evalSequence.go, evalGeneric]
  simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, List.nil_append]
  -- After step 1: horizon = exception.normalInstances
  -- Step 2: exception.normalInstances.any general.restrictor = true
  --   because exception normal instances satisfy exception restrictor (her)
  --   and exception restrictor implies general restrictor (hsub)
  have hsub' : ∀ e ∈ exception.normalInstances, general.restrictor e = true :=
    fun e he => hsub e (her e he)
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil exception.normalInstances hne
  have h_has : exception.normalInstances.any general.restrictor = true :=
    any_eq_true_of_mem he₀ (hsub' e₀ he₀)
  simp only [h_has, ↓reduceIte]
  -- The second truth value is false: exception normal instances violate general scope
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, id]
  -- Need: filter ∧ all = false (right conjunct)
  have h_false : (exception.normalInstances.filter general.restrictor).all general.scope = false :=
    all_eq_false_of_mem
      (List.mem_filter.mpr ⟨he₀, hsub' e₀ he₀⟩)
      (hcounter e₀ he₀)
  simp [h_false]


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
