/-!
# Generics: Dynamic Semantics with Horizon Expansion
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

This cumulative expansion explains why generic Sobel sequences
("Ravens are black; but albino ravens aren't") are consistent while their
reverses ("#Albino ravens aren't black; but ravens are") are not: the
evaluation order determines which individuals are salient.

## Static as special case

Discourse-initial evaluation (`evalGeneric []`) reduces to a static
restricted universal (`evalGeneric_empty_eq_static`). The `fromPredicate`
constructor builds a `GenericSentence` from the same primitives as the
classical `traditionalGEN` style (binary normalcy predicate).

## Formal components

- `GenericSentence E`: restrictor + scope + normal instances (`E → Prop` with bundled `DecidablePred`)
- `evalGeneric`: single-generic evaluation, returning a Prop truth value
- `evalSequence`: sequence evaluation
- `fromPredicate`: construct from binary normalcy
- `fromOrder`: construct from normality ordering

## What's not here

This formalizes the single-world case of Kirkpatrick's theory. The full
multi-world version (definition 24, with dispositional orbits `DO(w)` and
per-world modal horizons `σ : W → ℘(W × Eⁿ)`) quantifies over accessible
worlds. The single-world simplification suffices for all the paper's
examples about Sobel sequences.
-/

namespace Semantics.Dynamic.Generics

-- ═══ Computable Model ═══

/-- A generic sentence: restrictor, scope, and normal instances.

The `normalInstances` field packages the output of applying a normality
restriction to the restrictor class. In a full implementation these would
be computed from a `NormalityOrder` via `optimal`; here they are provided
directly to keep the model concrete and the propositional theorems
decidable on finite witnesses.

Kirkpatrick's contextual variable C (the set of alternatives to the
matrix-clause property) is incorporated into the restrictor: the full
restrictor is `kind(x) ∧ C(x)`. Different generics about the same kind
can have different C values, yielding different restrictors. This is how
mixed generic sequences ("Lions have manes and lions give birth") avoid
mutual interference (§5.3). -/
structure GenericSentence (E : Type) where
  restrictor : E → Prop
  scope : E → Prop
  normalInstances : List E
  [decRestrictor : DecidablePred restrictor]
  [decScope : DecidablePred scope]

attribute [instance] GenericSentence.decRestrictor GenericSentence.decScope

variable {E : Type} [DecidableEq E]

/-- Process a single generic against a horizon.

**Expansion rule** (definition 24a): if no restrictor-satisfying
individual is currently salient, expand the horizon to include
the normal restrictor-satisfying individuals.

**Truth rule** (definition 24b): all restrictor-satisfying individuals
on the (possibly expanded) horizon must satisfy the scope. -/
def evalGeneric (horizon : List E) (g : GenericSentence E) :
    List E × Prop :=
  let horizon' : List E :=
    if ∃ e ∈ horizon, g.restrictor e then horizon
    else horizon ++ g.normalInstances
  (horizon', ∀ e ∈ horizon', g.restrictor e → g.scope e)

instance evalGeneric_snd_decidable (horizon : List E) (g : GenericSentence E) :
    Decidable (evalGeneric horizon g).2 := by
  unfold evalGeneric
  infer_instance

/-- Process a sequence of generics left-to-right, threading the horizon.
    Returns the conjunction of all truth values. -/
def evalSequenceFrom : List E → List (GenericSentence E) → Prop
  | _, [] => True
  | horizon, g :: gs =>
    let r := evalGeneric horizon g
    r.2 ∧ evalSequenceFrom r.1 gs

instance evalSequenceFrom_decidable :
    ∀ (horizon : List E) (gs : List (GenericSentence E)),
      Decidable (evalSequenceFrom horizon gs)
  | _, [] => isTrue trivial
  | horizon, g :: gs => by
    have ih := evalSequenceFrom_decidable (evalGeneric horizon g).1 gs
    unfold evalSequenceFrom
    infer_instance

/-- A generic sequence is consistent iff every generic evaluates to true. -/
def isConsistent (gs : List (GenericSentence E)) : Prop :=
  evalSequenceFrom [] gs

instance isConsistent_decidable (gs : List (GenericSentence E)) :
    Decidable (isConsistent gs) := by
  unfold isConsistent; infer_instance


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
/-- General Sobel sequence consistency (§5.1).

    If two generics form a Sobel pair — the general's normal instances
    satisfy the general scope, the exception's normal instances satisfy
    their restrictor and scope, and the general's normal instances are
    disjoint from the exception's restrictor — then the Sobel sequence
    [general, exception] is consistent. -/
theorem sobel_pair_consistent
    (general exception : GenericSentence E)
    (hgs : ∀ e ∈ general.normalInstances, general.scope e)
    (hdis : ∀ e ∈ general.normalInstances, ¬ exception.restrictor e)
    (her : ∀ e ∈ exception.normalInstances, exception.restrictor e)
    (hes : ∀ e ∈ exception.normalInstances, exception.scope e) :
    isConsistent [general, exception] := by
  -- Both evaluations: empty horizon → no restrictor-satisfying element → expansion fires.
  have h_no_gen : ¬ ∃ e ∈ ([] : List E), general.restrictor e := by simp
  have h1 : (evalGeneric [] general).2 := by
    simp only [evalGeneric, h_no_gen, ↓reduceIte, List.nil_append]
    intro e he _; exact hgs e he
  have h_horizon1 : (evalGeneric [] general).1 = general.normalInstances := by
    simp only [evalGeneric, h_no_gen, ↓reduceIte, List.nil_append]
  have h_no_exc :
      ¬ ∃ e ∈ general.normalInstances, exception.restrictor e := by
    rintro ⟨e, he, hr⟩; exact hdis e he hr
  have h2 : (evalGeneric general.normalInstances exception).2 := by
    simp only [evalGeneric, h_no_exc, ↓reduceIte]
    intro e he hrestr
    rcases List.mem_append.mp he with hmem_gen | hmem_exc
    · exact absurd hrestr (hdis e hmem_gen)
    · exact hes e hmem_exc
  -- Glue into isConsistent: conjunction of h1, h2 (with horizon rewritten), and trivial.
  refine ⟨h1, ?_, trivial⟩
  rw [h_horizon1]; exact h2

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
    (her : ∀ e ∈ exception.normalInstances, exception.restrictor e)
    (hsub : ∀ e, exception.restrictor e → general.restrictor e)
    (hcounter : ∀ e ∈ exception.normalInstances, ¬ general.scope e)
    (hne : exception.normalInstances ≠ []) :
    ¬ isConsistent [exception, general] := by
  -- Step 1: exception evaluates true (empty horizon → expansion to its normals).
  have h_no_exc : ¬ ∃ e ∈ ([] : List E), exception.restrictor e := by simp
  have h_horizon1 : (evalGeneric [] exception).1 = exception.normalInstances := by
    simp only [evalGeneric, h_no_exc, ↓reduceIte, List.nil_append]
  -- Step 2: general evaluates false on the exception-normals horizon
  -- because some witness fails the scope.
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil exception.normalInstances hne
  have h_has_gen : ∃ e ∈ exception.normalInstances, general.restrictor e :=
    ⟨e₀, he₀, hsub e₀ (her e₀ he₀)⟩
  have h_general_false : ¬ (evalGeneric exception.normalInstances general).2 := by
    simp only [evalGeneric, h_has_gen, ↓reduceIte]
    intro hall
    exact hcounter e₀ he₀ (hall e₀ he₀ (hsub e₀ (her e₀ he₀)))
  -- Glue: isConsistent unfolds to a conjunction; the second conjunct is false.
  intro hcon
  apply h_general_false
  rw [← h_horizon1]
  exact hcon.2.1


-- ═══ Static-Dynamic Bridge ═══

omit [DecidableEq E] in
/-- Discourse-initial evaluation reduces to a restricted universal over
    `normalInstances` — the propositional analogue of static `traditionalGEN`
    with `situations = normalInstances`, `normal ≡ True`. -/
theorem evalGeneric_empty_eq_static (g : GenericSentence E) :
    (evalGeneric [] g).2 ↔ ∀ e ∈ g.normalInstances, g.restrictor e → g.scope e := by
  have h_no : ¬ ∃ e ∈ ([] : List E), g.restrictor e := by simp
  simp only [evalGeneric, h_no, ↓reduceIte, List.nil_append]


-- ═══ Horizon Evolution ═══

/-! ### Structural characterization of horizon evolution

The horizon-step function is the state-transition component of `evalGeneric`:
it describes how the set of salient individuals evolves as generics are
processed. The step has exactly two behaviors, controlled by a conditional
test:

- **Expansion** (`horizonStep_expand`): when no element of the current
  horizon satisfies the restrictor, the normal instances are appended
- **Blocking** (`horizonStep_blocked`): when some element already satisfies
  the restrictor, the horizon is unchanged

The Sobel asymmetry arises because the subset relation between restrictors
(exception ⊆ general) makes this conditional test asymmetric: in the
forward direction both expansions fire (general normals don't satisfy the
exception restrictor); in the reverse direction the exception's expansion
blocks the general's (exception normals DO satisfy the general restrictor). -/

omit [DecidableEq E] in
/-- The horizon-step function: how `evalGeneric` updates the horizon
    (ignoring the truth value). This is the state-transition component
    of the generic CCP. -/
def horizonStep (g : GenericSentence E) (horizon : List E) : List E :=
  (evalGeneric horizon g).1

omit [DecidableEq E] in
/-- Empty horizon always expands: the output is exactly `normalInstances`. -/
@[simp]
theorem horizonStep_empty (g : GenericSentence E) :
    horizonStep g [] = g.normalInstances := by
  have h_no : ¬ ∃ e ∈ ([] : List E), g.restrictor e := by simp
  simp [horizonStep, evalGeneric, h_no]

omit [DecidableEq E] in
/-- **Expansion**: when no horizon element satisfies the restrictor,
    the normal instances are appended to the horizon. -/
theorem horizonStep_expand (g : GenericSentence E) (horizon : List E)
    (h : ∀ e ∈ horizon, ¬ g.restrictor e) :
    horizonStep g horizon = horizon ++ g.normalInstances := by
  have h_no : ¬ ∃ e ∈ horizon, g.restrictor e := by
    rintro ⟨e, he, hr⟩; exact h e he hr
  simp [horizonStep, evalGeneric, h_no]

omit [DecidableEq E] in
/-- **Blocking**: when some horizon element satisfies the restrictor,
    the horizon is unchanged — no expansion occurs.

    This is the mechanism that creates the Sobel asymmetry: exception
    individuals made salient by a prior generic block the expansion of
    a subsequent general generic, because (by the subset condition)
    they satisfy the general's restrictor. -/
theorem horizonStep_blocked (g : GenericSentence E) (horizon : List E)
    {e : E} (he : e ∈ horizon) (hr : g.restrictor e) :
    horizonStep g horizon = horizon := by
  have h_yes : ∃ e ∈ horizon, g.restrictor e := ⟨e, he, hr⟩
  simp [horizonStep, evalGeneric, h_yes]


-- ═══ Algebraic Properties of Horizon Evolution ═══

/-! ### Closure operator analysis

`horizonStep` satisfies two of the three axioms of a closure operator
(Mathlib: `Order.ClosureOperator`):

1. **Extensive** (`horizonStep_subset`): `horizon ⊆ horizonStep g horizon`
2. **Idempotent** (`horizonStep_idempotent`): `horizonStep g (horizonStep g h) = horizonStep g h`
   (under the natural hypothesis that normal instances satisfy the restrictor)

But it fails the third axiom:

3. **NOT monotone** (`horizonStep_not_monotone`): ∃ g h₁ h₂, h₁ ⊆ h₂ but
   `horizonStep g h₁ ⊄ horizonStep g h₂`

This is structurally interesting: eliminative updates (assertion, test) ARE
monotone (`updateFromSat_monotone` in `Core/CCP.lean`), so they form closure
operators on the dual lattice. Expansive generic updates fail monotonicity
precisely because a LARGER input can BLOCK expansion that a smaller input
would trigger — a phenomenon impossible in eliminative semantics. -/

omit [DecidableEq E] in
/-- `horizonStep` is extensive: the input horizon is always a subset of
    the output. Together with idempotency, this gives two of the three
    closure operator axioms. -/
theorem horizonStep_subset (g : GenericSentence E) (horizon : List E) :
    horizon ⊆ horizonStep g horizon := by
  intro e he
  exact evalGeneric_horizon_superset horizon g e he

omit [DecidableEq E] in
/-- `horizonStep` is idempotent when normal instances satisfy their own
    restrictor: applying it twice gives the same result as applying it once.

    The hypothesis `hnr` ensures that after the first application, the
    horizon contains restrictor-satisfying elements. The second application
    therefore sees these elements and triggers the blocking branch —
    no further expansion occurs.

    Together with `horizonStep_subset`, this establishes that `horizonStep`
    satisfies 2/3 closure operator axioms. -/
theorem horizonStep_idempotent (g : GenericSentence E)
    (hnr : ∀ e ∈ g.normalInstances, g.restrictor e)
    (hne : g.normalInstances ≠ []) (horizon : List E) :
    horizonStep g (horizonStep g horizon) = horizonStep g horizon := by
  by_cases h : ∃ e ∈ horizon, g.restrictor e
  · -- Blocking branch on first step → horizon unchanged → blocking again.
    obtain ⟨e, he, hr⟩ := h
    have hb := horizonStep_blocked g horizon he hr
    rw [hb, hb]
  · -- Expansion branch on first step → output contains normalInstances.
    have h1 : horizonStep g horizon = horizon ++ g.normalInstances := by
      apply horizonStep_expand
      intro e he hr; exact h ⟨e, he, hr⟩
    rw [h1]
    obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ hne
    apply horizonStep_blocked g _ (List.mem_append_right _ he₀) (hnr e₀ he₀)

omit [DecidableEq E] in
/-- `horizonStep` is NOT monotone: there exist `g`, `h₁ ⊆ h₂` such that
    `horizonStep g h₁ ⊄ horizonStep g h₂`.

    Witness: over `Bool`, take `restrictor = (· = true)` (the identity
    Prop on Bool) and `normalInstances = [false]`. Then `h₁ = []`
    triggers expansion (producing `[false]`), but `h₂ = [true]` triggers
    blocking (because `true` satisfies the restrictor). So `false ∈
    horizonStep g []` but `false ∉ horizonStep g [true]`.

    This contrasts with eliminative updates, which ARE monotone
    (`updateFromSat_monotone` in `Core/CCP.lean`): for eliminative
    semantics, `s ⊆ t → u(s) ⊆ u(t)`. The failure of monotonicity
    for expansive updates is what prevents `horizonStep` from being
    a closure operator (`Order.ClosureOperator` in Mathlib), despite
    satisfying extensiveness and idempotency. -/
theorem horizonStep_not_monotone :
    ∃ (g : GenericSentence Bool) (h₁ h₂ : List Bool),
      h₁ ⊆ h₂ ∧ ¬(horizonStep g h₁ ⊆ horizonStep g h₂) := by
  let g : GenericSentence Bool :=
    { restrictor := fun b => b = true
      scope := fun b => b = true
      normalInstances := [false] }
  refine ⟨g, [], [true], List.nil_subset _, ?_⟩
  intro hsub
  have hmem : false ∈ horizonStep g [] := by
    rw [horizonStep_empty]; simp [g]
  have hblock : horizonStep g [true] = [true] :=
    horizonStep_blocked g [true] (List.mem_singleton.mpr rfl) rfl
  have := hsub hmem
  rw [hblock] at this
  simp at this


-- ═══ Sobel Horizon Characterization ═══

omit [DecidableEq E] in
/-- **Forward Sobel: both expansions fire.**

    In the forward sequence [general, exception], the general's normal
    instances don't satisfy the exception restrictor (disjointness), so
    the exception's expansion is not blocked. The final horizon contains
    both sets of normal instances. -/
theorem sobel_forward_horizons (general exception : GenericSentence E)
    (hdis : ∀ e ∈ general.normalInstances, ¬ exception.restrictor e) :
    horizonStep exception (horizonStep general []) =
    general.normalInstances ++ exception.normalInstances := by
  rw [horizonStep_empty, horizonStep_expand _ _ hdis]

omit [DecidableEq E] in
/-- **Reverse Sobel: the general's expansion is blocked.**

    In the reverse sequence [exception, general], the exception's normal
    instances satisfy the general restrictor (by the subset condition),
    so the general's conditional expansion test finds restrictor-satisfying
    individuals already on the horizon. The general does NOT expand — its
    normal instances never become salient. The final horizon contains only
    the exception's normal instances.

    This is the structural reason for the reverse Sobel's inconsistency:
    the general is evaluated against a horizon containing only
    counterexamples (exception normals that violate the general scope). -/
theorem sobel_reverse_horizons (general exception : GenericSentence E)
    (her : ∀ e ∈ exception.normalInstances, exception.restrictor e)
    (hsub : ∀ e, exception.restrictor e → general.restrictor e)
    (hne : exception.normalInstances ≠ []) :
    horizonStep general (horizonStep exception []) =
    exception.normalInstances := by
  rw [horizonStep_empty]
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ hne
  exact horizonStep_blocked general _ he₀ (hsub _ (her _ he₀))

omit [DecidableEq E] in
/-- **Horizon non-commutativity under Sobel conditions.**

    The forward and reverse horizons are structurally different: the forward
    horizon is `general.normalInstances ++ exception.normalInstances` while
    the reverse is just `exception.normalInstances`. Since the general has
    nonempty normal instances, these lists have different lengths.

    This is the structural content of the Sobel asymmetry: horizon evolution
    is non-commutative precisely because the restrictor subset relation is
    asymmetric — exception normals satisfy the general restrictor but
    general normals do not satisfy the exception restrictor. -/
theorem sobel_horizon_noncommutative (general exception : GenericSentence E)
    (hdis : ∀ e ∈ general.normalInstances, ¬ exception.restrictor e)
    (her : ∀ e ∈ exception.normalInstances, exception.restrictor e)
    (hsub : ∀ e, exception.restrictor e → general.restrictor e)
    (hne : exception.normalInstances ≠ [])
    (hne_gen : general.normalInstances ≠ []) :
    horizonStep exception (horizonStep general []) ≠
    horizonStep general (horizonStep exception []) := by
  rw [sobel_forward_horizons _ _ hdis, sobel_reverse_horizons _ _ her hsub hne]
  intro heq
  have hlen : (general.normalInstances ++ exception.normalInstances).length =
      exception.normalInstances.length := by rw [heq]
  simp only [List.length_append] at hlen
  have : general.normalInstances.length ≠ 0 :=
    fun h => hne_gen (List.eq_nil_of_length_eq_zero h)
  omega


-- ═══ Non-interference for Disjoint Restrictors (§5.3) ═══

omit [DecidableEq E] in
/-- **Non-interference for disjoint restrictors** (§5.3).

    When two generics have disjoint restrictors — neither's normal instances
    satisfy the other's restrictor — both orders are consistent, provided
    each generic's normal instances satisfy their own restrictor and scope.

    This is the structural explanation for why mixed generic sequences like
    "Lions have manes and lions give birth to live young" are felicitous
    in both orders: the two generics use different contextual variables C,
    making their restrictors disjoint.

    Note that this follows directly from `sobel_pair_consistent` applied
    symmetrically — the disjointness conditions play the same role as
    the Sobel pair's `hdis` hypothesis, but in both directions. -/
theorem disjoint_pair_consistent
    (g₁ g₂ : GenericSentence E)
    (h₁r : ∀ e ∈ g₁.normalInstances, g₁.restrictor e)
    (h₁s : ∀ e ∈ g₁.normalInstances, g₁.scope e)
    (h₂r : ∀ e ∈ g₂.normalInstances, g₂.restrictor e)
    (h₂s : ∀ e ∈ g₂.normalInstances, g₂.scope e)
    (hdis₁₂ : ∀ e ∈ g₁.normalInstances, ¬ g₂.restrictor e)
    (hdis₂₁ : ∀ e ∈ g₂.normalInstances, ¬ g₁.restrictor e) :
    isConsistent [g₁, g₂] ∧ isConsistent [g₂, g₁] :=
  ⟨sobel_pair_consistent g₁ g₂ h₁s hdis₁₂ h₂r h₂s,
   sobel_pair_consistent g₂ g₁ h₂s hdis₂₁ h₁r h₁s⟩


-- ═══ Commutativity Impossibility (Appendix A) ═══

/-! ### Appendix A: Why @cite{veltman-1996} cannot model the asymmetry

@cite{kirkpatrick-2024} Appendix A (pp. 544–548) shows that
@cite{veltman-1996}'s update semantics predicts both generic Sobel
sequences and their reverses are consistent, because Veltman's
`normallyUpdate` is commutative (`normallyUpdate_comm` in
`UpdateSemantics/Default.lean`): the final expectation state σ₁ = σ₂
regardless of processing order, since the expectation frame π₁ = π₂.

The theorem `commutative_implies_equal_verdicts` generalizes this: ANY
commutative state-transformer forces any state-dependent predicate to
agree on both orders. Combined with `sobel_horizon_noncommutative`,
this establishes that Kirkpatrick's theory escapes the impossibility
precisely because horizon evolution is non-commutative. -/

variable {G S : Type}

/-- **Commutativity forces equal verdicts** (Appendix A, abstract form).

    If the state-transformation function commutes, then any predicate
    on the final state gives the same truth value in both orders.

    This is the formal content of Kirkpatrick's argument against Veltman:
    since `normallyUpdate` commutes, the consistency predicate cannot
    distinguish σ[φ₁][φ₂] from σ[φ₂][φ₁]. In particular, if a Sobel
    sequence is consistent under Veltman's semantics, its reverse must
    be too — contrary to empirical judgment.

    The proof is trivial (congruence under commutativity), but the
    theorem is substantive: it rules out an entire class of theories
    from modeling order-sensitive phenomena. -/
theorem commutative_implies_equal_verdicts
    (process : G → S → S) (P : S → Prop)
    (hcomm : ∀ (a b : G) (s : S), process a (process b s) = process b (process a s))
    (init : S) (g₁ g₂ : G) :
    P (process g₂ (process g₁ init)) ↔ P (process g₁ (process g₂ init)) := by
  rw [hcomm]

/-- **Contrapositive**: if a pair exhibits the Sobel asymmetry for any
    predicate P, then the processing function is not commutative. -/
theorem sobel_asymmetry_rules_out_commutativity
    (process : G → S → S) (P : S → Prop)
    (init : S) (g₁ g₂ : G)
    (hfwd : P (process g₂ (process g₁ init)))
    (hrev : ¬P (process g₁ (process g₂ init))) :
    ∃ (a b : G) (s : S), process a (process b s) ≠ process b (process a s) := by
  refine ⟨g₁, g₂, init, ?_⟩
  intro heq
  exact hrev (heq ▸ hfwd)


-- ═══ Presupposition–Expansion Duality ═══

/-! ### Horizon expansion as presupposition-triggered accommodation

@cite{kirkpatrick-2024} §4.2 (fn. 23) credits @cite{von-fintel-2001}
and @cite{gillies-2007}: the expansion mechanism adapts their dynamic
semantics for counterfactuals. Both use presupposition failure to
trigger context adjustment, but in opposite directions:

- **Eliminative accommodation** (`Presupposition/Accommodation.lean`):
  presupposition failure → *shrink* context (remove non-presupposition worlds)
- **Expansive accommodation** (horizon expansion):
  presupposition failure → *grow* context (add normal restrictor-satisfying individuals)

Both share the same abstract structure:

1. A **presupposition test**: does the context already satisfy a condition?
2. **On success**: no change (the context already works)
3. **On failure**: adjust the context minimally to satisfy the condition
4. **Idempotent**: once satisfied, further applications are no-ops

The key divergence: eliminative accommodation is monotone (larger
contexts yield larger results); expansive accommodation is NOT
(`horizonStep_not_monotone`), because a larger horizon can BLOCK
expansion that a smaller one triggers. -/

/-- The horizon presupposition: restrictor-satisfying individuals are
    already salient. When this holds, no expansion occurs. -/
def horizonPresupposition (restrictor : E → Prop) (horizon : List E) : Prop :=
  ∃ e ∈ horizon, restrictor e

omit [DecidableEq E] in
/-- Presupposition success → no expansion. Delegates to `horizonStep_blocked`. -/
theorem presup_success_no_expansion (g : GenericSentence E) (horizon : List E)
    (h : horizonPresupposition g.restrictor horizon) :
    horizonStep g horizon = horizon := by
  obtain ⟨e, he, hr⟩ := h
  exact horizonStep_blocked g horizon he hr

omit [DecidableEq E] in
/-- Presupposition failure → expansion fires. Delegates to `horizonStep_expand`. -/
theorem presup_failure_expansion (g : GenericSentence E) (horizon : List E)
    (h : ¬ horizonPresupposition g.restrictor horizon) :
    horizonStep g horizon = horizon ++ g.normalInstances := by
  apply horizonStep_expand
  intro e he hr; exact h ⟨e, he, hr⟩


-- ═══ Constructors: Grounding `normalInstances` ═══

/-! ### Constructors for `GenericSentence`

The `normalInstances` field of `GenericSentence` is a stipulation — the
constructors below derive it from different theoretical primitives:

- **`fromPredicate`** — binary normalcy predicate (classical `traditionalGEN`
  style).  Normal instances = domain elements satisfying both restrictor
  and normalcy.

- **`fromOrder`** — normality ordering (`NormalityOrder` style).
  Normal instances = optimal restrictor-satisfying entities under the ordering.
  Bridges to @cite{kirkpatrick-2024} Definition 21's N_n functors.

**Why no `fromThreshold`?** Threshold semantics (Cohen's prevalence > θ)
measures the *proportion* of restrictor-satisfying cases where scope holds.
This is a single Boolean judgment — it doesn't decompose into "select
normal instances, then universally quantify." The `GenericSentence` shape
(restrict → select normals → ∀) captures the normality-based family of
theories; threshold semantics is a genuinely different algebraic shape.
See `CovertQuantifier.reduces_to_threshold` for the threshold ↔ GEN
eliminability result. -/

/-- Construct a `GenericSentence` from a binary normalcy predicate.

    The normal instances are exactly those domain elements satisfying both
    restrictor and normalcy.  Discourse-initial evaluation reduces to a
    restricted universal over those elements. -/
def GenericSentence.fromPredicate
    (restrictor scope : E → Prop) [DecidablePred restrictor] [DecidablePred scope]
    (domain : List E)
    (normal : E → Prop) [DecidablePred normal] : GenericSentence E :=
  ⟨restrictor, scope, domain.filter fun e => decide (restrictor e ∧ normal e)⟩

omit [DecidableEq E] in
/-- Discourse-initial evaluation of `fromPredicate` is a restricted universal
    over normal restrictor-satisfying elements of the domain. -/
theorem fromPredicate_static
    (restrictor scope : E → Prop)
    [DecidablePred restrictor] [DecidablePred scope]
    (domain : List E)
    (normal : E → Prop) [DecidablePred normal] :
    (evalGeneric [] (GenericSentence.fromPredicate restrictor scope domain normal)).2 ↔
    ∀ e ∈ domain, restrictor e → normal e → restrictor e → scope e := by
  rw [evalGeneric_empty_eq_static]
  constructor
  · intro h e he hr hn _
    apply h e _ hr
    simp only [GenericSentence.fromPredicate, List.mem_filter, decide_eq_true_eq]
    exact ⟨he, hr, hn⟩
  · intro h e he hr
    simp only [GenericSentence.fromPredicate, List.mem_filter, decide_eq_true_eq] at he
    obtain ⟨hd, hr', hn⟩ := he
    exact h e hd hr' hn hr

/-- Compute a `GenericSentence` from a decidable normality ordering.

    `le e₁ e₂` means `e₁` is at least as normal as `e₂`,
    matching `NormalityOrder.le`. The normal instances are the
    **optimal** restrictor-satisfying entities: those not strictly
    dominated by any other restrictor-satisfying entity in the domain.

    This is the computable realization of @cite{kirkpatrick-2024}
    Definition 21's N_n functors:
    `N(P)(w) = { a ∈ P(w) | ∀ b ∈ P(w), b ≤ a → a ≤ b }`. -/
def GenericSentence.fromOrder
    (restrictor scope : E → Prop) [DecidablePred restrictor] [DecidablePred scope]
    (domain : List E)
    (le : E → E → Prop) [DecidableRel le] : GenericSentence E :=
  let restricted := domain.filter (fun e => decide (restrictor e))
  let normals := restricted.filter fun e =>
    decide (∀ e' ∈ restricted, le e' e → le e e')
  ⟨restrictor, scope, normals⟩

end Semantics.Dynamic.Generics
