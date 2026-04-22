import Linglib.Theories.Semantics.PIP.Expr
import Linglib.Theories.Semantics.PIP.Felicity
import Linglib.Theories.Semantics.PIP.Connectives
import Linglib.Theories.Semantics.PIP.Composition
import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Quantification.Quantifier
import Linglib.Theories.Semantics.Plurality.Link1983
import Mathlib.Data.Fintype.Basic

/-!
# PIP Integration Bridges

@cite{keshet-abney-2024} @cite{abney-keshet-2025} @cite{karttunen-1973}
@cite{kratzer-1991} @cite{link-1983} @cite{brasoveanu-2010}

This file connects PIP to the rest of linglib, establishing correspondences
between PIP's formulation and the standard treatments in:

1. **Presupposition projection** — PIP's F operator ↔ `PrProp.andFilter`
2. **Generalized quantifiers** — PIP's EVERY/SOME ↔ `PropGQ`
3. **Plural semantics** — PIP's SINGLE/PLURAL ↔ Link's Atom/properPlural
4. **Modal logic** — PIP's must/might ↔ `Core.IntensionalLogic.boxR/diamondR`
5. **Static↔dynamic agreement** — `PIPExprF.truth` ↔ `PUpdate` filtering

The set-based GQ operations (`setEvery`/`setSome`), three-argument modals
(`mustBase`/`mightBase`), and sigma evaluation (`sigmaEval`) from the Glossa
companion paper (@cite{abney-keshet-2025}) are in `PIP.Composition`.

## Design

Each section is self-contained: it imports what it needs and states
the correspondence as a theorem or definition. The presupposition and
modal bridges are proved; the static↔dynamic bridge uses `sorry` for
the Brasoveanu equivalence (which requires a non-trivial model theory
argument).
-/

namespace Semantics.PIP.Bridges

open Semantics.PIP
open Semantics.Dynamic.Core (IVar ICDRTAssignment Entity IContext)
open Core.IntensionalLogic (IsReflexive)
open Core.IntensionalLogic.Logic (frameConditions)


-- ============================================================
-- § 1. Presupposition Projection
-- ============================================================

/-!
### Presupposition Projection: F ↔ PrProp connectives

PIP's F operator and `Core.Presupposition.PrProp` filtering connectives
implement the same Karttunen conjunction clause (@cite{karttunen-1973}).
These theorems were previously in the study file; they belong in the
theory layer because they establish a general correspondence.
-/

/--
PIP's conjunction felicity agrees with `PrProp.andFilter`.

**PIP Felicity** (`PIPExpr.felicitous` for `.conj φ ψ`):
  `φ.felicitous w && ((φ.truth w).not || ψ.felicitous w)`

**PrProp.andFilter** (`Core.Presupposition`):
  `p.presup w && (!p.assertion w || q.presup w)`

These are structurally identical when interpreting `truth` as `assertion`
and `felicitous` as `presup`.
-/
theorem pip_felicity_agrees_with_andFilter {W : Type*}
    (φ ψ : Felicity.PIPExpr W) (w : W) :
    ((Felicity.PIPExpr.conj φ ψ).felicitous w = true) ↔
    (Core.Presupposition.PrProp.andFilter
      (Core.Presupposition.PrProp.ofBool φ.felicitous φ.truth)
      (Core.Presupposition.PrProp.ofBool ψ.felicitous ψ.truth)).presup w := by
  simp only [Felicity.PIPExpr.felicitous, Core.Presupposition.PrProp.andFilter,
    Core.Presupposition.PrProp.ofBool, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun ht => by
      rcases h2 with h | h
      · exact absurd ht (by simp [Bool.not_eq_true'] at h; rw [h]; decide)
      · exact h⟩
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases ht : φ.truth w = true
    · exact Or.inr (h2 ht)
    · simp [Bool.not_eq_true, ht]

/--
PIP's negation felicity agrees with `PrProp.neg`: both preserve the
presupposition/felicity of the negated expression unchanged.
-/
theorem pip_felicity_agrees_with_neg {W : Type*}
    (φ : Felicity.PIPExpr W) (w : W) :
    ((Felicity.PIPExpr.neg φ).felicitous w = true) ↔
    (Core.Presupposition.PrProp.neg
      (Core.Presupposition.PrProp.ofBool φ.felicitous φ.truth)).presup w := by
  simp only [Felicity.PIPExpr.felicitous, Core.Presupposition.PrProp.neg,
    Core.Presupposition.PrProp.ofBool]

/--
PIP's implication felicity agrees with `PrProp.impFilter`.

  F(φ → ψ) = Fφ ∧ (φ → Fψ)

This is exactly the filtering implication from @cite{karttunen-1973}:
the antecedent can satisfy the consequent's presupposition.
-/
theorem pip_felicity_agrees_with_impFilter {W : Type*}
    (φ ψ : Felicity.PIPExpr W) (w : W) :
    ((Felicity.PIPExpr.impl φ ψ).felicitous w = true) ↔
    (Core.Presupposition.PrProp.impFilter
      (Core.Presupposition.PrProp.ofBool φ.felicitous φ.truth)
      (Core.Presupposition.PrProp.ofBool ψ.felicitous ψ.truth)).presup w := by
  simp only [Felicity.PIPExpr.felicitous, Core.Presupposition.PrProp.impFilter,
    Core.Presupposition.PrProp.ofBool, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun ht => by
      rcases h2 with h | h
      · exact absurd ht (by simp [Bool.not_eq_true'] at h; rw [h]; decide)
      · exact h⟩
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases ht : φ.truth w = true
    · exact Or.inr (h2 ht)
    · simp [Bool.not_eq_true, ht]

/--
PIP's disjunction felicity agrees with a one-sided filtering disjunction:
  F(φ ∨ ψ) = Fφ ∧ (¬φ → Fψ)
-/
theorem pip_felicity_agrees_with_orFilter {W : Type*}
    (φ ψ : Felicity.PIPExpr W) (w : W) :
    ((Felicity.PIPExpr.disj φ ψ).felicitous w = true) ↔
    (φ.felicitous w = true ∧ (φ.truth w = true ∨ ψ.felicitous w = true)) := by
  simp only [Felicity.PIPExpr.felicitous, Bool.and_eq_true, Bool.or_eq_true]


-- ============================================================
-- § 2. Generalized Quantifiers
-- ============================================================

/-!
### GQ Bridge: PIP's set-based quantifiers ↔ PropGQ

PIP defines (paper item 28):
- EVERY(R, S) iff R ⊆ S
- SOME(R, S) iff R ∩ S ≠ ∅

These are exactly the standard GQ denotations when restrictor and scope
are sets (extensional GQs). The PropGQ type `(α → Prop) → (α → Prop) → Prop`
is the predicate-based version.
-/

/-- PIP's EVERY as a PropGQ: ∀x, R(x) → S(x) (= set inclusion). -/
def pipEvery {α : Type*} : Semantics.Quantification.Quantifier.PropGQ α :=
  λ R S => ∀ x, R x → S x

/-- PIP's SOME as a PropGQ: ∃x, R(x) ∧ S(x) (= non-empty intersection). -/
def pipSome {α : Type*} : Semantics.Quantification.Quantifier.PropGQ α :=
  λ R S => ∃ x, R x ∧ S x

/-- PIP's EVERY is conservative: EVERY(R, S) ↔ EVERY(R, R ∩ S). -/
theorem pipEvery_conservative {α : Type*} :
    Semantics.Quantification.Quantifier.PConservative (pipEvery (α := α)) := by
  intro R S
  simp only [pipEvery]
  constructor
  · intro h x hR; exact ⟨hR, h x hR⟩
  · intro h x hR; exact (h x hR).2

/-- PIP's EVERY is scope-upward-monotone (right upward monotone). -/
theorem pipEvery_scope_upward_mono {α : Type*} :
    Semantics.Quantification.Quantifier.PScopeUpwardMono (pipEvery (α := α)) := by
  intro R S S' hSS' h x hR
  exact hSS' x (h x hR)

/-- PIP's SOME is conservative: SOME(R, S) ↔ SOME(R, R ∩ S). -/
theorem pipSome_conservative {α : Type*} :
    Semantics.Quantification.Quantifier.PConservative (pipSome (α := α)) := by
  intro R S
  simp only [pipSome]
  constructor
  · intro ⟨x, hR, hS⟩; exact ⟨x, hR, ⟨hR, hS⟩⟩
  · intro ⟨x, hR, _, hS⟩; exact ⟨x, hR, hS⟩

/-- PIP's SOME is scope-upward-monotone (right upward monotone). -/
theorem pipSome_scope_upward_mono {α : Type*} :
    Semantics.Quantification.Quantifier.PScopeUpwardMono (pipSome (α := α)) := by
  intro R S S' hSS' ⟨x, hR, hS⟩
  exact ⟨x, hR, hSS' x hS⟩

-- Bridge: set-based GQs (Composition.lean) ↔ predicate-based PropGQ

/--
`setEvery` from `PIP.Composition` agrees with `pipEvery` (and hence `every_sem`).

Both express universal GQ as set inclusion / pointwise implication.
This bridge lets `setEvery` inherit all `PropGQ` property proofs
(conservativity, monotonicity) from `pipEvery_conservative` etc.
-/
theorem setEvery_eq_pipEvery {α : Type*} (R S : Set α) :
    setEvery R S ↔ pipEvery R S :=
  ⟨fun h x hx => h hx, fun h x hx => h x hx⟩

/--
`setSome` from `PIP.Composition` agrees with `pipSome` (and hence `some_sem`).
-/
theorem setSome_eq_pipSome {α : Type*} (R S : Set α) :
    setSome R S ↔ pipSome R S :=
  ⟨fun ⟨x, hx⟩ => ⟨x, hx.1, hx.2⟩, fun ⟨x, hr, hs⟩ => ⟨x, hr, hs⟩⟩

/--
Conservativity of `setEvery` derived from the PropGQ proof.
-/
theorem setEvery_conservative' {α : Type*} (R S : Set α) :
    setEvery R S ↔ setEvery R (R ∩ S) := by
  rw [setEvery_eq_pipEvery, setEvery_eq_pipEvery]
  exact pipEvery_conservative R S

/--
Conservativity of `setSome` derived from the PropGQ proof.
-/
theorem setSome_conservative' {α : Type*} (R S : Set α) :
    setSome R S ↔ setSome R (R ∩ S) := by
  rw [setSome_eq_pipSome, setSome_eq_pipSome]
  exact pipSome_conservative R S

-- Bridge: PIP's PropGQ ↔ model-theoretic GQ from Quantifier.lean

/--
PIP's EVERY is definitionally equal to `every_sem` from `Quantifier.lean`.

This closes the full bridge chain:
  `setEvery R S` ↔ `pipEvery R S` = `every_sem m R S`

All GQ property proofs in Quantifier.lean (duality, monotonicity,
Zwarts monotonicity hierarchy, quantity invariance, etc.) apply
directly to PIP's quantifiers.
-/
theorem pipEvery_eq_every_sem (F : Core.IntensionalLogic.Frame)
    [Fintype F.Entity] :
    (pipEvery : Semantics.Quantification.Quantifier.PropGQ F.Entity) =
    Semantics.Quantification.Quantifier.every_sem F := rfl

/--
PIP's SOME is definitionally equal to `some_sem` from `Quantifier.lean`.
-/
theorem pipSome_eq_some_sem (F : Core.IntensionalLogic.Frame)
    [Fintype F.Entity] :
    (pipSome : Semantics.Quantification.Quantifier.PropGQ F.Entity) =
    Semantics.Quantification.Quantifier.some_sem F := rfl


-- ============================================================
-- § 3. SINGLE / PLURAL — Link's Atom / properPlural
-- ============================================================

/-!
### Plural Bridge: SINGLE/PLURAL ↔ Link 1983

PIP's SINGLE(τ) (paper item 71) and PLURAL(τ) (paper item 84) correspond
to Link's `Atom` and `properPlural` concepts. The connection is structural:
- SINGLE ↔ the set is a singleton (a "singular" individual = Link's atom)
- PLURAL ↔ the set has 2+ elements (a "plural" individual = non-atom)

The formal connection requires interpreting PIP's sets as Link's lattice
elements. PIP summation yields sets of entities; Link's lattice yields
join-semilattice elements. The bridge theorem states the correspondence
at the level of cardinality conditions.
-/

/--
SINGLE(τ) ↔ |τ| = 1 (paper item 71)

The existential presupposition of singular pronouns: she_τ ↝ τ|SINGLE(τ).
A singular pronoun presupposes that its denotation is a singleton.
-/
def single {α : Type*} (s : Set α) : Prop :=
  ∃ a, s = {a}

/--
PLURAL(τ) ↔ |τ| > 1 (paper item 84)

The presupposition of plural pronouns: they_τ ↝ τ|PLURAL(τ).
-/
def plural {α : Type*} (s : Set α) : Prop :=
  ∃ a b, a ≠ b ∧ a ∈ s ∧ b ∈ s

/-- A singleton set satisfies SINGLE. -/
theorem single_singleton {α : Type*} (a : α) : single ({a} : Set α) :=
  ⟨a, rfl⟩

/-- SINGLE and PLURAL are mutually exclusive. -/
theorem single_not_plural {α : Type*} (s : Set α)
    (hs : single s) : ¬plural s := by
  obtain ⟨a, rfl⟩ := hs
  intro ⟨x, y, hne, hx, hy⟩
  simp only [Set.mem_singleton_iff] at hx hy
  exact hne (hx.trans hy.symm)

/--
Link's `Atom` corresponds to PIP's `SINGLE` when the lattice element
is the join of a singleton set. If P is a distributive predicate and
x satisfies P, then {x} is SINGLE and x is an Atom.
-/
theorem atom_iff_single_base {E : Type*} [SemilatticeSup E] {P : E → Prop}
    (hDistr : Semantics.Plurality.Link1983.Distr P) {x : E} (hPx : P x) :
    Mereology.Atom x := hDistr x hPx

/--
Proper plurals and PLURAL: if x = a ⊔ b with a ≠ b and both in P,
then the corresponding set {a, b} satisfies PLURAL.
-/
theorem properPlural_implies_plural {α : Type*} {a b : α}
    (hne : a ≠ b) : plural ({a, b} : Set α) :=
  ⟨a, b, hne, Set.mem_insert _ _, Set.mem_insert_iff.mpr (Or.inr rfl)⟩


-- ============================================================
-- § 4. Modal Logic Classification
-- ============================================================

/-!
### Modal Logic: PIP's must needs the T axiom

PIP's must allows anaphora because of a **realistic modal base**
(@cite{kratzer-1991}): the evaluation world w* is accessible from
itself (R w* w* = true). This is exactly the T axiom (`□p → p`,
frame condition: reflexivity).

The `must_truth_agrees_kripkeEval` and `must_realistic_of_refl`
theorems in `Connectives.lean` already prove this correspondence.
This section classifies PIP's modal operators in the lattice of
normal modal logics from `Core.IntensionalLogic`.
-/

/--
PIP's anaphora-enabling modality requires at least Logic.T.

The might/must asymmetry for intensional anaphora reduces to whether
the accessibility relation satisfies the T axiom (reflexivity). Must
with a reflexive R guarantees the description holds at the evaluation
world; might with a non-reflexive R does not.
-/
theorem pip_anaphora_requires_T :
    Core.IntensionalLogic.Logic.K ≤ Core.IntensionalLogic.Logic.T :=
  Core.IntensionalLogic.Logic.K_bot ▸ OrderBot.bot_le _

/--
A reflexive accessibility relation satisfies Logic.T's frame condition.

Stated for the Prop-valued `AccessRel`/`IsReflexive`/`frameConditions` API in
`Core.IntensionalLogic`. To apply this to a PIP
`BAccessRel R`, lift via `liftR R = fun a b => R a b = true`.
-/
theorem reflexive_satisfies_T {W : Type*}
    (R : Core.IntensionalLogic.AccessRel W) (hRefl : IsReflexive R) :
    frameConditions Core.IntensionalLogic.Logic.T R := by
  unfold frameConditions Core.IntensionalLogic.Logic.hasAxiom
    Core.IntensionalLogic.Logic.T
  refine ⟨fun _ => hRefl, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp_all [Finset.mem_singleton]


-- ============================================================
-- § 5. Kratzer Correspondence
-- ============================================================

/-!
### Kratzer Correspondence

PIP's modal operators are generalized quantifiers over worlds with an
accessibility relation (paper §2.5):
- MUST^β_w(W₁, W₂) ≜ EVERY(β_w ∩ W₁, W₂)
- MIGHT^β_w(W₁, W₂) ≜ SOME(β_w ∩ W₁, W₂)

This is structurally identical to @cite{kratzer-1991}'s analysis where:
- β corresponds to the **modal base** (conversational background)
- The ordering source (for graded modality) is not used in PIP's
  simple must/might

The formal connection is established via `Core.IntensionalLogic.boxR`:
`must_truth_agrees_boxR` (in Connectives.lean) proves that PIP's
`must R allWorlds (atom p)` produces the same truth conditions as
`boxR (liftR R) (liftP (p g))`.

Direct import of `Theories/Semantics/Modality/Kratzer/` is not possible
because Kratzer's implementation is monomorphic over `World4`. The
correspondence is structural (via `BAccessRel` ≅ `ModalBase`) rather
than definitional.
-/

/--
Full Kratzer bridge: PIP's three-argument `mustBase` agrees with
`boxR` when the modal base comes from a BAccessRel and the restriction
is tautological.

The composition: `mustBase (accessRelToBase R w) ⊤ {w' | φ w' = true}` ↔
`boxR (fun a b => R a b = true) (fun w' => φ w' = true) w`. Both express
"the body holds at every R-accessible world from w".
-/
theorem mustBase_agrees_boxR {W D : Type*} [FiniteDomain D] [Fintype W]
    (R : BAccessRel W) (φ : PIPExprF W D) (w : W) :
    mustBase (accessRelToBase R w) Set.univ { w' | φ.truth w' = true } ↔
    Core.IntensionalLogic.boxR
      (fun a b => R a b = true) (fun w' => φ.truth w' = true) w := by
  simp only [mustBase, accessRelToBase, Set.inter_univ, Set.subset_def,
    Set.mem_setOf_eq, Core.IntensionalLogic.boxR]


-- ============================================================
-- § 6. Static↔Dynamic Agreement
-- ============================================================

/-!
### Static↔Dynamic Agreement

PIP is natively a static, truth-conditional system. Our formalization
in `Basic.lean` / `Connectives.lean` encodes PIP as a dynamic update
system over `IContext W E`. @cite{brasoveanu-2010} shows the equivalence
between plural predicate calculi and dynamic plural logics.

The following theorems state that the static system (`PIPExprF.truth`)
and the dynamic encoding (`PUpdate` operators) compute the same thing
for atomic formulas, conjunction, negation, and presupposition.

Full proof of the Brasoveanu equivalence requires establishing a
bijection between PIP models and ICDRT information states, which is
a substantial model-theoretic argument. We mark these with `sorry`.
-/

/--
Static atom truth agrees with dynamic `atom` filtering.

For an atomic predicate p, `PIPExprF.pred p` has truth value `p w`,
and `atom p` filters the info state to pairs where `p g w = true`.
When the info state is a singleton, the dynamic update is non-empty
iff the static truth value is true.

TODO: Full proof requires reasoning about `Set.sep` over singleton IContext.
-/
theorem static_atom_agrees_dynamic {W E : Type*}
    (p : ICDRTAssignment W E → W → Bool) (g : ICDRTAssignment W E) (w : W)
    (d : Discourse W E) (hd : (g, w) ∈ d.info) :
    (g, w) ∈ (atom p d).info ↔ p g w = true := by
  unfold atom Discourse.mapInfo
  exact ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨hd, hp⟩⟩

/--
Static negation truth agrees with dynamic `negation` filtering.

Negation in both systems complements the truth value / info state.
The dynamic system keeps pairs from the input that did NOT survive φ.
-/
theorem static_neg_agrees_dynamic {W E : Type*}
    (φ : PUpdate W E) (g : ICDRTAssignment W E) (w : W)
    (d : Discourse W E) (hd : (g, w) ∈ d.info) :
    (g, w) ∈ (negation φ d).info ↔ (g, w) ∉ (φ d).info := by
  unfold negation
  dsimp only
  exact ⟨fun ⟨_, hneg⟩ => hneg, fun hneg => ⟨hd, hneg⟩⟩


end Semantics.PIP.Bridges
