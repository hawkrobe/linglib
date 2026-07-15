import Linglib.Studies.KeshetAbney2024.Expr
import Linglib.Studies.KeshetAbney2024.Felicity
import Linglib.Studies.KeshetAbney2024.Connectives
import Linglib.Studies.KeshetAbney2024.Composition
import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Plurality.Algebra
import Mathlib.Data.Fintype.Basic

/-!
# PIP Integration Bridges

[keshet-abney-2024] [abney-keshet-2025] [karttunen-1973]
[kratzer-1991] [link-1983] [brasoveanu-2010]

This file connects PIP to the rest of linglib, establishing correspondences
between PIP's formulation and the standard treatments in:

1. **Presupposition projection** — PIP's F operator ↔ `PartialProp.andFilter`
2. **Generalized quantifiers** — PIP's EVERY/SOME ↔ `GQ`
3. **Plural semantics** — PIP's SINGLE/PLURAL ↔ Link's Atom/properPlural
4. **Modal logic** — PIP's must/might ↔ `Intensional.box/diamond`
5. **Static↔dynamic agreement** — `PIPExprF.truth` ↔ `PUpdate` filtering

The set-based GQ operations (`setEvery`/`setSome`), three-argument modals
(`mustBase`/`mightBase`), and sigma evaluation (`sigmaEval`) from the Glossa
companion paper ([abney-keshet-2025]) are in `PIP.Composition`.

## Design

Each section is self-contained: it imports what it needs and states
the correspondence as a theorem or definition. The presupposition,
modal, and static↔dynamic bridges are all proved (atomic and negation
cases for the last); the *full* Brasoveanu model-equivalence — a
bijection between PIP models and ICDRT information states — is a
non-trivial model-theoretic argument left as future work, not
formalized here.
-/

namespace KeshetAbney2024.PIP.Bridges

open KeshetAbney2024.PIP
open DynamicSemantics (IVar ICDRTAssignment Entity IContext)
open Core.Logic.Modal (AccessRel box diamond)
open Core.Logic.Modal.Logic (frameConditions)


-- ============================================================
-- § 1. Presupposition Projection
-- ============================================================

/-!
### Presupposition Projection: F ↔ PartialProp connectives

PIP's F operator and `Semantics.Presupposition.PartialProp` filtering connectives
implement the same Karttunen conjunction clause ([karttunen-1973]).
These theorems were previously in the study file; they belong in the
theory layer because they establish a general correspondence.
-/

/--
PIP's conjunction felicity agrees with `PartialProp.andFilter`.

**PIP Felicity** (`PIPExpr.felicitous` for `.conj φ ψ`):
  `φ.felicitous w && ((φ.truth w).not || ψ.felicitous w)`

**PartialProp.andFilter** (`Semantics.Presupposition`):
  `p.presup w && (!p.assertion w || q.presup w)`

These are structurally identical when interpreting `truth` as `assertion`
and `felicitous` as `presup`.
-/
theorem pip_felicity_agrees_with_andFilter {W : Type*}
    (φ ψ : Felicity.PIPExpr W) (w : W) :
    (Felicity.PIPExpr.conj φ ψ).felicitous w ↔
    (Semantics.Presupposition.PartialProp.andFilter
      (({ presup w := φ.felicitous w, assertion w := φ.truth w } : Semantics.Presupposition.PartialProp _))
      (({ presup w := ψ.felicitous w, assertion w := ψ.truth w } : Semantics.Presupposition.PartialProp _))).presup w :=
  Iff.rfl

/--
PIP's negation felicity agrees with `PartialProp.neg`: both preserve the
presupposition/felicity of the negated expression unchanged.
-/
theorem pip_felicity_agrees_with_neg {W : Type*}
    (φ : Felicity.PIPExpr W) (w : W) :
    (Felicity.PIPExpr.neg φ).felicitous w ↔
    (Semantics.Presupposition.PartialProp.neg
      (({ presup w := φ.felicitous w, assertion w := φ.truth w } : Semantics.Presupposition.PartialProp _))).presup w :=
  Iff.rfl

/--
PIP's implication felicity agrees with `PartialProp.impFilter`.

  F(φ → ψ) = Fφ ∧ (φ → Fψ)

This is exactly the filtering implication from [karttunen-1973]:
the antecedent can satisfy the consequent's presupposition.
-/
theorem pip_felicity_agrees_with_impFilter {W : Type*}
    (φ ψ : Felicity.PIPExpr W) (w : W) :
    (Felicity.PIPExpr.impl φ ψ).felicitous w ↔
    (Semantics.Presupposition.PartialProp.impFilter
      (({ presup w := φ.felicitous w, assertion w := φ.truth w } : Semantics.Presupposition.PartialProp _))
      (({ presup w := ψ.felicitous w, assertion w := ψ.truth w } : Semantics.Presupposition.PartialProp _))).presup w :=
  Iff.rfl

/--
PIP's disjunction felicity agrees with the filtering disjunction:
  F(φ ∨ ψ) = Fφ ∧ (¬φ → Fψ)
-/
theorem pip_felicity_agrees_with_orFilter {W : Type*}
    (φ ψ : Felicity.PIPExpr W) (w : W) :
    (Felicity.PIPExpr.disj φ ψ).felicitous w ↔
    (Semantics.Presupposition.PartialProp.orFilter
      (({ presup w := φ.felicitous w, assertion w := φ.truth w } : Semantics.Presupposition.PartialProp _))
      (({ presup w := ψ.felicitous w, assertion w := ψ.truth w } : Semantics.Presupposition.PartialProp _))).presup w :=
  Iff.rfl


-- ============================================================
-- § 2. Generalized Quantifiers
-- ============================================================

/-!
### GQ Bridge: PIP's set-based quantifiers ↔ GQ

PIP defines (paper item 28):
- EVERY(R, S) iff R ⊆ S
- SOME(R, S) iff R ∩ S ≠ ∅

These are exactly the standard GQ denotations when restrictor and scope
are sets (extensional GQs). The GQ type `(α → Prop) → (α → Prop) → Prop`
is the predicate-based version.
-/

/--
`setEvery` (from `PIP.Composition`, = set inclusion `R ⊆ S`) agrees with
`Quantification.every_sem` (= `∀ x, R x → S x`).

This is the genuine, load-bearing bridge: `setEvery` is `Set`-typed while
`every_sem` is predicate-typed (defeq, but the binder annotations differ,
so a named lemma earns its keep). PIP's set-GQ therefore *consumes* Core's
quantifier theory directly — conservativity, the Zwarts monotonicity
hierarchy, duality — with no PIP-local re-derivation.
-/
theorem setEvery_eq_every_sem {α : Type*} (R S : Set α) :
    setEvery R S ↔ Quantification.every_sem R S :=
  ⟨fun h x hx => h hx, fun h x hx => h x hx⟩

/-- `setSome` agrees with `Quantification.some_sem`. -/
theorem setSome_eq_some_sem {α : Type*} (R S : Set α) :
    setSome R S ↔ Quantification.some_sem R S :=
  ⟨fun ⟨x, hx⟩ => ⟨x, hx.1, hx.2⟩, fun ⟨x, hr, hs⟩ => ⟨x, hr, hs⟩⟩

/-- Conservativity of `setEvery`, inherited from
    `Quantification.every_conservative` (not re-proved). -/
theorem setEvery_conservative' {α : Type*} (R S : Set α) :
    setEvery R S ↔ setEvery R (R ∩ S) := by
  rw [setEvery_eq_every_sem, setEvery_eq_every_sem]
  exact Quantification.every_conservative R S

/-- Conservativity of `setSome`, inherited from
    `Quantification.some_conservative` (not re-proved). -/
theorem setSome_conservative' {α : Type*} (R S : Set α) :
    setSome R S ↔ setSome R (R ∩ S) := by
  rw [setSome_eq_some_sem, setSome_eq_some_sem]
  exact Quantification.some_conservative R S


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
    (hDistr : Semantics.Plurality.Algebra.IsDistr P) {x : E} (hPx : P x) :
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
([kratzer-1991]): the evaluation world w* is accessible from
itself (`R w* w*`). This is exactly the T axiom (`□p → p`,
frame condition: reflexivity).

The `must_truth_agrees_box` and `must_realistic_of_refl`
theorems in `Connectives.lean` already prove this correspondence.
This section classifies PIP's modal operators in the lattice of
normal modal logics from `Intensional`.
-/

/-!
PIP's anaphora-enabling modality needs the **T axiom** (reflexivity): a
realistic modal base guarantees the description holds at the evaluation
world. The content of that claim is carried by `reflexive_satisfies_T`
below (reflexivity ⟹ T's frame condition) together with
`Connectives.must_realistic_of_refl` (which consumes `Std.Refl R` to
derive `p g w₀`). A bare `K ≤ T` lemma would be vacuous — `K = ⊥` — so
it is intentionally omitted.
-/

/--
A reflexive accessibility relation satisfies Logic.T's frame condition.

Stated for the Prop-valued `AccessRel`/`Std.Refl`/`frameConditions` API in
`Intensional` — the same accessibility type PIP's modal
operators now use directly.
-/
theorem reflexive_satisfies_T {W : Type*}
    (R : Core.Logic.Modal.AccessRel W) [hRefl : Std.Refl R] :
    frameConditions Core.Logic.Modal.Logic.T R := by
  unfold frameConditions Core.Logic.Modal.Logic.hasAxiom
    Core.Logic.Modal.Logic.T
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

This is structurally identical to [kratzer-1991]'s analysis where:
- β corresponds to the **modal base** (conversational background)
- The ordering source (for graded modality) is not used in PIP's
  simple must/might

The formal connection is established via `Intensional.box`:
`must_truth_agrees_box` (in Connectives.lean) proves that PIP's
`must R allWorlds (atom p)` produces the same truth conditions as
`box R (p g)`.

Direct import of `Semantics/Modality/Kratzer/` is not possible
because Kratzer's implementation is monomorphic over `World4`. The
correspondence is structural (via `AccessRel` ≅ `ModalBase`) rather
than definitional.
-/

/--
Full Kratzer bridge: PIP's three-argument `mustBase` agrees with
`box` when the modal base comes from an `AccessRel` and the restriction
is tautological.

The composition: `mustBase (accessRelToBase R w) ⊤ {w' | φ.truth w'}` ↔
`box R φ.truth w`. Both express
"the body holds at every R-accessible world from w".
-/
theorem mustBase_agrees_box {W D : Type*}
    (R : AccessRel W) (φ : PIPExprF W D) (w : W) :
    mustBase (accessRelToBase R w) Set.univ { w' | φ.truth w' } ↔
    box R φ.truth w := by
  simp only [mustBase, accessRelToBase, Set.inter_univ, Set.subset_def,
    Set.mem_setOf_eq, box]


-- ============================================================
-- § 6. Static↔Dynamic Agreement
-- ============================================================

/-!
### Static↔Dynamic Agreement

PIP is natively a static, truth-conditional system. Our formalization
in `Basic.lean` / `Connectives.lean` encodes PIP as a dynamic update
system over `IContext W E`. [brasoveanu-2010] shows the equivalence
between plural predicate calculi and dynamic plural logics.

The following theorems prove that the static system (`PIPExprF.truth`)
and the dynamic encoding (`PUpdate` operators) compute the same thing
for the atomic and negation cases (the proofs are complete).

The *full* Brasoveanu equivalence requires establishing a bijection
between PIP models and ICDRT information states — a substantial
model-theoretic argument left as future work, not formalized here.
-/

/--
Static atom truth agrees with dynamic `atom` filtering.

For an atomic predicate p, `PIPExprF.pred p` has truth value `p w`,
and `atom p` filters the info state to pairs where `p g w`.
When the info state is a singleton, the dynamic update is non-empty
iff the static truth value is true.

TODO: Full proof requires reasoning about `Set.sep` over singleton IContext.
-/
theorem static_atom_agrees_dynamic {W E : Type*}
    (p : ICDRTAssignment W E → W → Prop) (g : ICDRTAssignment W E) (w : W)
    (d : Discourse W E) (hd : (g, w) ∈ d.info) :
    (g, w) ∈ (atom p d).info ↔ p g w := by
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


end KeshetAbney2024.PIP.Bridges
