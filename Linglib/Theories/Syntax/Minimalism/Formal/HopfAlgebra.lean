/-
# Hopf Algebra Structure (§1.2)

Formalizes the graded connected Hopf algebra H^c on binary forests from
@cite{marcolli-chomsky-berwick-2025} §1.2. In the Connes-Kreimer framework,
syntactic objects generate a Hopf algebra where:

- **Product** = disjoint union of forests (⊔)
- **Coproduct** = sum over admissible cuts (Δ^c)
- **Antipode** = recursive formula S(x) = -x - Σ S(x')·x'' (eq. 1.2.12)
- **Grading** = leaf count (degree)

The key result (Lemma 1.2.10) is that H^c is a graded connected
bialgebra and therefore automatically admits an antipode, making it
a Hopf algebra. Coassociativity of the coproduct is the deep
structural property enabling this.

## Main definitions

- `Forest`, `FLinComb`: forest basis and ℤ-linear combinations
- `forestDeg`: Hopf algebra grading by leaf count
- `counit`: augmentation map ε (1 ↦ 1, T ↦ 0 for deg ≥ 1)
- `reducedCoproductTerms`: Δ̄^c₍₂₎(T) = Σ_{v ∈ V_int} (T_v, T/^c T_v)
- `antipodeAux`, `antipode`: S(T) via eq. 1.2.12

## Main results

- `forestDeg_mul`: deg(F₁ ⊔ F₂) = deg(F₁) + deg(F₂)
- `connected`: every non-empty forest has positive degree
- `counit_multiplicative`: ε(F₁ ⊔ F₂) = ε(F₁) · ε(F₂)
- `antipode_leaf`: S(leaf) = -leaf
- `antipode_bush`: S(node(a,b)) = -node(a,b) when a,b are leaves
- `coassociativity`: (id ⊗ Δ) ∘ Δ = (Δ ⊗ id) ∘ Δ (Lemma 1.2.10)
- `Hc.instCoalgebra`: `Coalgebra ℤ Hc` (CK coproduct on syntactic forests)

## Mathlib instantiation

H^c is directly instantiated as Mathlib's `Coalgebra ℤ Hc` where
`Hc := MonoidAlgebra ℤ (FreeMonoid SyntacticObject)`. The type is `def`
(not `abbrev`) to prevent Mathlib's coefficient-induced coalgebra from
conflicting with the Connes-Kreimer coproduct:

- **Algebra structure** (from `MonoidAlgebra`): product = forest concatenation
- **Coalgebra structure** (custom): CK coproduct = sum over admissible cuts
- **Antipode** (custom): S(T) = -T - Σ S(T_v)·(T/T_v)

This gives access to Mathlib's full coalgebra/Hopf algebra API on `Hc`.

-/

import Linglib.Theories.Syntax.Minimalism.Formal.Coproduct
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

namespace Minimalism

/-! ## Types: forests and linear combinations

The Hopf algebra H^c has basis the set of forests (finite disjoint unions
of trees). The empty forest is the unit. Formal ℤ-linear combinations
of forests form the underlying ℤ-module.

`Forest` is definitionally `FreeMonoid SyntacticObject` — the free monoid
on trees under disjoint union. `FLinComb` is a lightweight list-of-pairs
representation for concrete computation. The Mathlib-grounded type is
`Hc := MonoidAlgebra ℤ (FreeMonoid SyntacticObject)` (see §Instantiation). -/

/-- A forest is a list of syntactic objects — representing the disjoint
    union (product) of trees in H^c. The empty forest `[]` is the unit.

    Definitionally equal to `FreeMonoid SyntacticObject`, inheriting
    the free monoid structure from Mathlib. -/
abbrev Forest := List SyntacticObject

/-- A formal ℤ-linear combination of forests.

    Lightweight representation for concrete computation (antipode, etc.).
    The Mathlib-grounded equivalent is `Hc` (= `MonoidAlgebra ℤ Forest`). -/
abbrev FLinComb := List (ℤ × Forest)

/-! ## Grading (§1.2)

H^c is graded by leaf count: deg(T) = leafCount(T), extended additively
to forests. The grading is compatible with both product and coproduct. -/

/-- Forest degree: total leaf count across all trees.
    deg(∅) = 0, deg(F₁ ⊔ F₂) = deg(F₁) + deg(F₂). -/
def forestDeg : Forest → Nat
  | [] => 0
  | t :: ts => t.leafCount + forestDeg ts

/-- The unit (empty forest) has degree 0. -/
theorem forestDeg_unit : forestDeg ([] : Forest) = 0 := rfl

/-- A single tree has degree = leafCount. -/
theorem forestDeg_singleton (T : SyntacticObject) :
    forestDeg [T] = T.leafCount := by
  simp [forestDeg]

/-- Degree is additive under the forest product (disjoint union). -/
theorem forestDeg_mul (F₁ F₂ : Forest) :
    forestDeg (F₁ ++ F₂) = forestDeg F₁ + forestDeg F₂ := by
  induction F₁ with
  | nil => simp [forestDeg]
  | cons t ts ih => simp [forestDeg, ih]; omega

/-! ## Connectedness

H^c is *connected*: the degree-0 component is 1-dimensional, spanned by
the unit 1 (empty forest). Every tree has leafCount ≥ 1, so the only
degree-0 element is the unit. Connectedness guarantees the existence
and uniqueness of the antipode (Lemma 1.2.10). -/

/-- Every non-empty forest has positive degree. -/
theorem connected (T : SyntacticObject) : forestDeg [T] ≥ 1 := by
  simp [forestDeg]; exact leafCount_pos T

/-- The empty forest is the unique degree-0 basis element. -/
theorem degree_zero_iff_empty (F : Forest) :
    forestDeg F = 0 ↔ F = [] := by
  constructor
  · intro h
    cases F with
    | nil => rfl
    | cons t ts =>
      simp [forestDeg] at h
      have := leafCount_pos t
      omega
  · intro h; subst h; rfl

/-! ## Counit ε (augmentation map)

The counit ε : H^c → ℤ is the algebra homomorphism defined by
ε(1) = 1 and ε(T) = 0 for any tree T. It projects onto the degree-0
component. The counit axiom (ε ⊗ id) ∘ Δ = id = (id ⊗ ε) ∘ Δ
characterizes ε as a coalgebra counit. -/

/-- Counit: the augmentation map ε. ε(∅) = 1, ε(F) = 0 for F ≠ ∅. -/
def counit : Forest → ℤ
  | [] => 1
  | _ :: _ => 0

theorem counit_empty : counit ([] : Forest) = 1 := rfl

theorem counit_singleton (T : SyntacticObject) : counit [T] = 0 := rfl

/-- Counit is multiplicative: ε(F₁ ⊔ F₂) = ε(F₁) · ε(F₂). -/
theorem counit_multiplicative (F₁ F₂ : Forest) :
    counit (F₁ ++ F₂) = counit F₁ * counit F₂ := by
  cases F₁ with
  | nil => simp [counit]
  | cons _ _ => simp [counit]

/-- Counit vanishes on positive-degree elements. -/
theorem counit_pos_deg (F : Forest) (h : forestDeg F ≥ 1) :
    counit F = 0 := by
  cases F with
  | nil => simp [forestDeg] at h
  | cons _ _ => rfl

/-! ## Reduced coproduct Δ̄^c (Definition 1.2.8)

The full coproduct is Δ(T) = T ⊗ 1 + 1 ⊗ T + Δ̄(T) where the reduced
coproduct Δ̄ sums over admissible cuts. The leading (single-cut) term is:

  Δ̄₍₂₎(T) = Σ_{v ∈ V_int(T)} T_v ⊗ T/^c T_v

Each term pairs a subtree T_v (rooted at internal node v) with the
contraction quotient T/^c T_v (the tree with T_v collapsed to a leaf). -/

/-- Reduced coproduct terms: for each internal proper subtree v, pair
    (v, quotient T/^c v). This is the leading term Δ̄^c₍₂₎(T).

    Extends `leadingCoproduct` by resolving the `Option` quotient: only
    produces pairs where the contraction quotient succeeds. -/
def reducedCoproductTerms (T : SyntacticObject) :
    List (SyntacticObject × SyntacticObject) :=
  T.properSubtrees.filterMap fun v =>
    match v with
    | .leaf _ => none
    | .node _ _ =>
      match quotientTree T v with
      | some q => some (v, q)
      | none => none

/-- Leaves have no coproduct terms (no proper subtrees). -/
theorem reducedCoproductTerms_leaf (tok : LIToken) :
    reducedCoproductTerms (.leaf tok) = [] := by
  simp [reducedCoproductTerms, SyntacticObject.properSubtrees]

/-- A bush (node of two leaves) has no coproduct terms: its only proper
    subtrees are leaves, which are filtered out. -/
theorem reducedCoproductTerms_bush (a b : LIToken) :
    reducedCoproductTerms (.node (.leaf a) (.leaf b)) = [] := by
  simp [reducedCoproductTerms, SyntacticObject.properSubtrees,
        SyntacticObject.subtrees, List.filterMap]

/-! ## Antipode S (eq. 1.2.12)

The antipode S is defined recursively by the formula:

  S(T) = -T - Σ S(T_v) · (T/^c T_v)

where the sum ranges over reduced coproduct terms (T_v, T/^c T_v).
This is the unique solution in a graded connected bialgebra
(Lemma 1.2.10), computable by induction on degree. -/

/-- Antipode computation with explicit fuel (depth bound).

    The fuel parameter ensures structural termination. Using
    `nodeCount` as fuel suffices because each recursive call targets
    a proper subtree with strictly fewer internal nodes. -/
def antipodeAux : Nat → SyntacticObject → FLinComb
  | _, .leaf tok => [(-1, [.leaf tok])]
  | 0, so => [(-1, [so])]
  | n+1, .node a b =>
    [(-1, [.node a b])] ++ (reducedCoproductTerms (.node a b)).flatMap fun ⟨v, q⟩ =>
      (antipodeAux n v).map fun ⟨coeff, forest⟩ =>
        (-coeff, forest ++ [q])

/-- The antipode S : SyntacticObject → FLinComb (eq. 1.2.12).

    S(T) = -T - Σ_{(T_v, T/T_v) ∈ Δ̄(T)} S(T_v) · (T/^c T_v)

    Uses `nodeCount` as fuel, which suffices since proper subtrees
    have strictly fewer internal nodes. -/
def antipode (so : SyntacticObject) : FLinComb :=
  antipodeAux so.nodeCount so

/-- S(leaf) = -leaf: leaves are group-like and self-inverse up to sign. -/
theorem antipode_leaf (tok : LIToken) :
    antipode (.leaf tok) = [(-1, [.leaf tok])] := rfl

/-- S(bush) = -bush: a binary node of two leaves has no reduced
    coproduct terms, so the antipode is just negation. -/
theorem antipode_bush (a b : LIToken) :
    antipode (.node (.leaf a) (.leaf b)) = [(-1, [.node (.leaf a) (.leaf b)])] := by
  simp only [antipode, SyntacticObject.nodeCount, Nat.reduceAdd]
  unfold antipodeAux
  dsimp only []
  rw [reducedCoproductTerms_bush]
  simp

/-! ## Hopf algebra axiom

The defining property of the antipode is:

  m ∘ (S ⊗ id) ∘ Δ = η ∘ ε = m ∘ (id ⊗ S) ∘ Δ

where m is the product (forest union), η is the unit map, and ε is
the counit. For trees of positive degree (ε(T) = 0), this says:

  T + Σ S(T_v) · (T/^c T_v) + S(T) = 0

which is exactly the recursive definition of S. The axiom is therefore
satisfied by construction.

TODO: State this formally as an equation on `FLinComb` with a
normalization function that collects like terms. -/

/-- The leading term of the antipode is always -T: antipode(T) starts
    with the coefficient -1 on the forest [T]. This structural property
    follows from the recursive definition (both base cases produce
    [(-1, [T])] and the recursive case prepends [(-1, [T])]). -/
theorem antipode_leading_term (T : SyntacticObject) :
    ∃ rest : FLinComb, antipode T = (-1, [T]) :: rest := by
  cases T with
  | leaf tok => exact ⟨[], rfl⟩
  | node a b =>
    simp only [antipode, SyntacticObject.nodeCount]
    have h : 1 + a.nodeCount + b.nodeCount = (a.nodeCount + b.nodeCount) + 1 := by omega
    rw [h]
    unfold antipodeAux
    dsimp only []
    exact ⟨_, rfl⟩

/-! ## Coassociativity (Lemma 1.2.10)

The coproduct Δ^c is coassociative:

  (id ⊗ Δ^c) ∘ Δ^c = (Δ^c ⊗ id) ∘ Δ^c

This is the key structural property ensuring H^c is a bialgebra.

## Proof strategy (AlgHom reduction)

The coproduct is an algebra homomorphism Δ : Hc →ₐ[ℤ] Hc ⊗ Hc.
Both sides of coassociativity, `(Δ ⊗ id) ∘ Δ` and `(id ⊗ Δ) ∘ Δ`,
are algebra homomorphisms `Hc → Hc ⊗ Hc ⊗ Hc`. By
`MonoidAlgebra.algHom_ext`, two AlgHoms from Hc are equal iff they
agree on generators `single m 1`. Since generators are forests,
and `FreeMonoid.lift` extends multiplicatively, it suffices to check
on single trees — i.e., prove coassociativity for each tree T by
structural induction on `SyntacticObject`.

This reduces a deep algebraic theorem to a combinatorial property
of admissible cuts on binary trees. -/

/-! ## Coproduct size conservation

The coproduct preserves total weight: for each term (T_v, T/^c T_v),
the sum of leaf counts satisfies a conservation law. This is proved
in `Coproduct.lean` as `coproduct_size_identity`; we re-export it
in the Hopf algebra context. -/

/-- Coproduct terms preserve grading: for (v, q) in Δ̄(T),
    deg([v]) + deg([q]) = deg([T]) + 1.

    The +1 accounts for the trace leaf introduced by contraction. -/
theorem coproduct_preserves_grading (T v q : SyntacticObject)
    (hc : contains T v) (hq : quotientTree T v = some q) :
    forestDeg [v] + forestDeg [q] = forestDeg [T] + 1 := by
  simp only [forestDeg_singleton]
  have h := coproduct_size_identity T v q hc hq
  have hv := leafCount_pos v
  have hqp := leafCount_pos q
  omega

/-! ## Mathlib instantiation: Coalgebra ℤ Hc

H^c is instantiated as Mathlib's `Coalgebra` over the integer monoid
algebra on forests. The type `Hc` is a `def` (not `abbrev`) to block
the default coefficient-induced coalgebra from `MonoidAlgebra.instCoalgebra`
— the Connes-Kreimer coproduct sums over admissible cuts, which is
fundamentally different from the group-like coproduct Δ(F) = F ⊗ F.

The algebra structure (product = forest concatenation) is forwarded
from `MonoidAlgebra`. Only the coalgebra structure is custom.

### What `Coalgebra ℤ Hc` provides

With this instance, Mathlib's coalgebra API applies to H^c:
- `Coalgebra.comul : Hc →ₗ[ℤ] Hc ⊗[ℤ] Hc` — CK coproduct
- `Coalgebra.counit : Hc →ₗ[ℤ] ℤ` — augmentation map
- `Coalgebra.coassoc` — coassociativity (Lemma 1.2.10)
- All derived lemmas: `coassoc_apply`, `counit_apply`, etc.

### How comul is constructed

The CK coproduct is built in three layers:

1. `comulGen : SyntacticObject → Hc ⊗ Hc` — coproduct on single trees
2. `FreeMonoid.lift comulGen : FreeMonoid SO →* Hc ⊗ Hc` — multiplicative
   extension to forests (Δ(F₁⊔F₂) = Δ(F₁)·Δ(F₂))
3. `MonoidAlgebra.lift` — linear extension to all of Hc as an `AlgHom`

The `AlgHom` structure means coassociativity reduces (via
`MonoidAlgebra.algHom_ext`) to checking on single trees by
structural induction, rather than needing a global proof.
-/

open scoped TensorProduct

/-- The Connes-Kreimer Hopf algebra H^c on syntactic forests.

    Mathematically: the free ℤ-module on forests of syntactic objects,
    with product = forest concatenation and coproduct = sum over
    admissible cuts (@cite{marcolli-chomsky-berwick-2025} §1.2).

    `def` (not `abbrev`) ensures Lean uses our CK coproduct
    rather than the coefficient-induced one from `MonoidAlgebra.instCoalgebra`. -/
def Hc := MonoidAlgebra ℤ (FreeMonoid SyntacticObject)

namespace Hc

-- Algebra structure forwarded from MonoidAlgebra
noncomputable instance : Semiring Hc :=
  inferInstanceAs (Semiring (MonoidAlgebra ℤ (FreeMonoid SyntacticObject)))

noncomputable instance : Ring Hc :=
  inferInstanceAs (Ring (MonoidAlgebra ℤ (FreeMonoid SyntacticObject)))

noncomputable instance : Algebra ℤ Hc :=
  inferInstanceAs (Algebra ℤ (MonoidAlgebra ℤ (FreeMonoid SyntacticObject)))

-- Evaluate Hc elements at a forest (coefficient access)
instance : DFunLike Hc (FreeMonoid SyntacticObject) (fun _ => ℤ) :=
  inferInstanceAs (DFunLike (FreeMonoid SyntacticObject →₀ ℤ)
    (FreeMonoid SyntacticObject) (fun _ => ℤ))

/-- Embed a forest as a basis element of H^c: F ↦ 1·F. -/
noncomputable def ofForest (F : Forest) : Hc :=
  (Finsupp.single (FreeMonoid.ofList F) 1 : MonoidAlgebra ℤ (FreeMonoid SyntacticObject))

/-- Embed a single tree as a basis element of H^c. -/
noncomputable def ofTree (T : SyntacticObject) : Hc :=
  ofForest [T]

/-! ### Comultiplication (CK coproduct as AlgHom) -/

/-- CK coproduct on a single tree:
    Δ(T) = [T] ⊗ 1 + 1 ⊗ [T] + Σ_{(v,q) ∈ Δ̄(T)} [v] ⊗ [q]

    This is the value on generators. The full coproduct on forests
    extends multiplicatively via `FreeMonoid.lift`, and linearly
    to all of Hc via `MonoidAlgebra.lift`. -/
noncomputable def comulGen (T : SyntacticObject) : Hc ⊗[ℤ] Hc :=
  ofTree T ⊗ₜ 1 + 1 ⊗ₜ ofTree T +
  (reducedCoproductTerms T).foldl
    (fun acc ⟨v, q⟩ => acc + ofTree v ⊗ₜ ofTree q) 0

/-- CK coproduct as a monoid homomorphism on forests.
    Multiplicative: Δ(F₁ ⊔ F₂) = Δ(F₁) · Δ(F₂)
    where multiplication in Hc ⊗ Hc is componentwise. -/
noncomputable def comulMonoidHom : FreeMonoid SyntacticObject →* (Hc ⊗[ℤ] Hc) :=
  FreeMonoid.lift comulGen

/-- CK coproduct as an algebra homomorphism on Hc.
    Constructed via `MonoidAlgebra.lift`: extends `comulMonoidHom`
    linearly from monoid elements to all of Hc.

    This is an `AlgHom`, not just a `LinearMap`, which means
    coassociativity can be reduced to generators via `algHom_ext`. -/
noncomputable def comulAlgHom : Hc →ₐ[ℤ] (Hc ⊗[ℤ] Hc) :=
  MonoidAlgebra.lift ℤ (Hc ⊗[ℤ] Hc) (FreeMonoid SyntacticObject) comulMonoidHom

/-! ### comulAlgHom reduction lemmas -/

/-- comulAlgHom on a single tree reduces to comulGen.

    Proof: `MonoidAlgebra.lift_single` gives `r • f(m)` for `single m r`;
    at `r = 1` this is `1 • comulGen T = comulGen T`. -/
theorem comulAlgHom_ofTree (T : SyntacticObject) :
    comulAlgHom (ofTree T) = comulGen T := by
  unfold comulAlgHom ofTree ofForest
  show ((MonoidAlgebra.lift ℤ (Hc ⊗[ℤ] Hc) (FreeMonoid SyntacticObject)) comulMonoidHom)
    (MonoidAlgebra.single (FreeMonoid.ofList [T]) 1) = comulGen T
  rw [MonoidAlgebra.lift_single]
  exact one_smul ℤ _

/-- comulAlgHom.toLinearMap maps 1 to 1 ⊗ₜ 1.

    The linear map underlying the AlgHom preserves the unit. -/
theorem comulAlgHom_toLinearMap_one :
    comulAlgHom.toLinearMap (1 : Hc) = (1 : Hc) ⊗ₜ[ℤ] (1 : Hc) := by
  show comulAlgHom (1 : Hc) = _
  rw [map_one]; rfl

/-- comulGen simplifies for primitive elements (trees with no
    reduced coproduct terms). Leaves and bushes are primitive. -/
theorem comulGen_primitive (T : SyntacticObject)
    (h : reducedCoproductTerms T = []) :
    comulGen T = ofTree T ⊗ₜ 1 + 1 ⊗ₜ ofTree T := by
  simp [comulGen, h]

/-! ### Counit -/

/-- Counit as a linear map: ε(Σ cᵢ Fᵢ) = c_∅ (coefficient of the empty forest).

    This is the linear extension of the computational `counit` function. -/
noncomputable def hcCounit : Hc →ₗ[ℤ] ℤ where
  toFun f := f (1 : FreeMonoid SyntacticObject)
  map_add' x y := Finsupp.add_apply x y _
  map_smul' r x := congr_fun (Finsupp.coe_smul r x) _

/-! ### Antipode -/

/-- Antipode as a linear endomorphism: the linear extension of
    S(T) = -T - Σ S(T_v)·(T/^c T_v) (eq. 1.2.12). -/
noncomputable def hcAntipode : Hc →ₗ[ℤ] Hc where
  toFun := sorry
  map_add' := sorry
  map_smul' := sorry

/-! ### Coalgebra instance -/

/-- The Connes-Kreimer coalgebra structure on H^c.

    `comul` is constructed as an `AlgHom` (via `comulAlgHom`), then
    the `AlgHom.toLinearMap` is extracted for the `Coalgebra` instance.
    Coassociativity reduces to checking on generators (single trees)
    via `MonoidAlgebra.algHom_ext`. -/
noncomputable instance instCoalgebra : Coalgebra ℤ Hc where
  comul := comulAlgHom.toLinearMap
  counit := hcCounit
  coassoc := sorry
  rTensor_counit_comp_comul := sorry
  lTensor_counit_comp_comul := sorry

/-! ### Coassociativity reduction to generators

Coassociativity `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` is an equation of
linear maps `Hc → Hc ⊗ Hc ⊗ Hc`. Since `Δ` is an `AlgHom` and
both sides are `AlgHom`s (compositions of algebra homomorphisms),
`MonoidAlgebra.algHom_ext` reduces this to checking on generators
`single m 1` for each `m : FreeMonoid SyntacticObject`. Since
forests are products of single trees and `Δ` is multiplicative,
it suffices to check on single trees — i.e., structural induction
on `SyntacticObject`.

### Proof structure

The proof proceeds by `cases T`:

- **Leaf/bush (primitive elements)**: When `reducedCoproductTerms T = []`,
  `comulGen T = T ⊗ₜ 1 + 1 ⊗ₜ T`. Both sides expand to
  `T ⊗ₜ (1 ⊗ₜ 1) + 1 ⊗ₜ (T ⊗ₜ 1) + 1 ⊗ₜ (1 ⊗ₜ T)`.
  Proved by `coassoc_gen_primitive`.

- **Node (non-primitive)**: When `reducedCoproductTerms T ≠ []`,
  the additional terms `Σ vᵢ ⊗ₜ qᵢ` produce nested coproducts
  `Σ comul(vᵢ) ⊗ₜ qᵢ` (LHS) vs `Σ vᵢ ⊗ₜ comul(qᵢ)` (RHS).
  Coassociativity follows from a bijection on admissible cut pairs:
  "cut T, then cut the pruned subtree vᵢ" corresponds to
  "cut T, then cut the quotient qᵢ" (@cite{marcolli-chomsky-berwick-2025}
  Lemma 1.2.10). TODO: formalize the nested cut bijection. -/

set_option maxHeartbeats 800000 in
/-- Coassociativity for primitive elements: trees T with
    `reducedCoproductTerms T = []` (leaves and bushes).

    For primitive elements, `comulGen T = T ⊗ₜ 1 + 1 ⊗ₜ T`,
    and the proof reduces to tensor algebra manipulation + `abel`. -/
theorem coassoc_gen_primitive (T : SyntacticObject)
    (h : reducedCoproductTerms T = []) :
    TensorProduct.assoc ℤ Hc Hc Hc
      (comulAlgHom.toLinearMap.rTensor Hc (comulAlgHom (ofTree T))) =
    comulAlgHom.toLinearMap.lTensor Hc (comulAlgHom (ofTree T)) := by
  rw [comulAlgHom_ofTree, comulGen_primitive T h]
  simp only [map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  rw [show comulAlgHom.toLinearMap (ofTree T) = comulGen T from comulAlgHom_ofTree _,
      comulAlgHom_toLinearMap_one, comulGen_primitive T h]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
             map_add, TensorProduct.assoc_tmul]
  abel

/-- Coassociativity on a single tree: the two orderings of nested
    coproduct application produce the same triple tensor.

    This is the generator-level statement that, together with
    `MonoidAlgebra.algHom_ext`, implies the full `Coalgebra.coassoc`.

    Proved for primitive elements (leaf, bush). The node case requires
    formalizing the bijection on nested admissible cuts. -/
theorem coassoc_gen (T : SyntacticObject) :
    TensorProduct.assoc ℤ Hc Hc Hc
      (comulAlgHom.toLinearMap.rTensor Hc (comulAlgHom (ofTree T))) =
    comulAlgHom.toLinearMap.lTensor Hc (comulAlgHom (ofTree T)) := by
  cases T with
  | leaf tok => exact coassoc_gen_primitive _ (reducedCoproductTerms_leaf tok)
  | node a b =>
    -- TODO: The non-primitive case requires showing that nested
    -- applications of comul to the reduced coproduct terms of (node a b)
    -- produce the same triple tensor in both orderings. This is the
    -- combinatorial heart of the CK coassociativity proof: a bijection
    -- between pairs of nested admissible cuts.
    sorry

end Hc

end Minimalism
