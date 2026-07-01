import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Multiset.Basic

set_option autoImplicit false

/-!
# Connes-Kreimer Hopf algebra carrier on n-ary rooted trees
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The **Connes-Kreimer Hopf algebra** on a tree type T is the formal
R-linear combinations of forests (multisets of trees), with product =
forest disjoint union and coproduct = sum over admissible cuts (defined
in `Coproduct/Pruning.lean` for Δ^ρ, `Coproduct/Trace.lean` for Δ^c).

This file provides the **carrier and counit** generic over a tree type T
(parameterized over `Type*`) — nothing here pattern-matches on the tree
carrier. The intended specializations:

- `T = RoseTree α` — n-ary rooted trees (the root-level carrier in
  `Linglib/Core/Data/RoseTree/Basic.lean`; the sibling coproduct files
  instantiate here).
- `T = RootedTree.Nonplanar α` — n-ary nonplanar rooted trees
  (`Nonplanar α := Quotient RoseTree.instSetoid`, a quotient of `RoseTree α`).

The product structure (algebra) doesn't depend on which T is used —
forests are multisets, multiset addition is commutative (Hopf
algebra is commutative). The coproduct depends on the cut substrate
of T; see sibling files for specific instantiations.

## Layer status

`[UPSTREAM]` candidate. No sorries.

## MCB anchor

[marcolli-chomsky-berwick-2025] §1.2 "Workspaces: Product and
Coproduct" introduces the Hopf algebra of workspaces; the carrier is
`V(𝔉_{SO_0}) = AddMonoidAlgebra R (Multiset (FCM α))`. This file
generalizes the carrier to arbitrary tree type T, with binary FCM as
one specialization (eventual Phase B target).

[foissy-introduction-hopf-algebras-trees] §1.2: "The Hopf algebra
H_R is the free associative commutative unitary K-algebra generated
by T", where T is the set of rooted trees. Same structure here, with
T parameterized.

## Naming

Type: `RootedTree.ConnesKreimer R T` with eponymous namespace
`RootedTree.ConnesKreimer`. Eponymous-type-and-namespace pattern matches
mathlib idiom (`Polynomial`, `WittVector`, `PowerSeries`, etc.) — no
abbreviation. The legacy `open ConnesKreimer` statements in soon-to-be-
rebuilt consumer files (Adger2025, Merge/*, etc.) referred to the now-
deleted top-level `ConnesKreimer.{TraceTree, Hc, ...}` and won't compile
against the new substrate anyway, so the silent re-binding hazard is
moot — those files need full Phase D rewrites.

The eventual upstream-mathlib home would be
`Mathlib.RingTheory.HopfAlgebra.RootedTree.ConnesKreimer` or similar.
-/

namespace RootedTree

/-! ## §1: Forest type alias

A **forest** is a multiset of trees. Multiset addition is the disjoint
union (forest concatenation). -/

/-- A forest of T-shaped trees: finite multiset. -/
abbrev Forest (T : Type*) : Type _ := Multiset T

/-! ## §2: The Connes-Kreimer Hopf algebra carrier -/

/-- The **Connes-Kreimer Hopf algebra** on tree type T:
    `AddMonoidAlgebra R (Forest T)`. As an algebra: product = forest
    disjoint union (commutative), unit = empty forest. The Bialgebra
    structure (coproduct + coassoc + counit laws) is in sibling files. -/
def ConnesKreimer (R : Type*) [CommSemiring R] (T : Type*) : Type _ :=
  AddMonoidAlgebra R (Forest T)

namespace ConnesKreimer

/-! ## §3: Forwarded mathlib instances

`ConnesKreimer R T` is a `def`, not `abbrev`, isolating its eventual
Bialgebra structure from mathlib's default `AddMonoidAlgebra.instBialgebra`
(group-like coproduct). Forward `CommSemiring`, `Algebra`, and `FunLike`
explicitly. -/

variable {R : Type*} [CommSemiring R] {T : Type*}

noncomputable instance instCommSemiring : CommSemiring (ConnesKreimer R T) :=
  inferInstanceAs (CommSemiring (AddMonoidAlgebra R (Forest T)))

noncomputable instance instAlgebra : Algebra R (ConnesKreimer R T) :=
  inferInstanceAs (Algebra R (AddMonoidAlgebra R (Forest T)))

instance instFunLike : FunLike (ConnesKreimer R T) (Forest T) R :=
  inferInstanceAs (FunLike (Forest T →₀ R) (Forest T) R)

/-! ### Field-coherent `AddCommGroup` for `[CommRing R]`

Constructed manually as `{ instAddCommMonoid with ... }` — fields typed
`CK → CK → CK`, not `Finsupp → Finsupp → Finsupp`. This avoids the kernel
mismatch that `inferInstanceAs (AddCommGroup (Forest T →₀ R))` triggers:
that form's `_aux_1_*` fields carry Finsupp types and reject when used as
`AddCommGroup CK`.

The `neg`/`sub`/`zsmul` fields delegate to the underlying Finsupp
operations via the identity coercion (CK = AddMonoidAlgebra R (Forest T) =
Forest T →₀ R as defs). They agree definitionally with the operations
coming through `Algebra ℤ CK → Module ℤ CK → SMul ℤ CK`, so no SMul ℤ
diamond arises at downstream call sites. -/

/-! ### AddCommGroup helper (NOT a global instance — use `attribute [local instance]`)

**Diamond verdict (2026-05-19, task #12 deep-dive)**: registering `AddCommGroup CK`
globally creates a `SMul ℤ CK` diamond. Two paths to `SMul ℤ CK`:
- `Algebra ℤ CK → Module ℤ CK → SMul ℤ CK` (existing, via instAlgebra)
- `AddCommGroup CK → SubNegMonoid → SubNegMonoid.toZSMul → SMul ℤ CK` (new)

Lean's typeclass elaboration picks one OR the other depending on context.
At `op_smul := rfl` sites in `PreLie/OudomGuinBridge.lean`, the LHS (CK-side
`r • x`) may pick SubNeg while the RHS (GL-side `r • op x` via GL's frozen
`instModule = inferInstanceAs (Module R CK)`) is locked to Algebra-derived.

**Structural fix would be**: refactor CK from `def` to `structure` (mathlib's
pattern for `Polynomial`, `WittVector`). This isolates all instances — no
parent-type alternative paths exist. Large refactor (hundreds of call sites).

**Tactical fix**: provide AddCommGroup as a `def` (not an instance), and use
`attribute [local instance]` at the consumer site so other files don't pick
it up. -/

/-- `AddCommGroup` on `ConnesKreimer R T` (not a global instance). Register
    locally in consumer files via `attribute [local instance] addCommGroupOf`.

    Takes both `[CommSemiring R]` and `[CommRing R]` to avoid a typeclass-instance
    diamond at consumer sites where the section variable has `[CommSemiring R]`
    and the theorem adds `[CommRing R]` (Lean treats these as separate hypotheses
    even though `CommRing` extends `CommSemiring`). -/
@[reducible] noncomputable def addCommGroupOf {R : Type*}
    [CommRing R] {T : Type*} :
    AddCommGroup (ConnesKreimer R T) :=
  inferInstanceAs (AddCommGroup (AddMonoidAlgebra R (Forest T)))

/-! ## §4: Basis embeddings — `of'`, `ofTree`

The natural inclusions of basis elements (forests, single trees) into
the algebra. Mirrors mathlib's `MonoidAlgebra.of'` (bare function form)
and `MonoidAlgebra.of` (`MonoidHom` form). -/

/-- **Bare embedding**: a forest as the basis vector `Finsupp.single F 1`. -/
noncomputable def of' (F : Forest T) : ConnesKreimer R T :=
  Finsupp.single F (1 : R)

/-- **MonoidHom embedding**: `Multiplicative (Forest T) →* ConnesKreimer R T`. -/
noncomputable def of : Multiplicative (Forest T) →* ConnesKreimer R T where
  toFun F := of' (R := R) F.toAdd
  map_one' := by
    show (of' (R := R) (1 : Multiplicative (Forest T)).toAdd : ConnesKreimer R T) = 1
    show (Finsupp.single (0 : Forest T) (1 : R)
            : AddMonoidAlgebra R (Forest T))
       = (1 : AddMonoidAlgebra R (Forest T))
    exact AddMonoidAlgebra.one_def.symm
  map_mul' F G := by
    show of' (R := R) (F * G).toAdd = of' (R := R) F.toAdd * of' (R := R) G.toAdd
    show of' (R := R) (F.toAdd + G.toAdd) = of' (R := R) F.toAdd * of' (R := R) G.toAdd
    unfold of'
    exact (AddMonoidAlgebra.single_mul_single
      (R := R) (M := Forest T) F.toAdd G.toAdd 1 1
      |>.trans (by rw [mul_one])).symm

/-- Embed a single tree as a singleton-forest basis vector. -/
noncomputable def ofTree (t : T) : ConnesKreimer R T :=
  of' ({t} : Forest T)

theorem of_apply (F : Multiplicative (Forest T)) :
    (of (R := R) F : ConnesKreimer R T) = of' F.toAdd := rfl

theorem of'_apply (F : Forest T) :
    (of' (R := R) F : ConnesKreimer R T) = Finsupp.single F 1 := rfl

@[simp] theorem of'_zero :
    (of' (R := R) (0 : Forest T) : ConnesKreimer R T) = 1 :=
  (of (R := R) (T := T)).map_one

/-- Headline algebraic fact: forest disjoint union ↔ algebra product. -/
@[simp] theorem of'_add (F G : Forest T) :
    (of' (R := R) (F + G) : ConnesKreimer R T)
      = of' (R := R) F * of' (R := R) G :=
  (of (R := R) (T := T)).map_mul (Multiplicative.ofAdd F) (Multiplicative.ofAdd G)

@[simp] theorem of'_singleton (t : T) :
    (of' (R := R) ({t} : Forest T) : ConnesKreimer R T) = ofTree t := rfl

/-! ## §5: Counit

The counit ε : ConnesKreimer R T → R extracts the coefficient of the
empty forest, packaged as an algebra hom. -/

/-- The counit as a `Multiplicative (Forest T) →* R` monoid hom.

    Uses `Multiset.card_eq_zero` to avoid requiring `DecidableEq T`:
    test "is empty" via "has cardinality zero" (card is Nat, decidable). -/
noncomputable def counitMonoidHom :
    Multiplicative (Forest T) →* R where
  toFun F := if F.toAdd.card = 0 then 1 else 0
  map_one' := by
    show (if (0 : Forest T).card = 0 then (1 : R) else 0) = 1
    rw [Multiset.card_zero, if_pos rfl]
  map_mul' F G := by
    show (if (F.toAdd + G.toAdd).card = 0 then (1 : R) else 0)
       = (if F.toAdd.card = 0 then (1 : R) else 0)
       * (if G.toAdd.card = 0 then (1 : R) else 0)
    rw [Multiset.card_add]
    by_cases hF : F.toAdd.card = 0
    · by_cases hG : G.toAdd.card = 0
      · rw [if_pos hF, if_pos hG, if_pos (by rw [hF, hG]), mul_one]
      · rw [if_pos hF, if_neg hG, if_neg (by rw [hF, zero_add]; exact hG), one_mul]
    · by_cases hG : G.toAdd.card = 0
      · rw [if_neg hF, if_pos hG, if_neg (by rw [hG, Nat.add_zero]; exact hF), mul_one]
      · have h : ¬ (F.toAdd.card + G.toAdd.card = 0) :=
          fun h => hF (Nat.add_eq_zero_iff.mp h).1
        rw [if_neg hF, if_neg hG, if_neg h, mul_zero]

/-- The **counit** on `ConnesKreimer R T` as an algebra hom. -/
noncomputable def counit : ConnesKreimer R T →ₐ[R] R :=
  AddMonoidAlgebra.lift R R (Forest T) counitMonoidHom

/-- `counit (of' F) = if F.card = 0 then 1 else 0`. The `card`
    formulation avoids needing `DecidableEq T`. -/
@[simp] theorem counit_of' (F : Forest T) :
    (counit : ConnesKreimer R T →ₐ[R] R) (of' F)
      = (if F.card = 0 then 1 else 0 : R) := by
  show AddMonoidAlgebra.lift R R (Forest T) counitMonoidHom
        (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem counit_one :
    (counit : ConnesKreimer R T →ₐ[R] R) 1 = 1 := map_one _

@[simp] theorem counit_ofTree (t : T) :
    (counit : ConnesKreimer R T →ₐ[R] R) (ofTree t) = 0 := by
  unfold ofTree
  rw [counit_of', Multiset.card_singleton]
  exact if_neg (by decide)

end ConnesKreimer

end RootedTree
