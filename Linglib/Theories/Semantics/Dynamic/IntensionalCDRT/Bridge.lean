import Linglib.Theories.Semantics.Dynamic.IntensionalCDRT.Operators
import Linglib.Theories.Semantics.Dynamic.Core.CCP

/-!
# ICDRT ↔ Dynamic Algebra Bridge

@cite{hofmann-2025} @cite{muskens-1996} @cite{groenendijk-stokhof-1991}

This module establishes the precise mathematical connection between
ICDRT's static relation semantics and the abstract dynamic algebra
of `DRS`/`CCP` in `Core.DynProp`/`Core.CCP`.

## Type identifications

| ICDRT type | Abstract type | Identity |
|------------|---------------|----------|
| `ICDRTUpdate W E` | `DRS (ICDRTAssignment W E)` | definitional |
| `ICDRTUpdate.seq` | `dseq` | definitional |
| `ICDRTUpdate.idUp` | identity relation | definitional |
| `DynProp W E` | `CCP (ICDRTAssignment W E × W)` | definitional |

## Key results

1. **Fiberwise lift**: `toDynProp D = lift (fiberDRS D)` where `fiberDRS`
   embeds an assignment relation into a pair relation holding worlds fixed.
   This is the mathematical content of ICDRT's static-to-dynamic bridge:
   updates operate on assignments only, with worlds as passive fibers.

2. **`fiberDRS` is a monoid homomorphism**: `fiberDRS` preserves sequential
   composition (`fiberDRS_seq`) and identity (`fiberDRS_idUp`). Combined
   with `lift_dseq` from CCP.lean, this gives the algebraic derivation
   of `seq_toDynProp` from Operators.lean.

3. **Distributivity**: `toDynProp D` is always distributive (`IsDistributive`)
   — it processes each assignment-world pair independently. This is a
   corollary of `lift_isDistributive`, since `toDynProp = lift ∘ fiberDRS`.

4. **ICDRT negation stays distributive**: unlike CCP's test-based `neg`
   (which tests the *whole* input state and is NOT distributive), ICDRT's
   negation via propositional dref complementation is an ordinary update
   relation. Its `toDynProp` image is distributive. This is the algebraic
   content of @cite{hofmann-2025}'s insight that negation in ICDRT is
   static complementation, not dynamic state inspection.

## Architecture

```
ICDRTUpdate W E ──fiberDRS──→ DRS (ICDRTAssignment W E × W) ──lift──→ CCP (... × W)
       ‖                              ‖                                    ‖
   DRS (Assign)              DRS (Assign × World)                 DynProp W E
       │                              │                                    │
    seq = dseq              dseq (fiber level)                    CCP.seq
```

The factorization `toDynProp = lift ∘ fiberDRS` separates two concerns:
- `fiberDRS`: embed assignment-only relations into pair relations (passive worlds)
- `lift`: convert relational meanings to set-transformer meanings
-/

namespace Semantics.Dynamic.IntensionalCDRT

open Core
open Core.DynProp


-- ════════════════════════════════════════════════════════════════
-- § 1. Type Identifications
-- ════════════════════════════════════════════════════════════════

variable {W E : Type*}

/-- `ICDRTUpdate W E` IS `DRS (ICDRTAssignment W E)`.
Both are `S → S → Prop` for `S = ICDRTAssignment W E`. -/
theorem icdrtUpdate_eq_drs :
    ICDRTUpdate W E = DRS (ICDRTAssignment W E) := rfl

/-- `DynProp W E` IS `CCP (ICDRTAssignment W E × W)`.
Both are `Set P → Set P` for `P = ICDRTAssignment W E × W`. -/
theorem dynProp_eq_ccp :
    DynProp W E = CCP (ICDRTAssignment W E × W) := rfl


-- ════════════════════════════════════════════════════════════════
-- § 2. Operation Correspondences
-- ════════════════════════════════════════════════════════════════

/-- ICDRT sequential composition IS relational composition (`dseq`).
Both are `λ i j => ∃ k, D₁ i k ∧ D₂ k j`. -/
theorem seq_eq_dseq (D₁ D₂ : ICDRTUpdate W E) :
    ICDRTUpdate.seq D₁ D₂ = dseq D₁ D₂ := rfl

/-- ICDRT identity update IS the identity relation. -/
theorem idUp_eq_id :
    (ICDRTUpdate.idUp : ICDRTUpdate W E) = λ i j => i = j := rfl


-- ════════════════════════════════════════════════════════════════
-- § 3. Fiberwise Lift
-- ════════════════════════════════════════════════════════════════

/--
Embed an assignment-only relation into a pair relation with passive worlds.

`fiberDRS D (i, w) (j, w') ↔ w = w' ∧ D i j`

This is the key mathematical construction: ICDRT updates operate on
assignments only, and worlds are inert fibers. `fiberDRS` makes this
structure explicit at the type level of `DRS (ICDRTAssignment W E × W)`.
-/
def fiberDRS (D : ICDRTUpdate W E) : DRS (ICDRTAssignment W E × W) :=
  λ ⟨i, w⟩ ⟨j, w'⟩ => w = w' ∧ D i j

/-- `toDynProp = lift ∘ fiberDRS`: the static-to-dynamic bridge factors
through fiberwise embedding followed by relational image. -/
theorem toDynProp_eq_lift_fiberDRS (D : ICDRTUpdate W E) :
    D.toDynProp = lift (fiberDRS D) := by
  funext σ
  apply Set.ext; intro ⟨j, w⟩
  simp only [ICDRTUpdate.toDynProp, lift, fiberDRS, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hic, hD⟩
    exact ⟨⟨i, w⟩, hic, rfl, hD⟩
  · rintro ⟨⟨i, _⟩, hiw, rfl, hD⟩
    exact ⟨i, hiw, hD⟩

/-- `fiberDRS` preserves sequential composition:
`fiberDRS (D₁ ; D₂) = fiberDRS D₁ ⨟ fiberDRS D₂`. -/
theorem fiberDRS_seq (D₁ D₂ : ICDRTUpdate W E) :
    fiberDRS (ICDRTUpdate.seq D₁ D₂) = dseq (fiberDRS D₁) (fiberDRS D₂) := by
  funext p q; cases p; cases q
  simp only [fiberDRS, ICDRTUpdate.seq, dseq, eq_iff_iff]
  constructor
  · rintro ⟨rfl, k, h1, h2⟩
    exact ⟨⟨k, _⟩, ⟨rfl, h1⟩, ⟨rfl, h2⟩⟩
  · rintro ⟨⟨k, _⟩, ⟨rfl, h1⟩, ⟨rfl, h2⟩⟩
    exact ⟨rfl, k, h1, h2⟩

/-- `fiberDRS` preserves identity: the fiberwise embedding of the identity
relation is the identity relation on pairs. -/
theorem fiberDRS_idUp :
    fiberDRS (ICDRTUpdate.idUp : ICDRTUpdate W E) = λ p q => p = q := by
  funext p q; cases p; cases q
  simp only [fiberDRS, ICDRTUpdate.idUp, eq_iff_iff, Prod.mk.injEq]
  exact ⟨λ ⟨h1, h2⟩ => ⟨h2, h1⟩, λ ⟨h1, h2⟩ => ⟨h2, h1⟩⟩


-- ════════════════════════════════════════════════════════════════
-- § 4. Distributivity
-- ════════════════════════════════════════════════════════════════

/-- `toDynProp D` is always distributive: it processes each
assignment-world pair independently.

This is a corollary of `lift_isDistributive`, since
`toDynProp D = lift (fiberDRS D)`. -/
theorem toDynProp_isDistributive (D : ICDRTUpdate W E) :
    IsDistributive (D.toDynProp) := by
  rw [toDynProp_eq_lift_fiberDRS]
  exact lift_isDistributive (fiberDRS D)

/-- ICDRT negation via complementation stays distributive.

Unlike `CCP.neg` (which tests the *whole* context and is NOT
distributive — cf. `might_not_isDistributive`), ICDRT's negation
operates through propositional dref complementation. Since this is
an ordinary update relation, its `toDynProp` image is distributive.

This is the algebraic content of @cite{hofmann-2025}'s key insight:
negation in ICDRT is static complementation over propositional drefs,
not dynamic whole-state inspection. -/
theorem notCondition_update_distributive
    (φ_outer φ_inner : PVar) :
    IsDistributive (ICDRTUpdate.toDynProp
      (λ i j : ICDRTAssignment W E =>
        i = j ∧ notCondition φ_outer φ_inner j)) := by
  apply toDynProp_isDistributive


-- ════════════════════════════════════════════════════════════════
-- § 5. Monoid Homomorphism
-- ════════════════════════════════════════════════════════════════

/-- `toDynProp` preserves sequential composition — algebraic derivation.

This reproves `seq_toDynProp` (from Operators.lean) by factoring through
the fiberwise lift: `toDynProp ∘ seq = CCP.seq ∘ (toDynProp × toDynProp)`
follows from `fiberDRS_seq` + `lift_dseq`. -/
theorem toDynProp_seq_algebraic (D₁ D₂ : ICDRTUpdate W E) (c : IContext W E) :
    (ICDRTUpdate.seq D₁ D₂).toDynProp c = CCP.seq D₁.toDynProp D₂.toDynProp c := by
  conv_lhs => rw [toDynProp_eq_lift_fiberDRS, fiberDRS_seq, lift_dseq]
  conv_rhs => rw [toDynProp_eq_lift_fiberDRS D₁, toDynProp_eq_lift_fiberDRS D₂]

/-- `toDynProp` preserves identity — algebraic derivation.

The identity update lifts to the identity CCP. This reproves
`idUp_toDynProp` (from Operators.lean) via `fiberDRS_idUp`. -/
theorem toDynProp_id_algebraic (c : IContext W E) :
    ICDRTUpdate.idUp.toDynProp c = CCP.id c := by
  rw [toDynProp_eq_lift_fiberDRS, fiberDRS_idUp]
  apply Set.ext; intro ⟨j, w⟩
  simp only [lift, CCP.id, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro hjw; exact ⟨⟨j, w⟩, hjw, rfl⟩

/-- `fiberDRS` is a monoid homomorphism from `(ICDRTUpdate, seq, idUp)` to
`(DRS, dseq, id)` — collected statement. The two components are
`fiberDRS_seq` (multiplication) and `fiberDRS_idUp` (unit). Combined
with `lift_dseq` and `lift_isDistributive`, this yields all properties
of `toDynProp` as corollaries. -/
theorem fiberDRS_homomorphism :
    (∀ (D₁ D₂ : ICDRTUpdate W E),
      fiberDRS (ICDRTUpdate.seq D₁ D₂) = dseq (fiberDRS D₁) (fiberDRS D₂)) ∧
    fiberDRS (ICDRTUpdate.idUp : ICDRTUpdate W E) = λ p q => p = q :=
  ⟨fiberDRS_seq, fiberDRS_idUp⟩


-- ════════════════════════════════════════════════════════════════
-- § 6. Test Updates and Eliminativity
-- ════════════════════════════════════════════════════════════════

/-- A test update — one that preserves the assignment — lifts to an
eliminative CCP: it can only shrink the context, never grow it. -/
theorem toDynProp_test_eliminative (C : ICDRTAssignment W E → Prop) :
    IsEliminative (ICDRTUpdate.toDynProp (λ i j => i = j ∧ C j)) := by
  intro σ ⟨j, w⟩ hjw
  obtain ⟨i, hiw, rfl, _⟩ := hjw
  exact hiw

/-- The DEC condition lifts to an eliminative CCP: asserting narrows
the context (removes worlds from the commitment set). -/
theorem toDynProp_dec_eliminative (φ_DC φ : PVar) :
    IsEliminative (ICDRTUpdate.toDynProp
      (λ i j : ICDRTAssignment W E => i = j ∧ decCondition φ_DC φ j)) :=
  toDynProp_test_eliminative _


-- ════════════════════════════════════════════════════════════════
-- § 7. Round-Trip via Lower
-- ════════════════════════════════════════════════════════════════

/-- Round-trip: `lower (toDynProp D) = fiberDRS D`.

Lowering the CCP back to a relation recovers the fiberwise embedding.
Combined with `lower_lift`, this shows no information is lost in
the `fiberDRS`/`lift` factorization. -/
theorem lower_toDynProp (D : ICDRTUpdate W E) :
    lower (D.toDynProp) = fiberDRS D := by
  rw [toDynProp_eq_lift_fiberDRS, lower_lift]


-- ════════════════════════════════════════════════════════════════
-- § 8. End-to-End: CCP Composition for Negated Existentials
-- ════════════════════════════════════════════════════════════════

/-! ### Negated existential via CCP composition

"There's no bathroom" is processed as a sequence of three ICDRT updates:
1. Existential introduction (random assignment for v in local context φ_inner)
2. NOT condition (φ_outer = complement of φ_inner)
3. DEC condition (DC ⊆ φ_outer)

Each update is a `DRS (ICDRTAssignment W E)`. The full sentence meaning
is their `dseq` composition. By `fiberDRS_seq` + `lift_dseq`, the
`toDynProp` of the full composition equals the CCP sequential composition
of the individual `toDynProp` images — each distributive.

The algebraic chain:

```
toDynProp (D_exist ; D_not ; D_dec)
  = toDynProp D_exist ;; toDynProp D_not ;; toDynProp D_dec    [seq_toDynProp]
  = lift (fiberDRS D_exist) ;; lift (fiberDRS D_not) ;; ...     [toDynProp_eq_lift_fiberDRS]
```

Each stage is distributive, the composition is CCP-sequential, and
the final result carries the counterfactuality condition
(`dec_complement_counterfactual` from Operators.lean).
-/

/-- The three-stage ICDRT update for a negated existential:
existential introduction + complementation + DEC assertion.
The full composition lifts to a CCP that is the sequential composition
of three distributive stages. -/
theorem negated_existential_ccp_composition
    (D_intro D_not D_dec : ICDRTUpdate W E) (c : IContext W E) :
    (ICDRTUpdate.seq (ICDRTUpdate.seq D_intro D_not) D_dec).toDynProp c =
    CCP.seq (CCP.seq D_intro.toDynProp D_not.toDynProp) D_dec.toDynProp c := by
  simp only [ICDRTUpdate.seq_toDynProp, CCP.seq]

/-- Each stage of the negated existential pipeline is distributive,
so the full composition is distributive. -/
theorem negated_existential_distributive
    (D_intro D_not D_dec : ICDRTUpdate W E) :
    IsDistributive
      (ICDRTUpdate.seq (ICDRTUpdate.seq D_intro D_not) D_dec).toDynProp :=
  toDynProp_isDistributive _


end Semantics.Dynamic.IntensionalCDRT
