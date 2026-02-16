/-
# Kaplan's LD Formal System

The model-theoretic semantics from Kaplan (1989) "Demonstratives" §XVIII-XIX:
the formal logic LD (Logic of Demonstratives) with its operators, dthat,
and metatheorems.

## Key Results

- `LDStructure`: Full LD model with proper-context constraint
- `dthat`/`dthatW`: Rigidifier operator (§XII)
- `dthat_isRigid`: dthat[α] has Stable Content
- `alpha_eq_dthat_alpha`: α = dthat[α] is valid (Remark 3)
- `box_alpha_eq_dthat_not_valid`: □(α = dthat[α]) fails
- `opNow`, `opActually`: Content operators (indexical, §VI)
- `opFuture`, `opPast`: Tense operators (circumstance, §XVIII)
- `opBox`, `opDiamond`: Modal operators
- `exist_i_valid`: ⊨ Exist I (from proper-context constraint)
- `actually_stable`: A(φ) has Stable Content (world-independent)

## References

- Kaplan, D. (1989). Demonstratives. In Almog, Perry & Wettstein (eds.),
  Themes from Kaplan. Oxford University Press, §VIII-XIX.
-/

import Linglib.Core.Context
import Linglib.Core.Intension
import Linglib.Theories.Semantics.Reference.Basic

namespace IntensionalSemantics.Reference.KaplanLD

open Core.Intension (Intension rigid IsRigid rigid_isRigid StableCharacter)
open Core.Context (KContext ProperContext LocatedContext)
open IntensionalSemantics.Reference.Basic (Context Character Content)

/-! ## LD Structure -/

/-- Full LD model structure (Kaplan 1989 §XVIII).

An LD structure provides the domains (worlds, entities, positions, times),
context parameters (agent, world, time, position projections), and the
proper-context constraint. -/
structure LDStructure where
  /-- Possible worlds -/
  W : Type
  /-- Universe of individuals -/
  U : Type
  /-- Positions (locations) -/
  P : Type
  /-- Times -/
  T : Type
  /-- Set of contexts (a subset of W × U × P × T) -/
  C : Type
  /-- Agent of a context -/
  cAgent : C → U
  /-- Addressee of a context (Speas & Tenny 2003 extension) -/
  cAddressee : C → U
  /-- World of a context -/
  cWorld : C → W
  /-- Time of a context -/
  cTime : C → T
  /-- Position of a context -/
  cPosition : C → P
  /-- Existence predicate: entity exists at world -/
  exists_ : U → W → Prop
  /-- Location predicate: entity is at position at time in world -/
  located : U → P → T → W → Prop
  /-- Proper-context constraint (Kaplan §XVIII):
      the agent of every context exists at the world of that context.
      This validates ⊨ Exist I. -/
  proper : ∀ c : C, exists_ (cAgent c) (cWorld c)

/-- Extract a `KContext` from an LD structure at a context index. -/
def LDStructure.toKContext (ld : LDStructure) (c : ld.C) :
    KContext ld.W ld.U ld.P ld.T :=
  ⟨ld.cAgent c, ld.cAddressee c, ld.cWorld c, ld.cTime c, ld.cPosition c⟩

/-! ## Dthat Operator (§XII) -/

/-- `dthat α cW cT` — Kaplan's rigidifier: evaluate α at the context
parameters (world cW, time cT), then rigidify the result.

dthat[α] is an expression whose content at context c is the rigid intension
constantly returning α's extension at ⟨c_w, c_t⟩. -/
def dthat {W T τ : Type*} (α : W → T → τ) (cW : W) (cT : T) : Intension W τ :=
  rigid (α cW cT)

/-- Simplified world-only dthat (when T is not relevant). -/
def dthatW {W τ : Type*} (α : Intension W τ) (cW : W) : Intension W τ :=
  rigid (α cW)

/-- dthat[α] has Stable Content: it is rigid. -/
theorem dthat_isRigid {W T τ : Type*} (α : W → T → τ) (cW : W) (cT : T) :
    IsRigid (dthat α cW cT) :=
  rigid_isRigid (α cW cT)

/-- dthatW[α] is rigid. -/
theorem dthatW_isRigid {W τ : Type*} (α : Intension W τ) (cW : W) :
    IsRigid (dthatW α cW) :=
  rigid_isRigid (α cW)

/-- Remark 3: α = dthat[α] is valid — at the context world, α and
dthat[α] agree.

For any α and world w, `α w = dthatW α w w`. -/
theorem alpha_eq_dthat_alpha {W τ : Type*} (α : Intension W τ) (w : W) :
    α w = dthatW α w w := rfl

/-- □(α = dthat[α]) is NOT valid in general: dthat[α] is rigid but α
may not be. If α varies across worlds, there exists a world w' where
α w' ≠ dthatW α cW w'.

We state this as: given α that varies, the universal closure fails. -/
theorem box_alpha_eq_dthat_not_valid {W τ : Type*}
    (α : Intension W τ) (cW w' : W) (h : α w' ≠ α cW) :
    α w' ≠ dthatW α cW w' := by
  simp only [dthatW, rigid]
  exact h

/-! ## Indexical Operators (Content Operators, §VI) -/

/-- N ("now"): shift evaluation time to context time.

opNow cT φ evaluates φ at the context time cT instead of the
circumstance time. This is a content operator — it operates on the
circumstance of evaluation. -/
def opNow {W T : Type*} (cT : T) (φ : W → T → Prop) : W → T → Prop :=
  λ w _ => φ w cT

/-- A ("actually"): shift evaluation world to context world.

opActually cW φ evaluates φ at the context world cW instead of the
circumstance world. -/
def opActually {W T : Type*} (cW : W) (φ : W → T → Prop) : W → T → Prop :=
  λ _ t => φ cW t

/-- Y ("yesterday"): shift evaluation time to cT - 1 (requires HSub). -/
def opYesterday {W T : Type*} [HSub T Nat T] (cT : T) (φ : W → T → Prop) : W → T → Prop :=
  λ w _ => φ w (cT - 1)

/-! ## Tense Operators (Circumstance Operators) -/

/-- F (future): ∃t' in `times` with t' > t such that φ at ⟨w, t'⟩. -/
def opFuture {W T : Type*} [LT T] (times : List T) (φ : W → T → Prop) : W → T → Prop :=
  λ w t => ∃ t' ∈ times, t < t' ∧ φ w t'

/-- P (past): ∃t' in `times` with t' < t such that φ at ⟨w, t'⟩. -/
def opPast {W T : Type*} [LT T] (times : List T) (φ : W → T → Prop) : W → T → Prop :=
  λ w t => ∃ t' ∈ times, t' < t ∧ φ w t'

/-! ## Modal Operators -/

/-- □ (box): ∀w' in `worlds`, φ at ⟨w', t⟩. -/
def opBox {W T : Type*} (worlds : List W) (φ : W → T → Prop) : W → T → Prop :=
  λ _ t => ∀ w' ∈ worlds, φ w' t

/-- ◇ (diamond): ∃w' in `worlds`, φ at ⟨w', t⟩. -/
def opDiamond {W T : Type*} (worlds : List W) (φ : W → T → Prop) : W → T → Prop :=
  λ _ t => ∃ w' ∈ worlds, φ w' t

/-! ## Key Metatheorems -/

/-- ⊨ Exist I: at every (proper) context, the agent exists.

Follows directly from `LDStructure.proper`. Kaplan (1989) §XVIII Remark 3. -/
theorem exist_i_valid (ld : LDStructure) (c : ld.C) :
    ld.exists_ (ld.cAgent c) (ld.cWorld c) :=
  ld.proper c

/-- ⊨ N(Located(I, Here)): the agent is located at the context's position
at the context's time in the context's world.

Requires a `locatedProper` hypothesis: an LD structure where contexts
satisfy the location constraint. -/
theorem i_am_located_valid (ld : LDStructure)
    (locatedProper : ∀ c : ld.C,
      ld.located (ld.cAgent c) (ld.cPosition c) (ld.cTime c) (ld.cWorld c))
    (c : ld.C) :
    ld.located (ld.cAgent c) (ld.cPosition c) (ld.cTime c) (ld.cWorld c) :=
  locatedProper c

/-- A(φ) produces Stable Content: the result is world-independent.

`opActually cW φ` evaluates φ at cW regardless of the evaluation world,
so changing the evaluation world has no effect. -/
theorem actually_stable {W T : Type*} (cW : W) (φ : W → T → Prop) (t : T) :
    ∀ w₁ w₂ : W, opActually cW φ w₁ t = opActually cW φ w₂ t :=
  λ _ _ => rfl

end IntensionalSemantics.Reference.KaplanLD
