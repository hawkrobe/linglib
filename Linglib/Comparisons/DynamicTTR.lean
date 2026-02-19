import Linglib.Theories.Semantics.Dynamic.Systems.CDRT.Basic
import Linglib.Theories.Semantics.TypeTheoretic.Quantification

/-!
# Dynamic Semantics ↔ TTR: Truth-Conditional Equivalence

CDRT (Dynamic/) and TTR (TypeTheoretic/) handle overlapping phenomena
— discourse referents, donkey anaphora, cross-sentential binding — with
no connection. This file proves they have the same truth conditions for
a core fragment, and identifies where they diverge.

## The correspondence

| Dynamic (CDRT)          | Type-Theoretic (TTR)     | Classical          |
|-------------------------|--------------------------|--------------------|
| `DProp.ofStatic p`      | `propT (p i)`            | `p i`              |
| `DProp.new n ;; test P` | `Σ (x : E), P x`        | `∃ x, P x`        |
| `DProp.impl (new;;P) Q` | `Π (x : E), P x → Q x`  | `∀ x, P x → Q x`  |

The first column is state-threading (assignments as side effects).
The second is type-dependency (witnesses as structure). Both reduce
to the same classical truth conditions (third column).

## The divergence

The systems agree on truth conditions but differ on **anaphoric
potential**. In CDRT, `¬¬(∃x.P(x))` has the same truth conditions as
`∃x.P(x)` but different discourse effects: the dref `x` is inaccessible
after double negation (negation resets the register). In TTR, anaphoric
potential is carried by type structure, not side effects.

## References

- Muskens, R. (1996). Combining Montague Semantics and Discourse
  Representation. Linguistics and Philosophy 19: 143–186.
- Cooper, R. (2023). From Perception to Communication. OUP. Ch 7–8.
- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
  Linguistics and Philosophy 14: 39–100.
- Sutton, P. (2024). Types and Type Theories. Annual Review of
  Linguistics 10: 347–370.
-/

namespace Comparisons.DynamicTTR

open Semantics.Dynamic.CDRT (DProp Register SProp)
open Semantics.TypeTheoretic (Ppty PPpty Parametric IsTrue IsFalse
  propT purify purifyUniv)

variable {E : Type}

-- ════════════════════════════════════════════════════════════════
-- § 1. Existential Discourse Referents ↔ Σ-types
-- ════════════════════════════════════════════════════════════════

/-! CDRT introduces a dref with `DProp.new n`, then tests a property
on `r(n)`. The truth condition is `∃ x, P x`.

TTR represents the same thing as a Σ-type: `(x : E) × P x`, which
is inhabited iff `∃ x, P x`. This is `purify` applied to a parametric
property with background `E`. -/

/-- CDRT existential: introduce dref n, test P on r(n). -/
def cdrt_exists (n : Nat) (P : E → Prop) : DProp E :=
  DProp.new n ;; DProp.ofStatic (λ r => P (r n))

/-- TTR existential: Σ-type with entity witness.
This is `purify ⟨E, λ e _ => propT (P e)⟩ a` for any `a`,
but since the result doesn't depend on `a`, we state it directly. -/
def ttr_exists (P : E → Prop) : Type := (x : E) × propT (P x)

/-- **Equivalence 1**: CDRT dref introduction and TTR Σ-type have
the same truth conditions. Both reduce to `∃ x, P x`. -/
theorem exists_equiv (n : Nat) (P : E → Prop) (i : Register E) :
    DProp.true_at (cdrt_exists n P) i ↔ Nonempty (ttr_exists P) := by
  simp only [DProp.true_at, cdrt_exists, DProp.seq, DProp.new, DProp.ofStatic, ttr_exists]
  constructor
  · rintro ⟨o, k, ⟨e, rfl⟩, rfl, hp⟩
    exact ⟨⟨e, PLift.up (by simpa using hp)⟩⟩
  · rintro ⟨⟨x, ⟨hx⟩⟩⟩
    exact ⟨_, _, ⟨x, rfl⟩, rfl, by simpa⟩

/-- Both reduce to classical ∃. -/
theorem exists_classical (P : E → Prop) :
    Nonempty (ttr_exists P) ↔ ∃ x : E, P x :=
  ⟨λ ⟨⟨x, ⟨hx⟩⟩⟩ => ⟨x, hx⟩, λ ⟨x, hx⟩ => ⟨⟨x, PLift.up hx⟩⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § 2. Donkey Implication ↔ Π-types
-- ════════════════════════════════════════════════════════════════

/-! CDRT handles donkey anaphora via `DProp.impl`: the antecedent
introduces a dref, and the consequent refers back to it. The universal
force ("every farmer...every donkey") comes from `impl`'s ∀ over
output registers.

TTR handles the same thing via universal purification (`purifyUniv`):
a Π-type that universally quantifies over all background witnesses.
Both reduce to `∀ x, P x → Q x`. -/

/-- CDRT donkey: `impl(new n ;; test P, test Q)`.
"For every way of extending the register with a P-entity at n,
Q holds of that entity." -/
def cdrt_donkey (n : Nat) (P Q : E → Prop) : DProp E :=
  DProp.impl
    (DProp.new n ;; DProp.ofStatic (λ r => P (r n)))
    (DProp.ofStatic (λ r => Q (r n)))

/-- TTR donkey: Π-type over witnesses.
"For every P-witness, Q holds." This is `purifyUniv` on the
parametric property with background `{x : E // P x}`. -/
def ttr_donkey (P Q : E → Prop) : Type :=
  (x : E) → P x → propT (Q x)

/-- **Equivalence 2**: CDRT donkey implication and TTR Π-type have
the same truth conditions. Both reduce to `∀ x, P x → Q x`. -/
theorem donkey_equiv (n : Nat) (P Q : E → Prop) (i : Register E) :
    DProp.true_at (cdrt_donkey n P Q) i ↔ Nonempty (ttr_donkey P Q) := by
  simp only [DProp.true_at, cdrt_donkey, DProp.impl, DProp.seq, DProp.new,
    DProp.ofStatic, ttr_donkey]
  constructor
  · rintro ⟨o, rfl, hall⟩
    refine ⟨λ x hpx => PLift.up ?_⟩
    have := hall (λ m => if m = n then x else i m) ⟨_, ⟨x, rfl⟩, rfl, by simpa⟩
    obtain ⟨m, rfl, hq⟩ := this
    simpa using hq
  · rintro ⟨f⟩
    refine ⟨i, rfl, λ k ⟨j, ⟨e, hj⟩, hjk, hp⟩ => ?_⟩
    subst hj; subst hjk
    simp at hp
    have ⟨hq⟩ := f e hp
    exact ⟨_, rfl, by simpa⟩

/-- Both reduce to classical ∀→. -/
theorem donkey_classical (P Q : E → Prop) :
    Nonempty (ttr_donkey P Q) ↔ ∀ x : E, P x → Q x :=
  ⟨λ ⟨f⟩ x hx => (f x hx).down, λ h => ⟨λ x hx => PLift.up (h x hx)⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § 3. Two-Variable Donkey Sentence
-- ════════════════════════════════════════════════════════════════

/-! "Every farmer who owns a donkey beats it."

CDRT: impl(new 0 ;; farmer(r0) ;; new 1 ;; donkey(r1) ;; owns(r0,r1),
           beats(r0, r1))

TTR: ∀ x, farmer x → ∀ y, donkey y → owns x y → beats x y
     (= purifyUniv on a two-layer parametric property) -/

def cdrt_full_donkey (farmer donkey_ : E → Prop) (owns beats : E → E → Prop) :
    DProp E :=
  DProp.impl
    (DProp.new 0 ;; DProp.ofStatic (λ r => farmer (r 0)) ;;
     DProp.new 1 ;; DProp.ofStatic (λ r => donkey_ (r 1) ∧ owns (r 0) (r 1)))
    (DProp.ofStatic (λ r => beats (r 0) (r 1)))

def ttr_full_donkey (farmer donkey_ : E → Prop) (owns beats : E → E → Prop) :
    Type :=
  (x : E) → farmer x → (y : E) → donkey_ y → owns x y → propT (beats x y)

-- Helper: the donkey antecedent chain reduces to ∃ x y with properties
private theorem donkey_antecedent_iff
    (farmer donkey_ : E → Prop) (owns : E → E → Prop) (i k : Register E) :
    (DProp.new 0 ;; DProp.ofStatic (λ r => farmer (r 0)) ;;
     DProp.new 1 ;; DProp.ofStatic (λ r => donkey_ (r 1) ∧ owns (r 0) (r 1))) i k ↔
    ∃ x y, k = (λ m => if m = 1 then y else if m = 0 then x else i m) ∧
      farmer x ∧ donkey_ y ∧ owns x y := by
  simp only [DProp.seq, DProp.new, DProp.ofStatic]
  constructor
  · rintro ⟨k₃, ⟨k₂, ⟨k₁, ⟨e₀, rfl⟩, rfl, hf⟩, ⟨e₁, rfl⟩⟩, rfl, hd, ho⟩
    exact ⟨e₀, e₁, rfl, by simpa, by simpa, by simpa⟩
  · rintro ⟨x, y, rfl, hf, hd, ho⟩
    exact ⟨_, ⟨_, ⟨_, ⟨x, rfl⟩, rfl, by simpa⟩, ⟨y, rfl⟩⟩, rfl,
      by simpa, by simp [show (0 : ℕ) ≠ 1 from by omega]; exact ho⟩

/-- **Equivalence 3**: The full donkey sentence has the same truth
conditions in CDRT and TTR. -/
theorem full_donkey_equiv
    (farmer donkey_ : E → Prop) (owns beats : E → E → Prop)
    (i : Register E) :
    DProp.true_at (cdrt_full_donkey farmer donkey_ owns beats) i ↔
    Nonempty (ttr_full_donkey farmer donkey_ owns beats) := by
  simp only [cdrt_full_donkey]
  rw [DProp.impl_true_at]
  constructor
  · intro hall
    refine ⟨λ x hf y hd ho => PLift.up ?_⟩
    let k := λ m => if m = 1 then y else if m = 0 then x else i m
    have hk := (donkey_antecedent_iff farmer donkey_ owns i k).mpr ⟨x, y, rfl, hf, hd, ho⟩
    have := hall k hk
    rw [DProp.ofStatic_true_at] at this
    exact this
  · rintro ⟨f⟩
    intro k hk
    rw [donkey_antecedent_iff] at hk
    obtain ⟨x, y, rfl, hf, hd, ho⟩ := hk
    rw [DProp.ofStatic_true_at]
    simp [show (0 : ℕ) ≠ 1 from by omega]
    exact (f x hf y hd ho).down

-- ════════════════════════════════════════════════════════════════
-- § 4. Connection to purify / purifyUniv
-- ════════════════════════════════════════════════════════════════

/-! The TTR existential and donkey types are instances of `purify`
and `purifyUniv` from Quantification.lean. This makes the bridge
connect to the existing TTR infrastructure, not just raw Σ/Π. -/

/-- The parametric property whose purification is `ttr_exists P`.
Background: the entity domain. Foreground: test P at the witness. -/
def ttr_exists_as_pppty (P : E → Prop) : PPpty E :=
  ⟨E, λ x _ => propT (P x)⟩

/-- `purify` of the existential parametric property is definitionally
`ttr_exists`. -/
theorem purify_exists_eq (P : E → Prop) (a : E) :
    purify (ttr_exists_as_pppty P) a = ttr_exists P := rfl

/-- The parametric property whose universal purification is `ttr_donkey`.
Background: P-witnesses. Foreground: test Q at the witness. -/
def ttr_donkey_as_pppty (P Q : E → Prop) : PPpty E :=
  ⟨{x : E // P x}, λ ⟨x, _⟩ _ => propT (Q x)⟩

/-- purifyUniv of the donkey parametric property is inhabited iff
the donkey universal holds. -/
theorem purifyUniv_donkey_iff (P Q : E → Prop) (a : E) :
    Nonempty (purifyUniv (ttr_donkey_as_pppty P Q) a) ↔
    ∀ x : E, P x → Q x :=
  ⟨λ ⟨f⟩ x hx => (f ⟨x, hx⟩).down,
   λ h => ⟨λ ⟨x, hx⟩ => PLift.up (h x hx)⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § 5. Divergence: Anaphoric Potential
-- ════════════════════════════════════════════════════════════════

/-! The systems agree on truth conditions but differ on discourse
effect. CDRT tracks anaphoric potential via the **output register**:
after processing φ, the output register determines what drefs are
available for subsequent sentences.

- `new n ;; test P` outputs a register with `n` bound → dref available
- `neg (new n ;; test P)` outputs `i` unchanged → dref lost

TTR tracks anaphoric potential via **type structure**: the Σ-type
`(x : E) × P x` makes `x` available as a projection, regardless of
how many negations wrap it.

This is the fundamental architectural difference: CDRT uses *state*
for binding; TTR uses *structure*. -/

/-- In CDRT, negation destroys anaphoric potential.
After `¬φ`, the output register is unchanged from input —
any drefs introduced by φ are inaccessible. This is a general
property of `DProp.neg`, not specific to any particular φ. -/
theorem neg_destroys_dref {φ : DProp E} (i o : Register E)
    (h : DProp.neg φ i o) : o = i :=
  DProp.neg_output h

/-- Double negation preserves truth but not drefs.
`¬¬(∃x.P(x))` has the same truth conditions as `∃x.P(x)`,
but the output register is the *input* register (no binding). -/
theorem dne_same_truth (n : Nat) (P : E → Prop) (i : Register E) :
    DProp.true_at (DProp.neg (DProp.neg (cdrt_exists n P))) i ↔
    DProp.true_at (cdrt_exists n P) i := by
  simp only [DProp.true_at, DProp.neg]
  constructor
  · rintro ⟨_, rfl, h⟩
    exact Classical.byContradiction (λ hno => h ⟨i, rfl, hno⟩)
  · rintro h
    exact ⟨i, rfl, λ ⟨_, rfl, hno⟩ => hno h⟩

/-- In TTR, there is no analogous destruction. The Σ-type `(x : E) × P x`
carries its witness structurally. The projection `Sigma.fst` is always
available, regardless of logical context. -/
theorem ttr_witness_survives (P : E → Prop) (w : ttr_exists P) :
    ∃ x : E, P x :=
  ⟨w.1, w.2.down⟩

-- ════════════════════════════════════════════════════════════════
-- § 6. Concrete Verification
-- ════════════════════════════════════════════════════════════════

section ConcreteModel

inductive Ent where | john | bill | fido deriving DecidableEq

private def farmerP : Ent → Prop
  | .john => True | .bill => True | .fido => False

private def donkeyP : Ent → Prop
  | .fido => True | _ => False

private def ownsP : Ent → Ent → Prop
  | .john, .fido => True | _, _ => False

private def beatsP : Ent → Ent → Prop
  | .john, .fido => True | _, _ => False

private def initReg : Register Ent := λ _ => .john

/-- CDRT donkey sentence is true on this model. -/
theorem cdrt_donkey_concrete :
    DProp.true_at (cdrt_full_donkey farmerP donkeyP ownsP beatsP) initReg := by
  rw [full_donkey_equiv]
  exact ⟨λ x hf y hd ho => PLift.up (by
    cases x <;> cases y <;> simp_all [farmerP, donkeyP, ownsP, beatsP])⟩

/-- TTR donkey sentence is true on this model. -/
theorem ttr_donkey_concrete : Nonempty (ttr_full_donkey farmerP donkeyP ownsP beatsP) :=
  ⟨λ x hf y hd ho => PLift.up (by
    cases x <;> cases y <;> simp_all [farmerP, donkeyP, ownsP, beatsP])⟩

/-- The two concrete results agree (by the equivalence theorem). -/
theorem concrete_agreement :
    DProp.true_at (cdrt_full_donkey farmerP donkeyP ownsP beatsP) initReg ↔
    Nonempty (ttr_full_donkey farmerP donkeyP ownsP beatsP) :=
  full_donkey_equiv farmerP donkeyP ownsP beatsP initReg

end ConcreteModel

end Comparisons.DynamicTTR
