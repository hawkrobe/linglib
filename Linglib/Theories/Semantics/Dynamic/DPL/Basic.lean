/-
# Dynamic Predicate Logic
@cite{groenendijk-stokhof-1991}

Stub for Dynamic Predicate Logic (DPL), the foundational dynamic semantic
theory that treats meanings as relations between assignments.

## Key Ideas

In DPL:
- Sentences denote relations between input and output assignments
- Existential quantification introduces new discourse referents
- Conjunction is relation composition (dynamic!)
- Negation is a test (doesn't change assignment)

## Semantic Type

⟦φ⟧ : Assignment → Assignment → Prop

(A sentence maps input assignment to output assignment)

## Key Properties

1. Scope extension: ∃x(φ ∧ ψ) ≡ (∃xφ) ∧ ψ if x not free in ψ
2. Anaphora: variables persist across conjunction
3. DNE failure: ¬¬φ ≠ φ for anaphora (negation is a test)

-/

import Linglib.Theories.Semantics.Dynamic.Core.Update

namespace Semantics.Dynamic.DPL

open Semantics.Dynamic.Core

-- Placeholder: Full implementation TODO

/--
DPL semantic type: relation between assignments.

⟦φ⟧(g, h) means: starting from assignment g, the formula φ can
update to assignment h.
-/
def DPLRel (E : Type*) := (Nat → E) → (Nat → E) → Prop

/--
Atomic predicate in DPL: tests without changing assignment.
-/
def DPLRel.atom {E : Type*} (p : (Nat → E) → Prop) : DPLRel E :=
  λ g h => g = h ∧ p g

/--
DPL conjunction: relation composition.

⟦φ ∧ ψ⟧(g, h) iff ∃k. ⟦φ⟧(g, k) ∧ ⟦ψ⟧(k, h)
-/
def DPLRel.conj {E : Type*} (φ ψ : DPLRel E) : DPLRel E :=
  λ g h => ∃ k, φ g k ∧ ψ k h

/--
DPL existential: random assignment then scope.

⟦∃x.φ⟧(g, h) iff ∃d. ⟦φ⟧(g[x↦d], h)
-/
def DPLRel.exists_ {E : Type*} (x : Nat) (φ : DPLRel E) : DPLRel E :=
  λ g h => ∃ d : E, φ (λ n => if n = x then d else g n) h

/--
DPL negation: test without changing assignment.

⟦¬φ⟧(g, h) iff g = h ∧ ¬∃k. ⟦φ⟧(g, k)

Note: this does not validate DNE.
-/
def DPLRel.neg {E : Type*} (φ : DPLRel E) : DPLRel E :=
  λ g h => g = h ∧ ¬∃ k, φ g k

-- Key Theorems (TODO: Prove)

/--
DPL does not validate DNE for anaphora.

¬¬∃x.φ is not equivalent to ∃x.φ because negation resets the output assignment:
`neg(neg(exists_ x φ)) g h` forces `g = h` (it's a test), while `exists_ x φ`
can change the assignment to export a witness.

Requires `Nontrivial E` (at least 2 elements): for `Unit`, all assignments are
identical and DNE holds vacuously.
-/
theorem dpl_dne_fails_anaphora {E : Type*} [Nontrivial E] :
    ∃ (x : Nat) (φ : DPLRel E),
      DPLRel.neg (DPLRel.neg (DPLRel.exists_ x φ)) ≠ DPLRel.exists_ x φ := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  refine ⟨0, λ g h => g = h, ?_⟩
  intro heq
  -- exists_ 0 (=) at (λ _ => e₁, λ n => if n=0 then e₂ else e₁) is true (d = e₂)
  -- neg(neg(exists_ 0 (=))) at same args requires g = h, which fails (e₁ ≠ e₂)
  have hrhs : (DPLRel.exists_ 0 (λ (g h : Nat → E) => g = h))
              (λ _ => e₁) (λ n => if n = 0 then e₂ else e₁) :=
    ⟨e₂, rfl⟩
  rw [← heq] at hrhs
  have h_eq := congr_fun hrhs.1 0
  simp at h_eq
  exact hne h_eq

/--
Scope extension theorem: ∃x(φ ∧ ψ) ≡ (∃xφ) ∧ ψ when x not free in ψ.

"Not free in ψ" means ψ is invariant under reassigning x in both input and output
assignments. Under this condition, the existential can scope out past conjunction.

TODO: Prove by extensionality and reordering existential quantifiers.
-/
theorem scope_extension {E : Type*} (x : Nat) (φ ψ : DPLRel E)
    (_hfree : ∀ (g h : Nat → E) (d : E),
      ψ g h ↔ ψ (λ n => if n = x then d else g n) (λ n => if n = x then d else h n)) :
    DPLRel.exists_ x (DPLRel.conj φ ψ) = DPLRel.conj (DPLRel.exists_ x φ) ψ := by
  funext g h
  simp only [DPLRel.exists_, DPLRel.conj, eq_iff_iff]
  constructor
  · rintro ⟨d, k, hφ, hψ⟩
    exact ⟨k, ⟨d, hφ⟩, hψ⟩
  · rintro ⟨k, ⟨d, hφ⟩, hψ⟩
    exact ⟨d, k, hφ, hψ⟩

-- ════════════════════════════════════════════════════════════════
-- § Definition 2: Remaining Connectives (clauses 5, 6, 8)
-- ════════════════════════════════════════════════════════════════

/--
DPL implication: internally dynamic, externally static.

⟦φ → ψ⟧(g, h) iff g = h and every output of φ from g can be
extended by ψ. Implication passes on bindings from its antecedent
to its consequent (internally dynamic), but the implication as a
whole is a test (externally static). This gives existential
quantifiers in the antecedent *universal* force — the key to
donkey sentences.
-/
def DPLRel.impl {E : Type*} (φ ψ : DPLRel E) : DPLRel E :=
  λ g h => g = h ∧ ∀ k, φ g k → ∃ j, ψ k j

/--
DPL disjunction: externally and internally static.

⟦φ ∨ ψ⟧(g, h) iff g = h and at least one disjunct can be
successfully processed from g. No anaphoric relations are
possible between or across disjuncts.
-/
def DPLRel.disj {E : Type*} (φ ψ : DPLRel E) : DPLRel E :=
  λ g h => g = h ∧ ∃ k, φ g k ∨ ψ g k

/--
DPL universal quantification: a test.

⟦∀x.φ⟧(g, h) iff g = h and for every value d at position x,
φ can be successfully processed. Like negation, implication,
and disjunction, the universal quantifier is externally static.
-/
def DPLRel.forall_ {E : Type*} (x : Nat) (φ : DPLRel E) : DPLRel E :=
  λ g h => g = h ∧ ∀ d : E, ∃ m, φ (λ n => if n = x then d else g n) m

/--
DPL closure (the ◇ operator, Definition 17).

⟦◇φ⟧(g, h) iff g = h and φ can be successfully processed from g.
Closure turns any formula into a test with the same truth conditions.
-/
def DPLRel.close {E : Type*} (φ : DPLRel E) : DPLRel E :=
  λ g h => g = h ∧ ∃ k, φ g k

-- ════════════════════════════════════════════════════════════════
-- § Semantic Notions (Definitions 3, 6, 9)
-- ════════════════════════════════════════════════════════════════

/-- Truth (Definition 3): φ is true w.r.t. g iff it has an output. -/
def DPLRel.trueAt {E : Type*} (φ : DPLRel E) (g : Nat → E) : Prop :=
  ∃ h, φ g h

/-- Satisfaction set (Definition 6): inputs from which φ succeeds. -/
def DPLRel.satisfactionSet {E : Type*} (φ : DPLRel E) : Set (Nat → E) :=
  { g | ∃ h, φ g h }

/-- Production set (Definition 9): possible outputs of φ. -/
def DPLRel.productionSet {E : Type*} (φ : DPLRel E) : Set (Nat → E) :=
  { h | ∃ g, φ g h }

-- ════════════════════════════════════════════════════════════════
-- § Interdefinability of Connectives (§3.4)
-- ════════════════════════════════════════════════════════════════

/-! The connectives `→`, `∨`, `∀x` are interdefinable from `¬`, `∧`, `∃x`.
This is the standard classical interdefinability — but crucially, the
*reverse* does not hold in DPL: `∧` and `∃x` cannot be defined from
`→`, `∨`, `∀x` because the latter are all externally static. -/

/-- `φ → ψ ≈ ¬(φ ∧ ¬ψ)` — implication from conjunction and negation. -/
theorem impl_interdefinable {E : Type*} (φ ψ : DPLRel E) :
    DPLRel.impl φ ψ = DPLRel.neg (DPLRel.conj φ (DPLRel.neg ψ)) := by
  funext g h
  simp only [DPLRel.impl, DPLRel.neg, DPLRel.conj, eq_iff_iff]
  constructor
  · rintro ⟨rfl, hall⟩
    refine ⟨rfl, fun ⟨k, m, hφ, hmk, hnψ⟩ => ?_⟩
    subst hmk; exact hnψ (hall m hφ)
  · rintro ⟨rfl, hneg⟩
    exact ⟨rfl, fun k hφ => by_contra fun hne => hneg ⟨k, k, hφ, rfl, hne⟩⟩

/-- `φ ∨ ψ ≈ ¬(¬φ ∧ ¬ψ)` — disjunction from conjunction and negation. -/
theorem disj_interdefinable {E : Type*} (φ ψ : DPLRel E) :
    DPLRel.disj φ ψ = DPLRel.neg (DPLRel.conj (DPLRel.neg φ) (DPLRel.neg ψ)) := by
  funext g h
  simp only [DPLRel.disj, DPLRel.neg, DPLRel.conj, eq_iff_iff]
  constructor
  · rintro ⟨rfl, k, hφψ⟩
    refine ⟨rfl, ?_⟩
    rintro ⟨_, m, ⟨rfl, hnφ⟩, rfl, hnψ⟩
    cases hφψ with
    | inl hφ => exact hnφ ⟨k, hφ⟩
    | inr hψ => exact hnψ ⟨k, hψ⟩
  · rintro ⟨rfl, hneg⟩
    refine ⟨rfl, by_contra fun hne => ?_⟩
    push_neg at hne
    exact hneg ⟨g, g, ⟨rfl, fun ⟨j, hφ⟩ => (hne j).1 hφ⟩,
      rfl, fun ⟨j, hψ⟩ => (hne j).2 hψ⟩

/-- `∀x.φ ≈ ¬∃x.¬φ` — universal from existential and negation. -/
theorem forall_interdefinable {E : Type*} (x : Nat) (φ : DPLRel E) :
    DPLRel.forall_ x φ = DPLRel.neg (DPLRel.exists_ x (DPLRel.neg φ)) := by
  funext g h
  simp only [DPLRel.forall_, DPLRel.neg, DPLRel.exists_, eq_iff_iff]
  constructor
  · rintro ⟨rfl, hall⟩
    refine ⟨rfl, ?_⟩
    rintro ⟨k, d, rfl, hneg⟩
    exact hneg (hall d)
  · rintro ⟨rfl, hneg⟩
    refine ⟨rfl, fun d => by_contra fun hne => hneg ⟨_, d, rfl, hne⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § Key Equivalences
-- ════════════════════════════════════════════════════════════════

/--
**¬∃xφ ≈ ∀x¬φ** — negation commutes with quantifier switch.

This follows from the fact that negation turns anything into a test.
-/
theorem neg_exists_eq_forall_neg {E : Type*} (x : Nat) (φ : DPLRel E) :
    DPLRel.neg (DPLRel.exists_ x φ) = DPLRel.forall_ x (DPLRel.neg φ) := by
  funext g h
  simp only [DPLRel.neg, DPLRel.exists_, DPLRel.forall_, eq_iff_iff]
  constructor
  · rintro ⟨rfl, hneg⟩
    refine ⟨rfl, fun d => ⟨_, rfl, fun ⟨k, hφ⟩ => hneg ⟨k, d, hφ⟩⟩⟩
  · rintro ⟨rfl, hall⟩
    refine ⟨rfl, ?_⟩
    rintro ⟨k, d, hφ⟩
    obtain ⟨m, rfl, hneg⟩ := hall d
    exact hneg ⟨k, hφ⟩

/--
**The donkey equivalence: ∃xφ → ψ ≈ ∀x[φ → ψ]**

The central theorem of @cite{groenendijk-stokhof-1991}: an existential
quantifier in the antecedent of an implication has *universal* force.
This is what makes donkey sentences compositional — "if a farmer owns
a donkey, he beats it" gets the universal reading from the dynamic
semantics of implication alone, without stipulating wide-scope ∀.
-/
theorem donkey_equivalence {E : Type*} (x : Nat) (φ ψ : DPLRel E) :
    DPLRel.impl (DPLRel.exists_ x φ) ψ =
    DPLRel.forall_ x (DPLRel.impl φ ψ) := by
  funext g h
  simp only [DPLRel.impl, DPLRel.exists_, DPLRel.forall_, eq_iff_iff]
  constructor
  · rintro ⟨rfl, hall⟩
    refine ⟨rfl, fun d => ⟨_, rfl, fun k hφ => hall k ⟨d, hφ⟩⟩⟩
  · rintro ⟨rfl, hall⟩
    refine ⟨rfl, fun k ⟨d, hφ⟩ => ?_⟩
    obtain ⟨m, rfl, himpl⟩ := hall d
    exact himpl k hφ

/--
**Conjunction is not commutative in DPL.**

`∃xPx ∧ Qx` and `Qx ∧ ∃xPx` differ because in the first,
∃x binds x in Qx (left-to-right binding), while in the second,
Qx uses x's current value before ∃x reassigns it.

Requires `Nontrivial E` so that reassignment can change the value.
-/
theorem conj_not_comm {E : Type*} [Nontrivial E] :
    ∃ (φ ψ : DPLRel E), DPLRel.conj φ ψ ≠ DPLRel.conj ψ φ := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  -- φ = ∃₀(identity): random reassignment at variable 0
  let φ : DPLRel E := DPLRel.exists_ 0 (λ g h => g = h)
  -- ψ = test that variable 0 equals e₁
  let ψ : DPLRel E := DPLRel.atom (λ g => g 0 = e₁)
  refine ⟨φ, ψ, ?_⟩
  intro heq
  -- conj φ ψ accepts input (λ _ => e₂) by setting var 0 to e₁
  have hfwd : (DPLRel.conj φ ψ) (λ _ => e₂)
      (λ n => if n = 0 then e₁ else e₂) := by
    refine ⟨λ n => if n = 0 then e₁ else e₂, ⟨e₁, ?_⟩, rfl, ?_⟩
    · funext n; simp
    · simp
  -- conj ψ φ rejects input (λ _ => e₂) because ψ tests g(0) = e₁ first
  rw [heq] at hfwd
  obtain ⟨k, ⟨rfl, hk0⟩, _⟩ := hfwd
  simp at hk0
  exact hne hk0.symm

-- ════════════════════════════════════════════════════════════════
-- § Closure Properties (Definition 17)
-- ════════════════════════════════════════════════════════════════

/-- ◇φ ≈ ¬¬φ — closure is double negation (s-equivalence). -/
theorem close_eq_neg_neg {E : Type*} (φ : DPLRel E) :
    DPLRel.close φ = DPLRel.neg (DPLRel.neg φ) := by
  funext g h
  simp only [DPLRel.close, DPLRel.neg, eq_iff_iff]
  constructor
  · rintro ⟨rfl, k, hφ⟩
    exact ⟨rfl, fun ⟨_, rfl, hneg⟩ => hneg ⟨k, hφ⟩⟩
  · rintro ⟨rfl, hneg⟩
    exact ⟨rfl, by_contra fun hne => hneg ⟨g, rfl, hne⟩⟩

/-- Implication is a test: ⟦φ → ψ⟧(g, h) implies g = h. -/
theorem impl_isTest {E : Type*} (φ ψ : DPLRel E) (g h : Nat → E)
    (h_impl : DPLRel.impl φ ψ g h) : g = h := h_impl.1

/-- Disjunction is a test. -/
theorem disj_isTest {E : Type*} (φ ψ : DPLRel E) (g h : Nat → E)
    (h_disj : DPLRel.disj φ ψ g h) : g = h := h_disj.1

/-- Universal quantification is a test. -/
theorem forall_isTest {E : Type*} (x : Nat) (φ : DPLRel E) (g h : Nat → E)
    (h_fa : DPLRel.forall_ x φ g h) : g = h := h_fa.1

end Semantics.Dynamic.DPL
