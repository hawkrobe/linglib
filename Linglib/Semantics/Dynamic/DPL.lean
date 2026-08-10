import Linglib.Logic.Assignment
import Linglib.Semantics.Dynamic.CDRT

/-!
# Dynamic Predicate Logic
[groenendijk-stokhof-1991]

The DPL substrate: meanings are relations between total assignments
(`Rel`, the paper's Definition 2), truth is having an output
(Definition 3), and `♦` closes a meaning to its test (Definition 17).
Conjunction is relational composition and the existential is random
reassignment — the two externally dynamic constants; negation,
implication, disjunction, and the universal are tests. The paper's
results about the system (scope extension, donkey equivalence, the
restricted double-negation laws, interdefinability) are proved in
`Studies/GroenendijkStokhof1991.lean`.

## Main definitions

- `Rel` with Definition 2's clauses: `atom`, `conj`, `exists_`,
  `neg`, `impl`, `disj`, `forall_`; `close` (Definition 17).
- `agreeOn`, `reset`: the agreement relations, with the existential
  factored through the reset (`exists_eq_reset_conj`).
- `trueAt`, `satisfactionSet`, `productionSet` (Definitions 3, 6, 9).
- `toDRS`/`ofDRS`: a DPL relation is an `Update` over assignments — DPL
  embeds in dynamic Ty2 at `S = Assignment E`, each connective matching
  its spine combinator (`conj_eq_dseq`, `neg_eq_test_dneg`, ...).
-/

namespace DPL

open DynamicSemantics
open DynamicSemantics.Update

variable {E : Type*}

/-- DPL semantic type (Definition 2): `⟦φ⟧ g h` means that starting from
input assignment `g`, the formula `φ` can update to output `h`. -/
def Rel (E : Type*) := (ℕ → E) → (ℕ → E) → Prop

instance : CompleteLattice (Rel E) :=
  inferInstanceAs (CompleteLattice ((ℕ → E) → (ℕ → E) → Prop))

/-- Atomic predicate (clauses 1–2): test the input without changing it. -/
def Rel.atom (p : (ℕ → E) → Prop) : Rel E :=
  λ g h => g = h ∧ p g

/-- Conjunction (clause 4): relation composition —
`⟦φ ∧ ψ⟧ g h` iff `∃k, ⟦φ⟧ g k ∧ ⟦ψ⟧ k h`. -/
def Rel.conj (φ ψ : Rel E) : Rel E :=
  λ g h => ∃ k, φ g k ∧ ψ k h

/-- Existential quantification (clause 7): random assignment at `x`,
then the scope — `⟦∃x φ⟧ g h` iff `∃d, ⟦φ⟧ g[x↦d] h`. -/
def Rel.exists_ (x : ℕ) (φ : Rel E) : Rel E :=
  λ g h => ∃ d : E, φ (λ n => if n = x then d else g n) h

/-- Negation (clause 3): the test that no output is reachable —
`⟦¬φ⟧ g h` iff `g = h ∧ ¬∃k, ⟦φ⟧ g k`. Not DNE-valid: see
`Studies/GroenendijkStokhof1991.lean`. -/
def Rel.neg (φ : Rel E) : Rel E :=
  λ g h => g = h ∧ ¬∃ k, φ g k

/-- Implication (clause 6): internally dynamic, externally static —
every output of the antecedent can be extended by the consequent. The
antecedent passes bindings to the consequent, giving its existentials
universal force (donkey sentences). -/
def Rel.impl (φ ψ : Rel E) : Rel E :=
  λ g h => g = h ∧ ∀ k, φ g k → ∃ j, ψ k j

/-- Disjunction (clause 5): externally and internally static — no
anaphoric relations across or out of the disjuncts. -/
def Rel.disj (φ ψ : Rel E) : Rel E :=
  λ g h => g = h ∧ ∃ k, φ g k ∨ ψ g k

/-- Universal quantification (clause 8): a test — for every value at
`x`, the scope can be processed. Externally static. -/
def Rel.forall_ (x : ℕ) (φ : Rel E) : Rel E :=
  λ g h => g = h ∧ ∀ d : E, ∃ m, φ (λ n => if n = x then d else g n) m

/-- Closure (Definition 17): `⟦♦φ⟧ g h` iff `g = h` and `φ` can be
successfully processed — the test with `φ`'s truth conditions. -/
def Rel.close (φ : Rel E) : Rel E :=
  λ g h => g = h ∧ ∃ k, φ g k

/-! ### Agreement relations -/

/-- Agreement on `V`: relate the assignments equal on `V`
([visser-1998], Definition 2.2). -/
def agreeOn (V : Set ℕ) : Rel E := λ f g => Set.EqOn f g V

/-- The random reset `k[x]g` of the existential clause: agree everywhere
but `x`, [visser-1998]'s `[x]`. -/
def reset (x : ℕ) : Rel E := agreeOn {x}ᶜ

/-- A relation embeds in its composition with agreement on either
side. -/
theorem le_agreeOn_conj (R : Rel E) (V W : Set ℕ) :
    R ≤ (agreeOn V).conj (R.conj (agreeOn W)) :=
  λ f g hR => ⟨f, Set.eqOn_refl _ _, g, hR, Set.eqOn_refl _ _⟩

/-! ### Semantic notions (Definitions 3, 6, 9) -/

/-- Truth (Definition 3): `φ` is true w.r.t. `g` iff it has an output. -/
def Rel.trueAt (φ : Rel E) (g : ℕ → E) : Prop :=
  ∃ h, φ g h

/-- Satisfaction set (Definition 6): inputs from which `φ` succeeds. -/
def Rel.satisfactionSet (φ : Rel E) : Set (ℕ → E) :=
  { g | ∃ h, φ g h }

/-- Production set (Definition 9): possible outputs of `φ`. -/
def Rel.productionSet (φ : Rel E) : Set (ℕ → E) :=
  { h | ∃ g, φ g h }

/-! ### DPL as dynamic Ty2

DPL embeds directly into dynamic Ty2 at `S = Assignment E`: DPL
assignments are Ty2 states, DPL relations are `Update` meanings, and
each connective matches its spine combinator. -/

/-- DPL dref: projection function for variable `n`. -/
def dref (n : ℕ) : Dref (Assignment E) E := λ g => g n

/-- DPL extend is `Function.update`. -/
abbrev extend (g : Assignment E) (n : ℕ) (e : E) : Assignment E :=
  Function.update g n e

theorem extend_at (g : Assignment E) (n : ℕ) (e : E) :
    dref n (extend g n e) = e := by simp [dref, extend]

theorem extend_other (g : Assignment E) (n m : ℕ) (e : E) (h : n ≠ m) :
    dref m (extend g n e) = dref m g := by simp [dref, extend, h.symm]

/-- A DPL relation is an `Update` over `Assignment E`. -/
def toDRS (φ : Rel E) : Update (Assignment E) := φ

/-- An `Update` is a DPL relation. -/
def ofDRS (D : Update (Assignment E)) : Rel E := D

@[simp] theorem toDRS_ofDRS (φ : Rel E) : ofDRS (toDRS φ) = φ := rfl
@[simp] theorem ofDRS_toDRS (D : Update (Assignment E)) : toDRS (ofDRS D) = D := rfl

theorem atom_eq_test (p : Assignment E → Prop) :
    toDRS (Rel.atom p) = test (λ g => p g) := by
  ext g h
  simp only [toDRS, Rel.atom, test]
  constructor
  · intro ⟨heq, hp⟩; exact ⟨heq, by rw [← heq]; exact hp⟩
  · intro ⟨heq, hp⟩; exact ⟨heq, by rw [heq]; exact hp⟩

theorem conj_eq_dseq (φ ψ : Rel E) :
    toDRS (Rel.conj φ ψ) = seq (toDRS φ) (toDRS ψ) := by
  ext g h
  simp only [toDRS, Rel.conj, seq, Relation.Comp]

theorem neg_eq_test_dneg (φ : Rel E) :
    toDRS (Rel.neg φ) = test (neg (toDRS φ)) := by
  ext g h
  simp only [toDRS, Rel.neg, test, neg]
  constructor
  · intro ⟨heq, hnex⟩; exact ⟨heq, by rw [← heq]; exact hnex⟩
  · intro ⟨heq, hnex⟩; exact ⟨heq, by rw [heq]; exact hnex⟩

theorem exists_eq (x : ℕ) (φ : Rel E) :
    toDRS (Rel.exists_ x φ) = λ g h => ∃ d : E, toDRS φ (extend g x d) h := by
  have hup : ∀ (g : Assignment E) (d : E),
      (fun n => if n = x then d else g n) = Function.update g x d := fun g d => by
    funext n; simp [Function.update_apply]
  funext g h
  exact propext (exists_congr fun d => by rw [hup g d]; exact Iff.rfl)

/-- The existential clause factored through the reset: `∃x φ` is the
random reset at `x` composed with the scope. -/
theorem exists_eq_reset_conj (x : ℕ) (φ : Rel E) :
    Rel.exists_ x φ = (reset x).conj φ := by
  have h1 : Rel.exists_ x φ =
      λ g h => ∃ d, φ (Function.update g x d) h := exists_eq x φ
  rw [h1]
  funext g h
  refine propext ⟨λ ⟨d, hφ⟩ =>
      ⟨_, λ v hv => (Function.update_of_ne hv d g).symm, hφ⟩,
    λ ⟨k, hk, hφ⟩ => ⟨k x, ?_⟩⟩
  rwa [Function.update_eq_iff.mpr ⟨rfl, λ v hv => hk hv⟩]

/-- DPL implication is the test of dynamic implication. -/
theorem impl_eq_test_dimpl (φ ψ : Rel E) :
    toDRS (Rel.impl φ ψ) = test (impl (toDRS φ) (toDRS ψ)) := by
  ext g h
  simp only [toDRS, Rel.impl, test, impl]
  constructor
  · intro ⟨heq, hall⟩; exact ⟨heq, by rw [← heq]; exact hall⟩
  · intro ⟨heq, hall⟩; exact ⟨heq, by rw [heq]; exact hall⟩

/-- DPL disjunction is the test of dynamic disjunction. -/
theorem disj_eq_test_ddisj (φ ψ : Rel E) :
    toDRS (Rel.disj φ ψ) = test (disj (toDRS φ) (toDRS ψ)) := by
  ext g h
  simp only [toDRS, Rel.disj, test, disj]
  constructor
  · intro ⟨heq, hd⟩; exact ⟨heq, by rw [← heq]; exact hd⟩
  · intro ⟨heq, hd⟩; exact ⟨heq, by rw [heq]; exact hd⟩

/-- DPL closure is the test of existential closure. -/
theorem close_eq_test_closure (φ : Rel E) :
    toDRS (Rel.close φ) = test (closure (toDRS φ)) := by
  ext g h
  simp only [toDRS, Rel.close, test, closure]
  constructor
  · intro ⟨heq, hc⟩; exact ⟨heq, by rw [← heq]; exact hc⟩
  · intro ⟨heq, hc⟩; exact ⟨heq, by rw [heq]; exact hc⟩

/-- DPL truth is existential closure. -/
theorem trueAt_eq_closure (φ : Rel E) (g : Assignment E) :
    Rel.trueAt φ g ↔ closure (toDRS φ) g := Iff.rfl

end DPL
