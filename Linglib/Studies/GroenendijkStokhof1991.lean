import Linglib.Logic.CylindricAlgebra
import Linglib.Semantics.Dynamic.DPL

/-!
# Groenendijk and Stokhof (1991): Dynamic Predicate Logic

This file formalizes the logical facts of [groenendijk-stokhof-1991], "Dynamic predicate
logic", about the system of its `Semantics/Dynamic/DPL.lean` substrate, where a formula
denotes a relation between assignments, conjunction is composition, and the existential is a
random reset. The notions of section 3.2 come first: s-equivalence and p-equivalence, which
equivalence implies but which together do not imply it, and the tests, on which all three
coincide. Section 3.4 then supplies the laws. The connectives are definable from negation,
conjunction, and the existential but not conversely, since a negation is a test and an
existential is one only over a contradictory scope (`isTest_exists_iff`); double negation,
commutativity, and idempotency of conjunction hold exactly of tests, while contraposition,
currying, and the de Morgan laws hold outright; an existential binds without limit to its
right (`scope_extension`) and has universal force in an antecedent (`donkey_equivalence`).
Section 3.5's dynamic entailment (`Entails`) satisfies the deduction theorem and reduces
s-entailment to entailment from the closed premiss, and it is neither reflexive nor
transitive, by the paper's own counterexamples. The satisfaction-set computations in the
proof of Fact 19 are stated in the library's cylindric vocabulary.

## Implementation notes

The paper quantifies over models; `DPL.Rel E` fixes one, so its equivalence is equality of
relations, its contradiction is `⊥`, and its counterexamples are stated over a domain with two
individuals, `[Nontrivial E]`. Tests are the substrate's `Update.IsTest` through the embedding
`toDRS`. The paper lists idempotency of disjunction as unconditional, but a disjunction is a
test by Definition 2, so `φ ∨ φ` is the closure of `φ` (`disj_self`) and the law holds exactly
of tests.

## References

* [groenendijk-stokhof-1991]
* [henkin-monk-tarski-1971]

## TODO

The laws with side conditions on active quantifiers and free variables, Facts 8, 9, and 13 to
16, the leftward scope extension, alphabetic variance, and the normal binding form of section
4.1 with Facts 17 to 24 need a syntax for DPL formulas, which the substrate lacks.
-/

namespace GroenendijkStokhof1991

open DPL DynamicSemantics.Update

variable {E : Type*} (x : ℕ) (φ ψ χ : Rel E)

/-! ### Meaning, truth, and equivalence, section 3.2 -/

/-- Validity and contradictoriness, Definitions 4 and 5: true, or false, with respect to
every assignment. -/
def Valid : Prop := ∀ g, φ.trueAt g

def Contradiction : Prop := ∀ g, ¬ φ.trueAt g

/-- s-equivalence, Definition 7: the same satisfaction set. -/
def SEquiv : Prop := φ.satisfactionSet = ψ.satisfactionSet

/-- p-equivalence, Definition 10: the same production set. -/
def PEquiv : Prop := φ.productionSet = ψ.productionSet

/-- Facts 1 and 2: equivalent formulas are s-equivalent and p-equivalent. -/
theorem SEquiv.of_eq {φ ψ : Rel E} (h : φ = ψ) : SEquiv φ ψ := h ▸ rfl

theorem PEquiv.of_eq {φ ψ : Rel E} (h : φ = ψ) : PEquiv φ ψ := h ▸ rfl

/-- Fact 3: s-equivalence and p-equivalence together do not give equivalence. The paper's
witnesses are the tautologies `Px ∨ ¬Px` and `∃x[Px ∨ ¬Px]`: a trivial test and its
existential closure have the total satisfaction and production sets and differ as relations. -/
theorem exists_sEquiv_pEquiv_ne [Nontrivial E] :
    ∃ φ ψ : Rel E, SEquiv φ ψ ∧ PEquiv φ ψ ∧ φ ≠ ψ := by
  refine ⟨Rel.atom λ _ => True, Rel.exists_ 0 (Rel.atom λ _ => True), ?_, ?_, λ h => ?_⟩
  · ext g
    simp [Rel.satisfactionSet, Rel.atom, Rel.exists_]
  · ext g
    simp only [Rel.productionSet, Rel.atom, Rel.exists_, and_true, Set.mem_ofPred_eq, exists_eq,
      true_iff]
    exact ⟨g, g 0, funext λ n => by split_ifs with hn <;> simp [hn]⟩
  · obtain ⟨a, b, hab⟩ := exists_pair_ne E
    have hb : Rel.exists_ 0 (Rel.atom λ _ => True) (λ _ => a) (λ n => if n = 0 then b else a) :=
      ⟨b, rfl, trivial⟩
    rw [← h] at hb
    exact hab (by simpa using congr_fun hb.1 0)

/-- Definition 12 and Fact 5: atomic formulas, negations, disjunctions, implications, and
universals are tests in the sense of Definition 11, and tests are closed under conjunction; so
is the closure of Definition 17. -/
theorem isTest_atom (p : (ℕ → E) → Prop) : IsTest (toDRS (Rel.atom p)) := λ _ _ h => h.1

theorem isTest_neg : IsTest (toDRS φ.neg) := λ _ _ h => h.1

theorem isTest_disj : IsTest (toDRS (φ.disj ψ)) := λ _ _ h => h.1

theorem isTest_impl : IsTest (toDRS (φ.impl ψ)) := λ _ _ h => h.1

theorem isTest_forall : IsTest (toDRS (Rel.forall_ x φ)) := λ _ _ h => h.1

theorem isTest_close : IsTest (toDRS φ.close) := λ _ _ h => h.1

theorem isTest_conj {φ ψ : Rel E} (hφ : IsTest (toDRS φ)) (hψ : IsTest (toDRS ψ)) :
    IsTest (toDRS (φ.conj ψ)) :=
  λ _ _ ⟨_, h₁, h₂⟩ => (hφ h₁).trans (hψ h₂)

/-- A test's outputs are its inputs: its production set is its satisfaction set. -/
theorem productionSet_eq_satisfactionSet {φ : Rel E} (h : IsTest (toDRS φ)) :
    φ.productionSet = φ.satisfactionSet :=
  Set.ext λ g => ⟨λ ⟨_, hk⟩ => ⟨g, h hk ▸ hk⟩, λ ⟨_, hk⟩ => ⟨g, (h hk).symm ▸ hk⟩⟩

/-- Fact 4: on tests, equivalence, s-equivalence, and p-equivalence coincide. -/
theorem sEquiv_iff_eq_of_isTest {φ ψ : Rel E} (hφ : IsTest (toDRS φ))
    (hψ : IsTest (toDRS ψ)) : SEquiv φ ψ ↔ φ = ψ :=
  ⟨λ h => (hφ.eq_test_closure.trans (congrArg test h)).trans hψ.eq_test_closure.symm, .of_eq⟩

theorem pEquiv_iff_eq_of_isTest {φ ψ : Rel E} (hφ : IsTest (toDRS φ))
    (hψ : IsTest (toDRS ψ)) : PEquiv φ ψ ↔ φ = ψ := by
  rw [PEquiv, productionSet_eq_satisfactionSet hφ, productionSet_eq_satisfactionSet hψ]
  exact sEquiv_iff_eq_of_isTest hφ hψ

/-! ### Some logical facts, section 3.4 -/

/-- Implication, disjunction, and the universal are definable from negation, conjunction,
and the existential in the usual way. -/
theorem impl_eq_neg_conj_neg : φ.impl ψ = (φ.conj ψ.neg).neg := by
  funext g h
  simp only [Rel.impl, Rel.neg, Rel.conj, eq_iff_iff]
  constructor
  · rintro ⟨rfl, hall⟩
    exact ⟨rfl, λ ⟨_, _, hφ, rfl, hnψ⟩ => hnψ (hall _ hφ)⟩
  · rintro ⟨rfl, hneg⟩
    exact ⟨rfl, λ k hφ => by_contra λ hne => hneg ⟨k, k, hφ, rfl, hne⟩⟩

theorem disj_eq_neg_conj_neg_neg : φ.disj ψ = (φ.neg.conj ψ.neg).neg := by
  funext g h
  simp only [Rel.disj, Rel.neg, Rel.conj, eq_iff_iff]
  constructor
  · rintro ⟨rfl, k, hφψ⟩
    refine ⟨rfl, ?_⟩
    rintro ⟨_, _, ⟨rfl, hnφ⟩, rfl, hnψ⟩
    exact hφψ.elim (λ hφ => hnφ ⟨k, hφ⟩) (λ hψ => hnψ ⟨k, hψ⟩)
  · rintro ⟨rfl, hneg⟩
    refine ⟨rfl, by_contra λ hne => ?_⟩
    push Not at hne
    exact hneg ⟨g, g, ⟨rfl, λ ⟨j, hφ⟩ => (hne j).1 hφ⟩, rfl, λ ⟨j, hψ⟩ => (hne j).2 hψ⟩

theorem forall_eq_neg_exists_neg : Rel.forall_ x φ = (Rel.exists_ x φ.neg).neg := by
  funext g h
  simp only [Rel.forall_, Rel.neg, Rel.exists_, eq_iff_iff]
  constructor
  · rintro ⟨rfl, hall⟩
    exact ⟨rfl, λ ⟨_, d, rfl, hneg⟩ => hneg (hall d)⟩
  · rintro ⟨rfl, hneg⟩
    exact ⟨rfl, λ d => by_contra λ hne => hneg ⟨_, d, rfl, hne⟩⟩

/-- Disjunction is definable from implication, `φ ∨ ψ ≃ ¬φ → ψ`; the converse fails below. -/
theorem disj_eq_neg_impl : φ.disj ψ = φ.neg.impl ψ := by
  funext g h
  simp only [Rel.disj, Rel.neg, Rel.impl, eq_iff_iff]
  refine and_congr_right λ _ => ⟨λ ⟨k, hk⟩ _ ⟨rfl, hn⟩ => hk.elim (λ h => (hn ⟨k, h⟩).elim)
    (⟨k, ·⟩), λ h => ?_⟩
  by_cases hφ : ∃ k, φ g k
  · exact hφ.imp λ _ => Or.inl
  · exact (h g ⟨rfl, hφ⟩).imp λ _ => Or.inr

/-- `¬∃xφ ≃ ∀x¬φ` holds unconditionally, negation turning anything into a test. -/
theorem neg_exists_eq_forall_neg : (Rel.exists_ x φ).neg = Rel.forall_ x φ.neg := by
  funext g h
  simp only [Rel.neg, Rel.exists_, Rel.forall_, eq_iff_iff]
  constructor
  · rintro ⟨rfl, hneg⟩
    exact ⟨rfl, λ d => ⟨_, rfl, λ ⟨k, hφ⟩ => hneg ⟨k, d, hφ⟩⟩⟩
  · rintro ⟨rfl, hall⟩
    exact ⟨rfl, λ ⟨k, d, hφ⟩ => (hall d).elim λ _ ⟨_, hneg⟩ => hneg ⟨k, hφ⟩⟩

/-! #### Closure and double negation, Definition 17 -/

/-- The closure operator is double negation. -/
theorem close_eq_neg_neg : φ.close = φ.neg.neg := by
  funext g h
  simp only [Rel.close, Rel.neg, eq_iff_iff]
  constructor
  · rintro ⟨rfl, k, hφ⟩
    exact ⟨rfl, λ ⟨_, rfl, hneg⟩ => hneg ⟨k, hφ⟩⟩
  · rintro ⟨rfl, hneg⟩
    exact ⟨rfl, by_contra λ hne => hneg ⟨g, rfl, hne⟩⟩

/-- Closure fixes exactly the tests. -/
theorem close_eq_self_iff_isTest : φ.close = φ ↔ IsTest (toDRS φ) := by
  constructor
  · intro h g k hφ
    rw [← h] at hφ
    exact hφ.1
  · intro htest
    funext g h
    simp only [Rel.close, eq_iff_iff]
    constructor
    · rintro ⟨rfl, k, hk⟩
      obtain rfl := htest hk
      exact hk
    · exact λ hφ => ⟨htest hφ, h, hφ⟩

/-- The restricted law of double negation: `¬¬φ ≃ φ` exactly when `φ` is a test. -/
theorem neg_neg_eq_self_iff_isTest : φ.neg.neg = φ ↔ IsTest (toDRS φ) :=
  close_eq_neg_neg φ ▸ close_eq_self_iff_isTest φ

/-- `◇φ ≃ ◇ψ` iff `φ ≃ₛ ψ`: closure retains exactly the truth conditions. -/
theorem close_eq_close_iff_sEquiv : φ.close = ψ.close ↔ SEquiv φ ψ := by
  refine ⟨λ h => Set.ext λ g => ?_, λ h => funext λ g => funext λ k => ?_⟩
  · simpa [Rel.close, Rel.satisfactionSet] using congr_fun (congr_fun h g) g
  · simp only [Rel.close]
    exact propext (and_congr_right λ _ => Set.ext_iff.mp h g)

theorem close_close : φ.close.close = φ.close :=
  (close_eq_self_iff_isTest _).mpr (isTest_close φ)

theorem close_neg : φ.neg.close = φ.neg := (close_eq_self_iff_isTest _).mpr (isTest_neg φ)

theorem neg_close : φ.close.neg = φ.neg := by
  funext g h
  simp [Rel.neg, Rel.close]

/-- `φ ≃ₛ ¬¬φ`: double negation keeps the truth conditions. -/
theorem sEquiv_neg_neg : SEquiv φ φ.neg.neg :=
  (close_eq_close_iff_sEquiv _ _).mp (by rw [close_neg, close_eq_neg_neg])

/-- The restricted interdefinability of the constants, stated through closure. -/
theorem close_conj : (φ.conj ψ).close = (φ.impl ψ.neg).neg := by
  funext g h
  simp only [Rel.close, Rel.conj, Rel.impl, Rel.neg, eq_iff_iff]
  refine and_congr_right λ _ => ⟨?_, ?_⟩
  · rintro ⟨_, m, hφ, hψ⟩ ⟨_, rfl, hall⟩
    obtain ⟨_, rfl, hnψ⟩ := hall m hφ
    exact hnψ ⟨_, hψ⟩
  · intro hn
    by_contra hne
    push Not at hne
    exact hn ⟨g, rfl, λ m hφ => ⟨m, rfl, λ ⟨k, hψ⟩ => hne k m hφ hψ⟩⟩

theorem close_conj_close : φ.close.conj ψ.close = (φ.neg.disj ψ.neg).neg := by
  funext g h
  simp only [Rel.close, Rel.conj, Rel.disj, Rel.neg, eq_iff_iff]
  constructor
  · rintro ⟨_, ⟨rfl, hφ⟩, rfl, hψ⟩
    refine ⟨rfl, ?_⟩
    rintro ⟨_, rfl, _, ⟨-, hn⟩ | ⟨-, hn⟩⟩
    exacts [hn hφ, hn hψ]
  · rintro ⟨rfl, hn⟩
    refine ⟨g, ⟨rfl, ?_⟩, rfl, ?_⟩
    · by_contra hφ
      exact hn ⟨g, rfl, g, .inl ⟨rfl, hφ⟩⟩
    · by_contra hψ
      exact hn ⟨g, rfl, g, .inr ⟨rfl, hψ⟩⟩

theorem close_exists : (Rel.exists_ x φ).close = (Rel.forall_ x φ.neg).neg := by
  rw [close_eq_neg_neg, neg_exists_eq_forall_neg]

theorem close_impl : φ.close.impl ψ = φ.neg.disj ψ := by
  funext g h
  simp only [Rel.close, Rel.impl, Rel.neg, Rel.disj, eq_iff_iff]
  refine and_congr_right λ _ => ?_
  constructor
  · intro hall
    by_cases hφ : ∃ k, φ g k
    · exact (hall g ⟨rfl, hφ⟩).imp λ _ => Or.inr
    · exact ⟨g, .inl ⟨rfl, hφ⟩⟩
  · rintro ⟨k, hk⟩ _ ⟨rfl, hφ⟩
    exact hk.elim (λ h => (h.2 hφ).elim) (⟨k, ·⟩)

/-! #### What the static constants cannot define -/

/-- An existential is a test only over a contradictory scope, given two individuals to reset
between: this is why the externally dynamic constants are not definable from the universal
and a static connective. -/
theorem isTest_exists_iff [Nontrivial E] :
    IsTest (toDRS (Rel.exists_ x φ)) ↔ Contradiction φ := by
  refine ⟨λ h g ⟨k, hφ⟩ => ?_, λ hc _ _ ⟨_, hφ⟩ => (hc _ ⟨_, hφ⟩).elim⟩
  have hg : ∀ g' : ℕ → E, (∀ n, n ≠ x → g' n = g n) → g' = k := λ g' hg' =>
    h (show toDRS (Rel.exists_ x φ) g' k from ⟨g x, by
      rwa [show (λ n => if n = x then g x else g' n) = g from
        funext λ n => by by_cases hn : n = x <;> simp [hn, hg']]⟩)
  obtain ⟨e, he⟩ := exists_ne (g x)
  have := congr_fun ((hg (λ n => if n = x then e else g n) λ _ hn => if_neg hn).trans
    (hg g λ _ _ => rfl).symm) x
  exact he (by simpa using this)

/-- `∃xφ ≃ ¬∀x¬φ` exactly when `∃xφ` is a test, so only over a contradictory scope; the two
are always s-equivalent. -/
theorem exists_eq_neg_forall_neg_iff [Nontrivial E] :
    Rel.exists_ x φ = (Rel.forall_ x φ.neg).neg ↔ Contradiction φ := by
  rw [← isTest_exists_iff]
  refine ⟨λ h => h ▸ isTest_neg _, λ h => ?_⟩
  rw [← (close_eq_self_iff_isTest _).mpr h, close_exists]

theorem sEquiv_exists_neg_forall_neg : SEquiv (Rel.exists_ x φ) (Rel.forall_ x φ.neg).neg :=
  (close_eq_close_iff_sEquiv _ _).mp (by rw [close_exists, close_neg])

/-- `φ ∧ ψ ≃ ¬[φ → ¬ψ]` exactly when `φ ∧ ψ` is a test; the two are always s-equivalent. -/
theorem conj_eq_neg_impl_neg_iff :
    φ.conj ψ = (φ.impl ψ.neg).neg ↔ IsTest (toDRS (φ.conj ψ)) := by
  rw [← close_conj, eq_comm, close_eq_self_iff_isTest]

theorem sEquiv_conj_neg_impl_neg : SEquiv (φ.conj ψ) (φ.impl ψ.neg).neg :=
  (close_eq_close_iff_sEquiv _ _).mp (by rw [close_conj, close_neg])

/-- The restricted law of double negation fails for the existential unless its scope is
contradictory; so a doubly negated indefinite licenses no anaphora. -/
theorem neg_neg_exists_eq_iff [Nontrivial E] :
    (Rel.exists_ x φ).neg.neg = Rel.exists_ x φ ↔ Contradiction φ :=
  (neg_neg_eq_self_iff_isTest _).trans (isTest_exists_iff x φ)

theorem dne_fails_anaphora [Nontrivial E] :
    ∃ (x : ℕ) (φ : Rel E), (Rel.exists_ x φ).neg.neg ≠ Rel.exists_ x φ :=
  ⟨0, Rel.atom λ _ => True, λ h =>
    (neg_neg_exists_eq_iff 0 _).mp h (λ _ => Classical.arbitrary E) ⟨_, rfl, trivial⟩⟩

/-- Disjunction, being internally static, does not define conjunction or implication even up
to truth conditions: `φ ∧ ψ ≄ₛ ¬[¬φ ∨ ¬ψ]` and `φ → ψ ≄ₛ ¬φ ∨ ψ`, with `P` and `Q` true of one
individual and `φ` the existential `∃xPx`. -/
theorem not_sEquiv_conj_neg_disj_neg [Nontrivial E] :
    ∃ φ ψ : Rel E, ¬ SEquiv (φ.conj ψ) (φ.neg.disj ψ.neg).neg := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨Rel.exists_ 0 (Rel.atom (· 0 = a)), Rel.atom (· 0 = a), λ h => ?_⟩
  have hb : (λ _ => b) ∈ ((Rel.exists_ 0 (Rel.atom (· 0 = a))).conj
      (Rel.atom (· 0 = a))).satisfactionSet := by
    refine ⟨_, _, ⟨a, rfl, ?_⟩, rfl, ?_⟩ <;> simp
  rw [SEquiv] at h
  rw [h] at hb
  obtain ⟨_, -, hn⟩ := hb
  refine hn ⟨_, rfl, _, .inr ⟨rfl, ?_⟩⟩
  rintro ⟨_, -, hb⟩
  exact hab (by simpa using hb.symm)

theorem not_sEquiv_impl_neg_disj [Nontrivial E] :
    ∃ φ ψ : Rel E, ¬ SEquiv (φ.impl ψ) (φ.neg.disj ψ) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨Rel.exists_ 0 (Rel.atom (· 0 = a)), Rel.atom (· 0 = a), λ h => ?_⟩
  have hb : (λ _ => b) ∈ ((Rel.exists_ 0 (Rel.atom (· 0 = a))).impl
      (Rel.atom (· 0 = a))).satisfactionSet := by
    refine ⟨_, rfl, ?_⟩
    rintro _ ⟨_, rfl, hd⟩
    exact ⟨_, rfl, hd⟩
  rw [SEquiv] at h
  rw [h] at hb
  obtain ⟨_, -, _, ⟨-, hn⟩ | ⟨-, hb⟩⟩ := hb
  · exact hn ⟨_, a, rfl, by simp⟩
  · exact hab (by simpa using hb.symm)

/-! #### Conjunction and disjunction -/

/-- Conjunction is associative despite the binding power of the existential: the rightmost
active occurrence of a quantifier is the one that binds. -/
theorem conj_assoc : (φ.conj ψ).conj χ = φ.conj (ψ.conj χ) := by
  funext g h
  simp only [Rel.conj, eq_iff_iff]
  exact ⟨λ ⟨k, ⟨j, hj, hjk⟩, hk⟩ => ⟨j, hj, k, hjk, hk⟩,
    λ ⟨j, hj, k, hjk, hk⟩ => ⟨k, ⟨j, hj, hjk⟩, hk⟩⟩

/-- Tests commute, and a test is idempotent, under conjunction. -/
theorem conj_comm_of_isTest {φ ψ : Rel E} (hφ : IsTest (toDRS φ)) (hψ : IsTest (toDRS ψ)) :
    φ.conj ψ = ψ.conj φ := by
  have key : ∀ {φ ψ : Rel E}, IsTest (toDRS φ) → IsTest (toDRS ψ) → φ.conj ψ ≤ ψ.conj φ :=
    λ hφ hψ _ _ ⟨_, h₁, h₂⟩ => by
      obtain rfl := hφ h₁
      obtain rfl := hψ h₂
      exact ⟨_, h₂, h₁⟩
  exact le_antisymm (key hφ hψ) (key hψ hφ)

theorem conj_self_of_isTest {φ : Rel E} (hφ : IsTest (toDRS φ)) : φ.conj φ = φ := by
  funext g h
  simp only [Rel.conj, eq_iff_iff]
  exact ⟨λ ⟨_, h₁, h₂⟩ => hφ h₁ ▸ h₂, λ h => ⟨_, h, hφ h ▸ h⟩⟩

/-- Conjunction is neither commutative nor idempotent in general: `∃xPx ∧ Qx` differs from
`Qx ∧ ∃xPx`, and the latter from its self-conjunction, binding being left to right. -/
theorem conj_not_comm [Nontrivial E] : ∃ φ ψ : Rel E, φ.conj ψ ≠ ψ.conj φ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨Rel.exists_ 0 (Rel.atom λ _ => True), Rel.atom (· 0 = a), λ h => ?_⟩
  have hb : (Rel.exists_ 0 (Rel.atom λ _ => True)).conj (Rel.atom (· 0 = a)) (λ _ => b)
      (λ n => if n = 0 then a else b) := by
    refine ⟨_, ⟨a, rfl, trivial⟩, rfl, ?_⟩
    simp
  rw [h] at hb
  obtain ⟨_, ⟨rfl, hb⟩, -⟩ := hb
  exact hab (by simpa using hb.symm)

theorem conj_not_idem [Nontrivial E] : ∃ φ : Rel E, φ.conj φ ≠ φ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(Rel.atom (· 0 = a)).conj (Rel.exists_ 0 (Rel.atom (· 0 = b))), λ h => ?_⟩
  have hb : (Rel.atom (· 0 = a)).conj (Rel.exists_ 0 (Rel.atom (· 0 = b))) (λ _ => a)
      (λ n => if n = 0 then b else a) := by
    refine ⟨_, ⟨rfl, rfl⟩, b, rfl, ?_⟩
    simp
  rw [← h] at hb
  obtain ⟨_, ⟨_, ⟨rfl, -⟩, _, rfl, hd⟩, _, ⟨-, hk⟩, -⟩ := hb
  exact hab (hk.symm.trans hd)

/-- Disjunction, static in both directions, is commutative and associative; its
self-disjunction is the closure of the disjunct. -/
theorem disj_self : φ.disj φ = φ.close := by
  funext g h
  simp [Rel.disj, Rel.close]

theorem disj_comm : φ.disj ψ = ψ.disj φ := by
  funext g h
  simp only [Rel.disj, or_comm]

theorem disj_assoc : (φ.disj ψ).disj χ = φ.disj (ψ.disj χ) := by
  funext g h
  simp only [Rel.disj, eq_iff_iff]
  refine and_congr_right λ _ => ⟨?_, ?_⟩
  · rintro ⟨k, ⟨rfl, j, hj⟩ | hχ⟩
    · exact hj.elim (λ hφ => ⟨j, .inl hφ⟩) (λ hψ => ⟨g, .inr ⟨rfl, j, .inl hψ⟩⟩)
    · exact ⟨g, .inr ⟨rfl, k, .inr hχ⟩⟩
  · rintro ⟨k, hφ | ⟨rfl, j, hj⟩⟩
    · exact ⟨g, .inl ⟨rfl, k, .inl hφ⟩⟩
    · exact hj.elim (λ hψ => ⟨g, .inl ⟨rfl, j, .inr hψ⟩⟩) (λ hχ => ⟨j, .inr hχ⟩)

/-- The de Morgan laws DPL validates, the second an instance of distribution when the
disjunct binds nothing in the conjunction. -/
theorem close_conj_disj :
    (φ.conj (ψ.disj χ)).close = (φ.conj ψ).disj (φ.conj χ) := by
  funext g h
  simp only [Rel.close, Rel.conj, Rel.disj, eq_iff_iff]
  refine and_congr_right λ _ => ⟨?_, ?_⟩
  · rintro ⟨_, k, hφ, rfl, j, hj⟩
    exact ⟨j, hj.imp (⟨k, hφ, ·⟩) (⟨k, hφ, ·⟩)⟩
  · rintro ⟨j, ⟨k, hφ, hj⟩ | ⟨k, hφ, hj⟩⟩
    · exact ⟨k, k, hφ, rfl, j, .inl hj⟩
    · exact ⟨k, k, hφ, rfl, j, .inr hj⟩

theorem disj_close_conj :
    φ.disj (ψ.close.conj χ) = (φ.disj ψ).conj (φ.disj χ) := by
  funext g h
  simp only [Rel.disj, Rel.close, Rel.conj, eq_iff_iff]
  constructor
  · rintro ⟨rfl, k, hφ | ⟨_, ⟨rfl, j, hψ⟩, hχ⟩⟩
    · exact ⟨g, ⟨rfl, k, .inl hφ⟩, rfl, k, .inl hφ⟩
    · exact ⟨g, ⟨rfl, j, .inr hψ⟩, rfl, k, .inr hχ⟩
  · rintro ⟨_, ⟨rfl, j, hj⟩, rfl, k, hk⟩
    refine ⟨rfl, ?_⟩
    rcases hj with hφ | hψ
    · exact ⟨j, .inl hφ⟩
    rcases hk with hφ | hχ
    · exact ⟨k, .inl hφ⟩
    · exact ⟨k, .inr ⟨g, ⟨rfl, j, hψ⟩, hχ⟩⟩

/-! #### Implication -/

/-- Contraposition holds outright for a negated antecedent, and for a closed one against a
negated consequent; the general law needs a binding condition. -/
theorem neg_impl_comm : φ.neg.impl ψ = ψ.neg.impl φ := by
  funext g h
  simp only [Rel.impl, Rel.neg, eq_iff_iff]
  refine and_congr_right λ _ => ⟨?_, ?_⟩ <;>
  · rintro hall _ ⟨rfl, hn⟩
    by_contra hne
    exact hn (hall _ ⟨rfl, hne⟩)

theorem close_impl_eq_neg_impl_neg : φ.close.impl ψ = ψ.neg.impl φ.neg := by
  funext g h
  simp only [Rel.impl, Rel.close, Rel.neg, eq_iff_iff]
  refine and_congr_right λ _ => ⟨?_, ?_⟩
  · rintro hall _ ⟨rfl, hn⟩
    exact ⟨g, rfl, λ hφ => hn (hall g ⟨rfl, hφ⟩)⟩
  · rintro hall _ ⟨rfl, hφ⟩
    by_contra hn
    obtain ⟨_, rfl, hnφ⟩ := hall g ⟨rfl, hn⟩
    exact hnφ hφ

/-- An implication is a test and turns its consequent into one, and it curries. -/
theorem impl_close_right : φ.impl ψ.close = φ.impl ψ := by
  funext g h
  simp [Rel.impl, Rel.close]

theorem impl_impl : φ.impl (ψ.impl χ) = (φ.conj ψ).impl χ := by
  funext g h
  simp only [Rel.impl, Rel.conj, eq_iff_iff]
  refine and_congr_right λ _ => ⟨?_, λ hall k hφ => ⟨k, rfl, λ _ hψ => hall _ ⟨k, hφ, hψ⟩⟩⟩
  rintro hall _ ⟨k, hφ, hψ⟩
  obtain ⟨_, rfl, hk⟩ := hall k hφ
  exact hk _ hψ

/-! #### Quantifiers and connectives -/

/-- Scope extension, `∃xφ ∧ ψ ≃ ∃x[φ ∧ ψ]`: the binding power of the existential extends
without limit to the right, which is what represents anaphora across sentences. -/
theorem scope_extension : (Rel.exists_ x φ).conj ψ = Rel.exists_ x (φ.conj ψ) := by
  funext g h
  simp only [Rel.exists_, Rel.conj, eq_iff_iff]
  exact ⟨λ ⟨k, ⟨d, hφ⟩, hψ⟩ => ⟨d, k, hφ, hψ⟩, λ ⟨d, k, hφ, hψ⟩ => ⟨k, ⟨d, hφ⟩, hψ⟩⟩

/-- The donkey equivalence, `∃xφ → ψ ≃ ∀x[φ → ψ]`: an existential in an antecedent binds
into the consequent with universal force. -/
theorem donkey_equivalence : (Rel.exists_ x φ).impl ψ = Rel.forall_ x (φ.impl ψ) := by
  funext g h
  simp only [Rel.impl, Rel.exists_, Rel.forall_, eq_iff_iff]
  constructor
  · rintro ⟨rfl, hall⟩
    exact ⟨rfl, λ d => ⟨_, rfl, λ k hφ => hall k ⟨d, hφ⟩⟩⟩
  · rintro ⟨rfl, hall⟩
    exact ⟨rfl, λ k ⟨d, hφ⟩ => (hall d).elim λ _ ⟨hm, himpl⟩ => himpl k (hm ▸ hφ)⟩

/-! ### Entailment, section 3.5 -/

/-- s-entailment, Definition 18: truth is preserved from premiss to conclusion. -/
def SEntails : Prop := ∀ g, φ.trueAt g → ψ.trueAt g

/-- Dynamic entailment, Definition 20: every output of the premiss is an input on which the
conclusion succeeds. -/
def Entails : Prop := ∀ ⦃g h⦄, φ g h → ψ.trueAt h

/-- Fact 10: meaning inclusion, Definition 19, which is `≤` on relations, implies
s-entailment; the converse fails, as `∃xPx ⊨ₛ ∃xPx → Px` with `∃xPx ≰ Px` shows. -/
theorem SEntails.of_le {φ ψ : Rel E} (h : φ ≤ ψ) : SEntails φ ψ :=
  λ _ ⟨k, hk⟩ => ⟨k, h _ _ hk⟩

/-- Fact 11, the deduction theorem: `φ ⊨ ψ` iff `φ → ψ` is valid. -/
theorem entails_iff_valid_impl : Entails φ ψ ↔ Valid (φ.impl ψ) :=
  ⟨λ h g => ⟨g, rfl, λ _ hk => h hk⟩, λ h _ _ hgk => (h _).elim λ _ hi => hi.2 _ hgk⟩

/-- Fact 12: s-entailment is dynamic entailment from the closed premiss. -/
theorem sEntails_iff_entails_close : SEntails φ ψ ↔ Entails φ.close ψ :=
  ⟨λ h _ _ ⟨hg, hc⟩ => hg ▸ h _ hc, λ h _ hg => h ⟨rfl, hg⟩⟩

/-- `∃xPx ⊨ Px`, the paper's *A man came in wearing a hat. So, he wore a hat*: the premiss's
output binds the free variable of the conclusion. -/
theorem entails_exists_atom (p : E → Prop) :
    Entails (Rel.exists_ x (Rel.atom λ g => p (g x))) (Rel.atom λ g => p (g x)) := by
  rintro _ _ ⟨_, rfl, hp⟩
  exact ⟨_, rfl, hp⟩

/-- `Px ⊨ ∃xPx` as well, so the two entail each other yet are not equivalent, the atom being
a test and the existential not: mutual entailment is weaker than equivalence. -/
theorem entails_atom_exists (p : E → Prop) :
    Entails (Rel.atom λ g => p (g x)) (Rel.exists_ x (Rel.atom λ g => p (g x))) :=
  λ _ h ⟨hgh, hp⟩ => ⟨_, h x, rfl, by simpa using hgh ▸ hp⟩

/-- `∃xPx ⊭ₛ Px`: s-entailment sees no binding from premiss to conclusion. -/
theorem not_sEntails_exists_atom [Nontrivial E] :
    ∃ p : E → Prop,
      ¬ SEntails (Rel.exists_ 0 (Rel.atom λ g => p (g 0))) (Rel.atom λ g => p (g 0)) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(· = a), λ h => ?_⟩
  obtain ⟨_, -, hb⟩ := h (λ _ => b) ⟨_, a, rfl, by simp⟩
  exact hab (by simpa using hb.symm)

/-- Dynamic entailment is not reflexive: `Px ∧ ∃xQx` does not entail itself, its outputs
having forgotten that the input satisfied `Px`. Fact 15 restores reflexivity when no active
quantifier of the formula binds a free variable of it. -/
theorem not_entails_self [Nontrivial E] : ∃ φ : Rel E, ¬ Entails φ φ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(Rel.atom (· 0 = a)).conj (Rel.exists_ 0 (Rel.atom λ _ => True)), λ h => ?_⟩
  have hb : (Rel.atom (· 0 = a)).conj (Rel.exists_ 0 (Rel.atom λ _ => True)) (λ _ => a)
      (λ n => if n = 0 then b else a) :=
    ⟨_, ⟨rfl, rfl⟩, b, rfl, trivial⟩
  obtain ⟨_, _, ⟨-, hb⟩, -⟩ := h hb
  exact hab (by simpa using hb.symm)

/-- A closed or doubly negated formula entails the formula. -/
theorem entails_close_self : Entails φ.close φ := λ _ _ ⟨hg, hk⟩ => hg ▸ hk

theorem entails_neg_neg_self : Entails φ.neg.neg φ :=
  close_eq_neg_neg φ ▸ entails_close_self φ

/-- Dynamic entailment is not transitive: `¬¬∃xPx ⊨ ∃xPx` and `∃xPx ⊨ Px`, but `¬¬∃xPx ⊭ Px`,
the doubly negated premiss binding nothing. Fact 16 restores transitivity when the premiss
fixes every variable the middle formula binds in the conclusion. -/
theorem not_entails_trans [Nontrivial E] :
    ∃ p : E → Prop, ¬ Entails (Rel.exists_ 0 (Rel.atom λ g => p (g 0))).neg.neg
      (Rel.atom λ g => p (g 0)) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(· = a), λ h => ?_⟩
  have hn : (Rel.exists_ 0 (Rel.atom λ g => g 0 = a)).neg.neg (λ _ => b) (λ _ => b) :=
    ⟨rfl, λ ⟨_, _, hno⟩ => hno ⟨_, a, rfl, by simp⟩⟩
  obtain ⟨_, -, hb⟩ := h hn
  exact hab (by simpa using hb.symm)

/-- Nor is it monotone in its premisses: `∃xPx ⊨ Px`, but a further premiss `∃xQx` resets
the binding, `∃xPx, ∃xQx ⊭ Px`, a sequence of premisses being their conjunction. -/
theorem not_entails_conj_exists [Nontrivial E] :
    ∃ p : E → Prop, ¬ Entails ((Rel.exists_ 0 (Rel.atom λ g => p (g 0))).conj
      (Rel.exists_ 0 (Rel.atom λ _ => True))) (Rel.atom λ g => p (g 0)) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(· = a), λ h => ?_⟩
  have hc : (Rel.exists_ 0 (Rel.atom λ g => g 0 = a)).conj (Rel.exists_ 0 (Rel.atom λ _ => True))
      (λ _ => b) (λ _ => b) :=
    ⟨_, ⟨a, rfl, by simp⟩, b, funext λ n => by split_ifs with hn <;> simp [hn], trivial⟩
  obtain ⟨_, -, hb⟩ := h hc
  exact hab (by simpa using hb.symm)

/-! ### Satisfaction sets and predicate logic, section 4.1

The proof of Fact 19 computes the satisfaction set of an existential as
`{g | ∃k: k[x]g & k ∈ \φ\}`, which is cylindrification of the satisfaction set in the cylindric
set algebra of [henkin-monk-tarski-1971]; the identity test is a diagonal element and negation
complements. -/

section SatisfactionSets

open CylindricAlgebra

theorem closure_exists_eq_cylindrify :
    closure (toDRS (Rel.exists_ x φ)) = cylindrify x (closure (toDRS φ)) := by
  have hup : ∀ (g : Assignment E) (d : E),
      (λ n => if n = x then d else g n) = Function.update g x d := λ g d => by
    funext n
    simp [Function.update_apply]
  ext g
  simp only [closure, toDRS, Rel.exists_, cylindrify]
  exact ⟨λ ⟨h, d, hφ⟩ => ⟨d, h, hup g d ▸ hφ⟩, λ ⟨d, h, hφ⟩ => ⟨h, d, (hup g d).symm ▸ hφ⟩⟩

theorem closure_identity_eq_diagonal (y : ℕ) :
    closure (toDRS (Rel.atom λ g : Assignment E => g x = g y)) = @diagonal E x y := by
  ext g
  simp only [closure, toDRS, Rel.atom, diagonal]
  exact ⟨λ ⟨_, rfl, h⟩ => h, λ h => ⟨g, rfl, h⟩⟩

theorem closure_neg_eq : closure (toDRS φ.neg) = λ g => ¬ closure (toDRS φ) g := by
  ext g
  simp only [closure, toDRS, Rel.neg]
  exact ⟨λ ⟨_, rfl, h⟩ => h, λ h => ⟨g, rfl, h⟩⟩

end SatisfactionSets

end GroenendijkStokhof1991
