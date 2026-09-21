import Linglib.Logic.CylindricAlgebra
import Linglib.Semantics.Dynamic.CDRT

/-!
# Groenendijk and Stokhof (1991): Dynamic Predicate Logic

This file formalizes the logical facts of [groenendijk-stokhof-1991], "Dynamic predicate
logic", in which a formula denotes a relation between assignments. The paper's semantics is
the update algebra of `Semantics/Dynamic/Update.lean`: conjunction is relational composition, the
existential is a random reset followed by its scope, and negation, implication, disjunction,
the universal, and closure are the tests of the conditions `neg`, `impl`, `disj`, `dforall`,
and `SetRel.dom`, which is the content of the paper's translation of discourse representation
theory. Only the quantifiers mention assignments, so the propositional laws are proved of
updates over any state type and the quantifier laws over any register structure.

The notions of section 3.2 come first: s-equivalence and p-equivalence, which equivalence
implies but which together do not imply it, and the tests, on which all three coincide.
Section 3.4 then supplies the laws. The connectives are definable from negation, conjunction,
and the existential but not conversely, since a negation is a test and an existential is one
only over a contradictory scope (`isTest_dexists_iff`); double negation, commutativity, and
idempotency of conjunction hold exactly of tests, while contraposition, currying, and the de
Morgan laws hold outright. An existential binds without limit to its right because composition
is associative (`scope_extension`), and it has universal force in an antecedent because
implication curries (`donkey_equivalence`). Section 3.5's dynamic entailment (`Entails`)
satisfies the deduction theorem and reduces s-entailment to entailment from the closed
premiss, and it is neither reflexive nor transitive, by the paper's own counterexamples. The
satisfaction set of an existential computed in the proof of Fact 19 is the cylindrification of
its scope's, in the cylindric set algebra of [henkin-monk-tarski-1971]; that is the substrate's
`dom_dexists`.

## Implementation notes

The paper quantifies over models; an `Update S` fixes one, so its equivalence is equality of
relations, its contradiction is `∅`, and its counterexamples are stated over assignments into
a domain with two individuals, `[Nontrivial E]`. Truth with respect to an assignment and the
satisfaction set are both `SetRel.dom`, and the production set is `SetRel.cod`. That conditions
are tests, that tests are closed under conjunction, and that a test's production set is its
satisfaction set are the substrate's `isTest_test`, `IsTest.comp`, and `IsTest.cod_eq_dom`;
that closure and negation are idempotent on tests is `dom_test`. The paper lists idempotency
of disjunction as unconditional, but a disjunction is a test by Definition 2, so `φ ∨ φ` is the
closure of `φ` (`disj_self`) and the law holds exactly of tests.

## References

* [groenendijk-stokhof-1991]
* [henkin-monk-tarski-1971]

## TODO

The laws with side conditions on active quantifiers and free variables, Facts 8, 9, and 13 to
16, the leftward scope extension, alphabetic variance, and the normal binding form of section
4.1 with Facts 17 to 24 need a syntax for DPL formulas.
-/

namespace GroenendijkStokhof1991

open DynamicSemantics DynamicSemantics.Update SetRel

/-- The test connectives of Definition 2 and the closure of Definition 17, as tests of the
substrate's conditions; conjunction is `○`. -/
local notation:max "∼" φ:max => test (neg φ)

local notation:max "◇" φ:max => test (dom φ)

local notation:25 φ:26 " ⇒ " ψ:25 => test (impl φ ψ)

local notation:30 φ:31 " ⋎ " ψ:30 => test (disj φ ψ)

variable {S : Type*} (φ ψ χ : Update S)

/-! ### Meaning, truth, and equivalence, section 3.2 -/

/-- Validity and contradictoriness, Definitions 4 and 5: true, or false, with respect to
every assignment. -/
def Valid : Prop := ∀ g, g ∈ φ.dom

def Contradiction : Prop := ∀ g, g ∉ φ.dom

/-- s-equivalence, Definition 7: the same satisfaction set. -/
def SEquiv : Prop := φ.dom = ψ.dom

/-- p-equivalence, Definition 10: the same production set. -/
def PEquiv : Prop := φ.cod = ψ.cod

variable {φ ψ} in
/-- Facts 1 and 2: equivalent formulas are s-equivalent and p-equivalent. -/
theorem SEquiv.of_eq (h : φ = ψ) : SEquiv φ ψ := h ▸ rfl

variable {φ ψ} in
theorem PEquiv.of_eq (h : φ = ψ) : PEquiv φ ψ := h ▸ rfl

/-- Fact 3: s-equivalence and p-equivalence together do not give equivalence. The paper's
witnesses are the tautologies `Px ∨ ¬Px` and `∃x[Px ∨ ¬Px]`: a trivial test and its
existential closure have the total satisfaction and production sets and differ as relations. -/
theorem exists_sEquiv_pEquiv_ne {E : Type*} [Nontrivial E] :
    ∃ φ ψ : Update (Assignment E), SEquiv φ ψ ∧ PEquiv φ ψ ∧ φ ≠ ψ := by
  have hself (g : Assignment E) : g ~[dexists 0 (test Set.univ)] g :=
    ⟨g, ⟨g 0, (Function.update_eq_self 0 g).symm⟩, rfl, trivial⟩
  refine ⟨test Set.univ, dexists 0 (test Set.univ), ?_, ?_, fun h ↦ ?_⟩
  · exact Set.ext fun g ↦ ⟨fun _ ↦ ⟨g, hself g⟩, fun _ ↦ ⟨g, rfl, trivial⟩⟩
  · exact Set.ext fun g ↦ ⟨fun _ ↦ ⟨g, hself g⟩, fun _ ↦ ⟨g, rfl, trivial⟩⟩
  · obtain ⟨a, b, hab⟩ := exists_pair_ne E
    have hb : (fun _ ↦ a) ~[dexists 0 (test Set.univ)] Function.update (fun _ ↦ a) 0 b :=
      ⟨_, ⟨b, rfl⟩, rfl, trivial⟩
    rw [← h] at hb
    exact hab (by simpa using congr_fun hb.1 0)

variable {φ ψ}

/-- Fact 4: on tests, equivalence, s-equivalence, and p-equivalence coincide. -/
theorem sEquiv_iff_eq_of_isTest (hφ : IsTest φ) (hψ : IsTest ψ) : SEquiv φ ψ ↔ φ = ψ :=
  ⟨fun h ↦ (hφ.eq_test_dom.trans (congrArg test h)).trans hψ.eq_test_dom.symm, .of_eq⟩

theorem pEquiv_iff_eq_of_isTest (hφ : IsTest φ) (hψ : IsTest ψ) : PEquiv φ ψ ↔ φ = ψ := by
  rw [PEquiv, hφ.cod_eq_dom, hψ.cod_eq_dom]
  exact sEquiv_iff_eq_of_isTest hφ hψ

variable (φ ψ)

/-! ### Some logical facts, section 3.4 -/

/-- Implication and disjunction are definable from negation and conjunction in the usual
way. -/
theorem impl_eq_neg_comp_neg : (φ ⇒ ψ) = ∼(φ ○ ∼ψ) := by
  simp only [neg_eq_compl_dom, dom_comp, dom_test, ← core_compl, compl_compl, impl_eq_core_dom]

theorem disj_eq_neg_comp_neg_neg : (φ ⋎ ψ) = ∼(∼φ ○ ∼ψ) := by
  rw [test_comp_test, neg_test, neg_eq_compl_dom, neg_eq_compl_dom, Set.compl_inter,
    compl_compl, compl_compl, disj_eq_dom_union_dom]

/-- Disjunction is definable from implication, `φ ∨ ψ ≃ ¬φ → ψ`; the converse fails below. -/
theorem disj_eq_neg_impl : (φ ⋎ ψ) = (∼φ ⇒ ψ) := by
  simp only [impl_eq_core_dom, core_test, neg_eq_compl_dom, compl_compl, disj_eq_dom_union_dom]

/-- A negated conjunction is an implication to the negated conjunct. -/
theorem neg_comp : ∼(φ ○ ψ) = (φ ⇒ ∼ψ) := by
  simp only [impl_eq_core_dom, dom_test, neg_eq_compl_dom, core_compl, dom_comp]

/-! #### Closure and double negation, Definition 17 -/

/-- The closure operator is double negation. -/
theorem close_eq_neg_neg : ◇φ = ∼∼φ := by
  rw [neg_test, neg_eq_compl_dom, compl_compl]

/-- Closure fixes exactly the tests. -/
theorem close_eq_self_iff_isTest : ◇φ = φ ↔ IsTest φ :=
  ⟨fun h ↦ h ▸ isTest_test _, fun h ↦ h.eq_test_dom.symm⟩

/-- The restricted law of double negation: `¬¬φ ≃ φ` exactly when `φ` is a test. -/
theorem neg_neg_eq_self_iff_isTest : ∼∼φ = φ ↔ IsTest φ :=
  close_eq_neg_neg φ ▸ close_eq_self_iff_isTest φ

/-- `◇φ ≃ ◇ψ` iff `φ ≃ₛ ψ`: closure retains exactly the truth conditions. -/
theorem close_eq_close_iff_sEquiv : ◇φ = ◇ψ ↔ SEquiv φ ψ := test_inj

theorem neg_close : ∼◇φ = ∼φ := by
  rw [neg_test, neg_eq_compl_dom]

/-- `φ ≃ₛ ¬¬φ`: double negation keeps the truth conditions. -/
theorem sEquiv_neg_neg : SEquiv φ ∼∼φ := by
  rw [SEquiv, ← close_eq_neg_neg, dom_test]

/-- The restricted interdefinability of the constants, stated through closure. -/
theorem close_comp : ◇(φ ○ ψ) = ∼(φ ⇒ ∼ψ) := by
  rw [← neg_comp, ← close_eq_neg_neg]

theorem close_comp_close : (◇φ ○ ◇ψ) = ∼(∼φ ⋎ ∼ψ) := by
  rw [disj_eq_neg_comp_neg_neg, ← close_eq_neg_neg, ← close_eq_neg_neg, ← close_eq_neg_neg]
  exact ((close_eq_self_iff_isTest _).mpr ((isTest_test _).comp (isTest_test _))).symm

theorem close_impl : (◇φ ⇒ ψ) = (∼φ ⋎ ψ) := by
  rw [disj_eq_neg_impl, ← close_eq_neg_neg]

/-! #### Conjunction and disjunction -/

variable {φ ψ} in
/-- Tests commute, and a test is idempotent, under conjunction; conjunction is associative
outright, as `SetRel.comp_assoc`. -/
theorem comp_comm_of_isTest (hφ : IsTest φ) (hψ : IsTest ψ) : φ ○ ψ = ψ ○ φ := by
  rw [hφ.eq_test_dom, hψ.eq_test_dom, test_comp_test, test_comp_test, Set.inter_comm]

variable {φ} in
theorem comp_self_of_isTest (hφ : IsTest φ) : φ ○ φ = φ := by
  rw [hφ.eq_test_dom, test_comp_test, Set.inter_self]

/-- Disjunction, static in both directions, is commutative and associative; its
self-disjunction is the closure of the disjunct. -/
theorem disj_self : (φ ⋎ φ) = ◇φ := by
  rw [disj_eq_dom_union_dom, Set.union_self]

theorem disj_comm : (φ ⋎ ψ) = (ψ ⋎ φ) := by
  rw [disj_eq_dom_union_dom, disj_eq_dom_union_dom, Set.union_comm]

theorem disj_assoc : ((φ ⋎ ψ) ⋎ χ) = (φ ⋎ (ψ ⋎ χ)) := by
  simp only [disj_eq_dom_union_dom, dom_test, Set.union_assoc]

/-- The de Morgan laws DPL validates, the second an instance of distribution when the
disjunct binds nothing in the conjunction. -/
theorem close_comp_disj : ◇(φ ○ (ψ ⋎ χ)) = ((φ ○ ψ) ⋎ (φ ○ χ)) := by
  simp only [dom_comp, dom_test, disj_eq_dom_union_dom, preimage_union]

theorem disj_close_comp : (φ ⋎ (◇ψ ○ χ)) = ((φ ⋎ ψ) ○ (φ ⋎ χ)) := by
  simp only [test_comp_test, disj_eq_dom_union_dom, dom_comp, preimage_test,
    Set.union_inter_distrib_left]

/-! #### Implication -/

/-- Contraposition holds outright for a negated antecedent, and for a closed one against a
negated consequent; the general law needs a binding condition. -/
theorem neg_impl_comm : (∼φ ⇒ ψ) = (∼ψ ⇒ φ) := by
  rw [← disj_eq_neg_impl, ← disj_eq_neg_impl, disj_comm]

theorem close_impl_eq_neg_impl_neg : (◇φ ⇒ ψ) = (∼ψ ⇒ ∼φ) := by
  rw [close_impl, disj_comm, disj_eq_neg_impl]

/-- An implication is a test and turns its consequent into one, and it curries, by
`SetRel.core_comp`. -/
theorem impl_close_right : (φ ⇒ ◇ψ) = (φ ⇒ ψ) := by
  rw [impl_eq_neg_comp_neg, neg_close, ← impl_eq_neg_comp_neg]

theorem impl_impl : (φ ⇒ (ψ ⇒ χ)) = ((φ ○ ψ) ⇒ χ) := by
  simp only [impl_eq_core_dom, dom_test, core_comp]

/-! #### Quantifiers and connectives

The existential is the random reset composed with its scope and the universal is implication
from the reset, so the quantifier laws are the propositional ones at the reset and hold over
any register structure. -/

section Quantifiers

variable {R S E : Type*} [RegisterStructure R S E] (x : R) (φ ψ : Update S)

/-- The universal is definable from negation and the existential, and `¬∃xφ ≃ ∀x¬φ` holds
unconditionally, negation turning anything into a test. -/
theorem forall_eq_neg_exists_neg : test (dforall x φ) = ∼(dexists x ∼φ) :=
  impl_eq_neg_comp_neg _ _

theorem neg_exists_eq_forall_neg : ∼(dexists x φ) = test (dforall x ∼φ) :=
  neg_comp _ _

theorem close_exists : ◇(dexists x φ) = ∼(test (dforall x ∼φ)) := by
  rw [close_eq_neg_neg, neg_exists_eq_forall_neg]

/-- Scope extension, `∃xφ ∧ ψ ≃ ∃x[φ ∧ ψ]`: the binding power of the existential extends
without limit to the right, which is what represents anaphora across sentences. It is the
associativity of composition. -/
theorem scope_extension : dexists x φ ○ ψ = dexists x (φ ○ ψ) :=
  comp_assoc ..

/-- The donkey equivalence, `∃xφ → ψ ≃ ∀x[φ → ψ]`: an existential in an antecedent binds
into the consequent with universal force. It is the currying of implication. -/
theorem donkey_equivalence : (dexists x φ ⇒ ψ) = test (dforall x (φ ⇒ ψ)) :=
  (impl_impl _ _ _).symm

end Quantifiers

/-! #### What the static constants cannot define -/

section Assignments

variable {E : Type*} (x : ℕ) (φ ψ : Update (Assignment E))

/-- An existential is a test only over a contradictory scope, given two individuals to reset
between: this is why the externally dynamic constants are not definable from the universal
and a static connective. -/
theorem isTest_dexists_iff [Nontrivial E] : IsTest (dexists x φ) ↔ Contradiction φ := by
  refine ⟨fun h g ⟨k, hφ⟩ ↦ ?_, fun hc ⟨_, _⟩ ⟨_, _, hφ⟩ ↦ (hc _ ⟨_, hφ⟩).elim⟩
  obtain ⟨e, he⟩ := exists_ne (g x)
  have hg (e' : E) : Function.update g x e' = k := h.eq ⟨g, ⟨g x, by simp⟩, hφ⟩
  exact he (by simpa using congr_fun ((hg e).trans (hg (g x)).symm) x)

/-- `∃xφ ≃ ¬∀x¬φ` exactly when `∃xφ` is a test, so only over a contradictory scope; the two
are always s-equivalent. -/
theorem exists_eq_neg_forall_neg_iff [Nontrivial E] :
    dexists x φ = ∼(test (dforall x ∼φ)) ↔ Contradiction φ := by
  rw [← isTest_dexists_iff, ← close_exists, eq_comm, close_eq_self_iff_isTest]

theorem sEquiv_exists_neg_forall_neg : SEquiv (dexists x φ) ∼(test (dforall x ∼φ)) := by
  rw [SEquiv, ← close_exists, dom_test]

/-- `φ ∧ ψ ≃ ¬[φ → ¬ψ]` exactly when `φ ∧ ψ` is a test; the two are always s-equivalent. -/
theorem comp_eq_neg_impl_neg_iff {S : Type*} (φ ψ : Update S) :
    φ ○ ψ = ∼(φ ⇒ ∼ψ) ↔ IsTest (φ ○ ψ) := by
  rw [← close_comp, eq_comm, close_eq_self_iff_isTest]

theorem sEquiv_comp_neg_impl_neg {S : Type*} (φ ψ : Update S) :
    SEquiv (φ ○ ψ) ∼(φ ⇒ ∼ψ) := by
  rw [SEquiv, ← close_comp, dom_test]

/-- The restricted law of double negation fails for the existential unless its scope is
contradictory; so a doubly negated indefinite licenses no anaphora. -/
theorem neg_neg_exists_eq_iff [Nontrivial E] :
    ∼∼(dexists x φ) = dexists x φ ↔ Contradiction φ :=
  (neg_neg_eq_self_iff_isTest _).trans (isTest_dexists_iff x φ)

theorem dne_fails_anaphora [Nontrivial E] :
    ∃ (x : ℕ) (φ : Update (Assignment E)), ∼∼(dexists x φ) ≠ dexists x φ :=
  ⟨0, test Set.univ, fun h ↦
    (neg_neg_exists_eq_iff 0 _).mp h (fun _ ↦ Classical.arbitrary E) ⟨_, rfl, trivial⟩⟩

/-- Disjunction, being internally static, does not define conjunction or implication even up
to truth conditions: `φ ∧ ψ ≄ₛ ¬[¬φ ∨ ¬ψ]` and `φ → ψ ≄ₛ ¬φ ∨ ψ`, with `P` and `Q` true of one
individual and `φ` the existential `∃xPx`. -/
theorem not_sEquiv_comp_neg_disj_neg [Nontrivial E] :
    ∃ φ ψ : Update (Assignment E), ¬ SEquiv (φ ○ ψ) ∼(∼φ ⋎ ∼ψ) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨dexists 0 (test {g | g 0 = a}), test {g | g 0 = a}, fun h ↦ ?_⟩
  have hb : (fun _ ↦ b) ∈ (dexists 0 (test {g | g 0 = a}) ○ test {g | g 0 = a}).dom :=
    ⟨_, _, ⟨_, ⟨a, rfl⟩, rfl, by simp⟩, rfl, by simp⟩
  rw [h, dom_test, neg_test, disj_eq_dom_union_dom, dom_test, dom_test, neg_test] at hb
  exact hb (.inr fun hba ↦ hab (by simpa using hba.symm))

theorem not_sEquiv_impl_neg_disj [Nontrivial E] :
    ∃ φ ψ : Update (Assignment E), ¬ SEquiv (φ ⇒ ψ) (∼φ ⋎ ψ) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨dexists 0 (test {g | g 0 = a}), test {g | g 0 = a}, fun h ↦ ?_⟩
  have hb : (fun _ ↦ b) ∈ (dexists 0 (test {g | g 0 = a}) ⇒ test {g | g 0 = a}).dom := by
    rw [dom_test]
    rintro _ ⟨_, -, rfl, hd⟩
    exact ⟨_, rfl, hd⟩
  rw [h, dom_test] at hb
  obtain ⟨_, -, hn⟩ | ⟨_, rfl, hb⟩ := hb
  · exact hn ⟨_, _, ⟨a, rfl⟩, rfl, by simp⟩
  · exact hab (by simpa using hb.symm)

/-- Conjunction is neither commutative nor idempotent in general: `∃xPx ∧ Qx` differs from
`Qx ∧ ∃xPx`, and the latter from its self-conjunction, binding being left to right. -/
theorem comp_not_comm [Nontrivial E] : ∃ φ ψ : Update (Assignment E), φ ○ ψ ≠ ψ ○ φ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨dexists 0 (test Set.univ), test {g | g 0 = a}, fun h ↦ ?_⟩
  have hb : (fun _ ↦ b) ~[dexists 0 (test Set.univ) ○ test {g | g 0 = a}]
      Function.update (fun _ ↦ b) 0 a :=
    ⟨_, ⟨_, ⟨a, rfl⟩, rfl, trivial⟩, rfl, by simp⟩
  rw [h] at hb
  obtain ⟨_, ⟨rfl, hb⟩, -⟩ := hb
  exact hab (by simpa using hb.symm)

theorem comp_not_idem [Nontrivial E] : ∃ φ : Update (Assignment E), φ ○ φ ≠ φ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨test {g | g 0 = a} ○ dexists 0 (test {g | g 0 = b}), fun h ↦ ?_⟩
  have hb : (fun _ ↦ a) ~[test {g | g 0 = a} ○ dexists 0 (test {g | g 0 = b})]
      Function.update (fun _ ↦ a) 0 b :=
    ⟨_, ⟨rfl, rfl⟩, _, ⟨b, rfl⟩, rfl, by simp⟩
  rw [← h] at hb
  obtain ⟨_, ⟨_, -, _, -, rfl, hd⟩, _, ⟨rfl, hk⟩, -⟩ := hb
  exact hab (hk.symm.trans hd)

end Assignments

/-! ### Entailment, section 3.5 -/

/-- s-entailment, Definition 18: truth is preserved from premiss to conclusion. -/
def SEntails : Prop := φ.dom ⊆ ψ.dom

/-- Dynamic entailment, Definition 20: every output of the premiss is an input on which the
conclusion succeeds. -/
def Entails : Prop := φ.cod ⊆ ψ.dom

variable {φ ψ} in
/-- Fact 10: meaning inclusion, Definition 19, which is `⊆` on relations, implies
s-entailment; the converse fails, as `∃xPx ⊨ₛ ∃xPx → Px` with `∃xPx ⊈ Px` shows. -/
theorem SEntails.of_subset (h : φ ⊆ ψ) : SEntails φ ψ :=
  fun _ ⟨k, hk⟩ ↦ ⟨k, h hk⟩

/-- Fact 11, the deduction theorem: `φ ⊨ ψ` iff `φ → ψ` is valid. -/
theorem entails_iff_valid_impl : Entails φ ψ ↔ Valid (φ ⇒ ψ) := by
  simp only [Valid, dom_test]
  exact ⟨fun h _ _ hk ↦ h ⟨_, hk⟩, fun h _ ⟨g, hk⟩ ↦ h g hk⟩

/-- Fact 12: s-entailment is dynamic entailment from the closed premiss. -/
theorem sEntails_iff_entails_close : SEntails φ ψ ↔ Entails ◇φ ψ := by
  rw [Entails, cod_test, SEntails]

/-- A closed or doubly negated formula entails the formula. -/
theorem entails_close_self : Entails ◇φ φ :=
  (sEntails_iff_entails_close φ φ).mp subset_rfl

theorem entails_neg_neg_self : Entails ∼∼φ φ :=
  close_eq_neg_neg φ ▸ entails_close_self φ

section Assignments

variable {E : Type*} (x : ℕ)

/-- `∃xPx ⊨ Px`, the paper's *A man came in wearing a hat. So, he wore a hat*: the premiss's
output binds the free variable of the conclusion. -/
theorem entails_exists_atom (p : E → Prop) :
    Entails (dexists x (test {g : Assignment E | p (g x)})) (test {g | p (g x)}) := by
  rintro _ ⟨_, _, -, rfl, hp⟩
  exact ⟨_, rfl, hp⟩

/-- `Px ⊨ ∃xPx` as well, so the two entail each other yet are not equivalent, the atom being
a test and the existential not: mutual entailment is weaker than equivalence. -/
theorem entails_atom_exists (p : E → Prop) :
    Entails (test {g : Assignment E | p (g x)}) (dexists x (test {g | p (g x)})) := by
  rintro _ ⟨h, rfl, hp⟩
  exact ⟨h, h, ⟨h x, (Function.update_eq_self x h).symm⟩, rfl, hp⟩

/-- `∃xPx ⊭ₛ Px`: s-entailment sees no binding from premiss to conclusion. -/
theorem not_sEntails_exists_atom [Nontrivial E] :
    ∃ p : E → Prop, ¬ SEntails (dexists 0 (test {g : Assignment E | p (g 0)}))
      (test {g | p (g 0)}) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(· = a), fun h ↦ ?_⟩
  obtain ⟨_, rfl, hb⟩ := h (a := fun _ ↦ b) ⟨_, _, ⟨a, rfl⟩, rfl, by simp⟩
  exact hab (by simpa using hb.symm)

/-- Dynamic entailment is not reflexive: `Px ∧ ∃xQx` does not entail itself, its outputs
having forgotten that the input satisfied `Px`. Fact 15 restores reflexivity when no active
quantifier of the formula binds a free variable of it. -/
theorem not_entails_self [Nontrivial E] : ∃ φ : Update (Assignment E), ¬ Entails φ φ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨test {g | g 0 = a} ○ dexists 0 (test Set.univ), fun h ↦ ?_⟩
  have hb : (fun _ ↦ a) ~[test {g | g 0 = a} ○ dexists 0 (test Set.univ)]
      Function.update (fun _ ↦ a) 0 b :=
    ⟨_, ⟨rfl, rfl⟩, _, ⟨b, rfl⟩, rfl, trivial⟩
  obtain ⟨_, _, ⟨rfl, hb⟩, -⟩ := h ⟨_, hb⟩
  exact hab (by simpa using hb.symm)

/-- Dynamic entailment is not transitive: `¬¬∃xPx ⊨ ∃xPx` and `∃xPx ⊨ Px`, but `¬¬∃xPx ⊭ Px`,
the doubly negated premiss binding nothing. Fact 16 restores transitivity when the premiss
fixes every variable the middle formula binds in the conclusion. -/
theorem not_entails_trans [Nontrivial E] :
    ∃ p : E → Prop, ¬ Entails ∼∼(dexists 0 (test {g : Assignment E | p (g 0)}))
      (test {g | p (g 0)}) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(· = a), fun h ↦ ?_⟩
  rw [← close_eq_neg_neg, ← sEntails_iff_entails_close] at h
  obtain ⟨_, rfl, hb⟩ := h (a := fun _ ↦ b) ⟨_, _, ⟨a, rfl⟩, rfl, by simp⟩
  exact hab (by simpa using hb.symm)

/-- Nor is it monotone in its premisses: `∃xPx ⊨ Px`, but a further premiss `∃xQx` resets
the binding, `∃xPx, ∃xQx ⊭ Px`, a sequence of premisses being their conjunction. -/
theorem not_entails_comp_exists [Nontrivial E] :
    ∃ p : E → Prop, ¬ Entails (dexists 0 (test {g : Assignment E | p (g 0)}) ○
      dexists 0 (test Set.univ)) (test {g | p (g 0)}) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(· = a), fun h ↦ ?_⟩
  have hc : (fun _ ↦ b) ~[dexists 0 (test {g : Assignment E | g 0 = a}) ○
      dexists 0 (test Set.univ)] fun _ ↦ b :=
    ⟨_, ⟨_, ⟨a, rfl⟩, rfl, by simp⟩, _, ⟨b, by simp⟩, rfl, trivial⟩
  obtain ⟨_, rfl, hb⟩ := h ⟨_, hc⟩
  exact hab (by simpa using hb.symm)

end Assignments

end GroenendijkStokhof1991
