import Linglib.Core.Logic.CylindricAlgebra
import Linglib.Semantics.Dynamic.DPL
import Linglib.Semantics.Dynamic.Transition

/-!
# Groenendijk & Stokhof (1991): Dynamic Predicate Logic
[groenendijk-stokhof-1991]

Dynamic Predicate Logic. *Linguistics and Philosophy* 14(1): 39–100.
The DPL substrate (`DPLRel`, Definition 2) lives in
`Semantics/Dynamic/DPL.lean`; this file proves the paper's claims about
it.

## Main results

- `scope_extension`, `donkey_equivalence`: the two central equivalences —
  existentials bind across conjunction (`∃xφ ∧ ψ ≃ ∃x[φ ∧ ψ]`), and get
  universal force in conditional antecedents (`∃xφ → ψ ≃ ∀x[φ → ψ]`),
  both unconditional (they are the normal-binding-form equivalences of
  Fact 17, §3.6).
- Blocking (§2.5): `neg`, `impl`, `disj`, `forall_` are tests — no
  binding escapes.
- §3.4's logical facts: `conj_assoc`, `conj_not_comm`,
  `close_eq_neg_neg` (`♦φ ≃ ¬¬φ`), the restricted double-negation law
  `neg_neg_eq_self_iff_isTest` (`¬¬φ ≃ φ` iff `φ` is a test), its
  anaphoric consequence `dne_fails_anaphora`, and the
  interdefinability of `→`, `∨`, `∀` from `¬`, `∧`, `∃`.
- `closure_exists_eq_cylindrify` and friends: the satisfaction-set
  computations from Fact 19's proof (§3.6), in cylindric-algebra
  vocabulary.
- The indexed reading: DPL's generators as context-extension arrows
  (`testTransition`, `Transition.randomAssign`), with clause 4 as
  transition composition and clause 7 factoring through the
  random-assignment arrow.
-/

namespace GroenendijkStokhof1991

open DPL

/-! ### Scope extension (§2.1, §2.3) -/

/-! "A man walks in the park. He whistles."

DPL translation: `∃x[man(x) ∧ walk(x)] ∧ whistle(x)`. Scope extension
makes this equal to `∃x[man(x) ∧ walk(x) ∧ whistle(x)]`: the
existential binds across conjunction, unconditionally — a later conjunct
with free `x` is simply captured. This accounts for
`Heim1982.Examples.indefinite_persists`. -/

variable {E : Type*}

/-- Scope extension: `∃xφ ∧ ψ ≃ ∃x[φ ∧ ψ]` — one of the four
normal-binding-form equivalences in Fact 17's proof (§3.6), and the
formal content of cross-sentential anaphora (§2.1). -/
theorem scope_extension (x : ℕ) (φ ψ : DPLRel E) :
    DPLRel.exists_ x (DPLRel.conj φ ψ) = DPLRel.conj (DPLRel.exists_ x φ) ψ := by
  funext g h
  simp only [DPLRel.exists_, DPLRel.conj, eq_iff_iff]
  exact ⟨fun ⟨d, k, hφ, hψ⟩ => ⟨k, ⟨d, hφ⟩, hψ⟩,
    fun ⟨k, ⟨d, hφ⟩, hψ⟩ => ⟨d, k, hφ, hψ⟩⟩

/-! ### Donkey sentences (§2.4) -/

/-! "If a farmer owns a donkey, he beats it."

DPL translation: `∃x[farmer(x) ∧ ∃y[donkey(y) ∧ own(x,y)]] → beat(x,y)`.
By `donkey_equivalence` (twice), this equals
`∀x∀y[farmer(x) ∧ donkey(y) ∧ own(x,y) → beat(x,y)]` — the universal
"strong" reading recorded for `Geach1962.Examples.donkey_classic` and
`Heim1982.Examples.conditional_donkey`. -/

/-- The donkey equivalence: `∃xφ → ψ ≃ ∀x[φ → ψ]`. An existential in the
antecedent of an implication has universal force — donkey sentences are
compositional without stipulating wide-scope `∀`. -/
theorem donkey_equivalence (x : ℕ) (φ ψ : DPLRel E) :
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

/-- `¬∃xφ ≃ ∀x¬φ`: negation commutes with the quantifier switch, since
negation turns anything into a test. -/
theorem neg_exists_eq_forall_neg (x : ℕ) (φ : DPLRel E) :
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

/-! ### Blocking: the externally static constants (§2.5) -/

/-! "Every man walked in. *He sat down." / "John didn't see a bird.
*It was singing."

Negation, implication, disjunction, and the universal are *tests*: they
force output = input, so no binding escapes them. This accounts for
`Heim1982.Examples.universal_blocks`, `standard_negation_blocks`, and
`conditional_antecedent`. -/

open DynamicSemantics (IsTest) in
/-- Negation is a test. -/
theorem neg_isTest (φ : DPLRel E) : DynamicSemantics.Update.IsTest (toDRS (DPLRel.neg φ)) :=
  fun _ _ hn => hn.1

open DynamicSemantics (IsTest) in
/-- Implication is a test: antecedent bindings do not escape. -/
theorem impl_isTest (φ ψ : DPLRel E) : DynamicSemantics.Update.IsTest (toDRS (DPLRel.impl φ ψ)) :=
  fun _ _ hi => hi.1

open DynamicSemantics (IsTest) in
/-- Disjunction is a test: no anaphora across or out of disjuncts. -/
theorem disj_isTest (φ ψ : DPLRel E) : DynamicSemantics.Update.IsTest (toDRS (DPLRel.disj φ ψ)) :=
  fun _ _ hd => hd.1

open DynamicSemantics (IsTest) in
/-- The universal quantifier is a test: it introduces no referents. -/
theorem forall_isTest (x : ℕ) (φ : DPLRel E) : DynamicSemantics.Update.IsTest (toDRS (DPLRel.forall_ x φ)) :=
  fun _ _ hfa => hfa.1

/-! ### Logical facts (§3.4) -/

/-- Conjunction is associative — despite the increased binding power of
the existential (§3.4). -/
theorem conj_assoc (φ ψ χ : DPLRel E) :
    DPLRel.conj (DPLRel.conj φ ψ) χ = DPLRel.conj φ (DPLRel.conj ψ χ) := by
  funext g h
  simp only [DPLRel.conj, eq_iff_iff]
  exact ⟨fun ⟨k, ⟨j, hj, hjk⟩, hk⟩ => ⟨j, hj, k, hjk, hk⟩,
    fun ⟨j, hj, k, hjk, hk⟩ => ⟨k, ⟨j, hj, hjk⟩, hk⟩⟩

/-- Conjunction is not commutative: binding is left-to-right (§3.4). -/
theorem conj_not_comm [Nontrivial E] :
    ∃ (φ ψ : DPLRel E), DPLRel.conj φ ψ ≠ DPLRel.conj ψ φ := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  refine ⟨DPLRel.exists_ 0 (fun g h => g = h),
    DPLRel.atom (fun g => g 0 = e₁), fun heq => ?_⟩
  have hfwd : (DPLRel.conj (DPLRel.exists_ 0 (fun g h => g = h))
      (DPLRel.atom (fun g => g 0 = e₁))) (fun _ => e₂)
      (fun n => if n = 0 then e₁ else e₂) := by
    refine ⟨fun n => if n = 0 then e₁ else e₂, ⟨e₁, ?_⟩, rfl, ?_⟩
    · funext n; simp
    · simp
  rw [heq] at hfwd
  obtain ⟨k, ⟨rfl, hk0⟩, -⟩ := hfwd
  simp at hk0
  exact hne hk0.symm

/-- `♦φ ≃ ¬¬φ`: closure is double negation (§3.4). -/
theorem close_eq_neg_neg (φ : DPLRel E) :
    DPLRel.close φ = DPLRel.neg (DPLRel.neg φ) := by
  funext g h
  simp only [DPLRel.close, DPLRel.neg, eq_iff_iff]
  constructor
  · rintro ⟨rfl, k, hφ⟩
    exact ⟨rfl, fun ⟨_, rfl, hneg⟩ => hneg ⟨k, hφ⟩⟩
  · rintro ⟨rfl, hneg⟩
    exact ⟨rfl, by_contra fun hne => hneg ⟨g, rfl, hne⟩⟩

/-- Closure fixes exactly the tests: `♦φ ≃ φ` iff `φ` is a test (§3.4). -/
theorem close_eq_self_iff_isTest (φ : DPLRel E) :
    DPLRel.close φ = φ ↔ ∀ g h, φ g h → g = h := by
  constructor
  · intro h g k hφ
    rw [← h] at hφ
    exact hφ.1
  · intro htest
    funext g h
    simp only [DPLRel.close, eq_iff_iff]
    constructor
    · rintro ⟨rfl, k, hk⟩
      obtain rfl := htest g k hk
      exact hk
    · exact fun hφ => ⟨htest g h hφ, h, hφ⟩

/-- The paper's restricted double-negation law (§3.4): `¬¬φ ≃ φ` exactly
when `φ` is a test. -/
theorem neg_neg_eq_self_iff_isTest (φ : DPLRel E) :
    DPLRel.neg (DPLRel.neg φ) = φ ↔ ∀ g h, φ g h → g = h :=
  close_eq_neg_neg φ ▸ close_eq_self_iff_isTest φ

/-- DNE fails for anaphora: `¬¬∃xφ ≠ ∃xφ`, since the existential is not
a test. The anaphoric consequence — doubly negated indefinites should
not license anaphora — underpredicts
(`ElliottSudo2025.Examples.double_negation` is acceptable); the
divergence theorem lives with the comparing paper, in
`Studies/ElliottSudo2025.lean`. -/
theorem dne_fails_anaphora [Nontrivial E] :
    ∃ (x : ℕ) (φ : DPLRel E),
      DPLRel.neg (DPLRel.neg (DPLRel.exists_ x φ)) ≠ DPLRel.exists_ x φ := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  refine ⟨0, fun g h => g = h, fun heq => ?_⟩
  have hrhs : (DPLRel.exists_ 0 (fun (g h : ℕ → E) => g = h))
      (fun _ => e₁) (fun n => if n = 0 then e₂ else e₁) :=
    ⟨e₂, rfl⟩
  rw [← heq] at hrhs
  have h_eq := congr_fun hrhs.1 0
  simp at h_eq
  exact hne h_eq

/-! ### Interdefinability (§3.4)

`→`, `∨`, `∀` are definable from `¬`, `∧`, `∃` — but not conversely:
the latter contains the only externally dynamic constants
(`conj_not_comm` separates `∧` from any test). -/

/-- `φ → ψ ≃ ¬[φ ∧ ¬ψ]`. -/
theorem impl_interdefinable (φ ψ : DPLRel E) :
    DPLRel.impl φ ψ = DPLRel.neg (DPLRel.conj φ (DPLRel.neg ψ)) := by
  funext g h
  simp only [DPLRel.impl, DPLRel.neg, DPLRel.conj, eq_iff_iff]
  constructor
  · rintro ⟨rfl, hall⟩
    refine ⟨rfl, fun ⟨k, m, hφ, hmk, hnψ⟩ => ?_⟩
    subst hmk; exact hnψ (hall m hφ)
  · rintro ⟨rfl, hneg⟩
    exact ⟨rfl, fun k hφ => by_contra fun hne => hneg ⟨k, k, hφ, rfl, hne⟩⟩

/-- `φ ∨ ψ ≃ ¬[¬φ ∧ ¬ψ]`. -/
theorem disj_interdefinable (φ ψ : DPLRel E) :
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
    push Not at hne
    exact hneg ⟨g, g, ⟨rfl, fun ⟨j, hφ⟩ => (hne j).1 hφ⟩,
      rfl, fun ⟨j, hψ⟩ => (hne j).2 hψ⟩

/-- `∀xφ ≃ ¬∃x¬φ`. -/
theorem forall_interdefinable (x : ℕ) (φ : DPLRel E) :
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

/-! ### Equivalence notions and conditions (§3.2, §3.4) -/

section Metatheory

open DynamicSemantics

/-- s-equivalence (Definition 7) at a fixed model: same satisfaction
set. The paper quantifies over models; `DPLRel` fixes one. -/
def sEquiv (φ ψ : DPLRel E) : Prop :=
  φ.satisfactionSet = ψ.satisfactionSet

/-- p-equivalence (Definition 10): same production set. -/
def pEquiv (φ ψ : DPLRel E) : Prop :=
  φ.productionSet = ψ.productionSet

/-- Facts 1–2: equivalence implies s-equivalence and p-equivalence. -/
theorem sEquiv_of_eq {φ ψ : DPLRel E} (h : φ = ψ) : sEquiv φ ψ := h ▸ rfl

theorem pEquiv_of_eq {φ ψ : DPLRel E} (h : φ = ψ) : pEquiv φ ψ := h ▸ rfl

/-- Fact 3: joint s- and p-equivalence does not imply equivalence — the
trivial test and the total relation agree on both sets. -/
theorem sEquiv_pEquiv_ne [Nontrivial E] :
    ∃ φ ψ : DPLRel E, sEquiv φ ψ ∧ pEquiv φ ψ ∧ φ ≠ ψ := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  refine ⟨DPLRel.atom (fun _ => True), fun _ _ => True, ?_, ?_, fun heq => ?_⟩
  · ext g
    simp [DPLRel.satisfactionSet, DPLRel.atom]
  · ext h
    simp [DPLRel.productionSet, DPLRel.atom]
  · have h2 : DPLRel.atom (fun _ => True) (fun _ => e₁) (fun _ => e₂) := by
      rw [heq]; trivial
    exact hne (congr_fun h2.1 0)

/-- Definition 12's semantic core, clause 2: a conjunction of tests is a
test. With the static constants (`neg_isTest`, ..., Fact 5) this closes
the conditions under the semantics. -/
theorem conj_isTest {φ ψ : DPLRel E} (hφ : DynamicSemantics.Update.IsTest (toDRS φ))
    (hψ : DynamicSemantics.Update.IsTest (toDRS ψ)) : DynamicSemantics.Update.IsTest (toDRS (DPLRel.conj φ ψ)) :=
  fun _ _ ⟨_, h1, h2⟩ => (hφ h1).trans (hψ h2)

/-- Fact 4: for tests, s-equivalence coincides with equivalence — a test
is determined by its truth conditions (`IsTest.eq_test_closure`, the
semantic form of Fact 6). -/
theorem sEquiv_iff_eq_of_isTest {φ ψ : DPLRel E}
    (hφ : DynamicSemantics.Update.IsTest (toDRS φ)) (hψ : DynamicSemantics.Update.IsTest (toDRS ψ)) :
    sEquiv φ ψ ↔ φ = ψ := by
  refine ⟨fun h => ?_, sEquiv_of_eq⟩
  have hc : closure (toDRS φ) = closure (toDRS ψ) :=
    funext fun g => congrArg (fun s => g ∈ s) h
  have h1 := hφ.eq_test_closure
  rw [hc] at h1
  exact h1.trans hψ.eq_test_closure.symm

/-! ### Entailment (§3.5)

Dynamic entailment (Definition 20) is the generic
`DynamicSemantics.entails`; s-entailment (Definition 18) is
`sEntails`, and meaning inclusion implies it (`sEntails_of_subset`,
Fact 10). Facts 13–16 — the restricted reflexivity and transitivity
laws — carry syntactic `AQV/FV` side conditions and await the syntax
stratum. -/

/-- The deduction theorem (Fact 11): `φ ⊨ ψ` iff `⊨ φ → ψ` — DPL
implication is the test of dynamic implication, so this is the generic
deduction theorem read through the Ty2 embedding. -/
theorem deduction (φ ψ : DPLRel E) :
    (toDRS φ ⊨ toDRS ψ) ↔ valid (toDRS (DPLRel.impl φ ψ)) := by
  rw [impl_eq_test_dimpl]
  exact entails_iff_valid_test_dimpl (toDRS φ) (toDRS ψ)

/-- Fact 12: s-entailment is dynamic entailment from the closed premiss
`♦φ`. -/
theorem sEntails_iff_close_entails (φ ψ : DPLRel E) :
    (toDRS φ ⊨ₛ toDRS ψ) ↔ (toDRS (DPLRel.close φ) ⊨ toDRS ψ) := by
  rw [close_eq_test_closure]
  exact sEntails_iff_test_closure_entails (toDRS φ) (toDRS ψ)

/-- The flagship dynamic entailment (§3.5): `∃xPx ⊨ Px` — the premiss's
output binds the conclusion's free variable ("A man came in. So, he wore
a hat."). Not an s-entailment. -/
theorem exists_atom_entails_atom (x : ℕ) (p : E → Prop) :
    toDRS (DPLRel.exists_ x (DPLRel.atom fun g => p (g x)))
      ⊨ toDRS (DPLRel.atom fun g => p (g x)) := by
  rintro g h ⟨d, rfl, hp⟩
  exact ⟨_, rfl, hp⟩

/-- Conversely `Px ⊨ ∃xPx` — so the pair entail each other, yet are not
equivalent (the atom is a test, the existential is not): mutual dynamic
entailment is weaker than equivalence (§3.5). -/
theorem atom_entails_exists (x : ℕ) (p : E → Prop) :
    toDRS (DPLRel.atom fun g => p (g x))
      ⊨ toDRS (DPLRel.exists_ x (DPLRel.atom fun g => p (g x))) := by
  rintro g h ⟨rfl, hp⟩
  exact ⟨_, g x, rfl, by simpa using hp⟩

/-- Dynamic entailment is not reflexive (§3.5): `Px ∧ ∃xQx` does not
entail itself — its outputs forget that the input satisfied `Px`. The
restricted law (Fact 15) needs `AQV(φ) ∩ FV(φ) = ∅`. -/
theorem entails_not_refl [Nontrivial E] :
    ∃ φ : DPLRel E, ¬(toDRS φ ⊨ toDRS φ) := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  refine ⟨DPLRel.conj (DPLRel.atom fun g => g 0 = e₁)
    (DPLRel.exists_ 0 (DPLRel.atom fun _ => True)), fun h => ?_⟩
  have hstep : (DPLRel.conj (DPLRel.atom fun g => g 0 = e₁)
      (DPLRel.exists_ 0 (DPLRel.atom fun _ => True)))
      (fun _ => e₁) (fun n => if n = 0 then e₂ else e₁) :=
    ⟨fun _ => e₁, ⟨rfl, rfl⟩, e₂, rfl, trivial⟩
  obtain ⟨k, m, ⟨-, h0⟩, -⟩ := h _ _ hstep
  simp only [reduceIte] at h0
  exact hne h0.symm

end Metatheory

/-! ### Satisfaction sets and PL (§3.6) -/

/-! Fact 19 (§3.6) relates DPL to PL through satisfaction sets: for
formulas in normal binding form, `\φ\` is the PL meaning. Its proof
computes `\∃xψ\ = {g | ∃k: k[x]g ∧ k ∈ \ψ\}` — cylindrification of the
satisfaction set. Under `closure` (`= satisfactionSet`, Definition 6)
these computations are algebraic identities in the cylindric set algebra
([henkin-monk-tarski-1971]). -/

section SatisfactionSets

open Core.CylindricAlgebra
open Core (Assignment)
open DynamicSemantics (closure)

/-- **DPL existential = cylindrification**: `\∃xφ\ = cₓ\φ\` — the
existential case of Fact 19's computation. -/
theorem closure_exists_eq_cylindrify (x : ℕ) (φ : DPLRel E) :
    closure (toDRS (DPLRel.exists_ x φ)) =
    cylindrify x (closure (toDRS φ)) := by
  have hup : ∀ (g : Assignment E) (d : E),
      (fun n => if n = x then d else g n) = Function.update g x d := fun g d => by
    funext n; simp [Function.update_apply]
  ext g; simp only [closure, toDRS, DPLRel.exists_, cylindrify]
  exact ⟨fun ⟨h, d, hφ⟩ => ⟨d, h, hup g d ▸ hφ⟩,
         fun ⟨d, h, hφ⟩ => ⟨h, d, (hup g d).symm ▸ hφ⟩⟩

/-- **DPL identity test = diagonal element**: `\x = y\ = Dxy`. -/
theorem closure_identity_eq_diagonal (x y : Nat) :
    closure (toDRS (DPLRel.atom (fun g : Assignment E => g x = g y))) =
    @diagonal E x y := by
  ext g; simp only [closure, toDRS, DPLRel.atom, diagonal]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨g, rfl, h⟩⟩

/-- DPL negation complements the satisfaction set: `\¬φ\ = ∁\φ\`. -/
theorem closure_neg_eq (φ : DPLRel E) :
    closure (toDRS (DPLRel.neg φ)) =
    fun g => ¬ closure (toDRS φ) g := by
  ext g; simp only [closure, toDRS, DPLRel.neg]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨g, rfl, h⟩⟩

end SatisfactionSets

/-! ### The indexed reading: DPL generators as context extension -/

/-! DPL meanings are relations on total assignments (Definition 2); the
indexed substrate (`Transition.lean`) types them by the contexts they read
and write. The two generators land as arrows: tests (clauses 1–3, 5, 6, 8
are all of this shape) become `testTransition`s `X ⟶ X`, and the random
reset of clause 7 is `Transition.randomAssign : X ⟶ insert x X`.
Sequencing is clause 4 (`rel_comp_iff_conj`), and the existential factors
as random assignment composed with its scope
(`rel_randomAssign_comp_iff_exists`) — so a DPL formula's indexed meaning is
a composite of the generating arrows of `DynamicSemantics.Ctx`. -/

section IndexedReading

open DynamicSemantics

variable {W : Type*} {X Y : Finset ℕ}

/-- A DPL test as a transition: a condition supported on the context,
checked without changing the assignment. Clauses 1–3, 5, 6, and 8 of
Definition 2 are all of this form. -/
def testTransition (X : Finset ℕ) (C : (ℕ → E) → Prop)
    (hC : DependsOn C ↑X) : Transition W E X X where
  rel _ f h := Set.EqOn f h ↑X ∧ C f
  grow := subset_rfl
  supported_left _ _ _ _ hff' :=
    and_congr ⟨(hff'.symm.trans ·), (hff'.trans ·)⟩ (iff_of_eq (hC hff'))
  supported_right _ _ _ _ hgg' :=
    and_congr ⟨(·.trans hgg'), (·.trans hgg'.symm)⟩ Iff.rfl

/-- Applying a test at a state indexed below its context filters the
carrier — the indexed form of Definition 2's test clauses. -/
theorem mem_testTransition_apply {C : (ℕ → E) → Prop} {hC : DependsOn C ↑X}
    {I : State W ℕ E} (hbase : I.base ⊆ X) {w : W} {g : ℕ → E} :
    (⟨w, g⟩ : Possibility W ℕ E) ∈ (testTransition X C hC).apply I ↔
      (⟨w, g⟩ : Possibility W ℕ E) ∈ I ∧ C g := by
  rw [Transition.mem_apply]
  constructor
  · rintro ⟨f, hf, hfg, hCf⟩
    exact ⟨(I.supported.mem_iff (hfg.mono (Finset.coe_subset.mpr hbase))).mp hf,
      (hC hfg) ▸ hCf⟩
  · rintro ⟨hg, hCg⟩
    exact ⟨g, hg, Set.eqOn_refl g _, hCg⟩

/-- Clause 4 is transition composition: if `u` and `v` realize `φ` and
`ψ` world-pointwise, their composite realizes `φ ∧ ψ`. -/
theorem rel_comp_iff_conj {Z : Finset ℕ} {u : Transition W E X Y}
    {v : Transition W E Y Z} {φ ψ : DPLRel E}
    (hu : ∀ w f h, u.rel w f h ↔ φ f h) (hv : ∀ w f h, v.rel w f h ↔ ψ f h)
    (w : W) (f h : ℕ → E) :
    (u.comp v).rel w f h ↔ DPLRel.conj φ ψ f h :=
  exists_congr fun k => and_congr (hu w f k) (hv w k h)

/-- Clause 7 factors through the category: the existential is the
random-assignment arrow composed with its scope. The scope's transition
reads only `insert x X`, which is what lets the reset's underspecification
off `x` collapse to Definition 2's `∃d`. -/
theorem rel_randomAssign_comp_iff_exists {x : ℕ}
    {u : Transition W E (insert x X) Y} {φ : DPLRel E}
    (hu : ∀ w f h, u.rel w f h ↔ φ f h) (w : W) (f h : ℕ → E) :
    ((Transition.randomAssign X x).comp u).rel w f h ↔
      DPLRel.exists_ x φ f h := by
  constructor
  · rintro ⟨k, hfk, huk⟩
    refine ⟨k x, (hu ..).mp ((u.supported_left fun y hy => ?_).mp huk)⟩
    rcases Finset.mem_insert.mp hy with rfl | hyX
    · simp
    · rcases eq_or_ne y x with rfl | hyx
      · simp
      · exact (hfk (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hyx, hyX⟩))).symm.trans
          (if_neg hyx).symm
  · rintro ⟨d, hφ⟩
    refine ⟨fun n => if n = x then d else f n, fun y hy => ?_, (hu ..).mpr hφ⟩
    exact (if_neg (Finset.mem_erase.mp hy).1).symm

end IndexedReading

end GroenendijkStokhof1991
