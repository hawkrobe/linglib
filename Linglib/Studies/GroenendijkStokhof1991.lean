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
- The based reading: DPL's generators as context-extension arrows
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

/-- Negation is a test. -/
theorem neg_isTest (φ : DPLRel E) (g h : ℕ → E)
    (hn : DPLRel.neg φ g h) : g = h := hn.1

/-- Implication is a test: antecedent bindings do not escape. -/
theorem impl_isTest (φ ψ : DPLRel E) (g h : ℕ → E)
    (hi : DPLRel.impl φ ψ g h) : g = h := hi.1

/-- Disjunction is a test: no anaphora across or out of disjuncts. -/
theorem disj_isTest (φ ψ : DPLRel E) (g h : ℕ → E)
    (hd : DPLRel.disj φ ψ g h) : g = h := hd.1

/-- The universal quantifier is a test: it introduces no referents. -/
theorem forall_isTest (x : ℕ) (φ : DPLRel E) (g h : ℕ → E)
    (hfa : DPLRel.forall_ x φ g h) : g = h := hfa.1

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
open DynamicSemantics.DynProp (closure)

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

/-! ### The based reading: DPL generators as context extension -/

/-! DPL meanings are relations on total assignments (Definition 2); the
based substrate (`Transition.lean`) types them by the contexts they read
and write. The two generators land as arrows: tests (clauses 1–3, 5, 6, 8
are all of this shape) become `testTransition`s `X ⟶ X`, and the random
reset of clause 7 is `Transition.randomAssign : X ⟶ insert x X`.
Sequencing is clause 4 (`rel_comp_iff_conj`), and the existential factors
as random assignment composed with its scope
(`rel_randomAssign_comp_iff_exists`) — so a DPL formula's based meaning is
a composite of the generating arrows of `DynamicSemantics.Ctx`. -/

section BasedReading

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

/-- Applying a test at a state based below its context filters the
carrier — the based form of Definition 2's test clauses. -/
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

end BasedReading

end GroenendijkStokhof1991
