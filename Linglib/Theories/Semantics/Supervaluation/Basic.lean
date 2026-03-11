import Linglib.Core.Logic.Truth3
import Mathlib.Data.Finset.Basic

/-!
# Supervaluation Framework
@cite{fine-1975} @cite{kamp-1975}

General supervaluation theory for vague languages. A vague sentence
is **super-true** iff true under all admissible precisifications,
**super-false** iff false under all, and **indefinite** otherwise.

## Key Results

- **Classical biconditional**: super-validity ↔ classical validity
- **Consequence preservation**: super-consequence = classical consequence
- **Penumbral connections**: logical relations preserved in borderline region
- **D operator**: satisfies T axiom (DA → A) but not converse (A → DA)
- **Stability**: restricting the specification space preserves definite truth
- **Kamp's dilemma resolved**: P ∧ P ≢ P ∧ ¬P under supervaluation,
  unlike any truth-functional three-valued logic

## Architecture

This file provides the *general* supervaluation framework, parameterized
by an abstract specification type `Spec`. Study files specialize `Spec`:
- `Threshold max` for gradable adjectives (@cite{fine-1975})
- `ComparisonClass Entity` for delineation (@cite{klein-1980})
- Product types for multi-predicate penumbral connections

Fine's full framework includes partial specifications with an extension
relation, but he shows (p. 277) that partial points can be identified
with sets of complete points, and extension = subset. We use this
simplified complete-point-only representation.
-/

namespace Semantics.Supervaluation

open Core.Duality (Truth3)

-- ════════════════════════════════════════════════════
-- § 1. Specification Spaces
-- ════════════════════════════════════════════════════

/-- A specification space: a non-empty finite set of admissible complete
    specifications. Each element represents one way of making all vague
    predicates precise simultaneously. -/
structure SpecSpace (Spec : Type*) where
  admissible : Finset Spec
  nonempty : admissible.Nonempty

/-- Singleton specification space: a single admissible precisification.
    Classical models are degenerate specification spaces. -/
def SpecSpace.singleton {Spec : Type*} [DecidableEq Spec] (s : Spec) : SpecSpace Spec where
  admissible := {s}
  nonempty := ⟨s, Finset.mem_singleton.mpr rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Supervaluation Operator
-- ════════════════════════════════════════════════════

/-- Supervaluation operator. Maps a Bool-valued predicate over
    specifications to a three-valued truth value:
    - `Truth3.true` if true at ALL admissible specifications
    - `Truth3.false` if false at ALL admissible specifications
    - `Truth3.indet` otherwise (the borderline case) -/
def superTrue {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) : Truth3 :=
  if ∀ s ∈ S.admissible, eval s = true then Truth3.true
  else if ∀ s ∈ S.admissible, eval s = false then Truth3.false
  else Truth3.indet

/-- The D (definitely) operator. DA is true iff A is true at ALL
    admissible specifications — i.e., A is super-true. In modal logic
    terms, D is □ in S5 with universal access among specification points. -/
def definitely {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) : Bool :=
  decide (∀ s ∈ S.admissible, eval s = true)

/-- The I (indefinite) operator. IA ≡ ¬DA ∧ ¬D¬A: A is neither
    definitely true nor definitely false. -/
def indefinite {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) : Bool :=
  !definitely eval S && !definitely (fun s => !eval s) S

-- ════════════════════════════════════════════════════
-- § 3. Characterization Lemmas
-- ════════════════════════════════════════════════════

/-- Super-truth ↔ universally true across the space. -/
theorem superTrue_true_iff {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) :
    superTrue eval S = Truth3.true ↔ ∀ s ∈ S.admissible, eval s = true := by
  unfold superTrue
  constructor
  · intro h
    by_contra hc; push_neg at hc; obtain ⟨s, hs, hv⟩ := hc
    rw [if_neg (fun h' => hv (h' s hs))] at h; split at h <;> cases h
  · exact fun h => if_pos h

/-- Super-falsity ↔ universally false across the space. -/
theorem superTrue_false_iff {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) :
    superTrue eval S = Truth3.false ↔ ∀ s ∈ S.admissible, eval s = false := by
  unfold superTrue
  constructor
  · intro h
    have hnt : ¬(∀ s ∈ S.admissible, eval s = true) := by
      by_contra ht
      rw [if_pos ht] at h; cases h
    rw [if_neg hnt] at h
    by_contra hc; push_neg at hc; obtain ⟨s, hs, hv⟩ := hc
    rw [if_neg (fun h' => hv (h' s hs))] at h; cases h
  · intro haf
    have hnt : ¬(∀ s ∈ S.admissible, eval s = true) := by
      obtain ⟨s₀, hs₀⟩ := S.nonempty
      intro ht; have := ht s₀ hs₀; rw [haf s₀ hs₀] at this; cases this
    rw [if_neg hnt, if_pos haf]

/-- Indefiniteness ↔ witnesses on both sides. -/
theorem superTrue_indet_iff {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) :
    superTrue eval S = Truth3.indet ↔
      (∃ s ∈ S.admissible, eval s = true) ∧ (∃ s ∈ S.admissible, eval s = false) := by
  unfold superTrue
  constructor
  · intro h
    have hnt : ¬(∀ s ∈ S.admissible, eval s = true) := by
      intro ht; rw [if_pos ht] at h; cases h
    have hnf : ¬(∀ s ∈ S.admissible, eval s = false) := by
      intro hf; rw [if_neg hnt, if_pos hf] at h; cases h
    push_neg at hnt hnf
    obtain ⟨st, hst, hvt⟩ := hnt; obtain ⟨sf, hsf, hvf⟩ := hnf
    exact ⟨⟨sf, hsf, by cases hv : eval sf <;> simp_all⟩,
           ⟨st, hst, by cases hv : eval st <;> simp_all⟩⟩
  · intro ⟨⟨st, hst, hvt⟩, ⟨sf, hsf, hvf⟩⟩
    have hnt : ¬(∀ s ∈ S.admissible, eval s = true) :=
      fun h => by rw [h sf hsf] at hvf; cases hvf
    have hnf : ¬(∀ s ∈ S.admissible, eval s = false) :=
      fun h => by rw [h st hst] at hvt; cases hvt
    rw [if_neg hnt, if_neg hnf]

/-- D = super-truth projected to Bool. -/
theorem definitely_iff_superTrue {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) :
    definitely eval S = true ↔ superTrue eval S = Truth3.true := by
  rw [superTrue_true_iff]; unfold definitely; rw [decide_eq_true_eq]

-- ════════════════════════════════════════════════════
-- § 4. Penumbral Connections
-- ════════════════════════════════════════════════════

/-- **Excluded middle is super-true.** P ∨ ¬P is true on every
    precisification, hence true on ALL. Classical tautologies survive. -/
theorem excludedMiddle_superTrue {Spec : Type*} (eval : Spec → Bool)
    (S : SpecSpace Spec) :
    superTrue (fun s => eval s || !eval s) S = Truth3.true :=
  (superTrue_true_iff _ S).mpr (fun s _ => by cases eval s <;> simp)

/-- **Non-contradiction is super-false.** P ∧ ¬P is false on every
    precisification, hence false on ALL. -/
theorem nonContradiction_superFalse {Spec : Type*} (eval : Spec → Bool)
    (S : SpecSpace Spec) :
    superTrue (fun s => eval s && !eval s) S = Truth3.false :=
  (superTrue_false_iff _ S).mpr (fun s _ => by cases eval s <;> simp)

/-- **Complementary predicates.** If P and Q never hold simultaneously at
    any admissible specification, their conjunction is super-false.

    This is Fine's "external penumbral connection": the relationship between
    "pink" and "red" across the color boundary (p. 270). -/
theorem complementary_superFalse {Spec : Type*}
    (P Q : Spec → Bool) (S : SpecSpace Spec)
    (hcomp : ∀ s ∈ S.admissible, (P s && Q s) = false) :
    superTrue (fun s => P s && Q s) S = Truth3.false := by
  rw [superTrue_false_iff]; exact hcomp

/-- **Conjunction with self.** P ∧ P has the same super-truth value as P.
    This is trivial (Bool.and_self), but combined with
    `nonContradiction_superFalse`, it resolves Kamp's dilemma:
    supervaluation distinguishes P ∧ P from P ∧ ¬P, while Strong Kleene
    three-valued logic maps both to `indet` when P is borderline. -/
theorem conjunction_self {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) :
    superTrue (fun s => eval s && eval s) S = superTrue eval S := by
  congr 1; funext s; exact Bool.and_self (eval s)

-- ════════════════════════════════════════════════════
-- § 5. Classical Validity = Super-Validity
-- ════════════════════════════════════════════════════

/-! Fine's central logical result (§ 4): the super-truth theory yields
    classical logic. A formula is super-valid (super-true in every
    specification space) iff it is classically valid (true in every
    classical model). Each direction has a clean proof. -/

/-- Forward: classical tautology → super-valid. -/
theorem classical_implies_superValid {Spec : Type*}
    (eval : Spec → Bool) (htaut : ∀ s, eval s = true) (S : SpecSpace Spec) :
    superTrue eval S = Truth3.true :=
  (superTrue_true_iff eval S).mpr (fun s _ => htaut s)

/-- Converse: super-valid → classical tautology. The key step: each
    classical model is a singleton specification space. If `eval` is
    super-true in the singleton `{s}`, then `eval s = true`. -/
theorem superValid_implies_classical {Spec : Type*} [DecidableEq Spec]
    (eval : Spec → Bool)
    (hvalid : ∀ S : SpecSpace Spec, superTrue eval S = Truth3.true) :
    ∀ s, eval s = true := by
  intro s
  exact (superTrue_true_iff eval (.singleton s)).mp (hvalid _) s
    (Finset.mem_singleton.mpr rfl)

/-- **Super-validity ↔ classical validity.** This is the deepest logical
    result in @cite{fine-1975}: supervaluationism makes a difference to
    truth but not to logic. -/
theorem superValid_iff_classical {Spec : Type*} [DecidableEq Spec]
    (eval : Spec → Bool) :
    (∀ S : SpecSpace Spec, superTrue eval S = Truth3.true) ↔ (∀ s, eval s = true) :=
  ⟨superValid_implies_classical eval, fun h S => classical_implies_superValid eval h S⟩

-- ════════════════════════════════════════════════════
-- § 6. Super-Consequence = Classical Consequence
-- ════════════════════════════════════════════════════

/-- Super-consequence: B follows from A iff B is super-true whenever A is,
    across all specification spaces. -/
def superConsequence {Spec : Type*} (evalA evalB : Spec → Bool) : Prop :=
  ∀ S : SpecSpace Spec, superTrue evalA S = Truth3.true → superTrue evalB S = Truth3.true

/-- Forward: classical consequence → super-consequence. -/
theorem classical_implies_superConsequence {Spec : Type*}
    (evalA evalB : Spec → Bool) (h : ∀ s, evalA s = true → evalB s = true) :
    superConsequence evalA evalB :=
  fun S hA => (superTrue_true_iff evalB S).mpr
    (fun s hs => h s ((superTrue_true_iff evalA S).mp hA s hs))

/-- Converse: super-consequence → classical consequence. -/
theorem superConsequence_implies_classical {Spec : Type*} [DecidableEq Spec]
    (evalA evalB : Spec → Bool) (h : superConsequence evalA evalB) :
    ∀ s, evalA s = true → evalB s = true := by
  intro s hAs
  have hA : superTrue evalA (.singleton s) = Truth3.true :=
    (superTrue_true_iff evalA _).mpr
      (fun s' hs' => by have := Finset.mem_singleton.mp hs'; subst this; exact hAs)
  have hB := (superTrue_true_iff evalB _).mp (h _ hA) s (Finset.mem_singleton.mpr rfl)
  exact hB

/-- **Super-consequence ↔ classical consequence.** -/
theorem superConsequence_iff_classical {Spec : Type*} [DecidableEq Spec]
    (evalA evalB : Spec → Bool) :
    superConsequence evalA evalB ↔ (∀ s, evalA s = true → evalB s = true) :=
  ⟨superConsequence_implies_classical evalA evalB,
   classical_implies_superConsequence evalA evalB⟩

-- ════════════════════════════════════════════════════
-- § 7. Stability
-- ════════════════════════════════════════════════════

/-! Fine's Stability condition (S): definite truth values are preserved
    under extension. In our complete-point-only representation, "extension"
    = restricting the set of admissible specifications (making the language
    more precise by ruling out some precisifications). Stability says
    super-truth is preserved under restriction — i.e., it is monotone
    with respect to the subset ordering on specification spaces. -/

/-- Restricting the specification space preserves super-truth. -/
theorem stability_superTrue {Spec : Type*} (eval : Spec → Bool)
    (S T : SpecSpace Spec) (hsub : T.admissible ⊆ S.admissible)
    (hst : superTrue eval S = Truth3.true) :
    superTrue eval T = Truth3.true :=
  (superTrue_true_iff eval T).mpr
    (fun s hs => (superTrue_true_iff eval S).mp hst s (hsub hs))

/-- Restricting the specification space preserves super-falsity. -/
theorem stability_superFalse {Spec : Type*} (eval : Spec → Bool)
    (S T : SpecSpace Spec) (hsub : T.admissible ⊆ S.admissible)
    (hsf : superTrue eval S = Truth3.false) :
    superTrue eval T = Truth3.false :=
  (superTrue_false_iff eval T).mpr
    (fun s hs => (superTrue_false_iff eval S).mp hsf s (hsub hs))

/-- Restriction can resolve indefiniteness but never create it.
    If A is definite (true or false) in S, it stays definite in T ⊆ S. -/
theorem stability_definite {Spec : Type*} (eval : Spec → Bool)
    (S T : SpecSpace Spec) (hsub : T.admissible ⊆ S.admissible)
    (hdef : superTrue eval S ≠ Truth3.indet) :
    superTrue eval T ≠ Truth3.indet := by
  match hs : superTrue eval S with
  | .true => rw [stability_superTrue eval S T hsub hs]; exact Truth3.noConfusion
  | .false => rw [stability_superFalse eval S T hsub hs]; exact Truth3.noConfusion
  | .indet => exact absurd hs hdef

-- ════════════════════════════════════════════════════
-- § 8. The D Operator
-- ════════════════════════════════════════════════════

/-! Fine's D operator (§ 5) is the modal necessity operator □ on
    specification spaces. DA is true at a specification point iff A is
    true at ALL specification points (S5 with universal access). Since D
    is constant across points, DA → A is super-valid (the T axiom), but
    A → DA is not (A may hold at this point but fail at another). -/

/-- **T axiom: DA → A is super-valid.** Material implication
    `¬(DA) ∨ A` is true at every specification point: either D is false
    (the disjunction holds) or D is true and A holds at all points. -/
theorem D_implies_A {Spec : Type*} (eval : Spec → Bool) (S : SpecSpace Spec) :
    superTrue (fun s => !definitely eval S || eval s) S = Truth3.true := by
  apply (superTrue_true_iff _ S).mpr
  intro s hs
  match hd : definitely eval S with
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    have hall := (definitely_iff_superTrue eval S).mp hd
    exact (superTrue_true_iff eval S).mp hall s hs
  | false => simp

/-- **Converse fails: A → DA is NOT super-valid.** Counterexample: two
    specification points, `eval = id`, space = `{true, false}`.
    At point `true`: A is true but DA is false (A fails at `false`).
    So `A → DA` is false at `true`, hence not super-true. -/
theorem A_not_implies_DA :
    ∃ (eval : Bool → Bool) (S : SpecSpace Bool),
      superTrue (fun s => !eval s || definitely eval S) S ≠ Truth3.true := by
  refine ⟨id, ⟨{true, false}, ⟨true, by simp⟩⟩, ?_⟩
  -- definitely id this_space = false (since id false ≠ true)
  -- So the formula is (fun s => !s || false) = (fun s => !s)
  -- superTrue (!·) {true, false} = indet ≠ true
  rw [show superTrue (fun s => !id s || definitely id ⟨{true, false}, ⟨true, by simp⟩⟩)
        ⟨{true, false}, ⟨true, by simp⟩⟩ = Truth3.indet from by native_decide]
  exact Truth3.noConfusion

/-- **DA is a consequence of A.** If A is super-true, then DA is
    super-true (since DA just says "A is true at all specs"). Combined
    with `A_not_implies_DA`, this shows the asymmetry characteristic of
    supervaluationism (Fine § 5, p. 290): asserting A commits one to DA,
    but A → DA is not a logical truth. -/
theorem DA_consequence_of_A {Spec : Type*} (eval : Spec → Bool) :
    ∀ S : SpecSpace Spec,
      superTrue eval S = Truth3.true → superTrue (fun _ => definitely eval S) S = Truth3.true := by
  intro S hA
  apply (superTrue_true_iff _ S).mpr
  intro _ _
  exact (definitely_iff_superTrue eval S).mpr hA

-- ════════════════════════════════════════════════════
-- § 9. Fidelity
-- ════════════════════════════════════════════════════

/-- **Fidelity**: at a singleton specification space (a complete
    specification / classical model), every sentence is either true or
    false — never indefinite. Supervaluation reduces to classical
    evaluation. -/
theorem fidelity {Spec : Type*} [DecidableEq Spec]
    (eval : Spec → Bool) (s : Spec) :
    superTrue eval (.singleton s) ≠ Truth3.indet := by
  intro h
  have hi := (superTrue_indet_iff eval (.singleton s)).mp h
  obtain ⟨⟨st, hst, hvt⟩, ⟨sf, hsf, hvf⟩⟩ := hi
  have hst' := Finset.mem_singleton.mp hst
  have hsf' := Finset.mem_singleton.mp hsf
  subst hst'; subst hsf'
  rw [hvt] at hvf; cases hvf

end Semantics.Supervaluation
