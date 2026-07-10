import Linglib.Core.Logic.Trivalent
import Linglib.Core.Logic.Duality
import Mathlib.Data.Finset.Basic

/-!
# Supervaluation Framework
[fine-1975] [kamp-1975]

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
- `Threshold max` for gradable adjectives ([fine-1975])
- `ComparisonClass Entity` for delineation ([klein-1980])
- Product types for multi-predicate penumbral connections

Fine's full framework includes partial specifications with an extension
relation, but he shows (p. 277) that partial points can be identified
with sets of complete points, and extension = subset. We use this
simplified complete-point-only representation.
-/

namespace Semantics.Supervaluation


-- ════════════════════════════════════════════════════
-- § 1. Specification Spaces
-- ════════════════════════════════════════════════════

/-- A specification space: a non-empty finite set of admissible complete
    specifications. Each element represents one way of making all vague
    predicates precise simultaneously. -/
structure SpecSpace (Spec : Type*) where
  admissible : Finset Spec
  nonempty : admissible.Nonempty

/-- Specification spaces ordered by **reverse inclusion** on admissible
    sets: `S ≤ T` iff `T.admissible ⊆ S.admissible`. A "larger" spec
    space in this ordering has *fewer* admissible specs — it is *more
    precise*. This is the information ordering: more precision = more
    information = higher in the order.

    Fine's Stability condition (§ 7) says super-truth is `Antitone`
    under this ordering: making the language more precise (restricting
    admissible specs) preserves definite truth values. -/
instance instPreorderSpecSpace {Spec : Type*} : Preorder (SpecSpace Spec) where
  le S T := T.admissible ⊆ S.admissible
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Finset.Subset.trans h₂ h₁

/-- Singleton specification space: a single admissible precisification.
    Classical models are degenerate specification spaces. -/
def SpecSpace.singleton {Spec : Type*} [DecidableEq Spec] (s : Spec) : SpecSpace Spec where
  admissible := {s}
  nonempty := ⟨s, Finset.mem_singleton.mpr rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Supervaluation Operator
-- ════════════════════════════════════════════════════

/-- Supervaluation operator. Maps a Prop-valued predicate over
    specifications to a three-valued truth value:
    - `Trivalent.true` if the predicate holds at ALL admissible specifications
    - `Trivalent.false` if the predicate fails at ALL admissible specifications
    - `Trivalent.indet` otherwise (the borderline case) -/
def superTrue {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) : Trivalent :=
  if ∀ s ∈ S.admissible, eval s then Trivalent.true
  else if ∀ s ∈ S.admissible, ¬ eval s then Trivalent.false
  else Trivalent.indet

/-- The D (definitely) operator. DA is true iff A is true at ALL
    admissible specifications — i.e., A is super-true. In modal logic
    terms, D is □ in S5 with universal access among specification points. -/
def definitely {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) : Prop :=
  ∀ s ∈ S.admissible, eval s

instance definitely.instDecidable {Spec : Type*} (eval : Spec → Prop)
    [DecidablePred eval] (S : SpecSpace Spec) :
    Decidable (definitely eval S) := by unfold definitely; infer_instance

/-- The I (indefinite) operator. IA ≡ ¬DA ∧ ¬D¬A: A is neither
    definitely true nor definitely false. -/
def indefinite {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) : Prop :=
  ¬ definitely eval S ∧ ¬ definitely (fun s => ¬ eval s) S

instance indefinite.instDecidable {Spec : Type*} (eval : Spec → Prop)
    [DecidablePred eval] (S : SpecSpace Spec) :
    Decidable (indefinite eval S) := by unfold indefinite; infer_instance

-- ════════════════════════════════════════════════════
-- § 3. Characterization Lemmas
-- ════════════════════════════════════════════════════

/-- Super-truth ↔ universally true across the space. -/
theorem superTrue_true_iff {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) :
    superTrue eval S = Trivalent.true ↔ ∀ s ∈ S.admissible, eval s := by
  unfold superTrue
  refine ⟨fun h => ?_, fun h => if_pos h⟩
  by_cases hall : ∀ s ∈ S.admissible, eval s
  · exact hall
  · rw [if_neg hall] at h
    split at h <;> cases h

/-- Super-falsity ↔ universally false across the space. -/
theorem superTrue_false_iff {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) :
    superTrue eval S = Trivalent.false ↔ ∀ s ∈ S.admissible, ¬ eval s := by
  unfold superTrue
  refine ⟨fun h => ?_, fun haf => ?_⟩
  · have hnt : ¬(∀ s ∈ S.admissible, eval s) := by
      intro ht; rw [if_pos ht] at h; cases h
    rw [if_neg hnt] at h
    by_cases haf : ∀ s ∈ S.admissible, ¬ eval s
    · exact haf
    · rw [if_neg haf] at h; cases h
  · have hnt : ¬(∀ s ∈ S.admissible, eval s) := by
      obtain ⟨s₀, hs₀⟩ := S.nonempty
      intro ht; exact haf s₀ hs₀ (ht s₀ hs₀)
    rw [if_neg hnt, if_pos haf]

/-- Indefiniteness ↔ witnesses on both sides. -/
theorem superTrue_indet_iff {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) :
    superTrue eval S = Trivalent.indet ↔
      (∃ s ∈ S.admissible, eval s) ∧ (∃ s ∈ S.admissible, ¬ eval s) := by
  unfold superTrue
  refine ⟨fun h => ?_, fun ⟨⟨st, hst, hvt⟩, ⟨sf, hsf, hvf⟩⟩ => ?_⟩
  · have hnt : ¬(∀ s ∈ S.admissible, eval s) := by
      intro ht; rw [if_pos ht] at h; cases h
    have hnf : ¬(∀ s ∈ S.admissible, ¬ eval s) := by
      intro hf; rw [if_neg hnt, if_pos hf] at h; cases h
    refine ⟨?_, ?_⟩
    · by_contra hcon
      apply hnf
      intro s hs hes
      exact hcon ⟨s, hs, hes⟩
    · by_contra hcon
      apply hnt
      intro s hs
      by_contra hes
      exact hcon ⟨s, hs, hes⟩
  · have hnt : ¬(∀ s ∈ S.admissible, eval s) := fun h => hvf (h sf hsf)
    have hnf : ¬(∀ s ∈ S.admissible, ¬ eval s) := fun h => h st hst hvt
    rw [if_neg hnt, if_neg hnf]

/-- **`superTrue` is `Trivalent.dist` on the admissible Finset.**

    The bridge between Fine 1975 supervaluation (this file) and the
    canonical trivalent classifier (`Trivalent.dist` in
    `Linglib/Core/Logic/Duality.lean`). Both are van Fraassen 1966's
    supervaluation construction; `dist` is the more general form
    parameterized over an arbitrary `Finset α + (α → Prop)`, while
    `superTrue` adds the `SpecSpace` wrapper (admissible Finset +
    nonemptiness witness) and Fine's specification-space ordering.

    On the empty case the two agree definitionally (both give `.true`
    vacuously), but `SpecSpace` rules out empty admissible sets by
    construction so the empty case never arises here. -/
theorem superTrue_eq_dist {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) :
    superTrue eval S = Trivalent.dist S.admissible eval := by
  unfold superTrue Trivalent.dist
  by_cases h_all : ∀ a ∈ S.admissible, eval a
  · rw [if_pos h_all, if_pos h_all]
  · rw [if_neg h_all, if_neg h_all]
    by_cases h_some : ∃ a ∈ S.admissible, eval a
    · rw [if_pos h_some]
      have hnaf : ¬ ∀ s ∈ S.admissible, ¬ eval s := by
        obtain ⟨s, hs, hev⟩ := h_some
        intro hf; exact hf s hs hev
      rw [if_neg hnaf]
    · rw [if_neg h_some]
      have haf : ∀ s ∈ S.admissible, ¬ eval s := by
        intro s hs hev; exact h_some ⟨s, hs, hev⟩
      rw [if_pos haf]

/-- D = super-truth projected to its `Prop` characterization. -/
theorem definitely_iff_superTrue {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) :
    definitely eval S ↔ superTrue eval S = Trivalent.true := by
  rw [superTrue_true_iff]; rfl

-- ════════════════════════════════════════════════════
-- § 4. Penumbral Connections
-- ════════════════════════════════════════════════════

/-- **Excluded middle is super-true.** P ∨ ¬P is true on every
    precisification, hence true on ALL. Classical tautologies survive. -/
theorem excludedMiddle_superTrue {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) :
    superTrue (fun s => eval s ∨ ¬ eval s) S = Trivalent.true :=
  (superTrue_true_iff _ S).mpr (fun s _ => Decidable.em _)

/-- **Non-contradiction is super-false.** P ∧ ¬P is false on every
    precisification, hence false on ALL. -/
theorem nonContradiction_superFalse {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) :
    superTrue (fun s => eval s ∧ ¬ eval s) S = Trivalent.false :=
  (superTrue_false_iff _ S).mpr (fun _ _ ⟨h, hn⟩ => hn h)

/-- **Complementary predicates.** If P and Q never hold simultaneously at
    any admissible specification, their conjunction is super-false.

    This is Fine's "external penumbral connection": the relationship between
    "pink" and "red" across the color boundary (p. 270). -/
theorem complementary_superFalse {Spec : Type*}
    (P Q : Spec → Prop) [DecidablePred P] [DecidablePred Q]
    (S : SpecSpace Spec) (hcomp : ∀ s ∈ S.admissible, ¬ (P s ∧ Q s)) :
    superTrue (fun s => P s ∧ Q s) S = Trivalent.false :=
  (superTrue_false_iff _ S).mpr hcomp

/-- **Conjunction with self.** P ∧ P has the same super-truth value as P.
    This is trivial (`and_self`), but combined with
    `nonContradiction_superFalse`, it resolves Kamp's dilemma:
    supervaluation distinguishes P ∧ P from P ∧ ¬P, while Strong Kleene
    three-valued logic maps both to `indet` when P is borderline. -/
theorem conjunction_self {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) :
    superTrue (fun s => eval s ∧ eval s) S = superTrue eval S := by
  congr 1; funext s; exact propext (and_self_iff)

-- ════════════════════════════════════════════════════
-- § 5. Classical Validity = Super-Validity
-- ════════════════════════════════════════════════════

/-! Fine's central logical result (§ 4): the super-truth theory yields
    classical logic. A formula is super-valid (super-true in every
    specification space) iff it is classically valid (true in every
    classical model). Each direction has a clean proof. -/

/-- Forward: classical tautology → super-valid. -/
theorem classical_implies_superValid {Spec : Type*}
    (eval : Spec → Prop) [DecidablePred eval]
    (htaut : ∀ s, eval s) (S : SpecSpace Spec) :
    superTrue eval S = Trivalent.true :=
  (superTrue_true_iff eval S).mpr (fun s _ => htaut s)

/-- Converse: super-valid → classical tautology. The key step: each
    classical model is a singleton specification space. If `eval` is
    super-true in the singleton `{s}`, then `eval s` holds. -/
theorem superValid_implies_classical {Spec : Type*} [DecidableEq Spec]
    (eval : Spec → Prop) [DecidablePred eval]
    (hvalid : ∀ S : SpecSpace Spec, superTrue eval S = Trivalent.true) :
    ∀ s, eval s := by
  intro s
  exact (superTrue_true_iff eval (.singleton s)).mp (hvalid _) s
    (Finset.mem_singleton.mpr rfl)

/-- **Super-validity ↔ classical validity.** This is the deepest logical
    result in [fine-1975]: supervaluationism makes a difference to
    truth but not to logic. -/
theorem superValid_iff_classical {Spec : Type*} [DecidableEq Spec]
    (eval : Spec → Prop) [DecidablePred eval] :
    (∀ S : SpecSpace Spec, superTrue eval S = Trivalent.true) ↔ (∀ s, eval s) :=
  ⟨superValid_implies_classical eval, fun h S => classical_implies_superValid eval h S⟩

-- ════════════════════════════════════════════════════
-- § 6. Super-Consequence = Classical Consequence
-- ════════════════════════════════════════════════════

/-- Super-consequence: B follows from A iff B is super-true whenever A is,
    across all specification spaces. -/
def superConsequence {Spec : Type*}
    (evalA evalB : Spec → Prop) [DecidablePred evalA] [DecidablePred evalB] : Prop :=
  ∀ S : SpecSpace Spec, superTrue evalA S = Trivalent.true →
    superTrue evalB S = Trivalent.true

/-- Forward: classical consequence → super-consequence. -/
theorem classical_implies_superConsequence {Spec : Type*}
    (evalA evalB : Spec → Prop) [DecidablePred evalA] [DecidablePred evalB]
    (h : ∀ s, evalA s → evalB s) :
    superConsequence evalA evalB :=
  fun S hA => (superTrue_true_iff evalB S).mpr
    (fun s hs => h s ((superTrue_true_iff evalA S).mp hA s hs))

/-- Converse: super-consequence → classical consequence. -/
theorem superConsequence_implies_classical {Spec : Type*} [DecidableEq Spec]
    (evalA evalB : Spec → Prop) [DecidablePred evalA] [DecidablePred evalB]
    (h : superConsequence evalA evalB) :
    ∀ s, evalA s → evalB s := by
  intro s hAs
  have hA : superTrue evalA (.singleton s) = Trivalent.true :=
    (superTrue_true_iff evalA _).mpr
      (fun s' hs' => by have := Finset.mem_singleton.mp hs'; subst this; exact hAs)
  exact (superTrue_true_iff evalB _).mp (h _ hA) s (Finset.mem_singleton.mpr rfl)

/-- **Super-consequence ↔ classical consequence.** -/
theorem superConsequence_iff_classical {Spec : Type*} [DecidableEq Spec]
    (evalA evalB : Spec → Prop) [DecidablePred evalA] [DecidablePred evalB] :
    superConsequence evalA evalB ↔ (∀ s, evalA s → evalB s) :=
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
theorem stability_superTrue {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S T : SpecSpace Spec) (hsub : T.admissible ⊆ S.admissible)
    (hst : superTrue eval S = Trivalent.true) :
    superTrue eval T = Trivalent.true :=
  (superTrue_true_iff eval T).mpr
    (fun s hs => (superTrue_true_iff eval S).mp hst s (hsub hs))

/-- Restricting the specification space preserves super-falsity. -/
theorem stability_superFalse {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S T : SpecSpace Spec) (hsub : T.admissible ⊆ S.admissible)
    (hsf : superTrue eval S = Trivalent.false) :
    superTrue eval T = Trivalent.false :=
  (superTrue_false_iff eval T).mpr
    (fun s hs => (superTrue_false_iff eval S).mp hsf s (hsub hs))

/-- Restriction can resolve indefiniteness but never create it.
    If A is definite (true or false) in S, it stays definite in T ⊆ S. -/
theorem stability_definite {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S T : SpecSpace Spec) (hsub : T.admissible ⊆ S.admissible)
    (hdef : superTrue eval S ≠ Trivalent.indet) :
    superTrue eval T ≠ Trivalent.indet := by
  match hs : superTrue eval S with
  | .true => rw [stability_superTrue eval S T hsub hs]; exact Trivalent.noConfusion
  | .false => rw [stability_superFalse eval S T hsub hs]; exact Trivalent.noConfusion
  | .indet => exact absurd hs hdef

/-- **Stability as antitonicity**: super-truth is preserved under
    the information ordering on spec spaces (= reverse inclusion on
    admissible sets). Making the language more precise (`S ≤ T`, i.e.,
    `T.admissible ⊆ S.admissible`) preserves super-truth.

    This is Mathlib's `Antitone` applied to `superTrue eval` with
    the codomain ordered by `Trivalent.true ≤ · ≤ Trivalent.true` (super-truth
    entails super-truth). The theorem says: if `superTrue eval S = .true`
    and `S ≤ T` (T is more precise), then `superTrue eval T = .true`.

    The full antitonicity on `Trivalent`'s lattice ordering does NOT hold
    (restriction can turn `indet` into `true`), but this weaker
    preservation-of-definiteness property is what matters for Fine. -/
theorem stability_antitone_superTrue {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    {S T : SpecSpace Spec} (hle : S ≤ T)
    (h : superTrue eval S = Trivalent.true) :
    superTrue eval T = Trivalent.true :=
  stability_superTrue eval S T hle h

/-- Dual: super-falsity is also preserved under the information ordering. -/
theorem stability_antitone_superFalse {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    {S T : SpecSpace Spec} (hle : S ≤ T)
    (h : superTrue eval S = Trivalent.false) :
    superTrue eval T = Trivalent.false :=
  stability_superFalse eval S T hle h

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
theorem D_implies_A {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval]
    (S : SpecSpace Spec) :
    superTrue (fun s => ¬ definitely eval S ∨ eval s) S = Trivalent.true := by
  apply (superTrue_true_iff _ S).mpr
  intro s hs
  by_cases hd : definitely eval S
  · exact Or.inr (hd s hs)
  · exact Or.inl hd

/-- **Converse fails: A → DA is NOT super-valid.** Counterexample: two
    specification points, `eval = id`, space = `{true, false}`.
    At point `true`: A is true but DA is false (A fails at `false`).
    So `A → DA` is false at `true`, hence not super-true. -/
theorem A_not_implies_DA :
    ∃ (eval : Bool → Prop) (_ : DecidablePred eval) (S : SpecSpace Bool),
      superTrue (fun s => ¬ eval s ∨ definitely eval S) S ≠ Trivalent.true := by
  refine ⟨fun b => b = true, inferInstance,
          ⟨{true, false}, ⟨true, by simp⟩⟩, ?_⟩
  intro h
  have := (superTrue_true_iff _ _).mp h true (by simp)
  rcases this with h1 | h2
  · exact h1 rfl
  · have := h2 false (by simp); cases this

/-- **DA is a consequence of A.** If A is super-true, then DA is
    super-true (since DA just says "A is true at all specs"). Combined
    with `A_not_implies_DA`, this shows the asymmetry characteristic of
    supervaluationism (Fine § 5, p. 290): asserting A commits one to DA,
    but A → DA is not a logical truth. -/
theorem DA_consequence_of_A {Spec : Type*} (eval : Spec → Prop) [DecidablePred eval] :
    ∀ S : SpecSpace Spec,
      superTrue eval S = Trivalent.true →
      superTrue (fun _ => definitely eval S) S = Trivalent.true := by
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
    (eval : Spec → Prop) [DecidablePred eval] (s : Spec) :
    superTrue eval (.singleton s) ≠ Trivalent.indet := by
  intro h
  have hi := (superTrue_indet_iff eval (.singleton s)).mp h
  obtain ⟨⟨st, hst, hvt⟩, ⟨sf, hsf, hvf⟩⟩ := hi
  have hst' := Finset.mem_singleton.mp hst
  have hsf' := Finset.mem_singleton.mp hsf
  subst hst'; subst hsf'
  exact hvf hvt

end Semantics.Supervaluation
