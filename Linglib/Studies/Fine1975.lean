import Mathlib.Order.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Basic
import Linglib.Semantics.Supervaluation
import Linglib.Logic.Trivalent.Propositional
import Linglib.Core.Order.Bilattice.Kleene

/-!
# Fine (1975): Vagueness, truth and logic

This file formalizes [fine-1975]'s case for the super-truth theory of vagueness. §1 treats
Indefinite as a third truth-value: a partial specification assigns True, False or Indefinite
to the atomic sentences, and a truth-functional valuation is constrained by Fidelity — classical
on definite values — and Stability — definite values preserved under extension (the knowledge
order `Trivalent.toFlat`). Those two conditions fix negation (`neg_eq_of_faithful_stable`) and
leave a commutative conjunction exactly the minimizing and maximizing options of [kleene-1952]'s
weak and strong tables (`conj_eq_inf_or_meetWeak`). Yet no truth-functional account respects
penumbral connection: with the blob on the border of pink and red, *pink and red* is false while
*pink and pink* is indefinite, though every conjunct is indefinite (`conj_not_truthFunctional`,
and likewise for disjunction). §2 answers with specification spaces: points partially ordered by
extension, complete points to which every point extends (Completability), and super-truth at a
point as truth at all its complete extensions (`SuperTrue`), which satisfies Fidelity and
Stability (`superTrue_iff_of_complete`, `SuperTrue.mono`); the partial points are recovered from
the complete ones as the sets of their completions, extension becoming inclusion
(`completions`, `completions_mono`), which is the reduced form of `Semantics.Supervaluation`
(`superTrue_completions`). §3 argues that the theory is forced: an account satisfying Fidelity,
Stability and Resolution is the super-truth account (`Account.eq_superTruth_of_resolves`), and
so is one satisfying Fidelity, Stability and the A-clauses — Resolution for atoms, the classical
clauses for negation, and for conjunction the truth clause with the falsity clause that redeems
its pledge (`Account.eq_superTruth_of_aClauses`). §4 draws the logic: validity and consequence
are classical (`Semantics.Supervaluation.superValid_iff_classical`), the law of excluded middle
holds where bivalence fails (`herbert_lem`, `herbert_indet`), and the sorites' tolerance premise
is false because a hair-splitting number exists in every complete specification
(`tolerance_superFalse`). §5 adds the definitely-operator: `I A := ¬DA ∧ ¬D¬A`
(`Semantics.Supervaluation.indefinite`), `D` an S5 modality over the complete specifications
(`definitely_definitely_iff`, `not_definitely_definitely`), consequence as validity of `DA ⊃ B`
(`superConsequence_iff_definitely_imp`), and, for higher-order vagueness, truth relative to
boundaries — nested admissible spaces — under a reflexive accessibility whose logic is T
(`Boundary.R_refl`, `Boundary.definitely_self`).

## Implementation notes

* A specification space is the class `SpecificationSpace` over a partial order: the complete
  points, Completability, and the condition that a complete point admits no proper extension,
  which is automatic when points are specifications (the extensional account of §2) and is
  what makes super-truth classical at complete points. `Semantics.Supervaluation.SpecSpace` is
  the §2 reduction to nonempty sets of complete points; `completions` is the reduction map.
* Partial specifications are `Atom → Flat Bool` with the pointwise knowledge order, so that
  extension is the order of `Flat`; they instantiate the class. Connectives are evaluated on
  `Trivalent`, whose strong Kleene tables are the maximizing account and `meetWeak` the
  minimizing one; its logic with True designated (`Trivalent.k3_no_tautologies`) has no valid
  formulas, as §4 observes.
* The examples are Fine's: *bald* over hair counts with the admissible thresholds 40 to 60 of
  §5 (Herbert at 50 hairs, Yul Brynner at 0, the million-haired man), and the blob at hue 5
  with colour boundaries 3 to 7; the intuitionistic and anticipatory accounts, the infinite-
  order truth-values and the hierarchy of truth-predicates are not formalized.
* Sentences in §3 are `Trivalent.Formula`, classically evaluated at a point by
  `Formula.Realize` on the Boolean model the point's atomic values determine.

## References

* [fine-1975]
* [kleene-1952]
* [van-fraassen-1966]
* [van-fraassen-1969]
* [kamp-1975]
* [lewis-1970]
-/

namespace Fine1975

open Trivalent Semantics.Supervaluation

/-! ### The truth-value approach (§1) -/

section TruthValue

/-- Fidelity for a connective: classical on definite values. -/
def Faithful (f : Trivalent → Trivalent → Trivalent) (g : Bool → Bool → Bool) : Prop :=
  ∀ x y, f (ofBool x) (ofBool y) = ofBool (g x y)

/-- Stability for a connective: definite values are preserved when the arguments are extended,
monotonicity in the knowledge order. -/
def Stable (f : Trivalent → Trivalent → Trivalent) : Prop :=
  ∀ a a' b b', toFlat a ≤ toFlat a' → toFlat b ≤ toFlat b' → toFlat (f a b) ≤ toFlat (f a' b')

private theorem eq_indet_of_le (v : Trivalent) (h₁ : toFlat v ≤ toFlat .true)
    (h₂ : toFlat v ≤ toFlat .false) : v = .indet := by
  cases v <;> revert h₁ h₂ <;> decide

private theorem flat_le_refl (a : Trivalent) : toFlat a ≤ toFlat a := le_rfl

private theorem indet_le (a : Trivalent) : toFlat .indet ≤ toFlat a := by cases a <;> decide

/-- Fidelity and Stability determine negation: it is [kleene-1952]'s. -/
theorem neg_eq_of_faithful_stable (n : Trivalent → Trivalent) (hF : ∀ x, n (ofBool x) = ofBool (!x))
    (hS : ∀ a a', toFlat a ≤ toFlat a' → toFlat (n a) ≤ toFlat (n a')) : n = neg := by
  have hT : n .true = .false := hF Bool.true
  have hFa : n .false = .true := hF Bool.false
  funext a
  cases a
  · exact hT
  · exact hFa
  · exact eq_indet_of_le _ (hFa ▸ hS .indet .false (indet_le _)) (hT ▸ hS .indet .true (indet_le _))

/-- A commutative conjunction satisfying Fidelity and Stability is the maximizing strong Kleene
`⊓` or the minimizing weak Kleene `meetWeak`: they differ only on an indefinite conjunct beside a
false one. -/
theorem conj_eq_inf_or_meetWeak (f : Trivalent → Trivalent → Trivalent) (hF : Faithful f (· && ·))
    (hS : Stable f) (hC : ∀ a b, f a b = f b a) : f = (· ⊓ ·) ∨ f = meetWeak := by
  have hTT : f .true .true = .true := hF Bool.true Bool.true
  have hTF : f .true .false = .false := hF Bool.true Bool.false
  have hFT : f .false .true = .false := hF Bool.false Bool.true
  have hFF : f .false .false = .false := hF Bool.false Bool.false
  have hIT : f .indet .true = .indet := eq_indet_of_le _
    (by simpa only [hTT] using hS .indet .true .true .true (indet_le _) (flat_le_refl _))
    (by simpa only [hFT] using hS .indet .false .true .true (indet_le _) (flat_le_refl _))
  have hII : f .indet .indet = .indet := eq_indet_of_le _
    (by simpa only [hTT] using hS .indet .true .indet .true (indet_le _) (indet_le _))
    (by simpa only [hFF] using hS .indet .false .indet .false (indet_le _) (indet_le _))
  have hIF : f .indet .false ≠ .true := λ h => by
    have := hS .indet .true .false .false (indet_le _) (flat_le_refl _)
    rw [h, hTF] at this
    exact absurd this (by decide)
  rcases h : f .indet .false with _ | _ | _
  · exact absurd h hIF
  · left
    funext a b
    cases a <;> cases b <;>
      simp only [hTT, hTF, hFT, hFF, hIT, hII, h, hC .true .indet, hC .false .indet] <;> decide
  · right
    funext a b
    cases a <;> cases b <;>
      simp only [hTT, hTF, hFT, hFF, hIT, hII, h, hC .true .indet, hC .false .indet] <;> decide

/-! The blob on the border of pink and red (§1, §3): a colour boundary between hue 3 and hue 7
is admissible, the blob has hue 5, and *pink* is above the boundary, *red* at or below it. -/

/-- The admissible colour boundaries. -/
def colour : SpecSpace ℕ := ⟨Finset.Icc 3 7, ⟨3, by simp⟩⟩

/-- *x is pink*: its hue is above the boundary. -/
abbrev pink (hue θ : ℕ) : Prop := θ < hue

/-- *x is red*: its hue is at or below the boundary. -/
abbrev red (hue θ : ℕ) : Prop := hue ≤ θ

/-- *The blob is pink* and *the blob is red* are indefinite, their conjunction false and their
disjunction true, and *if pink then not red* true where *if pink then not pink* is not: the
penumbral truths. -/
theorem blob :
    superTrue (pink 5) colour = .indet ∧ superTrue (red 5) colour = .indet ∧
      superTrue (λ θ => pink 5 θ ∧ red 5 θ) colour = .false ∧
      superTrue (λ θ => pink 5 θ ∨ red 5 θ) colour = .true ∧
      superTrue (λ θ => pink 5 θ → ¬ red 5 θ) colour = .true ∧
      superTrue (λ θ => pink 5 θ → ¬ pink 5 θ) colour = .indet := by
  decide

/-- No truth-functional conjunction respects penumbral connection: *pink and pink* and *pink
and red* have indefinite conjuncts alike, but the first is indefinite and the second false. -/
theorem conj_not_truthFunctional :
    ¬ ∃ f : Trivalent → Trivalent → Trivalent, ∀ (P Q : ℕ → Prop) [DecidablePred P]
      [DecidablePred Q], superTrue (λ θ => P θ ∧ Q θ) colour = f (superTrue P colour)
        (superTrue Q colour) := by
  rintro ⟨f, hf⟩
  have h₁ := hf (pink 5) (pink 5)
  have h₂ := hf (pink 5) (red 5)
  rw [blob.1, blob.2.1] at h₂
  rw [blob.1, ← h₂, blob.2.2.1] at h₁
  exact absurd h₁ (by decide)

/-- Nor does any truth-functional disjunction: *pink or pink* is indefinite and *pink or red*
true. -/
theorem disj_not_truthFunctional :
    ¬ ∃ f : Trivalent → Trivalent → Trivalent, ∀ (P Q : ℕ → Prop) [DecidablePred P]
      [DecidablePred Q], superTrue (λ θ => P θ ∨ Q θ) colour = f (superTrue P colour)
        (superTrue Q colour) := by
  rintro ⟨f, hf⟩
  have h₁ := hf (pink 5) (pink 5)
  have h₂ := hf (pink 5) (red 5)
  rw [blob.1, blob.2.1] at h₂
  rw [blob.1, ← h₂, blob.2.2.2.1] at h₁
  exact absurd h₁ (by decide)

end TruthValue

/-! ### Specification spaces (§2) -/

/-- A specification space: points partially ordered by extension, among them the complete
points, to one of which every point extends (Completability), and which admit no proper
extension. -/
class SpecificationSpace (Point : Type*) [PartialOrder Point] where
  /-- The complete points. -/
  Complete : Point → Prop
  /-- Completability: every point extends to a complete point. -/
  completable : ∀ t, ∃ u, t ≤ u ∧ Complete u
  /-- A complete point admits no proper extension. -/
  isMax_of_complete : ∀ t, Complete t → IsMax t

export SpecificationSpace (Complete completable isMax_of_complete)

section Space

variable {Point : Type*} [PartialOrder Point] [SpecificationSpace Point] {A : Point → Prop}
  {t u : Point}

/-- Super-truth at a point: truth at every complete extension. -/
def SuperTrue (A : Point → Prop) (t : Point) : Prop := ∀ u, t ≤ u → Complete u → A u

/-- Super-falsity at a point: falsity at every complete extension. -/
def SuperFalse (A : Point → Prop) (t : Point) : Prop := ∀ u, t ≤ u → Complete u → ¬ A u

/-- Fidelity: at a complete point super-truth is classical truth. -/
theorem superTrue_iff_of_complete (ht : Complete t) : SuperTrue A t ↔ A t :=
  ⟨λ h => h t le_rfl ht, λ h _ htu _ => (isMax_of_complete t ht htu).antisymm htu ▸ h⟩

/-- Fidelity for falsity. -/
theorem superFalse_iff_of_complete (ht : Complete t) : SuperFalse A t ↔ ¬ A t :=
  ⟨λ h => h t le_rfl ht, λ h _ htu _ => (isMax_of_complete t ht htu).antisymm htu ▸ h⟩

/-- Stability: super-truth is preserved under extension. -/
theorem SuperTrue.mono (h : SuperTrue A t) (htu : t ≤ u) : SuperTrue A u :=
  λ _ huv hv => h _ (htu.trans huv) hv

/-- Stability for falsity. -/
theorem SuperFalse.mono (h : SuperFalse A t) (htu : t ≤ u) : SuperFalse A u :=
  λ _ huv hv => h _ (htu.trans huv) hv

/-- Resolution: a sentence not super-true at a point is super-false at some extension. -/
theorem exists_superFalse_of_not_superTrue (h : ¬ SuperTrue A t) :
    ∃ u, t ≤ u ∧ SuperFalse A u := by
  simp only [SuperTrue, not_forall] at h
  obtain ⟨u, htu, hu, hA⟩ := h
  exact ⟨u, htu, (superFalse_iff_of_complete hu).2 hA⟩

/-- Resolution for falsity. -/
theorem exists_superTrue_of_not_superFalse (h : ¬ SuperFalse A t) :
    ∃ u, t ≤ u ∧ SuperTrue A u := by
  simp only [SuperFalse, not_forall, not_not] at h
  obtain ⟨u, htu, hu, hA⟩ := h
  exact ⟨u, htu, (superTrue_iff_of_complete hu).2 hA⟩

variable [Fintype Point] [DecidableLE Point] [DecidablePred (Complete (Point := Point))]

/-- The completions of a point: its complete extensions, a specification space in the reduced
sense of `Semantics.Supervaluation` (p. 277). -/
def completions (t : Point) : SpecSpace Point :=
  ⟨Finset.univ.filter λ u => t ≤ u ∧ Complete u, by
    obtain ⟨u, htu, hu⟩ := completable t
    exact ⟨u, by simp [htu, hu]⟩⟩

/-- Super-truth at a point is super-truth over its completions. -/
theorem superTrue_completions [DecidablePred A] :
    superTrue A (completions t) = .true ↔ SuperTrue A t := by
  rw [superTrue_true_iff]
  simp [completions, SuperTrue]

/-- Extension of points is inclusion of completions, the ordering of `SpecSpace`. -/
theorem completions_mono (htu : t ≤ u) : completions t ≤ completions u := by
  show (completions u).admissible ⊆ (completions t).admissible
  intro v hv
  simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact ⟨htu.trans hv.1, hv.2⟩

end Space

/-! ### Partial specifications -/

/-- A partial specification: each atom is True, False or undecided, ordered pointwise by the
knowledge order, so that `u` extends `t` when it assigns every definite value `t` does. -/
abbrev Specification (Atom : Type*) := Atom → Flat Bool

instance {Atom : Type*} : SpecificationSpace (Specification Atom) where
  Complete t := ∀ a, t a ≠ ⊥
  completable t := ⟨λ a => (t a).or ↑Bool.true, λ a => Flat.le_or_left _ _, λ a => by
    show (t a).or ↑Bool.true ≠ ⊥
    cases t a <;> exact Flat.coe_ne_bot⟩
  isMax_of_complete t ht _ htu a := (Flat.eq_of_le (htu a) λ _ => ht a).ge

/-- The trivalent model a specification determines. -/
def Specification.toModel {Atom : Type*} (t : Specification Atom) : Model Atom := ofFlat ∘ t

/-! ### The super-truth theory (§3) -/

section Account

variable {Point Sentence : Type*} [PartialOrder Point] [SpecificationSpace Point]

/-- An account of truth and falsity at points: the relations ⊨ and ⊣. -/
structure Account (Point Sentence : Type*) where
  verifies : Point → Sentence → Prop
  falsifies : Point → Sentence → Prop

/-- Fidelity: at complete points the account agrees with a classical valuation. -/
def Account.Faithful (V : Account Point Sentence) (c : Point → Sentence → Prop) : Prop :=
  ∀ t A, Complete t → (V.verifies t A ↔ c t A) ∧ (V.falsifies t A ↔ ¬ c t A)

/-- Stability: truth and falsity are preserved under extension. -/
def Account.Stable (V : Account Point Sentence) : Prop :=
  ∀ t u A, t ≤ u → (V.verifies t A → V.verifies u A) ∧ (V.falsifies t A → V.falsifies u A)

/-- Resolution at a sentence: what is not true is false at some extension, and what is not
false true at some extension. -/
def Account.Resolves (V : Account Point Sentence) (A : Sentence) : Prop :=
  ∀ t, (¬ V.verifies t A → ∃ u, t ≤ u ∧ V.falsifies u A) ∧
    (¬ V.falsifies t A → ∃ u, t ≤ u ∧ V.verifies u A)

/-- The super-truth account over a classical valuation. -/
def superTruth (c : Point → Sentence → Prop) : Account Point Sentence :=
  ⟨λ t A => SuperTrue (c · A) t, λ t A => SuperFalse (c · A) t⟩

theorem superTruth_faithful (c : Point → Sentence → Prop) : (superTruth c).Faithful c :=
  λ _ _ ht => ⟨superTrue_iff_of_complete ht, superFalse_iff_of_complete ht⟩

theorem superTruth_stable (c : Point → Sentence → Prop) : (superTruth c).Stable :=
  λ _ _ _ htu => ⟨(SuperTrue.mono · htu), (SuperFalse.mono · htu)⟩

theorem superTruth_resolves (c : Point → Sentence → Prop) (A : Sentence) :
    (superTruth c).Resolves A :=
  λ _ => ⟨exists_superFalse_of_not_superTrue, exists_superTrue_of_not_superFalse⟩

variable {V : Account Point Sentence} {c : Point → Sentence → Prop} {A : Sentence} {t : Point}

/-- Under Fidelity, Stability and Resolution at `A`, truth at a point is super-truth: Stability
carries truth up to every complete extension, and if some complete extension fails `A` while
the point does not verify it, Resolution falsifies `A` at an extension, Completability and
Stability at a complete one, where Fidelity contradicts. -/
theorem Account.verifies_iff (hF : V.Faithful c) (hS : V.Stable) (hR : V.Resolves A) :
    V.verifies t A ↔ SuperTrue (c · A) t := by
  refine ⟨λ h u htu hu => (hF u A hu).1.1 ((hS t u A htu).1 h), λ h => by_contra λ hn => ?_⟩
  obtain ⟨u, htu, hu⟩ := (hR t).1 hn
  obtain ⟨v, huv, hv⟩ := completable u
  exact (hF v A hv).2.1 ((hS u v A huv).2 hu) (h v (htu.trans huv) hv)

/-- The falsity half of `Account.verifies_iff`. -/
theorem Account.falsifies_iff (hF : V.Faithful c) (hS : V.Stable) (hR : V.Resolves A) :
    V.falsifies t A ↔ SuperFalse (c · A) t := by
  refine ⟨λ h u htu hu => (hF u A hu).2.1 ((hS t u A htu).2 h), λ h => by_contra λ hn => ?_⟩
  obtain ⟨u, htu, hu⟩ := (hR t).2 hn
  obtain ⟨v, huv, hv⟩ := completable u
  exact h v (htu.trans huv) hv ((hF v A hv).1.1 ((hS u v A huv).1 hu))

/-- The super-truth account is the only one satisfying Fidelity, Completability, Stability and
Resolution (§3). -/
theorem Account.eq_superTruth_of_resolves (hF : V.Faithful c) (hS : V.Stable)
    (hR : ∀ A, V.Resolves A) : V = superTruth c := by
  obtain ⟨ve, fa⟩ := V
  simp only [superTruth, Account.mk.injEq]
  exact ⟨funext₂ λ _ A => propext (Account.verifies_iff hF hS (hR A)),
    funext₂ λ _ A => propext (Account.falsifies_iff hF hS (hR A))⟩

end Account

section AClauses

variable {Point Atom : Type*} [PartialOrder Point] [SpecificationSpace Point]

open scoped Formula

/-- Classical truth of a sentence at a point, on the Boolean model of the point's atomic
values. -/
def classical (val : Point → Atom → Bool) (t : Point) (φ : Formula Atom) : Prop :=
  (ofBool ∘ val t) ⊨[.k3] φ

private theorem eval_ofBool_ne_indet (v : Atom → Bool) (φ : Formula Atom) :
    Formula.eval (ofBool ∘ v) φ ≠ .indet := by
  induction φ with
  | atom a => show ofBool (v a) ≠ .indet; cases v a <;> decide
  | neg φ ih => simpa using ih
  | conj φ ψ ihφ ihψ =>
    rcases min_choice (Formula.eval (ofBool ∘ v) φ) (Formula.eval (ofBool ∘ v) ψ) with h | h <;>
      simpa [h] using ‹_›

omit [PartialOrder Point] [SpecificationSpace Point] in
theorem classical_neg (val : Point → Atom → Bool) (t : Point) (φ : Formula Atom) :
    classical val t (.neg φ) ↔ ¬ classical val t φ := by
  unfold classical
  rw [Formula.realize_neg]
  have := eval_ofBool_ne_indet (val t) φ
  unfold Formula.Realize
  rcases h : Formula.eval (ofBool ∘ val t) φ with _ | _ | _ <;> simp_all

omit [PartialOrder Point] [SpecificationSpace Point] in
theorem classical_conj (val : Point → Atom → Bool) (t : Point) (φ ψ : Formula Atom) :
    classical val t (.conj φ ψ) ↔ classical val t φ ∧ classical val t ψ :=
  Formula.realize_conj _ _ _ _

/-- The A-clauses (§3): Resolution for atomic sentences; the classical clauses for negation; for
conjunction, truth of both conjuncts, and falsity that can always be redeemed by an extension
falsifying a conjunct. -/
structure Account.AClauses (V : Account Point (Formula Atom)) : Prop where
  resolves : ∀ a, V.Resolves (.atom a)
  verifies_neg : ∀ t φ, V.verifies t (.neg φ) ↔ V.falsifies t φ
  falsifies_neg : ∀ t φ, V.falsifies t (.neg φ) ↔ V.verifies t φ
  verifies_conj : ∀ t φ ψ, V.verifies t (.conj φ ψ) ↔ V.verifies t φ ∧ V.verifies t ψ
  falsifies_conj : ∀ t φ ψ, V.falsifies t (.conj φ ψ) ↔
    ∀ u, t ≤ u → ∃ v, u ≤ v ∧ (V.falsifies v φ ∨ V.falsifies v ψ)

variable {V : Account Point (Formula Atom)} {val : Point → Atom → Bool}

/-- Given Fidelity, Stability and Completability, the A-clauses are equivalent to the
super-truth account (§3): the claims of penumbral connection force the favoured view. -/
theorem Account.eq_superTruth_of_aClauses (hF : V.Faithful (classical val)) (hS : V.Stable)
    (hA : V.AClauses) : V = superTruth (classical val) := by
  suffices h : ∀ φ t, (V.verifies t φ ↔ SuperTrue (classical val · φ) t) ∧
      (V.falsifies t φ ↔ SuperFalse (classical val · φ) t) by
    obtain ⟨ve, fa⟩ := V
    simp only [superTruth, Account.mk.injEq]
    exact ⟨funext₂ λ t φ => propext (h φ t).1, funext₂ λ t φ => propext (h φ t).2⟩
  intro φ
  induction φ with
  | atom a =>
    exact λ t => ⟨Account.verifies_iff hF hS (hA.resolves a),
      Account.falsifies_iff hF hS (hA.resolves a)⟩
  | neg φ ih =>
    intro t
    rw [hA.verifies_neg, hA.falsifies_neg, (ih t).1, (ih t).2]
    refine ⟨?_, ?_⟩ <;> simp only [SuperTrue, SuperFalse, classical_neg, not_not]
  | conj φ ψ ihφ ihψ =>
    intro t
    constructor
    · rw [hA.verifies_conj, (ihφ t).1, (ihψ t).1]
      simp only [SuperTrue, classical_conj]
      exact ⟨λ ⟨h₁, h₂⟩ u htu hu => ⟨h₁ u htu hu, h₂ u htu hu⟩,
        λ h => ⟨λ u htu hu => (h u htu hu).1, λ u htu hu => (h u htu hu).2⟩⟩
    · rw [hA.falsifies_conj]
      simp only [(ihφ _).2, (ihψ _).2]
      constructor
      · intro h w htw hw
        obtain ⟨v, hwv, hv⟩ := h w htw
        have hvw := isMax_of_complete w hw hwv
        show ¬ classical val w (.conj φ ψ)
        rw [classical_conj, not_and_or]
        exact hv.imp (λ hf => hf w hvw hw) (λ hf => hf w hvw hw)
      · intro h u htu
        obtain ⟨v, huv, hv⟩ := completable u
        have := h v (htu.trans huv) hv
        change ¬ classical val v (.conj φ ψ) at this
        rw [classical_conj, not_and_or] at this
        exact ⟨v, huv, this.imp (λ hf => (superFalse_iff_of_complete hv).2 hf)
          (λ hf => (superFalse_iff_of_complete hv).2 hf)⟩

end AClauses

/-! ### The logic of vagueness (§4): *bald* -/

/-- The admissible thresholds for *bald*: a man is bald with fewer than `θ` hairs, and the
borderline cases are those with 40 to 60 hairs (§5). -/
def baldness : SpecSpace ℕ := ⟨Finset.Icc 40 60, ⟨40, by simp⟩⟩

/-- *A man with `n` hairs is bald* at threshold `θ`. -/
abbrev bald (n θ : ℕ) : Prop := n < θ

/-- Yul Brynner is bald, Mick Jagger is not, and Herbert, with fifty hairs, is a borderline
case. -/
theorem yulBrynner_herbert_mickJagger :
    superTrue (bald 0) baldness = .true ∧ superTrue (bald 50) baldness = .indet ∧
      superTrue (bald 100000) baldness = .false := by
  decide

/-- Herbert is a borderline case of a bald man. -/
theorem herbert_indet : superTrue (bald 50) baldness = .indet :=
  yulBrynner_herbert_mickJagger.2.1

/-- The law of excluded middle holds of Herbert though bivalence fails: *Herbert is bald or not
bald* is true while neither disjunct is. -/
theorem herbert_lem : superTrue (λ θ => bald 50 θ ∨ ¬ bald 50 θ) baldness = .true :=
  excludedMiddle_superTrue _ _

/-- The internal penumbral connection: if Herbert is to be bald, so is the man with fewer
hairs. -/
theorem bald_superConsequence {m n : ℕ} (h : m ≤ n) : superConsequence (bald n) (bald m) :=
  classical_implies_superConsequence _ _ λ _ hn => lt_of_le_of_lt h hn

/-- The sorites: its first premise is true, its tolerance premise false — a hair-splitting
number exists in every complete and admissible specification — and its conclusion false. -/
theorem sorites :
    superTrue (bald 0) baldness = .true ∧
      superTrue (λ θ => ∀ n, bald n θ → bald (n + 1) θ) baldness = .false ∧
      superTrue (bald 1000000) baldness = .false :=
  ⟨yulBrynner_herbert_mickJagger.1,
    (superTrue_false_iff _ _).2 λ θ hθ h => by
      have := Finset.mem_Icc.1 hθ
      exact absurd (h (θ - 1) (by unfold bald; omega)) (by unfold bald; omega),
    (superTrue_false_iff _ _).2 λ θ hθ h => by
      have := Finset.mem_Icc.1 hθ
      unfold bald at h
      omega⟩

/-- The tolerance premise is super-false. -/
theorem tolerance_superFalse :
    superTrue (λ θ => ∀ n, bald n θ → bald (n + 1) θ) baldness = .false :=
  sorites.2.1

/-! ### Higher-order vagueness (§5) -/

section Definitely

variable {Spec : Type*} (A : Spec → Prop) [DecidablePred A] (S : SpecSpace Spec)

/-- Axiom 4: `DA` and `DDA` coincide. -/
theorem definitely_definitely_iff :
    definitely (λ _ => definitely A S) S ↔ definitely A S :=
  ⟨λ h => let ⟨s, hs⟩ := S.nonempty; h s hs, λ h _ _ => h⟩

/-- Axiom 5: what is not definite is definitely not definite. -/
theorem not_definitely_definitely (h : ¬ definitely A S) :
    definitely (λ _ => ¬ definitely A S) S :=
  λ _ _ => h

/-- `B` is a consequence of `A` iff `DA ⊃ B` is valid (§5): the relation between consequence and
validity once the Deduction Theorem fails. -/
theorem superConsequence_iff_definitely_imp {B : Spec → Prop} [DecidablePred B] :
    superConsequence A B ↔
      ∀ S : SpecSpace Spec, superTrue (λ s => ¬ definitely A S ∨ B s) S = .true := by
  simp only [superConsequence, superTrue_true_iff]
  refine ⟨λ h S s hs => ?_, λ h S hA s hs => (h S s hs).resolve_left (not_not.2 hA)⟩
  by_cases hA : definitely A S
  · exact .inr (h S hA s hs)
  · exact .inl hA

end Definitely

/-- Spaces of order `n`: a zero-order space is a complete specification, an `(n + 1)`-order
space a set of `n`-order spaces. -/
abbrev Space (Spec : Type*) : ℕ → Type _
  | 0 => Spec
  | n + 1 => Set (Space Spec n)

/-- An ω-order boundary: a sequence of spaces of every order, each a member of the next. -/
structure Boundary (Spec : Type*) where
  s : ∀ n, Space Spec n
  mem : ∀ n, s n ∈ s (n + 1)

namespace Boundary

variable {Spec : Type*}

/-- Accessibility between boundaries: `c` is admissible from `b` when each of its spaces is a
member of the next space of `b`. -/
def R (b c : Boundary Spec) : Prop := ∀ i, c.s i ∈ b.s (i + 1)

/-- Accessibility is reflexive, so the logic of `D` is the modal system T. -/
theorem R_refl (b : Boundary Spec) : b.R b := b.mem

/-- `D φ` at a boundary: `φ` at every admissible boundary. -/
def Definitely (φ : Boundary Spec → Prop) (b : Boundary Spec) : Prop := ∀ c, b.R c → φ c

/-- Axiom T: what is definitely the case is the case. -/
theorem definitely_self {φ : Boundary Spec → Prop} {b : Boundary Spec} (h : Definitely φ b) :
    φ b :=
  h b b.R_refl

end Boundary

end Fine1975
