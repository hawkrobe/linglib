module

public import Mathlib.Order.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.Basic
public import Linglib.Logic.Trivalent.Flat
public import Linglib.Logic.Trivalent.Propositional
public import Linglib.Logic.Trivalent.Flat

/-!
# Fine (1975): Vagueness, truth and logic

Fine argues for the super-truth theory of vagueness. §1 treats Indefinite as a third truth-value: a
partial specification assigns True, False or Indefinite to the atomic sentences, and a
truth-functional valuation is constrained by Fidelity — classical on definite values — and Stability
— definite values preserved under extension (the knowledge order `SignType.toFlat`). Those two
conditions fix negation (`neg_eq_of_faithful_stable`) and leave a commutative conjunction exactly
the minimizing and maximizing options of Kleene's weak and strong tables
(`conj_eq_inf_or_meetWeak`). Yet no truth-functional account respects penumbral connection: with the
blob on the border of pink and red, *pink and red* is false while *pink and pink* is indefinite,
though every conjunct is indefinite (`maximal_pink_and_red`, `conj_not_truthFunctional`, and
likewise for disjunction). §2 answers with specification spaces: points partially ordered by
extension, complete points to which every point extends (Completability), and super-truth at a point
as truth at all its complete extensions (`SuperTrue`), which satisfies Fidelity and Stability
(`superTrue_iff_of_isMax`, `SuperTrue.mono`); the partial points are recovered from the complete
ones as the sets of their completions, extension becoming inclusion (`completions`,
`completions_mono`), and super-truth at a point is `SignType.supervaluation` over its completions
(`superTrue_completions`). §3 argues that the theory is forced: an account satisfying Fidelity,
Stability and Resolution is the super-truth account (`Account.eq_superTruth_of_resolves`), and the
A-clauses — Resolution for atoms, the classical clauses for negation, and for conjunction the truth
clause with the falsity clause that redeems its pledge — are equivalent to it
(`superTruth_aClauses`, `Account.eq_superTruth_of_aClauses`). §4 draws the logic: validity and
consequence are classical, since a classical model is a degenerate specification space
(`superValid_iff_classical`, `superConsequence_iff_classical`), the law of excluded middle holds
where bivalence fails (`herbert_lem`, `herbert_indet`), and the sorites' tolerance premise is false
because a hair-splitting number exists in every complete specification (`tolerance_superFalse`). §5
adds the definitely-operator: on the truth-value approach it breaks Stability
(`metaAssert_not_stable`); on specification spaces `I A := ¬DA ∧ ¬D¬A`, `D` is an S5 modality over
the complete specifications (`definitely_imp_valid`, `definitely_definitely_iff`,
`not_definitely_definitely`) whose falsity is not preserved into a more precise space
(`not_definitely_antitone`), the Deduction Theorem fails, `DA` being a consequence of `A` while
`A ⊃ DA` is indefinite where `A` is (`superTrue_definitely_of_superTrue`,
`superTrue_imp_definitely_of_indet`), and consequence is validity of `DA ⊃ B`
(`superConsequence_iff_definitely_imp`). Higher-order vagueness is truth relative to boundaries —
nested admissible spaces — under an accessibility that is reflexive but not transitive, so that the
logic of `D` is T (`Boundary.R_refl`, `Boundary.definitely_self`, `Boundary.R_not_trans`). The
construction is van Fraassen's supervaluation, whose conservative and radical variants are the
minimizing and maximizing options; Fine's note added in proof credits the same account of vagueness
to Kamp and to Lewis.

## Implementation notes

* A specification space is the class `SpecificationSpace` over a partial order: Completability,
  with the complete points the maximal ones. A complete point admits no proper extension when
  points are specifications (the extensional account of §2), and Fidelity needs it, since
  super-truth at a complete point with a further complete extension would not be classical;
  under Completability the maximal points are then exactly the complete ones.
  The §2 reduction takes a point to the finite set of its completions (`completions`); a reduced
  space is a `Finset` of complete specifications, more precise spaces being smaller sets.
* Partial specifications are `Atom → Flat Bool` with the pointwise knowledge order, so that
  extension is the order of `Flat`; they instantiate the class (`isMax_iff`). Connectives are
  evaluated on `SignType`, whose strong Kleene tables are the maximizing account and
  `meetWeak` the minimizing one; its logic with True designated (`Trivalent.k3_no_tautologies`)
  has no valid formulas, as §4 observes.
* The examples are Fine's: *bald* over hair counts with the admissible thresholds 40 to 60 of
  §5 (Herbert at 50 hairs, Yul Brynner at 0, the million-haired man), and the blob at hue 5
  with colour boundaries 3 to 7; the intuitionistic and anticipatory accounts, the infinite-
  order truth-values and the hierarchy of truth-predicates are not formalized.
* Sentences in §3 are `Trivalent.Formula` without quantifiers, so the A-clause for `∀` is
  absent; they are classically evaluated at a point by `Formula.evalBool` on the point's atomic
  values, which is their K3 realization on that Boolean model (`Formula.realize_ofProp`).

## References

* [fine-1975]
* [kleene-1952]
* [van-fraassen-1966]
* [van-fraassen-1969]
* [kamp-1975]
* [lewis-1970]
-/

@[expose] public section

namespace Fine1975

open SignType
open Trivalent (Formula)

/-! ### The truth-value approach (§1) -/

section TruthValue

/-- A connective satisfies Fidelity when it is classical on definite values. -/
def Faithful (f : SignType → SignType → SignType) (g : Bool → Bool → Bool) : Prop :=
  ∀ x y : Bool, f (ofProp x) (ofProp y) = ofProp (g x y)

/-- A connective satisfies Stability when it preserves definite values as its arguments are
extended, that is, when it is monotone in the knowledge order. -/
def Stable (f : SignType → SignType → SignType) : Prop :=
  ∀ a a' b b', toFlat a ≤ toFlat a' → toFlat b ≤ toFlat b' → toFlat (f a b) ≤ toFlat (f a' b')

private theorem eq_zero_of_le (v : SignType) (h₁ : toFlat v ≤ toFlat 1)
    (h₂ : toFlat v ≤ toFlat (-1)) : v = 0 := by
  cases v <;> revert h₁ h₂ <;> decide

/-- Fidelity and Stability determine negation as [kleene-1952]'s. -/
theorem neg_eq_of_faithful_stable (n : SignType → SignType)
    (hF : ∀ x : Bool, n (ofProp x) = ofProp (!x))
    (hS : ∀ a a', toFlat a ≤ toFlat a' → toFlat (n a) ≤ toFlat (n a')) : n = Neg.neg := by
  have hT : n 1 = -1 := hF Bool.true
  have hFa : n (-1) = 1 := hF Bool.false
  funext a
  cases a
  · exact eq_zero_of_le _ (hFa ▸ hS 0 (-1) bot_le) (hT ▸ hS 0 1 bot_le)
  · exact hFa
  · exact hT

/-- A commutative conjunction satisfying Fidelity and Stability is the maximizing strong Kleene
`⊓` or the minimizing weak Kleene `meetWeak`, which differ only on an indefinite conjunct beside a
false one. -/
theorem conj_eq_inf_or_meetWeak (f : SignType → SignType → SignType) (hF : Faithful f (· && ·))
    (hS : Stable f) (hC : ∀ a b, f a b = f b a) : f = (· ⊓ ·) ∨ f = meetWeak := by
  have hTT : f 1 1 = 1 := hF Bool.true Bool.true
  have hTF : f 1 (-1) = -1 := hF Bool.true Bool.false
  have hFT : f (-1) 1 = -1 := hF Bool.false Bool.true
  have hFF : f (-1) (-1) = -1 := hF Bool.false Bool.false
  have hIT : f 0 1 = 0 := eq_zero_of_le _
    (by simpa only [hTT] using hS 0 1 1 1 bot_le le_rfl)
    (by simpa only [hFT] using hS 0 (-1) 1 1 bot_le le_rfl)
  have hII : f 0 0 = 0 := eq_zero_of_le _
    (by simpa only [hTT] using hS 0 1 0 1 bot_le bot_le)
    (by simpa only [hFF] using hS 0 (-1) 0 (-1) bot_le bot_le)
  have hIF : f 0 (-1) ≠ 1 := fun h ↦ by
    have := hS 0 1 (-1) (-1) bot_le le_rfl
    rw [h, hTF] at this
    exact absurd this (by decide)
  obtain h | h | h := (f 0 (-1)).trichotomy
  · left
    funext a b
    cases a <;> cases b <;> simp only [zero_eq_zero, neg_eq_neg_one, pos_eq_one, hTT, hTF, hFT,
      hFF, hIT, hII, h, hC 1 0, hC (-1) 0] <;> decide
  · right
    funext a b
    cases a <;> cases b <;> simp only [zero_eq_zero, neg_eq_neg_one, pos_eq_one, hTT, hTF, hFT,
      hFF, hIT, hII, h, hC 1 0, hC (-1) 0] <;> decide
  · exact absurd h hIF

/-! The blob on the border of pink and red (§1, §3): a colour boundary between hue 3 and hue 7
is admissible, the blob has hue 5, and *pink* is above the boundary, *red* at or below it. -/

/-- The admissible colour boundaries. -/
def colour : Finset ℕ := Finset.Icc 3 7

/-- *x is pink* when its hue is above the boundary. -/
abbrev pink (hue θ : ℕ) : Prop := θ < hue

/-- *x is red* when its hue is at or below the boundary. -/
abbrev red (hue θ : ℕ) : Prop := hue ≤ θ

/-- *The blob is pink* is indefinite. -/
theorem pink_indet : supervaluation colour (pink 5) = 0 := by decide

/-- *The blob is red* is indefinite. -/
theorem red_indet : supervaluation colour (red 5) = 0 := by decide

/-- *The blob is pink and red* is false, since the predicates are contraries. -/
theorem pink_and_red_false : supervaluation colour (fun θ ↦ pink 5 θ ∧ red 5 θ) = -1 := by
  decide

/-- *The blob is pink or red* is true, since the predicates are complementary over the range. -/
theorem pink_or_red_true : supervaluation colour (fun θ ↦ pink 5 θ ∨ red 5 θ) = 1 := by decide

/-- *If the blob is pink, it is not red* is a penumbral truth, where *if pink, not pink* is not
true. -/
theorem pink_imp_not_red_true : supervaluation colour (fun θ ↦ pink 5 θ → ¬ red 5 θ) = 1 := by
  decide

theorem pink_imp_not_pink_indet :
    supervaluation colour (fun θ ↦ pink 5 θ → ¬ pink 5 θ) = 0 := by decide

/-- Even the maximizing account makes *pink and red* indefinite, as both conjuncts are. -/
theorem maximal_pink_and_red :
    supervaluation colour (pink 5) ⊓ supervaluation colour (red 5) = 0 := by
  decide

/-- No truth-functional conjunction respects penumbral connection, since *pink and pink* and
*pink and red* have indefinite conjuncts alike, but the first is indefinite and the second
false. -/
theorem conj_not_truthFunctional :
    ¬ ∃ f : SignType → SignType → SignType, ∀ (P Q : ℕ → Prop) [DecidablePred P]
      [DecidablePred Q], supervaluation colour (fun θ ↦ P θ ∧ Q θ) = f (supervaluation colour P)
        (supervaluation colour Q) := by
  rintro ⟨f, hf⟩
  have h₁ := hf (pink 5) (pink 5)
  have h₂ := hf (pink 5) (red 5)
  rw [pink_indet, red_indet] at h₂
  rw [pink_indet, ← h₂, pink_and_red_false] at h₁
  exact absurd h₁ (by decide)

/-- Nor does any truth-functional disjunction, since *pink or pink* is indefinite and *pink or
red* true. -/
theorem disj_not_truthFunctional :
    ¬ ∃ f : SignType → SignType → SignType, ∀ (P Q : ℕ → Prop) [DecidablePred P]
      [DecidablePred Q], supervaluation colour (fun θ ↦ P θ ∨ Q θ) = f (supervaluation colour P)
        (supervaluation colour Q) := by
  rintro ⟨f, hf⟩
  have h₁ := hf (pink 5) (pink 5)
  have h₂ := hf (pink 5) (red 5)
  rw [pink_indet, red_indet] at h₂
  rw [pink_indet, ← h₂, pink_or_red_true] at h₁
  exact absurd h₁ (by decide)

end TruthValue

/-! ### Specification spaces (§2) -/

/-- In a specification space the points are partially ordered by extension, every point extends
to a complete point (Completability), and the complete points are the maximal ones. -/
class SpecificationSpace (Point : Type*) [PartialOrder Point] : Prop where
  /-- Every point extends to a complete point (Completability). -/
  completable : ∀ t : Point, ∃ u, t ≤ u ∧ IsMax u

export SpecificationSpace (completable)

section Space

variable {Point : Type*} [PartialOrder Point] {A B : Point → Prop} {t u : Point}

/-- A sentence is super-true at a point when it is true at every complete extension. -/
def SuperTrue (A : Point → Prop) (t : Point) : Prop := ∀ u, t ≤ u → IsMax u → A u

/-- A sentence is super-false at a point when it is false at every complete extension. -/
def SuperFalse (A : Point → Prop) (t : Point) : Prop := ∀ u, t ≤ u → IsMax u → ¬ A u

/-- At a complete point super-truth is classical truth (Fidelity). -/
theorem superTrue_iff_of_isMax (ht : IsMax t) : SuperTrue A t ↔ A t :=
  ⟨fun h ↦ h t le_rfl ht, fun h _ htu _ ↦ ht.eq_of_le htu ▸ h⟩

/-- Fidelity for falsity. -/
theorem superFalse_iff_of_isMax (ht : IsMax t) : SuperFalse A t ↔ ¬ A t :=
  superTrue_iff_of_isMax ht

/-- Super-truth is preserved under extension (Stability). -/
theorem SuperTrue.mono (h : SuperTrue A t) (htu : t ≤ u) : SuperTrue A u :=
  fun _ huv hv ↦ h _ (htu.trans huv) hv

/-- Stability for falsity. -/
theorem SuperFalse.mono (h : SuperFalse A t) (htu : t ≤ u) : SuperFalse A u :=
  SuperTrue.mono h htu

/-- A sentence not super-true at a point is super-false at some extension (Resolution). -/
theorem exists_superFalse_of_not_superTrue (h : ¬ SuperTrue A t) :
    ∃ u, t ≤ u ∧ SuperFalse A u := by
  simp only [SuperTrue, not_forall] at h
  obtain ⟨u, htu, hu, hA⟩ := h
  exact ⟨u, htu, (superFalse_iff_of_isMax hu).2 hA⟩

/-- Resolution for falsity. -/
theorem exists_superTrue_of_not_superFalse (h : ¬ SuperFalse A t) :
    ∃ u, t ≤ u ∧ SuperTrue A u := by
  simp only [SuperFalse, not_forall, not_not] at h
  obtain ⟨u, htu, hu, hA⟩ := h
  exact ⟨u, htu, (superTrue_iff_of_isMax hu).2 hA⟩

/-- Super-truth of `¬A` is super-falsity of `A`. -/
theorem superTrue_not_iff : SuperTrue (fun u ↦ ¬ A u) t ↔ SuperFalse A t := Iff.rfl

theorem superFalse_not_iff : SuperFalse (fun u ↦ ¬ A u) t ↔ SuperTrue A t := by
  simp only [SuperFalse, SuperTrue, not_not]

/-- A conjunction is super-true iff both conjuncts are. -/
theorem superTrue_and_iff :
    SuperTrue (fun u ↦ A u ∧ B u) t ↔ SuperTrue A t ∧ SuperTrue B t :=
  ⟨fun h ↦ ⟨fun u htu hu ↦ (h u htu hu).1, fun u htu hu ↦ (h u htu hu).2⟩,
    fun h u htu hu ↦ ⟨h.1 u htu hu, h.2 u htu hu⟩⟩

section Completions

variable [Fintype Point] [DecidableLE Point] [DecidablePred (IsMax (α := Point))]

/-- The completions of a point are its complete extensions, Fine's reduced specification space. -/
def completions (t : Point) : Finset Point := Finset.univ.filter fun u ↦ t ≤ u ∧ IsMax u

theorem completions_nonempty [SpecificationSpace Point] (t : Point) :
    (completions t).Nonempty := by
  obtain ⟨u, htu, hu⟩ := completable t
  exact ⟨u, by simp [completions, htu, hu]⟩

/-- Super-truth at a point is super-truth over its completions. -/
theorem superTrue_completions [DecidablePred A] :
    supervaluation (completions t) A = 1 ↔ SuperTrue A t := by
  rw [supervaluation_eq_one_iff]
  simp [completions, SuperTrue]

/-- Extension of points is reverse inclusion of completions. -/
theorem completions_mono (htu : t ≤ u) : completions u ⊆ completions t := by
  intro v hv
  simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact ⟨htu.trans hv.1, hv.2⟩

end Completions

variable [SpecificationSpace Point]

/-- A conjunction is super-false iff every extension has a further extension at which a
conjunct is super-false, so that the falsehood pledge is redeemed. -/
theorem superFalse_and_iff :
    SuperFalse (fun u ↦ A u ∧ B u) t ↔
      ∀ u, t ≤ u → ∃ v, u ≤ v ∧ (SuperFalse A v ∨ SuperFalse B v) := by
  constructor
  · intro h u htu
    obtain ⟨v, huv, hv⟩ := completable u
    exact ⟨v, huv, (not_and_or.1 (h v (htu.trans huv) hv)).imp
      (superFalse_iff_of_isMax hv).2 (superFalse_iff_of_isMax hv).2⟩
  · intro h w htw hw
    obtain ⟨v, hwv, hv⟩ := h w htw
    have hvw := hw hwv
    exact not_and_or.2 (hv.imp (fun hf ↦ hf w hvw hw) (fun hf ↦ hf w hvw hw))

end Space

/-! ### Partial specifications -/

/-- A partial specification makes each atom True, False or undecided. It is ordered pointwise by
the knowledge order, so that `u` extends `t` when it assigns every definite value `t` does. -/
abbrev Specification (Atom : Type*) := Atom → Flat Bool

/-- A specification is complete, maximal in the extension order, iff it decides every atom. -/
theorem isMax_iff {Atom : Type*} {t : Specification Atom} : IsMax t ↔ ∀ a, t a ≠ ⊥ := by
  classical
  constructor
  · intro ht a hbot
    have := ht (b := fun b ↦ if b = a then ↑Bool.true else t b) fun b ↦ by
      by_cases hb : b = a
      · subst hb; simp [hbot]
      · simp [hb]
    simpa [hbot] using this a
  · intro ht _ htu a
    exact (Flat.eq_of_le (htu a) fun _ ↦ ht a).ge

instance {Atom : Type*} : SpecificationSpace (Specification Atom) where
  completable t := ⟨fun a ↦ (t a).or ↑Bool.true, fun a ↦ Flat.le_or_left _ _, isMax_iff.2 fun a ↦ by
    show (t a).or ↑Bool.true ≠ ⊥
    cases t a <;> exact Flat.coe_ne_bot⟩

/-! ### The super-truth theory (§3) -/

section Account

variable {Point Sentence : Type*} [PartialOrder Point]

/-- An account of truth and falsity at points gives the relations ⊨ and ⊣. -/
structure Account (Point Sentence : Type*) where
  verifies : Point → Sentence → Prop
  falsifies : Point → Sentence → Prop

/-- At complete points the account agrees with a classical valuation (Fidelity). -/
def Account.Faithful (V : Account Point Sentence) (c : Point → Sentence → Prop) : Prop :=
  ∀ t A, IsMax t → (V.verifies t A ↔ c t A) ∧ (V.falsifies t A ↔ ¬ c t A)

/-- Truth and falsity are preserved under extension (Stability). -/
def Account.Stable (V : Account Point Sentence) : Prop :=
  ∀ t u A, t ≤ u → (V.verifies t A → V.verifies u A) ∧ (V.falsifies t A → V.falsifies u A)

/-- Resolution holds at a sentence when what is not true is false at some extension, and what is
not false is true at some extension. -/
def Account.Resolves (V : Account Point Sentence) (A : Sentence) : Prop :=
  ∀ t, (¬ V.verifies t A → ∃ u, t ≤ u ∧ V.falsifies u A) ∧
    (¬ V.falsifies t A → ∃ u, t ≤ u ∧ V.verifies u A)

/-- The super-truth account over a classical valuation. -/
def superTruth (c : Point → Sentence → Prop) : Account Point Sentence :=
  ⟨fun t A ↦ SuperTrue (c · A) t, fun t A ↦ SuperFalse (c · A) t⟩

theorem superTruth_faithful (c : Point → Sentence → Prop) : (superTruth c).Faithful c :=
  fun _ _ ht ↦ ⟨superTrue_iff_of_isMax ht, superFalse_iff_of_isMax ht⟩

theorem superTruth_stable (c : Point → Sentence → Prop) : (superTruth c).Stable :=
  fun _ _ _ htu ↦ ⟨(SuperTrue.mono · htu), (SuperFalse.mono · htu)⟩

theorem superTruth_resolves (c : Point → Sentence → Prop) (A : Sentence) :
    (superTruth c).Resolves A :=
  fun _ ↦ ⟨exists_superFalse_of_not_superTrue, exists_superTrue_of_not_superFalse⟩

variable [SpecificationSpace Point] {V : Account Point Sentence} {c : Point → Sentence → Prop}
  {A : Sentence} {t : Point}

/-- Under Fidelity, Stability and Resolution at `A`, truth at a point is super-truth. Stability
carries truth up to every complete extension, and if some complete extension fails `A` while
the point does not verify it, Resolution falsifies `A` at an extension, Completability and
Stability at a complete one, where Fidelity contradicts. -/
theorem Account.verifies_iff (hF : V.Faithful c) (hS : V.Stable) (hR : V.Resolves A) :
    V.verifies t A ↔ SuperTrue (c · A) t := by
  refine ⟨fun h u htu hu ↦ (hF u A hu).1.1 ((hS t u A htu).1 h), fun h ↦ by_contra fun hn ↦ ?_⟩
  obtain ⟨u, htu, hu⟩ := (hR t).1 hn
  obtain ⟨v, huv, hv⟩ := completable u
  exact (hF v A hv).2.1 ((hS u v A huv).2 hu) (h v (htu.trans huv) hv)

/-- The falsity half of `Account.verifies_iff`. -/
theorem Account.falsifies_iff (hF : V.Faithful c) (hS : V.Stable) (hR : V.Resolves A) :
    V.falsifies t A ↔ SuperFalse (c · A) t := by
  refine ⟨fun h u htu hu ↦ (hF u A hu).2.1 ((hS t u A htu).2 h), fun h ↦ by_contra fun hn ↦ ?_⟩
  obtain ⟨u, htu, hu⟩ := (hR t).2 hn
  obtain ⟨v, huv, hv⟩ := completable u
  exact h v (htu.trans huv) hv ((hF v A hv).1.1 ((hS u v A huv).1 hu))

/-- The super-truth account is the only one satisfying Fidelity, Completability, Stability and
Resolution (§3). -/
theorem Account.eq_superTruth_of_resolves (hF : V.Faithful c) (hS : V.Stable)
    (hR : ∀ A, V.Resolves A) : V = superTruth c := by
  obtain ⟨ve, fa⟩ := V
  simp only [superTruth, Account.mk.injEq]
  exact ⟨funext₂ fun _ A ↦ propext (Account.verifies_iff hF hS (hR A)),
    funext₂ fun _ A ↦ propext (Account.falsifies_iff hF hS (hR A))⟩

end Account

section AClauses

variable {Point Atom : Type*}

/-- Classical truth of a sentence at a point, on the point's atomic values. -/
def classical (val : Point → Atom → Bool) (t : Point) (φ : Formula Atom) : Prop :=
  φ.evalBool (val t) = Bool.true

theorem classical_neg (val : Point → Atom → Bool) (t : Point) (φ : Formula Atom) :
    classical val t (.neg φ) ↔ ¬ classical val t φ := by
  simp [classical]

theorem classical_conj (val : Point → Atom → Bool) (t : Point) (φ ψ : Formula Atom) :
    classical val t (.conj φ ψ) ↔ classical val t φ ∧ classical val t ψ := by
  simp [classical]

variable [PartialOrder Point] [SpecificationSpace Point]

/-- The A-clauses of §3 are Resolution for atomic sentences, the classical clauses for negation,
and for conjunction truth of both conjuncts and falsity that an extension falsifying a conjunct
can always redeem. -/
structure Account.AClauses (V : Account Point (Formula Atom)) : Prop where
  resolves : ∀ a, V.Resolves (.atom a)
  verifies_neg : ∀ t φ, V.verifies t (.neg φ) ↔ V.falsifies t φ
  falsifies_neg : ∀ t φ, V.falsifies t (.neg φ) ↔ V.verifies t φ
  verifies_conj : ∀ t φ ψ, V.verifies t (.conj φ ψ) ↔ V.verifies t φ ∧ V.verifies t ψ
  falsifies_conj : ∀ t φ ψ, V.falsifies t (.conj φ ψ) ↔
    ∀ u, t ≤ u → ∃ v, u ≤ v ∧ (V.falsifies v φ ∨ V.falsifies v ψ)

variable {V : Account Point (Formula Atom)} {val : Point → Atom → Bool}

/-- The super-truth account satisfies the A-clauses. -/
theorem superTruth_aClauses (val : Point → Atom → Bool) :
    (superTruth (classical val)).AClauses where
  resolves a := superTruth_resolves (classical val) (Formula.atom a)
  verifies_neg _ φ := by simp only [superTruth, classical_neg, superTrue_not_iff]
  falsifies_neg _ φ := by simp only [superTruth, classical_neg, superFalse_not_iff]
  verifies_conj _ φ ψ := by simp only [superTruth, classical_conj, superTrue_and_iff]
  falsifies_conj _ φ ψ := by simp only [superTruth, classical_conj, superFalse_and_iff]

/-- Given Fidelity, Stability and Completability, the A-clauses force the super-truth account
(§3), so the claims of penumbral connection force the favoured view. -/
theorem Account.eq_superTruth_of_aClauses (hF : V.Faithful (classical val)) (hS : V.Stable)
    (hA : V.AClauses) : V = superTruth (classical val) := by
  suffices h : ∀ φ t, (V.verifies t φ ↔ SuperTrue (classical val · φ) t) ∧
      (V.falsifies t φ ↔ SuperFalse (classical val · φ) t) by
    obtain ⟨ve, fa⟩ := V
    simp only [superTruth, Account.mk.injEq]
    exact ⟨funext₂ fun t φ ↦ propext (h φ t).1, funext₂ fun t φ ↦ propext (h φ t).2⟩
  intro φ
  induction φ with
  | atom a =>
    exact fun t ↦ ⟨Account.verifies_iff hF hS (hA.resolves a),
      Account.falsifies_iff hF hS (hA.resolves a)⟩
  | neg φ ih =>
    intro t
    rw [hA.verifies_neg, hA.falsifies_neg, (ih t).1, (ih t).2]
    simp only [SuperTrue, SuperFalse, classical_neg, not_not, and_self]
  | conj φ ψ ihφ ihψ =>
    intro t
    rw [hA.verifies_conj, hA.falsifies_conj, (ihφ t).1, (ihψ t).1]
    simp only [(ihφ _).2, (ihψ _).2]
    constructor
    · simp only [superTrue_and_iff, classical_conj]
    · simp only [superFalse_and_iff, classical_conj]

end AClauses

/-! ### The logic of vagueness (§4) -/

section Logic

variable {Spec : Type*} (A B : Spec → Prop) [DecidablePred A] [DecidablePred B]

/-- A sentence is valid when it is super-true in every specification space. -/
def SuperValid : Prop := ∀ S : Finset Spec, supervaluation S A = 1

/-- `B` is a consequence of `A` when it is super-true in every specification space in which `A`
is. -/
def SuperConsequence : Prop :=
  ∀ S : Finset Spec, supervaluation S A = 1 → supervaluation S B = 1

/-- Validity is classical, since a classically valid sentence is true at every complete
specification of every space, and a classical model is a degenerate space. -/
theorem superValid_iff_classical : SuperValid A ↔ ∀ s, A s :=
  ⟨fun h s ↦ by simpa using h {s},
    fun h S ↦ (supervaluation_eq_one_iff ..).2 fun s _ ↦ h s⟩

/-- Consequence is classical, by the same argument. -/
theorem superConsequence_iff_classical : SuperConsequence A B ↔ ∀ s, A s → B s := by
  refine ⟨fun h s hA ↦ by simpa using h {s} (by simp [hA]), fun h S hA ↦ ?_⟩
  rw [supervaluation_eq_one_iff] at hA ⊢
  exact fun s hs ↦ h s (hA s hs)

end Logic

/-! ### *bald* -/

/-- The admissible thresholds for *bald* make a man bald with fewer than `θ` hairs, the borderline
cases being those with 40 to 60 hairs (§5). -/
def baldness : Finset ℕ := Finset.Icc 40 60

/-- *A man with `n` hairs is bald* at threshold `θ`. -/
abbrev bald (n θ : ℕ) : Prop := n < θ

/-- Yul Brynner is bald. -/
theorem yulBrynner_bald : supervaluation baldness (bald 0) = 1 := by decide

/-- Mick Jagger is not. -/
theorem mickJagger_not_bald : supervaluation baldness (bald 100000) = -1 := by decide

/-- Herbert, with fifty hairs, is a borderline case of a bald man. -/
theorem herbert_indet : supervaluation baldness (bald 50) = 0 := by decide

/-- The law of excluded middle holds of Herbert though bivalence fails, *Herbert is bald or not
bald* being true while neither disjunct is. -/
theorem herbert_lem : supervaluation baldness (fun θ ↦ bald 50 θ ∨ ¬ bald 50 θ) = 1 :=
  (supervaluation_eq_one_iff ..).2 fun _ _ ↦ Decidable.em _

/-- By the internal penumbral connection, if Herbert is to be bald, so is the man with fewer
hairs. -/
theorem bald_superConsequence {m n : ℕ} (h : m ≤ n) : SuperConsequence (bald n) (bald m) :=
  (superConsequence_iff_classical _ _).2 fun _ hn ↦ lt_of_le_of_lt h hn

/-- The sorites' tolerance premise is false, since a hair-splitting number exists in every
complete and admissible specification. -/
theorem tolerance_superFalse :
    supervaluation baldness (fun θ ↦ ∀ n, bald n θ → bald (n + 1) θ) = -1 :=
  (supervaluation_eq_neg_one_iff ..).2 ⟨⟨40, by simp [baldness]⟩, fun θ hθ h ↦ by
    have := Finset.mem_Icc.1 hθ
    exact absurd (h (θ - 1) (by unfold bald; omega)) (by unfold bald; omega)⟩

/-- In the sorites, the first premise is true, the tolerance premise false, and the conclusion
false. -/
theorem sorites :
    supervaluation baldness (bald 0) = 1 ∧
      supervaluation baldness (fun θ ↦ ∀ n, bald n θ → bald (n + 1) θ) = -1 ∧
      supervaluation baldness (bald 1000000) = -1 :=
  ⟨yulBrynner_bald, tolerance_superFalse, by decide⟩

/-! ### Higher-order vagueness (§5) -/

/-- On the truth-value approach `D` is the assertion `ofProp (a = 1)`, true of the true and
false of the rest, and Stability fails, since `DA` is false for `A` indefinite but true for `A`
true. -/
theorem metaAssert_not_stable :
    ¬ ∀ a b, toFlat a ≤ toFlat b → toFlat (ofProp (a = 1)) ≤ toFlat (ofProp (b = 1)) :=
  fun h ↦ absurd (h 0 1 bot_le) (by decide)

section Definitely

variable {Spec : Type*} (A : Spec → Prop) (S : Finset Spec)

/-- Fine's `D` says that `A` holds at every admissible specification. -/
def definitely : Prop := ∀ s ∈ S, A s

/-- `DA` and `DDA` coincide (Axiom 4). -/
theorem definitely_definitely_iff :
    definitely (fun _ ↦ definitely A S) S ↔ definitely A S :=
  ⟨fun h s hs ↦ h s hs s hs, fun h _ _ ↦ h⟩

/-- What is not definite is definitely not definite (Axiom 5). -/
theorem not_definitely_definitely (h : ¬ definitely A S) :
    definitely (fun _ ↦ ¬ definitely A S) S :=
  fun _ _ ↦ h

variable [DecidablePred A]

instance : Decidable (definitely A S) := inferInstanceAs (Decidable (∀ s ∈ _, _))

/-- `DA ⊃ A` is valid (Axiom T). -/
theorem definitely_imp_valid :
    supervaluation S (fun s ↦ ¬ definitely A S ∨ A s) = 1 :=
  (supervaluation_eq_one_iff ..).2 fun s hs ↦
    (Decidable.em (definitely A S)).symm.imp_right (· s hs)

/-- `DA` is a consequence of `A`, since to assert `A` is to assert `DA`. -/
theorem superTrue_definitely_of_superTrue (h : supervaluation S A = 1) :
    supervaluation S (fun _ : Spec ↦ definitely A S) = 1 :=
  (supervaluation_eq_one_iff ..).2 fun _ _ ↦ (supervaluation_eq_one_iff ..).1 h

/-- Yet `A ⊃ DA` is not valid, since where `A` is indefinite `DA` fails and `A ⊃ DA` inherits the
indefiniteness of `¬A`. -/
theorem superTrue_imp_definitely_of_indet (h : supervaluation S A = 0) :
    supervaluation S (fun s ↦ ¬ A s ∨ definitely A S) = 0 := by
  have hD : ¬ definitely A S := fun hD ↦ by simp [(supervaluation_eq_one_iff ..).2 hD] at h
  simp only [hD, or_false]
  obtain ⟨⟨s, hs, -⟩, -⟩ := (supervaluation_eq_zero_iff ..).1 h
  rw [supervaluation_not _ ⟨s, hs⟩, h]
  rfl

/-- So *if Herbert is bald, he is definitely bald* is not true, and the Deduction Theorem
fails. -/
theorem herbert_not_imp_definitely :
    supervaluation baldness (fun θ ↦ ¬ bald 50 θ ∨ definitely (bald 50) baldness) ≠ 1 := by
  rw [superTrue_imp_definitely_of_indet _ _ herbert_indet]
  decide

/-- `B` is a consequence of `A` iff `DA ⊃ B` is valid (§5), which relates consequence to validity
once the Deduction Theorem fails. -/
theorem superConsequence_iff_definitely_imp {B : Spec → Prop} [DecidablePred B] :
    SuperConsequence A B ↔
      ∀ S : Finset Spec, supervaluation S (fun s ↦ ¬ definitely A S ∨ B s) = 1 := by
  simp only [SuperConsequence, supervaluation_eq_one_iff]
  refine ⟨fun h S s hs ↦ ?_, fun h S hA s hs ↦ (h S s hs).resolve_left (not_not.2 hA)⟩
  by_cases hA : definitely A S
  · exact .inr (h S hA s hs)
  · exact .inl hA

end Definitely

/-- External Stability fails for `D`, as *definitely Herbert is bald* is false over the admissible
thresholds but true once the threshold is fixed at 60, a more precise space. -/
theorem not_definitely_antitone :
    {60} ⊆ baldness ∧ ¬ definitely (bald 50) baldness ∧ definitely (bald 50) {60} :=
  ⟨by simp [baldness], by decide, by decide⟩

/-- A zero-order space is a complete specification, and an `(n + 1)`-order space is a set of
`n`-order spaces. -/
abbrev Space (Spec : Type*) : ℕ → Type _
  | 0 => Spec
  | n + 1 => Set (Space Spec n)

/-- An ω-order boundary is a sequence of spaces of every order, each a member of the next. -/
structure Boundary (Spec : Type*) where
  s : ∀ n, Space Spec n
  mem : ∀ n, s n ∈ s (n + 1)

namespace Boundary

variable {Spec : Type*}

/-- A boundary `c` is admissible from `b` when each of its spaces is a member of the next space
of `b`. -/
def R (b c : Boundary Spec) : Prop := ∀ i, c.s i ∈ b.s (i + 1)

/-- Accessibility is reflexive. -/
theorem R_refl (b : Boundary Spec) : b.R b := b.mem

/-- `D φ` holds at a boundary when `φ` holds at every admissible boundary. -/
def Definitely (φ : Boundary Spec → Prop) (b : Boundary Spec) : Prop := ∀ c, b.R c → φ c

/-- What is definitely the case is the case (Axiom T). -/
theorem definitely_self {φ : Boundary Spec → Prop} {b : Boundary Spec} (h : Definitely φ b) :
    φ b :=
  h b b.R_refl

/-- The higher spaces of the witness boundaries are `{{true}, {true, false}}`, then
singletons. -/
private noncomputable def tower : ∀ n, Space Bool (n + 2)
  | 0 => {{Bool.true}, {Bool.true, Bool.false}}
  | n + 1 => {tower n}

private noncomputable def seq (x : Bool) (s : Set Bool) : ∀ n, Space Bool n
  | 0 => x
  | 1 => s
  | n + 2 => tower n

/-- A boundary over `Bool` from its first two spaces. -/
private noncomputable def ofHead (x : Bool) (s : Set Bool) (hx : x ∈ s) (hs : s ∈ tower 0) :
    Boundary Bool where
  s := seq x s
  mem
    | 0 => hx
    | 1 => hs
    | n + 2 => Set.mem_singleton (tower n)

/-- Accessibility is not transitive, so the logic of `D` is T and not S4. From the boundary
that fixes `true` and `{true}`, the one fixing `true` and `{true, false}` is admissible, and
from it the one fixing `false` and `{true, false}`, which is not admissible from the first. -/
theorem R_not_trans : ¬ ∀ b c d : Boundary Bool, b.R c → c.R d → b.R d := by
  intro h
  have := h (ofHead Bool.true {Bool.true} rfl (by simp [tower]))
    (ofHead Bool.true {Bool.true, Bool.false} (by simp) (by simp [tower]))
    (ofHead Bool.false {Bool.true, Bool.false} (by simp) (by simp [tower]))
    (fun i ↦ by rcases i with _ | _ | i <;> simp [ofHead, seq, tower])
    (fun i ↦ by rcases i with _ | _ | i <;> simp [ofHead, seq, tower])
  simpa [ofHead, seq, R] using this 0

end Boundary

end Fine1975
