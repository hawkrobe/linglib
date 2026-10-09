module

public import Linglib.Semantics.Presupposition.Basic

/-!
# Rival trivalent connective families

The rival connective families on `PartialProp`, beyond the classical (Weak Kleene) and
filtering (Middle Kleene) canon of `Presupposition.Basic`: Strong Kleene, Belnap conditional
assertion, and the symmetric two-dimensional disjunction of the Karttunen–Peters tradition.
The first two descend along `eval` to operations on `Trivalent` like the canon; the
two-dimensional disjunction provably does not (`orKPSymmetric_not_trivalent`), because its
presupposition reads the disjuncts' assertion values at worlds where their presuppositions
fail — the dimension `eval` forgets. This is what makes `PartialProp` strictly more
expressive than trivalent propositions.

## Main declarations

* `orStrong`, `andStrong`: Strong Kleene, the `Trivalent` lattice join and meet under `eval`.
* `orBelnap`, `andBelnap`: Belnap conditional assertion.
* `belnapLift`: Belnap's uniform rule, combining by a binary operator whose identity element
  substitutes for undefined operands.
* `orKPSymmetric`: the symmetric two-dimensional disjunction, with
  `orKPSymmetric_not_trivalent` showing it is no trivalent connective.
* `all_or_agree_when_both_defined`, `all_and_agree_when_both_defined`: the families diverge
  only when presuppositions conflict.

## References

* [kleene-1952]
* [belnap-1970]
* [karttunen-peters-1979]
* [yagi-2025]
-/

@[expose] public section

namespace Presupposition

namespace PartialProp

open Classical

variable {W : Type*}

/-- The symmetric two-dimensional disjunction of the [karttunen-peters-1979] tradition
    projects `Π(φ ∨ ψ) = (A(ψ) ∨ Π(φ)) ∧ (A(φ) ∨ Π(ψ))` and asserts
    `A(φ ∨ ψ) = A(φ) ∨ A(ψ)`. The name carries the `Symmetric` suffix because the literal
    1979 formulation was *asymmetric*, projecting the first disjunct's presupposition
    unconditionally ([yagi-2025] fn 2); this is the symmetrized variant standard in post-2021
    literature, matching [yagi-2025] Definition 2 (cf. [kalomoiros-schwarz-2021] for
    experimental support of symmetry). -/
def orKPSymmetric (p q : PartialProp W) : PartialProp W where
  presup := fun w => (q.assertion w ∨ p.presup w) ∧ (p.assertion w ∨ q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

/-- When presuppositions conflict at `w`, the symmetric K&P presupposition entails the
    assertion — defined implies true — so the disjunction can never be both defined and
    false ([yagi-2025] §2.2). -/
theorem orKPSymmetric_presup_entails_when_conflicting (p q : PartialProp W) (w : W)
    (h_conflict : ¬(p.presup w ∧ q.presup w))
    (h_presup : (orKPSymmetric p q).presup w) :
    (orKPSymmetric p q).assertion w := by
  simp only [orKPSymmetric] at h_presup ⊢
  obtain ⟨h1, h2⟩ := h_presup
  by_cases hp : p.presup w
  · have hq : ¬q.presup w := fun hq => h_conflict ⟨hp, hq⟩
    exact Or.inl (h2.resolve_right hq)
  · exact Or.inr (h1.resolve_right hp)

/-- **Two-dimensionalism exceeds trivalence.** No binary operation on `Trivalent` computes
    the evaluation of the symmetric two-dimensional disjunction from the evaluations of its
    disjuncts. Its presupposition reads the disjuncts' assertion values at worlds where their
    presuppositions fail, and `eval` forgets exactly those values (`eval_eq_eval_iff`). The
    canonical and rival trivalent families all descend (`eval_orFilter`, `eval_orStrong`,
    `eval_orBelnap`), so this disjunction is the reason `PartialProp` cannot be replaced by
    a trivalent proposition. -/
theorem orKPSymmetric_not_trivalent (w : W) :
    ¬ ∃ f : Trivalent → Trivalent → Trivalent,
      ∀ p q : PartialProp W, (orKPSymmetric p q).eval w = f (p.eval w) (q.eval w) := by
  rintro ⟨f, hf⟩
  have h₁ := hf ⟨fun _ => False, fun _ => True⟩ ⟨fun _ => False, fun _ => True⟩
  have h₂ := hf ⟨fun _ => False, fun _ => False⟩ ⟨fun _ => False, fun _ => True⟩
  simp only [eval, orKPSymmetric] at h₁ h₂
  simp at h₁ h₂
  exact absurd (h₁.trans h₂.symm) (by decide)

/-! ### Strong Kleene -/

/-- Strong Kleene disjunction ([kleene-1952]) is defined iff both disjuncts are defined or
    either is defined and true (`T ∨ # = T`, `F ∨ # = #`); under `eval` it is the
    `Trivalent` lattice join (`eval_orStrong`). -/
def orStrong (p q : PartialProp W) : PartialProp W where
  presup := fun w => (p.presup w ∧ q.presup w) ∨
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)
  assertion := fun w =>
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)

/-- Strong Kleene conjunction is defined iff both conjuncts are defined or either is
    defined and false (`F ∧ # = F`, `T ∧ # = #`); under `eval` it is the `Trivalent`
    lattice meet (`eval_andStrong`). -/
def andStrong (p q : PartialProp W) : PartialProp W where
  presup := fun w => (p.presup w ∧ q.presup w) ∨
    (p.presup w ∧ ¬p.assertion w) ∨ (q.presup w ∧ ¬q.assertion w)
  assertion := fun w =>
    (p.presup w → p.assertion w) ∧ (q.presup w → q.assertion w)

/-- `orStrong` evaluates to the `Trivalent` lattice join pointwise — Strong Kleene
    disjunction is `⊔` in the `false < indet < true` order, unconditionally. -/
theorem eval_orStrong (p q : PartialProp W) (w : W) :
    (orStrong p q).eval w = p.eval w ⊔ q.eval w := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, orStrong, hp, hq, ha, hb] <;> decide

/-- `andStrong` evaluates to the `Trivalent` lattice meet pointwise,
    unconditionally. -/
theorem eval_andStrong (p q : PartialProp W) (w : W) :
    (andStrong p q).eval w = p.eval w ⊓ q.eval w := by
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [eval, andStrong, hp, hq, ha, hb] <;> decide

/-! ### Belnap conditional assertion ([belnap-1970])

Under the Belnap reading, `presup` is the **assertive** field — whether the
proposition asserts something at `w` (vs being nonassertive / silent). -/

/-- Belnap conjunction ([belnap-1970], (8)) is assertive iff at least one conjunct is,
    asserting the conjunction of the assertive conjuncts' content. Contrast classical
    `PartialProp.and` (both must be defined) and filtering `PartialProp.andFilter`
    (left-to-right). -/
def andBelnap (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w =>
    (p.presup w → p.assertion w) ∧ (q.presup w → q.assertion w)

/-- Belnap disjunction ([belnap-1970], (9)) is assertive iff at least one disjunct is,
    asserting the disjunction of the assertive disjuncts' content. -/
def orBelnap (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w =>
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)


/-- The **Belnap lift** builds a conditional-assertion connective from a binary `Prop`
    operator `f` and its identity element `unit`. The result is assertive iff at least one
    operand is, and applies `f` with `unit` substituted for unasserted operands, so an
    undefined operand falls silent ([belnap-1970]). `orBelnap` and `andBelnap` are its
    instances at `(· ∨ ·), False` and `(· ∧ ·), True` (`orBelnap_eq_belnapLift`,
    `andBelnap_eq_belnapLift`). Noncomputable because it decides the operands' presupposition
    fields classically. -/
noncomputable def belnapLift (f : Prop → Prop → Prop) (unit : Prop)
    (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w => f (if p.presup w then p.assertion w else unit)
                          (if q.presup w then q.assertion w else unit)

/-! ### Eval: Belnap -/

/-- Belnap conjunction evaluates to `Trivalent.meetBelnap` pointwise. -/
theorem eval_andBelnap (p q : PartialProp W) (w : W) :
    (andBelnap p q).eval w = Trivalent.meetBelnap (p.eval w) (q.eval w) := by
  simp only [eval, andBelnap, Trivalent.meetBelnap]
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq] <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb]

/-- Belnap disjunction evaluates to `Trivalent.joinBelnap` pointwise. -/
theorem eval_orBelnap (p q : PartialProp W) (w : W) :
    (orBelnap p q).eval w = Trivalent.joinBelnap (p.eval w) (q.eval w) := by
  simp only [eval, orBelnap, Trivalent.joinBelnap]
  by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq] <;>
    by_cases ha : p.assertion w <;> by_cases hb : q.assertion w <;>
    simp [ha, hb]

/-! ### Belnap lift: unification -/

/-- `orBelnap` is the Belnap lift of `(· ∨ ·)` with identity `False`. -/
theorem orBelnap_eq_belnapLift (p q : PartialProp W) :
    orBelnap p q = belnapLift (· ∨ ·) False p q :=
  PartialProp.ext rfl (funext fun w => by
    simp only [orBelnap, belnapLift]
    by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq])

/-- `andBelnap` is the Belnap lift of `(· ∧ ·)` with identity `True`. -/
theorem andBelnap_eq_belnapLift (p q : PartialProp W) :
    andBelnap p q = belnapLift (· ∧ ·) True p q :=
  PartialProp.ext rfl (funext fun w => by
    simp only [andBelnap, belnapLift]
    by_cases hp : p.presup w <;> by_cases hq : q.presup w <;> simp [hp, hq])

/-- Belnap lift reduces to the classical operation when both presuppositions hold.
    The identity element is never used — both operands contribute directly. -/
theorem belnapLift_eq_classical (f : Prop → Prop → Prop) (unit : Prop)
    (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (belnapLift f unit p q).assertion w = f (p.assertion w) (q.assertion w) := by
  simp only [belnapLift, ite_eq_left hp, ite_eq_left hq]

/-- When only the left operand is defined and `unit` is a right identity, `belnapLift`
    returns the left operand's value; the right operand is invisible. -/
theorem belnapLift_right_undefined (f : Prop → Prop → Prop) (unit : Prop)
    (hunit : ∀ b, f b unit = b) (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : ¬q.presup w) :
    (belnapLift f unit p q).assertion w = p.assertion w := by
  simp only [belnapLift, ite_eq_left hp, ite_eq_right hq, hunit]

/-- When only the right operand is defined and `unit` is a left identity,
    belnapLift returns the right operand's value. -/
theorem belnapLift_left_undefined (f : Prop → Prop → Prop) (unit : Prop)
    (hunit : ∀ b, f unit b = b) (p q : PartialProp W) (w : W)
    (hp : ¬p.presup w) (hq : q.presup w) :
    (belnapLift f unit p q).assertion w = q.assertion w := by
  simp only [belnapLift, ite_eq_right hp, ite_eq_left hq, hunit]

/-- belnapLift is commutative when `f` is commutative. -/
theorem belnapLift_comm (f : Prop → Prop → Prop)
    (hcomm : ∀ a b, f a b = f b a) (unit : Prop) (p q : PartialProp W) :
    belnapLift f unit p q = belnapLift f unit q p :=
  PartialProp.ext
    (funext fun _ => propext or_comm)
    (funext fun w => by simp only [belnapLift]; exact hcomm _ _)

/-! ### Collapse: all connective families agree when both defined -/

/-- When both presuppositions hold at `w`, all the disjunction connectives — classical,
    filtering, symmetric K&P and Belnap — agree on assertion. The theories diverge only
    when presuppositions conflict. -/
theorem all_or_agree_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    ((or p q).assertion w ↔ (orFilter p q).assertion w) ∧
    ((or p q).assertion w ↔ (orKPSymmetric p q).assertion w) ∧
    ((or p q).assertion w ↔ (orBelnap p q).assertion w) := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  simp [or, orBelnap, hp, hq]

/-- When both presuppositions hold at `w`, all the conjunction connectives — classical,
    filtering and Belnap — agree on assertion. The theories diverge only when
    presuppositions conflict. -/
theorem all_and_agree_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    ((and p q).assertion w ↔ (andFilter p q).assertion w) ∧
    ((and p q).assertion w ↔ (andBelnap p q).assertion w) := by
  refine ⟨Iff.rfl, ?_⟩
  simp [and, andBelnap, hp, hq]

end PartialProp

end Presupposition
