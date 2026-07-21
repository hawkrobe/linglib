import Linglib.Semantics.Presupposition.Basic
import Mathlib.Data.Finset.Basic

/-!
# Rival trivalent connective families

The rival trivalent connective families on `PartialProp`, beyond the
classical (Weak Kleene) and filtering (middle Kleene) canon of
`Semantics.Presupposition.Basic`: Strong Kleene ([kleene-1952]), Belnap
conditional assertion / flexible accommodation ([belnap-1970],
[geurts-2005]), the symmetric K&P disjunction ([karttunen-peters-1979]),
and the positive-antecedent rival ([sharvit-2025]).

## Main declarations

* `orStrong`, `andStrong` — Strong Kleene: the `Trivalent` lattice
  join/meet (`eval_orStrong`/`eval_andStrong`).
* `orBelnap`, `andBelnap` — Belnap conditional assertion; the
  flexible-accommodation `orFlex`/`andFlex` are definitionally the same
  operators.
* `belnapLift` — unifier showing Belnap = flexible accommodation for any
  binary `Prop` operator with an identity.
* `orKPSymmetric` — symmetric two-dimensional K&P disjunction.
* `orPositive` — positive-antecedent symmetric disjunction, a documented
  rival ([sharvit-2025], [yagi-2025]).
* `liveness`, `genuineness` — [yagi-2025] disjunction-update conditions.
* `all_or_agree_when_both_defined` / `all_and_agree_when_both_defined` —
  the families diverge only when presuppositions conflict.

## Todo

* `evalLift : (Trivalent → Trivalent → Trivalent) → (PartialProp W → PartialProp W → PartialProp W)`
  would collapse `xor`, `andBelnap`, `orBelnap` into
  one definition each, with one bridge theorem instead of eight.
-/

namespace Semantics.Presupposition

namespace PartialProp

open Classical

variable {W : Type*}

/-! ### Positive-antecedent symmetric disjunction -/

/-- Positive-antecedent symmetric disjunction: each disjunct's
    presupposition is required where the *other disjunct's assertion
    holds*, plus at least one disjunct defined. This is NOT Karttunen
    filtering (`orFilter`): it demands the second disjunct's
    presupposition exactly where the first is *true*, un-filtering
    bathroom-sentence data. Retained as a documented rival:
    [sharvit-2025] identifies it as the root cause of K/P-style failure
    (`Studies/Sharvit2025.lean`), and [yagi-2025] §2.2 discusses the
    `Π(φ) ∨ Π(ψ)` conjunct as a candidate fix (`Studies/Yagi2025.lean`). -/
def orPositive (p q : PartialProp W) : PartialProp W where
  presup := fun w =>
    (p.assertion w → q.presup w) ∧
    (q.assertion w → p.presup w) ∧
    (p.presup w ∨ q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

/-! ### K&P two-dimensional disjunction -/

/-- Symmetric two-dimensional disjunction in the K&P
    ([karttunen-peters-1979]) tradition:

    Π(φ ∨ ψ) = (A(ψ) ∨ Π(φ)) ∧ (A(φ) ∨ Π(ψ))
    A(φ ∨ ψ) = A(φ) ∨ A(ψ)

    The name carries the `Symmetric` suffix because the literal K&P 1979
    formulation was *asymmetric* (it would project the first disjunct's
    presupposition unconditionally; [yagi-2025] fn 2). This is the
    symmetrized variant standard in post-2021 literature, matching
    [yagi-2025] Definition 2 (cf. [kalomoiros-schwarz-2021] for
    experimental support of symmetry). -/
def orKPSymmetric (p q : PartialProp W) : PartialProp W where
  presup := fun w => (q.assertion w ∨ p.presup w) ∧ (p.assertion w ∨ q.presup w)
  assertion := fun w => p.assertion w ∨ q.assertion w

/-- When presuppositions conflict at w, the symmetric K&P presupposition
    entails the assertion: defined → true, so the disjunction can never be
    both defined and false. [yagi-2025] §2.2 -/
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

/-! ### Strong Kleene -/

/-- Strong Kleene disjunction ([kleene-1952]): defined iff both disjuncts
    are defined or either is defined-and-true (`T ∨ # = T`, `F ∨ # = #`).
    This is the `Trivalent` lattice join — see `eval_orStrong`. -/
def orStrong (p q : PartialProp W) : PartialProp W where
  presup := fun w => (p.presup w ∧ q.presup w) ∨
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)
  assertion := fun w =>
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)

/-- Strong Kleene conjunction: defined iff both conjuncts are defined or
    either is defined-and-false (`F ∧ # = F`, `T ∧ # = #`). This is the
    `Trivalent` lattice meet — see `eval_andStrong`. -/
def andStrong (p q : PartialProp W) : PartialProp W where
  presup := fun w => (p.presup w ∧ q.presup w) ∨
    (p.presup w ∧ ¬p.assertion w) ∨ (q.presup w ∧ ¬q.assertion w)
  assertion := fun w =>
    (p.presup w → p.assertion w) ∧ (q.presup w → q.assertion w)

/-- `orStrong` evaluates to the `Trivalent` lattice join pointwise: Strong
    Kleene disjunction is ⊔ in the `false < indet < true` order,
    unconditionally. -/
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

/-- Belnap conjunction: assertive iff at least one conjunct is assertive.
    What it asserts = conjunction of assertive conjuncts' content.

    [belnap-1970], (8). Contrast with classical `PartialProp.and` (both
    must be defined) and filtering `PartialProp.andFilter` (left-to-right). -/
def andBelnap (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w =>
    (p.presup w → p.assertion w) ∧ (q.presup w → q.assertion w)

/-- Belnap disjunction: assertive iff at least one disjunct is assertive.
    What it asserts = disjunction of assertive disjuncts' content.

    [belnap-1970], (9). -/
def orBelnap (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w =>
    (p.presup w ∧ p.assertion w) ∨ (q.presup w ∧ q.assertion w)

/-! ### Flexible accommodation

The flexible-accommodation connectives of the pragmatic tradition
([geurts-2005], [aloni-2022], the static counterpart of [yagi-2025]'s
dynamic update) are *definitionally* the Belnap connectives: each operand
is evaluated only against worlds where its own presupposition holds, which
handles conflicting presuppositions (where classical and filtering
disjunction both fail). The two traditions differ in the *accommodation
theory* surrounding the operator (default ⊤ vs unconditional assertive),
not in the operator itself — see [yagi-2025] §3.2 for the distinction. -/

/-- Flexible accommodation disjunction = `orBelnap`. -/
abbrev orFlex : PartialProp W → PartialProp W → PartialProp W := orBelnap

/-- Flexible accommodation conjunction = `andBelnap`. -/
abbrev andFlex : PartialProp W → PartialProp W → PartialProp W := andBelnap

/-- **Belnap lift**: uniform construction for conditional assertion connectives.

    Given a binary Prop function `f` and its identity element `unit`,
    constructs a PartialProp connective where:
    - Defined (assertive) iff at least one operand is defined
    - Assertion applies `f` to each operand's content, substituting `unit`
      for undefined operands (making them "silent")

    [belnap-1970]: undefined operands contribute the identity element.
    Noncomputable because it uses classical `if` on Props.

    Defined instances:
    - `belnapLift (· ∨ ·) False` = `orBelnap` = `orFlex` (False is identity for ∨)
    - `belnapLift (· ∧ ·) True` = `andBelnap` = `andFlex` (True is identity for ∧)
    -/
noncomputable def belnapLift (f : Prop → Prop → Prop) (unit : Prop)
    (p q : PartialProp W) : PartialProp W where
  presup := fun w => p.presup w ∨ q.presup w
  assertion := fun w => f (if p.presup w then p.assertion w else unit)
                          (if q.presup w then q.assertion w else unit)

/-! ### Flex collapse theorems -/

/-- orFlex reduces to standard disjunction when both presuppositions hold. -/
theorem orFlex_eq_or_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (orFlex p q).assertion w ↔ (or p q).assertion w := by
  simp only [orFlex, or]
  constructor
  · rintro (⟨_, ha⟩ | ⟨_, ha⟩) <;> [exact Or.inl ha; exact Or.inr ha]
  · rintro (ha | ha) <;> [exact Or.inl ⟨hp, ha⟩; exact Or.inr ⟨hq, ha⟩]

/-- orFlex presupposition is weaker than or's (p ∨ q vs p ∧ q). -/
theorem orFlex_presup_weaker (p q : PartialProp W) (w : W)
    (h : (or p q).presup w) :
    (orFlex p q).presup w := by
  exact Or.inl h.1

/-- andFlex reduces to standard conjunction when both presuppositions hold. -/
theorem andFlex_eq_and_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    (andFlex p q).assertion w ↔ (and p q).assertion w := by
  simp only [andFlex, and]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨h1 hp, h2 hq⟩
  · intro ⟨h1, h2⟩; exact ⟨fun _ => h1, fun _ => h2⟩

/-- andFlex presupposition is weaker than and's (p ∨ q vs p ∧ q). -/
theorem andFlex_presup_weaker (p q : PartialProp W) (w : W)
    (h : (and p q).presup w) :
    (andFlex p q).presup w := by
  exact Or.inl h.1

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
  simp only [belnapLift, if_pos hp, if_pos hq]

/-- When only the left operand is defined and `unit` is a right identity,
    belnapLift returns the left operand's value: the right operand is
    invisible. -/
theorem belnapLift_right_undefined (f : Prop → Prop → Prop) (unit : Prop)
    (hunit : ∀ b, f b unit = b) (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : ¬q.presup w) :
    (belnapLift f unit p q).assertion w = p.assertion w := by
  simp only [belnapLift, if_pos hp, if_neg hq, hunit]

/-- When only the right operand is defined and `unit` is a left identity,
    belnapLift returns the right operand's value. -/
theorem belnapLift_left_undefined (f : Prop → Prop → Prop) (unit : Prop)
    (hunit : ∀ b, f unit b = b) (p q : PartialProp W) (w : W)
    (hp : ¬p.presup w) (hq : q.presup w) :
    (belnapLift f unit p q).assertion w = q.assertion w := by
  simp only [belnapLift, if_neg hp, if_pos hq, hunit]

/-- belnapLift is commutative when `f` is commutative. -/
theorem belnapLift_comm (f : Prop → Prop → Prop)
    (hcomm : ∀ a b, f a b = f b a) (unit : Prop) (p q : PartialProp W) :
    belnapLift f unit p q = belnapLift f unit q p :=
  PartialProp.ext
    (funext fun _ => propext or_comm)
    (funext fun w => by simp only [belnapLift]; exact hcomm _ _)

/-! ### Collapse: all connective families agree when both defined -/

/-- When both presuppositions hold at w, ALL disjunction connectives
    agree on assertion: classical = filtering = K&P = flex = Belnap.
    The theories diverge only when presuppositions conflict. -/
theorem all_or_agree_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    ((or p q).assertion w ↔ (orFilter p q).assertion w) ∧
    ((or p q).assertion w ↔ (orPositive p q).assertion w) ∧
    ((or p q).assertion w ↔ (orKPSymmetric p q).assertion w) ∧
    ((or p q).assertion w ↔ (orFlex p q).assertion w) := by
  refine ⟨Iff.rfl, Iff.rfl, Iff.rfl, ?_⟩
  exact (orFlex_eq_or_when_both_defined p q w hp hq).symm

/-- When both presuppositions hold at w, ALL conjunction connectives
    agree on assertion: classical = filtering = flex = Belnap.
    The theories diverge only when presuppositions conflict. -/
theorem all_and_agree_when_both_defined (p q : PartialProp W) (w : W)
    (hp : p.presup w) (hq : q.presup w) :
    ((and p q).assertion w ↔ (andFilter p q).assertion w) ∧
    ((and p q).assertion w ↔ (andFlex p q).assertion w) := by
  refine ⟨Iff.rfl, ?_⟩
  exact (andFlex_eq_and_when_both_defined p q w hp hq).symm

/-! ### Genuineness / liveness ([zimmermann-2000], [geurts-2005], [katzir-singh-2012]) -/

/-- **Liveness** for disjunction: each disjunct is satisfied (presupposition
    AND assertion hold) at some world of the state.

    This is the singleton-survival side of [yagi-2025] Definition 8:
    `{w}[φ] = {w}` for some `w ∈ s`. The disjunction-update side
    (`w ∈ s[φ ∨ ψ]`) is the additional constraint expressed by
    `genuineness` below. -/
def liveness (p q : PartialProp W) (s : Finset W) : Prop :=
  (∃ w ∈ s, p.holds w) ∧
  (∃ w ∈ s, q.holds w)

/-- **Genuineness** for disjunction ([yagi-2025] Definition 8, after
    [zimmermann-2000]). A disjunction `p ∨ q`, with disjunction-update
    realised by the connective `disj`, follows genuineness in a state `s` iff
    there are worlds `w, w' ∈ s` such that:

    - `{w}[p] = {w}` AND `w ∈ s[p ∨ q]` — the left disjunct's witness survives
      both its own update (= `p.holds w`) and the disjunction's update
      (= `disj.holds w`).
    - `{w'}[q] = {w'}` AND `w' ∈ s[p ∨ q]` — analogously for the right disjunct.

    The disjunction-update side rules out witnesses that survive the local
    presupposition+assertion update but are eliminated by the joint update —
    a vacuous addition under `orFlex`/`orBelnap` (`liveness_implies_genuineness_orFlex`),
    but the substantive constraint [yagi-2025] §3.2 invokes for dynamic
    negation: genuineness must hold even within the scope of negation, where
    "we end up negating both disjuncts".

    The `disj` argument is parametric so the substrate stays
    framework-neutral; consumers supply the disjunction *connective* whose
    update they wish to test against (orFlex / classical or / Geurts
    modal split). -/
def genuineness (disj : PartialProp W → PartialProp W → PartialProp W)
    (p q : PartialProp W) (s : Finset W) : Prop :=
  (∃ w ∈ s, p.holds w ∧ (disj p q).holds w) ∧
  (∃ w ∈ s, q.holds w ∧ (disj p q).holds w)

/-- Under `orFlex`, `liveness` implies `genuineness`: each witness for
    `p.holds`/`q.holds` automatically survives the disjunction's update,
    because `(orFlex p q).holds w` reduces to `p.holds w ∨ q.holds w`. -/
theorem liveness_implies_genuineness_orFlex (p q : PartialProp W) (s : Finset W)
    (h : liveness p q s) : genuineness orFlex p q s := by
  obtain ⟨⟨w, hw, hp⟩, ⟨w', hw', hq⟩⟩ := h
  refine ⟨⟨w, hw, hp, ?_⟩, ⟨w', hw', hq, ?_⟩⟩
  · exact ⟨Or.inl hp.1, Or.inl hp⟩
  · exact ⟨Or.inr hq.1, Or.inr hq⟩

/-- Liveness is symmetric. -/
theorem liveness_comm (p q : PartialProp W) (s : Finset W) :
    liveness p q s ↔ liveness q p s := by
  simp only [liveness, and_comm]

/-- Genuineness is symmetric whenever the supplied disjunction connective is
    symmetric in its operands. -/
theorem genuineness_comm (disj : PartialProp W → PartialProp W → PartialProp W)
    (p q : PartialProp W) (s : Finset W) (hcomm : disj p q = disj q p) :
    genuineness disj p q s ↔ genuineness disj q p s := by
  unfold genuineness
  rw [hcomm, and_comm]

end PartialProp

end Semantics.Presupposition
