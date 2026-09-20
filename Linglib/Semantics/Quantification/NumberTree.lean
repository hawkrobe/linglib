import Linglib.Semantics.Quantification.Counting
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# The tree of numbers

This file defines quantifiers on van Benthem's tree of numbers. A conservative quantifier that is
invariant under permutations of the universe holds of finite sets `A` and `B` according to the
two numbers `a = |A \ B|` and `b = |A ∩ B|` alone, so it is a set of points `(a, b)`. The points
with `a + b = n` form the `n`-th row of the tree, the ways of splitting an `n`-element `A`.

On this representation inner negation, which negates the scope, swaps the two coordinates, and
outer negation is the complement. The four corners of the square of opposition are *all*,
*some*, *no* and *not all*, and the two negations carry each corner to its neighbours.

Van Benthem's postulates of variety, continuity, absence of deadlock and uniformity are each
invariant under both negations. That symmetry carries the verification of the postulates, and the
proof that the corners are the only quantifiers satisfying them, from *all* to the other three.

## Main definitions

* `Quantifier.NumberTree`: a quantifier as a relation between `|A \ B|` and `|A ∩ B|`.
* `Quantifier.NumberTree.innerNeg`: inner negation, the swap of the two coordinates.
* `Quantifier.NumberTree.all`, `Quantifier.NumberTree.some`, `Quantifier.NumberTree.no`,
  `Quantifier.NumberTree.notAll`: the corners of the square of opposition.
* `Quantifier.NumberTree.cardinal`: the quantifiers that depend on `|A ∩ B|` alone.
* `Quantifier.NumberTree.Asymmetric`, `Quantifier.NumberTree.StronglyConnected`,
  `Quantifier.NumberTree.Euclidean`: relational conditions on a quantifier, read off the tree.
* `Quantifier.NumberTree.Variety`, `Quantifier.NumberTree.Cont`, `Quantifier.NumberTree.Plus`,
  `Quantifier.NumberTree.Uniform`: the postulates VAR, CONT, PLUS and UNIF.
* `Quantifier.NumberTree.ofGQ`: the tree of a generalized quantifier over a finite universe.

## Main results

* `Quantifier.NumberTree.Asymmetric.eq_bot`, `Quantifier.NumberTree.StronglyConnected.eq_top`,
  `Quantifier.NumberTree.Euclidean.eq_top`: the only asymmetric quantifier is the empty one, the
  only strongly connected one is the universal one, and a nonempty Euclidean quantifier is
  universal.
* `Quantifier.NumberTree.variety_cont_plus_uniform_iff`: the quantifiers satisfying the four
  postulates are exactly the four corners of the square of opposition.
* `Quantifier.NumberTree.ofGQ_iff`: a conservative, permutation-invariant generalized quantifier
  holds of `A` and `B` exactly when its tree holds of `|A \ B|` and `|A ∩ B|`.
* `Quantifier.NumberTree.card_powerset_points`: there are `2 ^ ((n + 1) * (n + 2) / 2)` sets of
  points in rows `0` to `n`, the number of quantifiers on a universe of `n` individuals.

## Implementation notes

`Variety` asks only that the quantifier hold somewhere and fail somewhere. Van Benthem's VAR is
stronger in both of its versions, so results assuming `Variety` apply under VAR. The paper asks
for a presence and an absence among the points `(0, 0)`, `(1, 0)` and `(0, 1)`, and the book's
chapter on quantifiers, which restates the tree and the postulates, asks for both in every row
below the top.

Continuity, absence of deadlock and uniformity each treat presence and absence of the quantifier
alike. Each is stated as a condition on presence (`RowConvex`, `NoDeadlock`, `Homogeneous`) that
is imposed on the quantifier and on its complement.

## References

* [van-benthem-1984]
* [van-benthem-1986]
-/

namespace Quantifier

/-- A quantifier on the tree of numbers is a relation between `a = |A \ B|` and `b = |A ∩ B|`. -/
abbrev NumberTree := ℕ → ℕ → Prop

namespace NumberTree

variable {q : NumberTree} {a b : ℕ}

theorem compl_apply : qᶜ a b ↔ ¬ q a b := Iff.rfl

/-! ### Negations and the square of opposition -/

/-- Inner negation negates the scope, which swaps `A \ B` with `A ∩ B`. -/
def innerNeg (q : NumberTree) : NumberTree := fun a b ↦ q b a

@[simp] theorem innerNeg_apply : q.innerNeg a b ↔ q b a := Iff.rfl

@[simp] theorem innerNeg_innerNeg (q : NumberTree) : q.innerNeg.innerNeg = q := rfl

theorem innerNeg_compl (q : NumberTree) : qᶜ.innerNeg = q.innerNegᶜ := rfl

instance [DecidableRel q] : DecidableRel q.innerNeg := fun a b ↦ inferInstanceAs (Decidable (q b a))

instance [DecidableRel q] : DecidableRel qᶜ := fun a b ↦ inferInstanceAs (Decidable ¬ q a b)

/-- The quantifier *all* holds when nothing in `A` lies outside `B`. -/
protected def all : NumberTree := fun a _ ↦ a = 0

/-- The quantifier *some* holds when something in `A` lies in `B`. -/
protected def some : NumberTree := fun _ b ↦ b ≠ 0

/-- The quantifier *no* holds when nothing in `A` lies in `B`. -/
protected def no : NumberTree := fun _ b ↦ b = 0

/-- The quantifier *not all* holds when something in `A` lies outside `B`. -/
protected def notAll : NumberTree := fun a _ ↦ a ≠ 0

instance : DecidableRel NumberTree.all := fun a _ ↦ inferInstanceAs (Decidable (a = 0))
instance : DecidableRel NumberTree.some := fun _ b ↦ inferInstanceAs (Decidable (b ≠ 0))
instance : DecidableRel NumberTree.no := fun _ b ↦ inferInstanceAs (Decidable (b = 0))
instance : DecidableRel NumberTree.notAll := fun a _ ↦ inferInstanceAs (Decidable (a ≠ 0))

theorem innerNeg_all : NumberTree.all.innerNeg = NumberTree.no := rfl

theorem innerNeg_some : NumberTree.some.innerNeg = NumberTree.notAll := rfl

theorem compl_all : NumberTree.allᶜ = NumberTree.notAll := rfl

theorem compl_no : NumberTree.noᶜ = NumberTree.some := rfl

/-- A cardinal quantifier holds according to `|A ∩ B|` alone, as the numerals do. -/
def cardinal (s : Set ℕ) : NumberTree := fun _ b ↦ b ∈ s

@[simp] theorem cardinal_apply {s : Set ℕ} : cardinal s a b ↔ b ∈ s := Iff.rfl

instance {s : Set ℕ} [DecidablePred (· ∈ s)] : DecidableRel (cardinal s) :=
  fun _ b ↦ inferInstanceAs (Decidable (b ∈ s))

theorem cardinal_singleton_zero : cardinal {0} = NumberTree.no := rfl

/-! ### Relational conditions

A condition on the relation `Q A B` between sets becomes a condition on the tree once the sets
are replaced by the sizes of the cells of their Venn diagram. -/

/-- A quantifier is asymmetric when `Q A B` excludes `Q B A`. The two share `|A ∩ B|`, and
`|A \ B|` and `|B \ A|` are arbitrary. -/
def Asymmetric (q : NumberTree) : Prop := ∀ a b c, q a c → ¬ q b c

/-- A quantifier is strongly connected when `Q A B` or `Q B A` holds of any two sets. -/
def StronglyConnected (q : NumberTree) : Prop := ∀ a b c, q a c ∨ q b c

/-- A quantifier is irreflexive when `Q A A` never holds. -/
def Irreflexive (q : NumberTree) : Prop := ∀ n, ¬ q 0 n

/-- A quantifier is Euclidean when `Q X Y` and `Q X Z` give `Q Y Z`. Among the cells of the Venn
diagram of `X`, `Y` and `Z`, `p` counts `X ∩ Y ∩ Z`, `x` the rest of `X ∩ Y`, `y` the rest of
`X ∩ Z`, `s` the rest of `X`, `t` the rest of `Y ∩ Z`, and `u` the rest of `Y`. -/
def Euclidean (q : NumberTree) : Prop :=
  ∀ p x y s t u, q (y + s) (p + x) → q (x + s) (p + y) → q (x + u) (p + t)

/-- The only asymmetric quantifier is the empty one. -/
theorem Asymmetric.eq_bot (h : q.Asymmetric) : q = ⊥ :=
  funext₂ fun a c ↦ eq_false fun hq ↦ h a a c hq hq

/-- The only strongly connected quantifier is the universal one. -/
theorem StronglyConnected.eq_top (h : q.StronglyConnected) : q = ⊤ :=
  funext₂ fun a c ↦ eq_true ((h a a c).elim id id)

/-- An irreflexive quantifier for which `Q A B` and `Q B A` give `Q A A`, as transitivity
requires, is asymmetric. So there is no strict partial order among the nonempty quantifiers. -/
theorem Irreflexive.asymmetric (hI : q.Irreflexive)
    (hT : ∀ a b c, q a c → q b c → q 0 (a + c)) : q.Asymmetric :=
  fun a b c h₁ h₂ ↦ hI _ (hT a b c h₁ h₂)

/-- A nonempty Euclidean quantifier is universal. -/
theorem Euclidean.eq_top (h : q.Euclidean) (hq : ∃ a b, q a b) : q = ⊤ := by
  obtain ⟨d, c, hdc⟩ := hq
  have h₁ : ∀ t u, q u (c + t) := fun t u ↦ by
    simpa using h c 0 0 d t u (by simpa using hdc) (by simpa using hdc)
  have h₂ : ∀ t u, q (c + u) t := fun t u ↦ by
    have hl : q (2 * c) c := by simpa using h₁ 0 (2 * c)
    have hr : q c (2 * c) := by simpa [two_mul] using h₁ c c
    simpa using h 0 c (2 * c) 0 t u (by simpa using hl) (by simpa using hr)
  refine funext₂ fun a b ↦ eq_true ?_
  simpa using h 0 0 c 0 b a (by simpa using h₂ 0 0) (by simpa using h₁ 0 0)

/-! ### The postulates -/

/-- A quantifier has variety when it holds somewhere and fails somewhere. -/
def Variety (q : NumberTree) : Prop := (∃ a b, q a b) ∧ ∃ a b, ¬ q a b

/-- A quantifier is row-convex when it meets each row of the tree in an uninterrupted stretch. -/
def RowConvex (q : NumberTree) : Prop :=
  ∀ ⦃a₁ b₁ a b a₂ b₂ : ℕ⦄, a₁ + b₁ = a + b → a₂ + b₂ = a + b → a₁ ≤ a → a ≤ a₂ →
    q a₁ b₁ → q a₂ b₂ → q a b

/-- The postulate CONT asks that both the presence and the absence of the quantifier be
uninterrupted along each row. -/
def Cont (q : NumberTree) : Prop := q.RowConvex ∧ qᶜ.RowConvex

/-- A quantifier has no deadlock when adding an individual to `A` can always keep it true. -/
def NoDeadlock (q : NumberTree) : Prop := ∀ ⦃a b : ℕ⦄, q a b → q (a + 1) b ∨ q a (b + 1)

/-- The postulate PLUS asks that neither the truth nor the falsity of the quantifier reach a
deadlock. -/
def Plus (q : NumberTree) : Prop := q.NoDeadlock ∧ qᶜ.NoDeadlock

/-- A quantifier is homogeneous when adding an individual to `A` has the same two outcomes
wherever the quantifier holds. -/
def Homogeneous (q : NumberTree) : Prop :=
  ∀ ⦃a₁ b₁ a₂ b₂ : ℕ⦄, q a₁ b₁ → q a₂ b₂ →
    (q (a₁ + 1) b₁ ↔ q (a₂ + 1) b₂) ∧ (q a₁ (b₁ + 1) ↔ q a₂ (b₂ + 1))

/-- The postulate UNIF asks that adding an individual have the same outcomes wherever the
quantifier holds, and the same outcomes wherever it fails. -/
def Uniform (q : NumberTree) : Prop := q.Homogeneous ∧ qᶜ.Homogeneous

theorem Variety.compl (h : q.Variety) : qᶜ.Variety :=
  ⟨h.2, h.1.imp fun _ ↦ Exists.imp fun _ ↦ not_not_intro⟩

theorem Cont.compl (h : q.Cont) : qᶜ.Cont := ⟨h.2, by rw [compl_compl]; exact h.1⟩

theorem Plus.compl (h : q.Plus) : qᶜ.Plus := ⟨h.2, by rw [compl_compl]; exact h.1⟩

theorem Uniform.compl (h : q.Uniform) : qᶜ.Uniform := ⟨h.2, by rw [compl_compl]; exact h.1⟩

theorem Variety.innerNeg (h : q.Variety) : q.innerNeg.Variety :=
  ⟨let ⟨a, b, hq⟩ := h.1; ⟨b, a, hq⟩, let ⟨a, b, hq⟩ := h.2; ⟨b, a, hq⟩⟩

theorem RowConvex.innerNeg (h : q.RowConvex) : q.innerNeg.RowConvex :=
  fun _ _ _ _ _ _ h₁ h₂ _ _ p₁ p₂ ↦ h (by omega) (by omega) (by omega) (by omega) p₂ p₁

theorem NoDeadlock.innerNeg (h : q.NoDeadlock) : q.innerNeg.NoDeadlock :=
  fun _ _ hq ↦ (h hq).symm

theorem Homogeneous.innerNeg (h : q.Homogeneous) : q.innerNeg.Homogeneous :=
  fun _ _ _ _ h₁ h₂ ↦ (h h₁ h₂).symm

theorem Cont.innerNeg (h : q.Cont) : q.innerNeg.Cont := ⟨h.1.innerNeg, h.2.innerNeg⟩

theorem Plus.innerNeg (h : q.Plus) : q.innerNeg.Plus := ⟨h.1.innerNeg, h.2.innerNeg⟩

theorem Uniform.innerNeg (h : q.Uniform) : q.innerNeg.Uniform := ⟨h.1.innerNeg, h.2.innerNeg⟩

/-! ### The square of opposition

The four corners are the only quantifiers with variety that satisfy CONT, PLUS and UNIF. -/

theorem variety_all : NumberTree.all.Variety := ⟨⟨0, 0, rfl⟩, 1, 0, one_ne_zero⟩

theorem cont_all : NumberTree.all.Cont := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ h₁ h₂ ↦ ?_, fun _ _ _ _ _ _ _ _ _ _ h₁ _ ↦ ?_⟩ <;>
    simp only [NumberTree.all, compl_apply] at * <;> omega

theorem plus_all : NumberTree.all.Plus :=
  ⟨fun _ _ h ↦ .inr h, fun _ _ _ ↦ .inl (Nat.succ_ne_zero _)⟩

theorem uniform_all : NumberTree.all.Uniform := by
  refine ⟨fun _ _ _ _ h₁ h₂ ↦ ?_, fun _ _ _ _ h₁ h₂ ↦ ?_⟩ <;>
    simp only [NumberTree.all, compl_apply] at * <;> omega

/-- A quantifier that holds at `(0, 0)` and whose row `1` reads absence, presence is *all*. -/
private theorem eq_all (hC : q.RowConvex) (hU : q.Uniform) (h00 : q 0 0) (h10 : ¬ q 1 0)
    (h01 : q 0 1) : q = NumberTree.all := by
  have hT : ∀ {a b}, q a b → ¬ q (a + 1) b ∧ q a (b + 1) := fun h ↦
    let ⟨hl, hr⟩ := hU.1 h h00; ⟨fun h' ↦ h10 (hl.mp h'), hr.mpr h01⟩
  have hcol : ∀ b, q 0 b := fun b ↦ by
    induction b with
    | zero => exact h00
    | succ b ih => exact (hT ih).2
  have h20 : ¬ q 2 0 := fun h ↦
    (hT (hcol 1)).1 (hC (a₁ := 0) (b₁ := 2) (a := 1) (b := 1) (b₂ := 0) rfl rfl zero_le_one
      one_le_two (hcol 2) h)
  have hF : ∀ {a b}, ¬ q a b → ¬ q (a + 1) b ∧ ¬ q a (b + 1) := fun h ↦
    let ⟨hl, hr⟩ := hU.2 h h10; ⟨hl.mpr h20, hr.mpr (hT (hcol 1)).1⟩
  have hrow : ∀ a b, ¬ q (a + 1) b := fun a ↦ by
    induction a with
    | zero => exact fun b ↦ (hT (hcol b)).1
    | succ a ih => exact fun b ↦ (hF (ih b)).1
  funext a b
  cases a with
  | zero => exact propext ⟨fun _ ↦ rfl, fun _ ↦ hcol b⟩
  | succ a => exact propext ⟨fun h ↦ (hrow a b h).elim, fun h ↦ (Nat.succ_ne_zero a h).elim⟩

/-- A quantifier satisfying the postulates that holds at `(0, 0)` is *all* or *no*. -/
private theorem eq_all_or_eq_no (hV : q.Variety) (hC : q.Cont) (hP : q.Plus) (hU : q.Uniform)
    (h00 : q 0 0) : q = NumberTree.all ∨ q = NumberTree.no := by
  by_cases h10 : q 1 0 <;> by_cases h01 : q 0 1
  · have hT : ∀ {a b}, q a b → q (a + 1) b ∧ q a (b + 1) := fun h ↦
      let ⟨hl, hr⟩ := hU.1 h h00; ⟨hl.mpr h10, hr.mpr h01⟩
    have hcol : ∀ b, q 0 b := fun b ↦ by
      induction b with
      | zero => exact h00
      | succ b ih => exact (hT ih).2
    have hall : ∀ a b, q a b := fun a ↦ by
      induction a with
      | zero => exact hcol
      | succ a ih => exact fun b ↦ (hT (ih b)).1
    obtain ⟨a, b, hq⟩ := hV.2
    exact (hq (hall a b)).elim
  · right
    have := eq_all (q := q.innerNeg) hC.1.innerNeg hU.innerNeg h00 h01 h10
    rw [← innerNeg_innerNeg q, this, innerNeg_all]
  · exact .inl (eq_all hC.1 hU h00 h10 h01)
  · exact ((hP.1 h00).elim h10 h01).elim

/-- The quantifiers with variety that satisfy CONT, PLUS and UNIF are exactly *all*, *some*,
*no* and *not all*. -/
theorem variety_cont_plus_uniform_iff :
    q.Variety ∧ q.Cont ∧ q.Plus ∧ q.Uniform ↔
      q = NumberTree.all ∨ q = NumberTree.some ∨ q = NumberTree.no ∨ q = NumberTree.notAll := by
  constructor
  · rintro ⟨hV, hC, hP, hU⟩
    by_cases h00 : q 0 0
    · exact (eq_all_or_eq_no hV hC hP hU h00).imp_right fun h ↦ .inr (.inl h)
    · rcases eq_all_or_eq_no hV.compl hC.compl hP.compl hU.compl h00 with h | h
      · exact .inr (.inr (.inr (by rw [← compl_compl q, h, compl_all])))
      · exact .inr (.inl (by rw [← compl_compl q, h, compl_no]))
  · have hno : NumberTree.no.Variety ∧ NumberTree.no.Cont ∧ NumberTree.no.Plus ∧
        NumberTree.no.Uniform :=
      ⟨variety_all.innerNeg, cont_all.innerNeg, plus_all.innerNeg, uniform_all.innerNeg⟩
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨variety_all, cont_all, plus_all, uniform_all⟩
    · exact ⟨hno.1.compl, hno.2.1.compl, hno.2.2.1.compl, hno.2.2.2.compl⟩
    · exact hno
    · exact ⟨variety_all.compl, cont_all.compl, plus_all.compl, uniform_all.compl⟩

/-- The quantifier *at least two* is not uniform. Adding an individual to `A ∩ B` leaves it false
at `(0, 0)` and makes it true at `(0, 1)`. -/
theorem not_uniform_two_le : ¬ Uniform fun _ b ↦ 2 ≤ b := fun h ↦ by
  have := (h.2 (a₁ := 0) (b₁ := 0) (a₂ := 0) (b₂ := 1) (by simp [compl_apply])
    (by simp [compl_apply])).2
  simp [compl_apply] at this

/-! ### Additivity -/

/-- A quantifier is additive when its points are closed under coordinatewise addition. -/
def Additive (q : NumberTree) : Prop :=
  ∀ ⦃a b a' b' : ℕ⦄, q a b → q a' b' → q (a + a') (b + b')

theorem Additive.innerNeg (h : q.Additive) : q.innerNeg.Additive := fun _ _ _ _ h₁ h₂ ↦ h h₁ h₂

theorem additive_all : NumberTree.all.Additive := fun _ _ _ _ h₁ h₂ ↦ by
  simp only [NumberTree.all] at *; omega

theorem additive_notAll : NumberTree.notAll.Additive := fun _ _ _ _ h₁ _ ↦ by
  simp only [NumberTree.notAll] at *; omega

theorem additive_no : NumberTree.no.Additive := additive_all.innerNeg

theorem additive_some : NumberTree.some.Additive := additive_notAll.innerNeg

/-! ### The tree of a generalized quantifier -/

section OfGQ

open Classical GQ

variable {α : Type*} [Fintype α] {Q : GQ α} {A B A' B' : α → Prop}

/-- Counts of equivalent predicates agree, whatever their decidability instances. -/
private theorem count_congr {P P' : α → Prop} {i : DecidablePred P} {i' : DecidablePred P'}
    (h : ∀ x, P x ↔ P' x) : @count α _ P i = @count α _ P' i' :=
  count_congr_iff h

/-- A conservative, permutation-invariant quantifier holds of `A` and `B` according to
`|A \ B|` and `|A ∩ B|` alone. -/
theorem _root_.Quantifier.GQ.iff_of_count_eq (hC : Conservative Q) (hQ : QuantityInvariant Q)
    (hd : count (fun x ↦ A x ∧ ¬ B x) = count fun x ↦ A' x ∧ ¬ B' x)
    (hi : count (fun x ↦ A x ∧ B x) = count fun x ↦ A' x ∧ B' x) : Q A B ↔ Q A' B' := by
  have hn : count (fun x ↦ ¬ A x) = count fun x ↦ ¬ A' x := by
    have hA := count_decompose A B
    have hA' := count_decompose A' B'
    have hN := count_decompose (fun _ : α ↦ True) A
    have hN' := count_decompose (fun _ : α ↦ True) A'
    have e : count (fun x ↦ True ∧ A x) = count fun x ↦ A x := count_congr fun _ ↦ by simp
    have e' : count (fun x ↦ True ∧ A' x) = count fun x ↦ A' x :=
      count_congr fun _ ↦ by simp
    have f : count (fun x ↦ True ∧ ¬ A x) = count fun x ↦ ¬ A x :=
      count_congr fun _ ↦ by simp
    have f' : count (fun x ↦ True ∧ ¬ A' x) = count fun x ↦ ¬ A' x :=
      count_congr fun _ ↦ by simp
    omega
  rw [hC A B, hC A' B']
  refine quantity_of_quantityInvariant Q hQ _ _ _ _ ?_ ?_ ?_ ?_
  · exact (count_congr fun x ↦ by tauto).trans (hi.trans (count_congr fun x ↦ by tauto))
  · exact (count_congr fun x ↦ by tauto).trans (hd.trans (count_congr fun x ↦ by tauto))
  · exact count_congr fun x ↦ by tauto
  · exact (count_congr fun x ↦ by tauto).trans (hn.trans (count_congr fun x ↦ by tauto))

/-- The tree of a generalized quantifier holds of `(a, b)` when the quantifier holds of some
`A` and `B` with `|A \ B| = a` and `|A ∩ B| = b`. -/
def ofGQ (Q : GQ α) : NumberTree := fun a b ↦
  ∃ A B : α → Prop, count (fun x ↦ A x ∧ ¬ B x) = a ∧ count (fun x ↦ A x ∧ B x) = b ∧ Q A B

/-- A conservative, permutation-invariant quantifier holds of `A` and `B` exactly when its tree
holds of `|A \ B|` and `|A ∩ B|`. -/
theorem ofGQ_iff (hC : Conservative Q) (hQ : QuantityInvariant Q) (A B : α → Prop) :
    ofGQ Q (count fun x ↦ A x ∧ ¬ B x) (count fun x ↦ A x ∧ B x) ↔ Q A B :=
  ⟨fun ⟨_, _, hd, hi, h⟩ ↦ (GQ.iff_of_count_eq hC hQ hd hi).mp h, fun h ↦ ⟨A, B, rfl, rfl, h⟩⟩

end OfGQ

/-! ### Counting quantifiers -/

/-- The points of rows `0` to `n` of the tree, each given with its row. -/
def points (n : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) := (Finset.range (n + 1)).sigma Finset.antidiagonal

theorem card_points (n : ℕ) : (points n).card = (n + 1) * (n + 2) / 2 := by
  have h : ∀ n, (∑ k ∈ Finset.range (n + 1), (k + 1)) * 2 = (n + 1) * (n + 2) := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  rw [points, Finset.card_sigma, Finset.sum_congr rfl fun k _ ↦ Finset.Nat.card_antidiagonal k,
    ← h n, Nat.mul_div_cancel _ two_pos]

end NumberTree

/-- The number of quantifiers on a universe of `n` individuals, which are the sets of points in
rows `0` to `n` of the tree. -/
def conservativeQuantifierCount (n : ℕ) : ℕ := 2 ^ ((n + 1) * (n + 2) / 2)

theorem NumberTree.card_powerset_points (n : ℕ) :
    (NumberTree.points n).powerset.card = conservativeQuantifierCount n := by
  rw [Finset.card_powerset, NumberTree.card_points, conservativeQuantifierCount]

end Quantifier
