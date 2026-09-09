import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Relation

/-!
# Dinis and Jacinto (2026): Marginality scales for gradable adjectives

This file formalizes [dinis-jacinto-2026]'s marginality scales account of vague gradable
adjectives. ML theory, the theory of marginal and large differences of [dinis-jacinto-2025],
is simplified to a strict linear order with one primitive, *marginally smaller than*:
*largely smaller than* is smaller but not marginally so, Definition 2.1, and five axioms
remain, Figure 1, from which marginal smallness is transitive and bounded, Theorem 2.2, at
most marginal difference is an equivalence relation and large difference is not transitive,
Definition 2.3 and fn. 9. The representative model of the representation theorem is the
lexicographic product of the rationals and the integers, a difference in the second
coordinate alone being marginal, Definition 3.1. The account then takes over [fara-2000]'s
interest-relative semantics after [kennedy-1999]: a gradable adjective denotes a scale with a
measure function from circumstances of evaluation and objects to degrees, the comparative
compares degrees, and the positive form holds of an object whose degree is significantly,
that is largely, greater than the standard of comparison, §5.1, on scales that satisfy ML,
§5.2. Three consequences follow. An object that was in the positive form's extension and no
longer is was greater on the scale, the case of Charles III of §5.4, which a two-scale account
that reads the comparative off precise degrees cannot deliver. Objects at most marginally
different are alike with respect to the positive form, [fara-2000]'s similarity constraint,
so that a chain of marginal steps preserves the positive form and a Soritical sequence must
contain a step that is not marginal, §6.1. And the clustering of the degrees of the objects in
a vague predicate's extension implies tolerance, §3, and holds of the positive form.

## Implementation notes

The strict order R is the `<` of a `LinearOrder`, whose axioms are the order conditions (1)
to (4). Figure 1 is an image; Axioms 3 to 5 are stated as the text glosses them, with largely
smaller than unfolded. The measure function's circumstances and objects are type parameters,
and the Kaplanian context enters only through the standard of comparison and the
agent-relative marginality relation, which are held fixed. The representation and uniqueness
theorems of [dinis-jacinto-2025] are not formalized; the representative model is shown to
satisfy ML and to carry the examples of §5.2 and fn. 9.

## References

* [dinis-jacinto-2026]
* [dinis-jacinto-2025]
* [fara-2000]
* [kennedy-1999]
* [kennedy-2007]
-/

namespace DinisJacinto2026

variable {α : Type*} [LinearOrder α]

/-! ### ML theory, §2 -/

/-- ML theory, Figure 1: a linear order with a primitive *marginally smaller than* relation
`M`, largely smaller than being `x < y ∧ ¬ M x y`. -/
structure MLScale (α : Type*) [LinearOrder α] where
  /-- `x` is marginally smaller than `y`. -/
  M : α → α → Prop
  /-- Axiom 1: some element is largely smaller than another. -/
  exists_large : ∃ x y, x < y ∧ ¬ M x y
  /-- Axiom 2: marginally smaller than implies smaller than. -/
  lt_of_m : ∀ x y, M x y → x < y
  /-- Axiom 3, M-irrelevance: when `x` is marginally smaller than `y`, whatever is largely
  smaller than `y` is largely smaller than `x`, and `y` is largely smaller than whatever `x`
  is largely smaller than. -/
  irrelevance : ∀ x y z, M x y →
    (z < y ∧ ¬ M z y → z < x ∧ ¬ M z x) ∧ (x < z ∧ ¬ M x z → y < z ∧ ¬ M y z)
  /-- Axiom 4: largely smaller than extends along smaller than: whatever is smaller than
  something largely smaller than `z` is largely smaller than `z`, and whatever is largely
  smaller than something smaller than `z` is largely smaller than `z`. -/
  extends_lt : ∀ x y z, x < y →
    (y < z ∧ ¬ M y z → x < z ∧ ¬ M x z) ∧ (z < x ∧ ¬ M z x → z < y ∧ ¬ M z y)
  /-- Axiom 5, decomposition: a large difference is a marginal step followed by a large one,
  and a large one followed by a marginal step. -/
  decomposition : ∀ x y, x < y ∧ ¬ M x y →
    (∃ z, M x z ∧ z < y ∧ ¬ M z y) ∧ ∃ w, M w y ∧ x < w ∧ ¬ M x w

namespace MLScale

variable (ml : MLScale α)

/-- Largely smaller than, Definition 2.1. -/
def L (x y : α) : Prop := x < y ∧ ¬ ml.M x y

/-- Marginal difference, Definition 2.3. -/
def MarginalDiff (x y : α) : Prop := ml.M x y ∨ ml.M y x

/-- At most marginal difference, Definition 2.3: sameness for present purposes. -/
def AtMostMarginal (x y : α) : Prop := x = y ∨ ml.MarginalDiff x y

/-- Large difference, Definition 2.3. -/
def LargeDiff (x y : α) : Prop := ml.L x y ∨ ml.L y x

variable {ml} {x y z : α}

theorem M.lt (h : ml.M x y) : x < y := ml.lt_of_m x y h

theorem L.lt (h : ml.L x y) : x < y := h.1

theorem M.not_l (h : ml.M x y) : ¬ ml.L x y := λ h' => h'.2 h

theorem l_of_lt_of_not_m (hlt : x < y) (h : ¬ ml.M x y) : ml.L x y := ⟨hlt, h⟩

/-- Axiom 4, first half. -/
theorem L.of_lt_of_l (hxy : x < y) (h : ml.L y z) : ml.L x z := (ml.extends_lt x y z hxy).1 h

/-- Axiom 4, second half. -/
theorem L.trans_lt (h : ml.L x y) (hyz : y < z) : ml.L x z := (ml.extends_lt y z x hyz).2 h

/-- Theorem 2.2, M-transitivity: marginal steps do not accrue to a large difference. -/
theorem M.trans (hxy : ml.M x y) (hyz : ml.M y z) : ml.M x z :=
  by_contra λ h => ((ml.irrelevance x y z hxy).2 ⟨hxy.lt.trans hyz.lt, h⟩).2 hyz

/-- Theorem 2.2, M-boundedness: what lies between marginally different elements is marginally
different from each. -/
theorem M.bounded (hxz : ml.M x z) (hxy : x < y) (hyz : y < z) : ml.M x y ∧ ml.M y z :=
  ⟨by_contra λ h => (L.trans_lt ⟨hxy, h⟩ hyz).2 hxz,
    by_contra λ h => (L.of_lt_of_l hxy ⟨hyz, h⟩).2 hxz⟩

theorem marginalDiff_irrefl (x : α) : ¬ ml.MarginalDiff x x :=
  λ h => h.elim (λ h => lt_irrefl x h.lt) λ h => lt_irrefl x h.lt

theorem MarginalDiff.symm (h : ml.MarginalDiff x y) : ml.MarginalDiff y x := Or.symm h

theorem largeDiff_irrefl (x : α) : ¬ ml.LargeDiff x x :=
  λ h => h.elim (λ h => lt_irrefl x h.lt) λ h => lt_irrefl x h.lt

theorem LargeDiff.symm (h : ml.LargeDiff x y) : ml.LargeDiff y x := Or.symm h

theorem AtMostMarginal.refl (x : α) : ml.AtMostMarginal x x := Or.inl rfl

theorem AtMostMarginal.symm (h : ml.AtMostMarginal x y) : ml.AtMostMarginal y x :=
  h.elim (λ h => Or.inl h.symm) λ h => Or.inr h.symm

/-- At most marginal difference is transitive, by M-transitivity when the steps agree in
direction and by M-boundedness when they do not. -/
theorem AtMostMarginal.trans (hxy : ml.AtMostMarginal x y) (hyz : ml.AtMostMarginal y z) :
    ml.AtMostMarginal x z := by
  rcases hxy with rfl | hxy | hyx
  · exact hyz
  · rcases hyz with rfl | hyz | hzy
    · exact Or.inr (Or.inl hxy)
    · exact Or.inr (Or.inl (hxy.trans hyz))
    · rcases lt_trichotomy x z with hxz | rfl | hzx
      · exact Or.inr (Or.inl (hxy.bounded hxz hzy.lt).1)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hzy.bounded hzx hxy.lt).1)
  · rcases hyz with rfl | hyz | hzy
    · exact Or.inr (Or.inr hyx)
    · rcases lt_trichotomy x z with hxz | rfl | hzx
      · exact Or.inr (Or.inl (hyz.bounded hyx.lt hxz).2)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hyx.bounded hyz.lt hzx).2)
    · exact Or.inr (Or.inr (hzy.trans hyx))

/-- Sameness for present purposes, Definition 2.3, as an equivalence relation. -/
def atMostMarginalSetoid : Setoid α :=
  ⟨ml.AtMostMarginal, ⟨AtMostMarginal.refl, AtMostMarginal.symm, AtMostMarginal.trans⟩⟩

/-! ### The similarity constraint, §6.1 -/

/-- Marginally different degrees are alike with respect to being largely greater than a
standard: the second half is M-irrelevance and the first M-boundedness. -/
theorem l_iff_of_m (hxy : ml.M x y) : ml.L z x ↔ ml.L z y :=
  ⟨λ h => ⟨h.1.trans hxy.lt, λ h' => h.2 (h'.bounded h.1 hxy.lt).1⟩, (ml.irrelevance x y z hxy).1⟩

/-- Fara's similarity constraint on degrees: at most marginally different degrees are alike
with respect to being largely greater than a standard. -/
theorem l_iff_of_atMostMarginal (h : ml.AtMostMarginal x y) : ml.L z x ↔ ml.L z y := by
  rcases h with rfl | h | h
  · exact Iff.rfl
  · exact l_iff_of_m h
  · exact (l_iff_of_m h).symm

/-- M-chains: however many marginal steps separate two degrees, they are alike with respect
to being largely greater than a standard. -/
theorem l_iff_of_reflTransGen (h : Relation.ReflTransGen ml.M x y) : ml.L z x ↔ ml.L z y := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hyz ih => exact ih.trans (l_iff_of_m hyz)

/-! ### The representative model, Definition 3.1 -/

/-- Marginally smaller in the representative model: the same first coordinate and a smaller
second one. -/
def repM (x y : ℚ ×ₗ ℤ) : Prop := (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2

/-- Largely smaller in the representative model is a smaller first coordinate. -/
theorem lt_and_not_repM_iff {x y : ℚ ×ₗ ℤ} :
    x < y ∧ ¬ repM x y ↔ (ofLex x).1 < (ofLex y).1 := by
  rw [show x < y ↔ _ from Prod.Lex.toLex_lt_toLex (x := ofLex x) (y := ofLex y)]
  constructor
  · rintro ⟨h | h, hm⟩
    · exact h
    · exact absurd h hm
  · exact λ h => ⟨Or.inl h, λ hm => by rw [hm.1] at h; exact lt_irrefl _ h⟩

theorem fst_le_of_lt {x y : ℚ ×ₗ ℤ} (h : x < y) : (ofLex x).1 ≤ (ofLex y).1 :=
  ((Prod.Lex.toLex_lt_toLex (x := ofLex x) (y := ofLex y)).1 h).elim le_of_lt λ h => le_of_eq h.1

/-- The representative model `R*`, Definition 3.1: rational-integer pairs in lexicographic
order, marginally smaller when the first coordinates agree. -/
def rep : MLScale (ℚ ×ₗ ℤ) where
  M := repM
  exists_large := ⟨toLex (0, 0), toLex (1, 0), lt_and_not_repM_iff.2 zero_lt_one⟩
  lt_of_m _ _ h := Prod.Lex.toLex_lt_toLex.2 (Or.inr h)
  irrelevance _ _ _ hxy :=
    ⟨λ h => lt_and_not_repM_iff.2 (lt_of_lt_of_eq (lt_and_not_repM_iff.1 h) hxy.1.symm),
      λ h => lt_and_not_repM_iff.2 (lt_of_eq_of_lt hxy.1.symm (lt_and_not_repM_iff.1 h))⟩
  extends_lt _ _ _ hxy :=
    ⟨λ h => lt_and_not_repM_iff.2 ((fst_le_of_lt hxy).trans_lt (lt_and_not_repM_iff.1 h)),
      λ h => lt_and_not_repM_iff.2 ((lt_and_not_repM_iff.1 h).trans_le (fst_le_of_lt hxy))⟩
  decomposition x y h := by
    refine ⟨⟨toLex ((ofLex x).1, (ofLex x).2 + 1), ⟨rfl, Int.lt_succ _⟩, ?_⟩,
      ⟨toLex ((ofLex y).1, (ofLex y).2 - 1), ⟨rfl, Int.sub_one_lt_iff.2 le_rfl⟩, ?_⟩⟩ <;>
      exact lt_and_not_repM_iff.2 ((lt_and_not_repM_iff (x := x) (y := y)).1 h)

theorem rep_l_iff {x y : ℚ ×ₗ ℤ} : rep.L x y ↔ (ofLex x).1 < (ofLex y).1 :=
  lt_and_not_repM_iff

/-- Large difference is not transitive, fn. 9: in Figure 2, `m` and `n` differ marginally
though each differs largely from `p`. -/
theorem largeDiff_not_trans :
    rep.LargeDiff (toLex (0, 0)) (toLex (1, 0)) ∧ rep.LargeDiff (toLex (1, 0)) (toLex (0, 1)) ∧
      ¬ rep.LargeDiff (toLex (0, 0)) (toLex (0, 1)) :=
  ⟨Or.inl (rep_l_iff.2 zero_lt_one), Or.inr (rep_l_iff.2 zero_lt_one),
    λ h => h.elim (λ h => lt_irrefl (0 : ℚ) (rep_l_iff.1 h))
      λ h => lt_irrefl (0 : ℚ) (rep_l_iff.1 h)⟩

/-! ### The marginality scales account, §5 -/

variable {C O : Type*} (ml) (μ : C → O → α)

/-- The comparative, §5.1: `y` at circumstance `v` is smaller on the scale than `x` at `u`. -/
def er (u : C) (x : O) (v : C) (y : O) : Prop := μ v y < μ u x

/-- The positive form, §5.1, after Fara: the standard of comparison is significantly, that is
largely, smaller than the object's degree at the circumstance. -/
def pos (norm : α) (w : C) (x : O) : Prop := ml.L norm (μ w x)

variable {ml μ} {norm : α} {w u v : C} {a b : O}

/-- The positive form entails exceeding the standard. -/
theorem pos.lt (h : ml.pos μ norm w a) : norm < μ w a := h.1

/-- Figure 5: an object whose degree exceeds the standard only marginally is not in the
positive form's extension. -/
theorem not_pos_of_m (h : ml.M norm (μ w a)) : ¬ ml.pos μ norm w a := h.not_l

/-- Charles III, §5.4: an object in the positive form's extension at one circumstance and out
of it at another was greater on the scale, since the scale relations do not vary with the
circumstance; a two-scale account that reads the comparative off unchanged precise degrees
cannot say so. -/
theorem er_of_pos_of_not_pos (h₁ : ml.pos μ norm u a) (h₂ : ¬ ml.pos μ norm v a) :
    er μ u a v a := by
  rcases lt_trichotomy (μ v a) (μ u a) with h | h | h
  · exact h
  · exact absurd (show ml.L norm (μ v a) from h ▸ (h₁ : ml.L norm (μ u a))) h₂
  · exact absurd (h₁.trans_lt h) h₂

/-- Tolerance, §3: an object out of the positive form's extension keeps out anything whose
degree is marginally greater, and one in it keeps in anything whose degree is marginally
smaller. -/
theorem tolerance :
    (¬ ml.pos μ norm w a → ml.M (μ w a) (μ w b) → ¬ ml.pos μ norm w b) ∧
      (ml.pos μ norm w a → ml.M (μ w b) (μ w a) → ml.pos μ norm w b) :=
  ⟨λ h hm h' => h ((l_iff_of_m hm).2 h'), λ h hm => (l_iff_of_m hm).2 h⟩

/-- A Soritical sequence for the positive form is no chain of marginal steps: some adjacent
pair differs largely, the nonstandard primitivist solution to the Sorites of §3 and §6.1. -/
theorem not_reflTransGen_of_pos (h₁ : ¬ ml.pos μ norm w a) (h₂ : ml.pos μ norm w b) :
    ¬ Relation.ReflTransGen ml.M (μ w a) (μ w b) :=
  λ h => h₁ ((l_iff_of_reflTransGen h).2 h₂)

/-- Clustered degrees, §3: something has the property iff its degree differs at most
marginally from the degree of something with the property. -/
def Clustered (B : O → Prop) (δ : O → α) : Prop :=
  ∀ x, B x ↔ ∃ y, B y ∧ ml.AtMostMarginal (δ y) (δ x)

/-- Clustered degrees imply degree tolerance, §3. -/
theorem Clustered.tolerance {B : O → Prop} {δ : O → α} (h : ml.Clustered B δ) :
    (¬ B a → ml.M (δ a) (δ b) → ¬ B b) ∧ (B a → ml.M (δ b) (δ a) → B b) :=
  ⟨λ ha hm hb => ha ((h a).2 ⟨b, hb, Or.inr (Or.inr hm)⟩),
    λ ha hm => (h b).2 ⟨a, ha, Or.inr (Or.inr hm)⟩⟩

/-- The positive form's extension is clustered: the marginality scales account implies the
nonstandard primitivist principle of §3. -/
theorem clustered_pos : ml.Clustered (ml.pos μ norm w) (μ w) := λ x =>
  ⟨λ h => ⟨x, h, AtMostMarginal.refl _⟩,
    λ ⟨_, hy, hxy⟩ => (l_iff_of_atMostMarginal hxy).1 hy⟩

/-! ### Ronaldo and Zidane, §5.2 -/

/-- The example of §5.2 in the representative model: with the standard at `⟨0, 0⟩`, Zidane at
`⟨1, 2⟩` is balder than Ronaldo at `⟨0, 10⟩`, and Zidane is bald where Ronaldo, though balder
than the standard, is not. -/
theorem zidane_ronaldo :
    er (λ _ : Unit => id) () (toLex ((1 : ℚ), (2 : ℤ))) () (toLex (0, 10)) ∧
      rep.pos (λ _ : Unit => id) (toLex (0, 0)) () (toLex (1, 2)) ∧
      ¬ rep.pos (λ _ : Unit => id) (toLex (0, 0)) () (toLex (0, 10)) :=
  ⟨Prod.Lex.toLex_lt_toLex.2 (Or.inl zero_lt_one), rep_l_iff.2 zero_lt_one,
    λ h => lt_irrefl (0 : ℚ) (rep_l_iff.1 h)⟩

end MLScale

end DinisJacinto2026
