import Mathlib.Data.Finset.Basic
import Linglib.Syntax.Category.Coordinator
import Linglib.Data.Examples.Fortuny2024

/-!
# Fortuny (2024): Deducing the Coordinand Constraint

This file formalizes [fortuny-2024]'s deduction of the Coordinand Constraint, [grosu-1973]'s
half of [ross-1967]'s Coordinate Structure Constraint that no coordinand may be moved (5). A
coordinator is the categorial-grammar functor `(X/X)/X` of [steedman-1985] (10), so two
constituents coordinate exactly when they are of one category, and a category is its set of
generalized categorial features together with its bar-level features (12), (18)–(21): the
Coordinability Condition (22) is a theorem (`coordinable_iff`), not a stipulation. A coordinand
moved for a criterial feature the other coordinand lacks is therefore not coordinable with it
(Case 1, `not_coordinable_of_mem_of_notMem`), and so are two coordinands moved for different
features (Case 2, subcase I). Categorially identical coordinands fall under the Integrity
Condition (50), by which a probe targets the coordinate structure and never a coordinand within
it, and the same constituent cannot occupy both coordinated positions (71), a coordination the
`Coordinator` substrate shows to be semantically vacuous (`op_self`).

The paper's judgments are the rows of `Data/Examples/Fortuny2024.json`; `rows_predicted` checks
them against the three-factor decomposition, and `rows_factor` that each ill-formed coordination
falls under exactly one factor, as §2.3 claims.

## Implementation notes

* Movement is not derived: the rows record which coordinands move, and the Integrity Condition
  is stated as the paper states it, with its Least Effort rationale (58) as `superfluous_of_twice`.
* Base categorial features are the paper's [D], [P], [C], [I], [V], [Adj] of (14) plus the
  criterial [wh], [focus], [topic] ([rizzi-1997]) and the unvalued case feature of (59)–(62);
  bar-level features follow [muysken-1982]. All coordinands in the data are maximal projections.
* Feature percolation (§2.2.1.3) is recorded on the rows rather than computed.

## References

* [fortuny-2024]
* [grosu-1973]
* [ross-1967]
* [steedman-1985]
* [muysken-1982]
* [rizzi-1997]
* [chomsky-1991]
* [zhang-2010]
-/

namespace Fortuny2024

open Data.Examples

/-! ### Categories as feature clusters (§2.1) -/

/-- The bar-level features of [muysken-1982]: a minimal category is `[−projected, −maximal]`, an
intermediate one `[+projected, −maximal]`, a maximal one `[+projected, +maximal]` (18)–(20). -/
structure BarLevel where
  projected : Bool
  maximal : Bool
  deriving DecidableEq, Repr

/-- The bar level of a maximal projection. -/
def BarLevel.max : BarLevel := ⟨true, true⟩

/-- Generalized categorial features (12): features determining a constituent's distribution — the
base categories of (14), the criterial features of the left periphery ([rizzi-1997]) that trigger
internal Merge (23), and the unvalued case feature of (59)–(62). -/
inductive CatFeature where
  | D
  | P
  | C
  | I
  | V
  | Adj
  | wh
  | focus
  | topic
  | uCase
  deriving DecidableEq, Repr

/-- A category is its categorial features and its bar level (18)–(21). -/
@[ext]
structure Category where
  cf : Finset CatFeature
  bar : BarLevel
  deriving DecidableEq

/-- (21): categorial identity is identity of categorial and bar-level features. -/
theorem Category.eq_iff (a b : Category) : a = b ↔ a.cf = b.cf ∧ a.bar = b.bar :=
  Category.ext_iff

/-! ### The categorematic coordinator (10)–(11) -/

/-- Categorial-grammar types over categories: `slash r a` selects an `a` and yields an `r`. -/
inductive CGType where
  | of : Category → CGType
  | slash : CGType → CGType → CGType
  deriving DecidableEq

/-- Functional application: `r / a` applied to `a` yields `r`. -/
def CGType.apply : CGType → CGType → Option CGType
  | .slash r a, b => if a = b then some r else none
  | .of _, _ => none

/-- (10): a coordinator is `(X/X)/X` — it selects an internal coordinand of category `X`, yields
`X/X`, selects an external coordinand of category `X`, and yields a coordinate structure of
category `X`. -/
def coord (X : Category) : CGType := .slash (.slash (.of X) (.of X)) (.of X)

/-- (11): the coordinator applied to the internal coordinand `β` and then to the external
coordinand `α`. -/
def coordinate (X α β : Category) : Option CGType :=
  ((coord X).apply (.of β)).bind (·.apply (.of α))

theorem coordinate_eq (X α β : Category) :
    coordinate X α β = if X = β ∧ X = α then some (.of X) else none := by
  unfold coordinate coord
  by_cases hβ : X = β
  · subst hβ
    simp [CGType.apply]
  · simp [CGType.apply, hβ]

/-- The coordination projects `X` exactly when both coordinands are of category `X`. -/
theorem coordinate_eq_some_iff (X α β : Category) :
    coordinate X α β = some (.of X) ↔ α = X ∧ β = X := by
  rw [coordinate_eq]
  split_ifs with h
  · exact ⟨λ _ => ⟨h.2.symm, h.1.symm⟩, λ _ => rfl⟩
  · exact ⟨λ h' => h'.elim, λ ⟨ha, hb⟩ => (h ⟨hb.symm, ha.symm⟩).elim⟩

/-- (66): the coordinator applied to a single coordinand is the unsaturated `X/X` — the structure
a sideward-moved coordinate phrase would land in (65). -/
theorem coord_apply_single (X : Category) :
    (coord X).apply (.of X) = some (.slash (.of X) (.of X)) := by
  simp [coord, CGType.apply]

/-- (22): two constituents are coordinable when some category is projected for them. -/
def Coordinable (α β : Category) : Prop := ∃ X, coordinate X α β = some (.of X)

/-- The Coordinability Condition (22) follows from the categorematic coordinator (10) and
categorial identity (21): coordinable iff the same categorial and bar-level features. -/
theorem coordinable_iff (α β : Category) : Coordinable α β ↔ α.cf = β.cf ∧ α.bar = β.bar := by
  rw [← Category.eq_iff]
  constructor
  · rintro ⟨X, h⟩
    obtain ⟨rfl, rfl⟩ := (coordinate_eq_some_iff X α β).1 h
    rfl
  · rintro rfl
    exact ⟨α, (coordinate_eq_some_iff α α α).2 ⟨rfl, rfl⟩⟩

instance (α β : Category) : Decidable (Coordinable α β) :=
  decidable_of_iff _ (coordinable_iff α β).symm

/-! ### Case 1 and Case 2, subcase I (§2.2.1, §2.2.2.1) -/

/-- (24): a coordinand carrying a categorial feature the other lacks — as when it alone is
attracted by a probe for that feature (23) — is not coordinable with it. -/
theorem not_coordinable_of_mem_of_notMem {α β : Category} {φ : CatFeature} (hα : φ ∈ α.cf)
    (hβ : φ ∉ β.cf) : ¬ Coordinable α β :=
  λ h => hβ (((coordinable_iff α β).1 h).1 ▸ hα)

/-- (25): *who* is `[+wh]`, *a girl* is not. -/
example : ¬ Coordinable ⟨{.D, .wh}, .max⟩ ⟨{.D}, .max⟩ :=
  not_coordinable_of_mem_of_notMem (φ := .wh) (by decide) (by decide)

/-- (47), subcase I of Case 2: a `[+topic]` and a `[+focus]` coordinand, each carrying a feature
the other lacks. -/
example : ¬ Coordinable ⟨{.D, .topic}, .max⟩ ⟨{.D, .focus}, .max⟩ :=
  not_coordinable_of_mem_of_notMem (φ := .topic) (by decide) (by decide)

/-- (30): identity is not required of the elements inside the coordinands. -/
example : Coordinable ⟨{.D}, .max⟩ ⟨{.D}, .max⟩ := by decide

/-! ### The Integrity Condition (50) and its rationale (§2.2.2.2) -/

/-- The positions of a coordinate structure a probe might target. -/
inductive Position where
  | whole
  | left
  | right
  deriving DecidableEq, Repr

/-- A well-formed coordinate structure: a coordinator of some role with two coordinands of one
category `X`, which it projects. -/
structure CoordStructure where
  role : Coordinator.Role
  X : Category

/-- (50): in a well-formed coordinate structure of category `X` whose coordinands carry `φ`, a
probe searching for `[+φ]` targets the coordinate structure and not a coordinand within it. -/
def CoordStructure.Goal (cs : CoordStructure) (φ : CatFeature) (p : Position) : Prop :=
  φ ∈ cs.X.cf ∧ p = .whole

/-- Pattern 1 (51b), (53): neither coordinand is a goal, so the coordinands cannot move to
separate specifiers, with or without the coordinate structure. -/
theorem CoordStructure.not_goal_coordinand (cs : CoordStructure) (φ : CatFeature) :
    ¬ cs.Goal φ .left ∧ ¬ cs.Goal φ .right :=
  ⟨λ h => Position.noConfusion h.2, λ h => Position.noConfusion h.2⟩

/-- (59)–(62): a probe for the unvalued case feature targets a DP coordination as a whole, so a
single coordinand cannot raise to the subject position. -/
theorem CoordStructure.goal_uCase (r : Coordinator.Role) :
    (CoordStructure.mk r ⟨{.D, .uCase}, .max⟩).Goal .uCase .whole ∧
      ¬ (CoordStructure.mk r ⟨{.D, .uCase}, .max⟩).Goal .uCase .left :=
  ⟨⟨by simp, rfl⟩, λ h => Position.noConfusion h.2⟩

/-- A derivation as the positions moved for each feature. -/
def Derivation := CatFeature → List Position

/-- (58): a derivation is superfluous when a coordinand moves twice for one feature, once on its
own and once inside the coordinate structure — what the Least Effort Principle (79) bans. -/
def Derivation.Superfluous (d : Derivation) : Prop :=
  ∃ φ, .whole ∈ d φ ∧ (.left ∈ d φ ∨ .right ∈ d φ)

/-- (53): moving the coordinate structure and both coordinands to specifiers of one head is
superfluous. -/
theorem superfluous_of_twice (φ : CatFeature) :
    Derivation.Superfluous λ ψ => if ψ = φ then [.left, .right, .whole] else [] :=
  ⟨φ, by simp⟩

/-! ### The Prohibition against Self-Coordination (71) -/

/-- An occurrence of a constituent: its category and the derivational step at which it entered
the computation (fn. 16); two selections of one constituent are two occurrences. -/
structure Occurrence where
  cat : Category
  step : ℕ
  deriving DecidableEq

/-- (71): a coordination is well formed only if its coordinands are coordinable and are distinct
occurrences — a constituent cannot appear in both coordinated positions. -/
def WellFormed (α β : Occurrence) : Prop := Coordinable α.cat β.cat ∧ α ≠ β

/-- Self-coordination is semantically vacuous: for the conjunctive, additive, disjunctive and
adversative roles the coordinator's operation on a constituent and itself returns it, the
interface counterpart of (71) that §2.3 relates to the Least Effort Principle. -/
theorem op_self {α : Type*} [BooleanAlgebra α] (r : Coordinator.Role)
    (hr : r = .j ∨ r = .mu ∨ r = .disj ∨ r = .advers) (x : α) : Coordinator.op r x x = x := by
  rcases hr with rfl | rfl | rfl | rfl <;> simp [Coordinator.op]

/-! ### The judgments -/

/-- Which coordinands a probe outside the coordinate structure attracts. -/
inductive Moved where
  | none
  | left
  | right
  | both
  | whole
  deriving DecidableEq, Repr

/-- A coordination of the data: the two coordinands' categories, which of them move, and whether
they are one and the same occurrence. -/
structure Row where
  left : Category
  right : Category
  moved : Moved
  same : Bool
  judgment : Features.Judgment
  deriving DecidableEq

/-- A coordinand, and not the whole, is attracted: the Integrity Condition (50) forbids it. -/
def Moved.Coordinand : Moved → Prop
  | .left | .right | .both => True
  | .none | .whole => False

instance : DecidablePred Moved.Coordinand := λ _ => by
  unfold Moved.Coordinand; split <;> infer_instance

/-- The three factors of §2.3: the coordinands are not coordinable (10)/(22); they are, but a
coordinand is attracted (50); or the coordinands are one occurrence (71). -/
def Row.Factor (r : Row) : Fin 3 → Prop
  | 0 => ¬ Coordinable r.left r.right
  | 1 => Coordinable r.left r.right ∧ r.moved.Coordinand
  | 2 => r.same = true

instance (r : Row) (i : Fin 3) : Decidable (r.Factor i) := by
  unfold Row.Factor; split <;> infer_instance

def IllFormed (r : Row) : Prop := ∃ i, r.Factor i

instance : DecidablePred IllFormed := λ r => inferInstanceAs (Decidable (∃ i, r.Factor i))

def categoryTable : List (String × Category) :=
  [("D", ⟨{.D}, .max⟩), ("D wh", ⟨{.D, .wh}, .max⟩), ("D focus", ⟨{.D, .focus}, .max⟩),
    ("D topic", ⟨{.D, .topic}, .max⟩), ("D uC", ⟨{.D, .uCase}, .max⟩), ("P", ⟨{.P}, .max⟩),
    ("C", ⟨{.C}, .max⟩), ("Adj", ⟨{.Adj}, .max⟩), ("Adj wh", ⟨{.Adj, .wh}, .max⟩),
    ("Adj focus", ⟨{.Adj, .focus}, .max⟩), ("Adj topic", ⟨{.Adj, .topic}, .max⟩)]

def movedTable : List (String × Moved) :=
  [("none", .none), ("left", .left), ("right", .right), ("both", .both), ("whole", .whole)]

def sameTable : List (String × Bool) := [("yes", true), ("no", false)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let l ← ex.parse? "left" categoryTable
  let r ← ex.parse? "right" categoryTable
  let m ← ex.parse? "moved" movedTable
  let s ← ex.parse? "same" sameTable
  pure ⟨l, r, m, s, ex.judgment⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The paper's judgments are the three-factor decomposition's: a coordination is ungrammatical
exactly when one of the factors applies. -/
theorem rows_predicted : ∀ r ∈ rows, (r.judgment = .acceptable ↔ ¬ IllFormed r) := by
  decide

/-- §2.3: each ill-formed coordination in the data falls under exactly one factor — only the
coordinator's definition rules out extraction of a single coordinand, only the Integrity Condition
extraction of identical coordinands, only the Prohibition against Self-Coordination the
across-the-board dependency with coordinated positions. -/
theorem rows_factor : ∀ r ∈ rows, ∀ i j, r.Factor i → r.Factor j → i = j := by
  decide

end Fortuny2024
