/-
# Horn Scales

Horn scales are ordered sets of expressions by semantic strength, where
stronger members entail weaker members. Scale ordering determines scalar implicatures.

## Main definitions

`HornScale`, `scalePosition`, `isWeaker`, `strongerAlternatives`, `quantScale`,
`worldMeaning`, `connScale`, `modalScale`

## References

Horn (1972). On the Semantic Properties of Logical Operators in English.
-/

import Mathlib.Data.Rat.Defs

namespace Core.Scale

-- General Scale Infrastructure

/-- Horn scale: list of expressions ordered by semantic strength. -/
structure HornScale (α : Type) where
  /-- Members ordered from weakest to strongest. -/
  members : List α
  deriving Repr

def scalePosition {α : Type} [BEq α] (s : HornScale α) (x : α) : Option Nat :=
  s.members.findIdx? (· == x)

def isWeaker {α : Type} [BEq α] (s : HornScale α) (x y : α) : Bool :=
  match scalePosition s x, scalePosition s y with
  | some px, some py => px < py
  | _, _ => false

def isStronger {α : Type} [BEq α] (s : HornScale α) (x y : α) : Bool :=
  isWeaker s y x

def strongerAlternatives {α : Type} [BEq α] (s : HornScale α) (x : α) : List α :=
  match scalePosition s x with
  | some px => s.members.drop (px + 1)
  | none => []

def weakerAlternatives {α : Type} [BEq α] (s : HornScale α) (x : α) : List α :=
  match scalePosition s x with
  | some px => s.members.take px
  | none => []

namespace Quantifiers

inductive QuantExpr where
  | none_ | some_ | most | all
  deriving DecidableEq, BEq, Repr, Inhabited

def QuantExpr.ofString? : String → Option QuantExpr
  | "none" => some .none_
  | "some" => some .some_
  | "most" => some .most
  | "all" => some .all
  | "every" => some .all
  | _ => none

def QuantExpr.toString : QuantExpr → String
  | .none_ => "none"
  | .some_ => "some"
  | .most => "most"
  | .all => "all"

instance : ToString QuantExpr := ⟨QuantExpr.toString⟩

def quantScale : HornScale QuantExpr :=
  ⟨[.none_, .some_, .most, .all]⟩

def entails : QuantExpr → QuantExpr → Bool
  | .all, .some_ => true
  | .all, .most => true
  | .all, .all => true
  | .most, .some_ => true
  | .most, .most => true
  | .some_, .some_ => true
  | .none_, .none_ => true
  | _, _ => false

theorem scale_matches_entailment :
    isStronger quantScale .all .most = true ∧
    isStronger quantScale .most .some_ = true ∧
    isStronger quantScale .all .some_ = true := by
  native_decide

theorem some_has_stronger_alternatives :
    strongerAlternatives quantScale .some_ = [.most, .all] := by
  native_decide

/-- Quantifier world: domain of size maxN with count of entities satisfying property. -/
structure QuantWorld (maxN : Nat) where
  /-- How many entities satisfy the predicate (0 to maxN). -/
  count : Fin (maxN + 1)
  deriving DecidableEq, BEq, Repr

/-- Intensional meaning: quantifier as function from worlds to truth values. -/
def worldMeaning (maxN : Nat) : QuantExpr → QuantWorld maxN → Bool
  | .none_, w => w.count.val == 0
  | .some_, w => w.count.val ≥ 1
  | .most, w => w.count.val > maxN / 2
  | .all, w => w.count.val == maxN

def allWorlds (maxN : Nat) : List (QuantWorld maxN) :=
  (List.range (maxN + 1)).filterMap λ n =>
    if h : n < maxN + 1 then some ⟨⟨n, h⟩⟩ else none

def w0 : QuantWorld 3 := ⟨⟨0, by omega⟩⟩
def w1 : QuantWorld 3 := ⟨⟨1, by omega⟩⟩
def w2 : QuantWorld 3 := ⟨⟨2, by omega⟩⟩
def w3 : QuantWorld 3 := ⟨⟨3, by omega⟩⟩

theorem entailment_preserved_all_some :
    (worldMeaning 3 .all w0 = true → worldMeaning 3 .some_ w0 = true) ∧
    (worldMeaning 3 .all w1 = true → worldMeaning 3 .some_ w1 = true) ∧
    (worldMeaning 3 .all w2 = true → worldMeaning 3 .some_ w2 = true) ∧
    (worldMeaning 3 .all w3 = true → worldMeaning 3 .some_ w3 = true) := by
  native_decide

theorem some_lower_bounded :
    worldMeaning 3 .some_ w0 = false ∧
    worldMeaning 3 .some_ w1 = true ∧
    worldMeaning 3 .some_ w2 = true ∧
    worldMeaning 3 .some_ w3 = true := by native_decide

theorem some_compatible_with_all : worldMeaning 3 .some_ w3 = true := by native_decide

end Quantifiers

namespace Connectives

inductive ConnExpr where
  | or_ | and_
  deriving DecidableEq, BEq, Repr, Inhabited

def ConnExpr.ofString? : String → Option ConnExpr
  | "or" => some .or_
  | "and" => some .and_
  | _ => none

def ConnExpr.toString : ConnExpr → String
  | .or_ => "or"
  | .and_ => "and"

instance : ToString ConnExpr := ⟨ConnExpr.toString⟩

def connScale : HornScale ConnExpr :=
  ⟨[.or_, .and_]⟩

def entails : ConnExpr → ConnExpr → Bool
  | .and_, .or_ => true
  | .and_, .and_ => true
  | .or_, .or_ => true
  | _, _ => false

theorem and_stronger_than_or :
    isStronger connScale .and_ .or_ = true ∧
    isStronger connScale .or_ .and_ = false := by
  native_decide

theorem or_alternative :
    strongerAlternatives connScale .or_ = [.and_] := by
  native_decide

end Connectives

namespace Modals

inductive ModalExpr where
  | possible | necessary
  deriving DecidableEq, BEq, Repr, Inhabited

def ModalExpr.ofString? : String → Option ModalExpr
  | "possible" => some .possible
  | "might" => some .possible
  | "may" => some .possible
  | "necessary" => some .necessary
  | "must" => some .necessary
  | _ => none

def ModalExpr.toString : ModalExpr → String
  | .possible => "possible"
  | .necessary => "necessary"

instance : ToString ModalExpr := ⟨ModalExpr.toString⟩

def modalScale : HornScale ModalExpr :=
  ⟨[.possible, .necessary]⟩

def entails : ModalExpr → ModalExpr → Bool
  | .necessary, .possible => true
  | .necessary, .necessary => true
  | .possible, .possible => true
  | _, _ => false

theorem necessary_stronger_than_possible :
    isStronger modalScale .necessary .possible = true := by
  native_decide

end Modals

/-!
### Numerals and Horn Scales

Numerals are NOT represented as a `HornScale` here because:

1. Under **lower-bound** semantics (Horn 1972), numerals do form a scale
   (⟨1, 2, 3, ...⟩), but it is **infinite** — a finite `HornScale` list
   can't represent it correctly ("five" would have no stronger alternatives).

2. Under **bilateral** semantics (Kennedy 2015), numerals are non-monotonic
   and do NOT form a Horn scale at all. The relevant alternatives are
   {bare n, Class A n, Class B n}, not other numerals.

Both cases are handled properly in
`Theories/TruthConditional/Determiner/Numeral/Semantics.lean`:
- `NumeralTheory.isStrongerThan` computes strength for any theory
- `NumeralAlternative` represents Kennedy's alternative sets
- `lowerBound_monotonic` / `bilateral_not_monotonic` prove the key contrast
-/

def scalarImplicatures {α : Type} [BEq α] (s : HornScale α) (x : α) : List α :=
  strongerAlternatives s x

example : scalarImplicatures Quantifiers.quantScale .some_ = [.most, .all] := by
  native_decide

example : scalarImplicatures Connectives.connScale .or_ = [.and_] := by
  native_decide

inductive Monotonicity where
  | upward
  | downward
  deriving DecidableEq, BEq, Repr

def scalarAlternativesInContext {α : Type} [BEq α]
    (s : HornScale α) (x : α) (m : Monotonicity) : List α :=
  match m with
  | .upward => strongerAlternatives s x
  | .downward => weakerAlternatives s x

theorem de_reversal_some :
    scalarAlternativesInContext Quantifiers.quantScale .some_ .upward = [.most, .all] ∧
    scalarAlternativesInContext Quantifiers.quantScale .some_ .downward = [.none_] := by
  native_decide

theorem de_blocks_some_not_all :
    scalarAlternativesInContext Quantifiers.quantScale .all .downward = [.none_, .some_, .most] := by
  native_decide

end Core.Scale
