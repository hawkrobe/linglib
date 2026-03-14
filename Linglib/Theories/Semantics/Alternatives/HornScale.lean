/-
# Horn Scales

Horn scales are ordered sets of expressions by semantic strength, where
stronger members entail weaker members. Scale ordering determines scalar implicatures.

## Main definitions

`HornScale`, `scalePosition`, `isWeaker`, `strongerAlternatives`, `quantScale`,
`worldMeaning`, `connScale`, `modalScale`

-/

import Linglib.Core.Polarity
import Mathlib.Data.Rat.Defs

namespace Alternatives

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
@cite{horn-1972} @cite{kennedy-2015}

Numerals are NOT represented as a `HornScale` here because:

1. Under **lower-bound** semantics, numerals do form a scale
   (⟨1, 2, 3,...⟩), but it is **infinite** — a finite `HornScale` list
   can't represent it correctly ("five" would have no stronger alternatives).

2. Under **bilateral** semantics, numerals are non-monotonic
   and do NOT form a Horn scale at all. The relevant alternatives are
   {bare n, Class A n, Class B n}, not other numerals.

Both cases are handled properly in
`Theories/Semantics.Montague/Determiner/Numeral/Semantics.lean`:
- `NumeralTheory.isStrongerThan` computes strength for any theory
- `NumeralAlternative` represents Kennedy's alternative sets
- `lowerBound_monotonic` / `bilateral_not_monotonic` prove the key contrast
-/

namespace Number

/-!
### Singular/Plural as a Horn Scale
@cite{sauerland-2003} @cite{spector-2007} @cite{tieu-etal-2020}

The singular and plural morphemes form a Horn scale ⟨singular, plural⟩
where singular ("a giraffe") is the stronger alternative to plural ("giraffes").

Under the implicature approach to multiplicity inferences, the plural
literally means "one or more" and the "more than one" inference arises
as a scalar implicature: the listener reasons that the speaker chose
the weaker "giraffes" over the stronger "a giraffe," implying that
the singular alternative is false — hence more than one.

This scale is structurally unusual: the alternatives differ in morphology
(number marking), not in lexical choice (unlike some/all, or/and).
-/

inductive NumberExpr where
  | singular | plural
  deriving DecidableEq, BEq, Repr, Inhabited

def NumberExpr.toString : NumberExpr → String
  | .singular => "singular"
  | .plural => "plural"

instance : ToString NumberExpr := ⟨NumberExpr.toString⟩

/-- Singular is stronger: "a giraffe" entails "giraffes" (one or more). -/
def numberScale : HornScale NumberExpr :=
  ⟨[.plural, .singular]⟩

theorem singular_stronger_than_plural :
    isStronger numberScale .singular .plural = true := by
  native_decide

theorem plural_alternative :
    strongerAlternatives numberScale .plural = [.singular] := by
  native_decide

end Number

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

/-- Sentence polarity determines monotonicity context:
    positive sentences are upward-entailing, negative are downward-entailing.
    This is the Ladusaw (1979) / Fauconnier (1975) connection. -/
def Polarity.toMonotonicity : Core.Polarity → Monotonicity
  | .positive => .upward
  | .negative => .downward

-- ============================================================
-- Semantic Scales (proposition-level Horn scales)
-- ============================================================

/--
A Horn scale with semantic content: a pair of propositions where
`stronger` entails `weaker` but not vice versa.

This is the proposition-level counterpart of `HornScale α` (form-level).
The entailment asymmetry drives scalar implicatures via exhaustification.
-/
structure SemanticScale (World : Type*) where
  /-- Name of the scale -/
  name : String
  /-- The weaker scalar term (e.g., "some") -/
  weakerTerm : String
  /-- The stronger scalar term (e.g., "all") -/
  strongerTerm : String
  /-- Semantic denotation of weaker term -/
  weaker : World → Prop
  /-- Semantic denotation of stronger term -/
  stronger : World → Prop
  /-- Stronger entails weaker -/
  entailment : ∀ w, stronger w → weaker w
  /-- Weaker does not entail stronger (non-trivial scale) -/
  nonTrivial : ¬(∀ w, weaker w → stronger w)

/--
Alternative set for a semantic scale: {weaker, stronger}.
-/
def SemanticScale.alts {World : Type*} (s : SemanticScale World) : Set (World → Prop) :=
  {s.weaker, s.stronger}


-- ============================================================
-- Quantifier Scale: some/all
-- ============================================================

/-- Worlds for quantifier scale: number satisfying predicate (0 to 3). -/
abbrev SemQuantWorld := Fin 4

/-- "Some Ps are Q" = at least one. -/
def someQ : SemQuantWorld → Prop := λ w => w.val ≥ 1

/-- "All Ps are Q" = all three. -/
def allQ : SemQuantWorld → Prop := λ w => w.val = 3

/-- All entails some. -/
theorem all_entails_some : ∀ w, allQ w → someQ w := by
  intro w h
  simp only [allQ] at h
  simp only [someQ, h]
  decide

/-- Some does not entail all. -/
theorem some_not_entails_all : ¬(∀ w, someQ w → allQ w) := by
  intro h
  have : allQ ⟨1, by omega⟩ := h ⟨1, by omega⟩ (by simp [someQ])
  simp [allQ] at this

/-- The some/all semantic scale. -/
def someAllScale : SemanticScale SemQuantWorld :=
  { name := "Quantifiers (some/all)"
  , weakerTerm := "some"
  , strongerTerm := "all"
  , weaker := someQ
  , stronger := allQ
  , entailment := all_entails_some
  , nonTrivial := some_not_entails_all
  }


-- ============================================================
-- Connective Scale: or/and
-- ============================================================

/-- Worlds for connective scale. -/
inductive ConnWorld where
  | neither | onlyA | onlyB | both
  deriving DecidableEq, Repr

/-- "A or B" (inclusive). -/
def orConn : ConnWorld → Prop
  | .neither => False
  | .onlyA => True
  | .onlyB => True
  | .both => True

/-- "A and B". -/
def andConn : ConnWorld → Prop
  | .neither => False
  | .onlyA => False
  | .onlyB => False
  | .both => True

/-- And entails or. -/
theorem and_entails_or : ∀ w, andConn w → orConn w := by
  intro w h
  cases w <;> simp [andConn, orConn] at h ⊢

/-- Or does not entail and. -/
theorem or_not_entails_and : ¬(∀ w, orConn w → andConn w) := by
  intro h
  have : andConn .onlyA := h .onlyA (by simp [orConn])
  simp [andConn] at this

/-- The or/and semantic scale. -/
def orAndScale : SemanticScale ConnWorld :=
  { name := "Connectives (or/and)"
  , weakerTerm := "or"
  , strongerTerm := "and"
  , weaker := orConn
  , stronger := andConn
  , entailment := and_entails_or
  , nonTrivial := or_not_entails_and
  }


-- ============================================================
-- Modal Scale: possible/necessary
-- ============================================================

/-- Worlds for modal scale: accessibility relation outcomes. -/
inductive ModalWorld where
  | none    -- no accessible world has P
  | some    -- some but not all accessible worlds have P
  | all     -- all accessible worlds have P
  deriving DecidableEq, Repr

/-- "Possibly P" = at least one accessible world has P. -/
def possibleP : ModalWorld → Prop
  | .none => False
  | .some => True
  | .all => True

/-- "Necessarily P" = all accessible worlds have P. -/
def necessaryP : ModalWorld → Prop
  | .none => False
  | .some => False
  | .all => True

/-- Necessary entails possible. -/
theorem necessary_entails_possible : ∀ w, necessaryP w → possibleP w := by
  intro w h
  cases w <;> simp [necessaryP, possibleP] at h ⊢

/-- Possible does not entail necessary. -/
theorem possible_not_entails_necessary : ¬(∀ w, possibleP w → necessaryP w) := by
  intro h
  have : necessaryP .some := h .some (by simp [possibleP])
  simp [necessaryP] at this

/-- The possible/necessary semantic scale. -/
def possibleNecessaryScale : SemanticScale ModalWorld :=
  { name := "Modals (possible/necessary)"
  , weakerTerm := "possible"
  , strongerTerm := "necessary"
  , weaker := possibleP
  , stronger := necessaryP
  , entailment := necessary_entails_possible
  , nonTrivial := possible_not_entails_necessary
  }

end Alternatives
