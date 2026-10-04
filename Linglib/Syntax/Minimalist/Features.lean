module

public import Linglib.Core.Order.Bundle
public import Linglib.Syntax.Case.Basic
public import Linglib.Semantics.Reference.Prominence
public import Linglib.Syntax.Gender.Basic
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Minimalist.FeatureSlot
public import Linglib.Syntax.Person.Basic

/-!
# Features for Minimalist Agree

A feature dimension is a kind of feature that Agree checks, such as person, number, case or
[±wh], and each dimension has a value type: `Person`, `Number`, `Gender` and `Case` for the
φ-features and case, as elsewhere in the library, and `Bool` for the bivalent features. A
feature value is a dimension with a value in it, and two values share a dimension when their
first components agree. A feature bundle assigns each dimension a three-state checking slot:
absent, unvalued (a probe), or valued.

Interpretability is orthogonal to valuation. Chomsky's interpretable features contribute to LF
(the φ-features of a noun, categorial features), and uninterpretable ones must be checked and
deleted before it (the φ-features of T and v, the case of a noun); which a feature is depends on
its host as well as its dimension.

## Main definitions

* `Minimalist.FeatureType`, `Minimalist.FeatureType.ValueOf` — the dimensions and their values
* `Minimalist.FeatureVal` — a dimension with a value
* `Minimalist.FeatureBundle` — a checking slot at each dimension, with `ofList`, `toList` and
  `valued`
* `Minimalist.Interpretability` — ±interpretable

## References

* [chomsky-1995], [chomsky-2000], [chomsky-2001]
* [adger-2003]
* [bjorkman-2011] — the [Infl] feature
* [marcolli-chomsky-berwick-2025] — bundles as assignments
-/

@[expose] public section

namespace Minimalist

open Reference.Prominence

/-- The inflectional feature `[Infl]` ([bjorkman-2011]) is valued on the verb by the higher temporal
or aspectual head that selects it, `perf` for a participle under Perf/Asp and `impf` under
imperfective Asp. -/
inductive Infl where
  | perf
  | impf
  deriving Repr, DecidableEq

/-! ### Dimensions and values -/

/-- The feature dimensions checked via Agree. φ-features split into their three
sub-dimensions (`person`, `number`, `gender`) so each is a slot in its own right. -/
inductive FeatureType where
  | person | number | gender
  | case | wh | tense | infl | oblique
  | atomic | minimal | participant | author
  deriving Repr, DecidableEq, Fintype

/-- All feature dimensions, for computable enumeration
(`Finset.univ.toList` is noncomputable). -/
def FeatureType.all : List FeatureType :=
  [.person, .number, .gender, .case, .wh, .tense, .infl, .oblique,
   .atomic, .minimal, .participant, .author]

/-- The value type of a dimension is `Person`, `Number`, `Gender` or `Case` for the φ-features and
case, the [Infl] values, and `Bool` for the bivalent features. -/
@[reducible] def FeatureType.ValueOf : FeatureType → Type
  | .person => Person
  | .number => Number
  | .gender => Gender
  | .case => Case
  | .infl => Infl
  | .wh | .tense | .oblique | .atomic | .minimal | .participant | .author => Bool

instance (t : FeatureType) : DecidableEq t.ValueOf := by
  cases t <;> exact inferInstance

instance (t : FeatureType) : Repr t.ValueOf := by
  cases t <;> exact inferInstance

/-- A feature value is a dimension with a value in it, written `⟨.person, .first⟩`. -/
abbrev FeatureVal := Σ t : FeatureType, t.ValueOf

/-! ### Feature bundles

A feature bundle is a total assignment from the dimensions to three-state checking slots
(`Minimalist.FeatureSlot`), absent, unvalued or valued, after [marcolli-chomsky-berwick-2025],
whose free-Merge core keeps the features of a syntactic object atomic, so the slots are an
Agree-layer structure decoupled from the `SyntacticObject` carrier. -/

/-- A feature bundle assigns each dimension a checking slot. -/
abbrev FeatureBundle := (t : FeatureType) → Minimalist.FeatureSlot t.ValueOf

namespace FeatureBundle

instance : BundleLike FeatureBundle FeatureType (fun t ↦ Minimalist.FeatureSlot t.ValueOf) :=
  ⟨fun b ↦ b⟩

instance : LawfulBundleLike FeatureBundle :=
  ⟨fun _ _ h ↦ h⟩

/-- The bundle has a valued feature of the given dimension. -/
def hasValuedFeature (a : FeatureBundle) (t : FeatureType) : Bool :=
  (a t).isValued

/-- The bundle has an unvalued (probe) feature of the given dimension. -/
def hasUnvaluedFeature (a : FeatureBundle) (t : FeatureType) : Bool :=
  (a t).isUnvalued

/-- The value at the given dimension, when valued. -/
def getValuedFeature (a : FeatureBundle) (t : FeatureType) : Option t.ValueOf :=
  (a t).value?

/-- The assignment specifying exactly one valued dimension, all others absent. -/
def single (t : FeatureType) (v : t.ValueOf) : FeatureBundle :=
  Function.update (⊥ : FeatureBundle) t (.valued v)

@[simp] theorem single_self (t : FeatureType) (v : t.ValueOf) :
    single t v t = .valued v := by
  simp [single]

/-- The bundle read off a list of slots, the list head winning on a repeated dimension. -/
def ofList (l : List (Σ t : FeatureType, Minimalist.FeatureSlot t.ValueOf)) : FeatureBundle :=
  l.foldr (fun p b ↦ Function.update b p.1 p.2) ⊥

@[simp] theorem ofList_nil : ofList [] = ⊥ := rfl

/-- The specified slots of a bundle, in `FeatureType.all` order. -/
def toList (b : FeatureBundle) : List (Σ t : FeatureType, Minimalist.FeatureSlot t.ValueOf) :=
  FeatureType.all.filterMap fun t ↦ if (b t).isSpecified then some ⟨t, b t⟩ else none

/-- The valued features of a bundle, in `FeatureType.all` order. -/
def valued (b : FeatureBundle) : List FeatureVal :=
  FeatureType.all.filterMap fun t ↦ (b t).value?.map (⟨t, ·⟩)

/-- The everywhere-`absent` bundle is the default. -/
instance : Inhabited FeatureBundle := ⟨⊥⟩

instance : DecidableEq FeatureBundle :=
  inferInstanceAs (DecidableEq ((t : FeatureType) → Minimalist.FeatureSlot t.ValueOf))

/-- A bundle is rendered by its specified (non-`absent`) dimensions. The function carrier has no
structural `Repr`, so containing structures that `deriving Repr` rely on this. -/
instance : Repr FeatureBundle where
  reprPrec fb _ :=
    repr <| FeatureType.all.filterMap fun t ↦
      if (fb t).isSpecified then some (reprStr t, reprStr (fb t)) else none

end FeatureBundle

/-! ### Interpretability -/

/-- A feature is interpretable when it contributes to LF and uninterpretable when it must be
checked and deleted before LF ([chomsky-1995]). The distinction is orthogonal to valuation: the
φ-features of a noun are interpretable and valued, those of T and v uninterpretable and
unvalued. -/
inductive Interpretability where
  | interpretable
  | uninterpretable
  deriving Repr, DecidableEq

end Minimalist
