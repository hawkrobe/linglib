module

public import Linglib.Core.Order.Bundle
public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Semantics.Reference.Prominence
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Minimalist.FeatureSlot
public import Linglib.Syntax.Person.Features

/-!
# Features for Minimalist Agree

A feature dimension is a kind of feature that Agree checks: an agreement dimension
(`Agreement.Dimension`), one of Harbour's person or number features (`Person.Feature`,
`Number.Feature`), or a Minimalist feature such as [±wh]. Each takes its values from the type
that already owns it, so the person dimension here is the person of an agreement bundle, and
Harbour's features are bivalent. A feature value is a dimension with a value in it, and two
values share a dimension when their first components agree. A feature bundle assigns each
dimension a three-state checking slot: absent, unvalued (a probe), or valued.

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
* [harbour-2014] — the number features
* [harbour-2016] — the person features
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

/-- The feature dimensions Agree checks are the agreement dimensions, Harbour's person and number
features, and the Minimalist [±wh], [±tense], [Infl] and [obl]. -/
inductive FeatureType where
  | agr (d : Agreement.Dimension)
  | personFeature (f : Person.Feature)
  | numberFeature (f : Number.Feature)
  | wh | tense | infl | oblique
  deriving Repr, DecidableEq, Fintype

namespace FeatureType

/-- `person` is the agreement dimension of person. -/
@[match_pattern] abbrev person : FeatureType := agr .person
/-- `number` is the agreement dimension of number. -/
@[match_pattern] abbrev number : FeatureType := agr .number
/-- `gender` is the agreement dimension of gender. -/
@[match_pattern] abbrev gender : FeatureType := agr .gender
/-- `case` is the agreement dimension of case. -/
@[match_pattern] abbrev case : FeatureType := agr .case
/-- `participant` is Harbour's [±participant]. -/
@[match_pattern] abbrev participant : FeatureType := personFeature .participant
/-- `author` is Harbour's [±author]. -/
@[match_pattern] abbrev author : FeatureType := personFeature .author
/-- `atomic` is Harbour's [±atomic]. -/
@[match_pattern] abbrev atomic : FeatureType := numberFeature .atomic
/-- `minimal` is Harbour's [±minimal]. -/
@[match_pattern] abbrev minimal : FeatureType := numberFeature .minimal

/-- All feature dimensions, for computable enumeration (`Finset.univ.toList` is
noncomputable). -/
def all : List FeatureType :=
  [person, number, gender, case, agr .definiteness, participant, author, atomic, minimal,
   wh, tense, infl, oblique]

/-- Every dimension is listed in `all`. -/
theorem mem_all (t : FeatureType) : t ∈ all := by
  revert t; decide

/-- The value type of a dimension is that of the agreement dimension it is, [Infl]'s values, or
`Bool` for the bivalent features. -/
@[reducible] def ValueOf : FeatureType → Type
  | agr d => d.Value
  | personFeature _ | numberFeature _ => Bool
  | infl => Infl
  | wh | tense | oblique => Bool

instance (t : FeatureType) : DecidableEq t.ValueOf := by
  cases t with
  | agr d => exact inferInstance
  | _ => exact inferInstance

instance (t : FeatureType) : Repr t.ValueOf := by
  cases t with
  | agr d => cases d <;> exact inferInstance
  | _ => exact inferInstance

end FeatureType

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
