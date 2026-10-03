module

public import Mathlib.Order.Nat
public import Mathlib.Tactic.DeriveFintype

/-!
# Grammatical number

`Number` is Corbett's inventory of number values, the vocabulary in which number systems,
agreement, resolution and the semantics of number are stated. A value is determinate when its
cardinality boundary is fixed, as for the singular, dual and trial, and the general, a form
noncommittal to cardinality, lies outside the number system. The Universal Dependencies tags
that corpora annotate (`Morphology/Word/UD.lean`) lack the general, minimal, augmented and unit
augmented values and add inverse, collective and count categories. The quadral is excluded,
Corbett reanalysing apparent quadrals (Sursurunga, Tangga) as paucals.

## Main definitions

* `Number`: the number values.
* `Number.instPartialOrder`: the markedness order, `a ≤ b` when every system with `b` has `a`.
* `Number.System`: a language's number values, with the implicational universals as decidable
  predicates and their conjunction `Number.System.WellFormed`.
* `Number.Stage`: Cysouw's four number-opposition stages, linearly ordered.

## Implementation notes

The markedness order is checked against Harbour's feature calculus in `Studies/Harbour2014.lean`.
The feature decomposition lives in `Semantics/Plurality/NumberFeatures.lean` and coordinate
resolution in `Syntax/Number/Resolve.lean`.

## References

* [corbett-2000]
* [greenberg-1963]
* [greenberg-1966]
* [harbour-2014]
* [cysouw-2003]
* [sauerland-2003]
* [grimm-2018]
-/

@[expose] public section

/-- The grammatical number values are those of [corbett-2000]'s typology. -/
inductive Number where
  /-- The general is noncommittal to cardinality and lies outside the number system (Bayso
      *lúban* 'lion(s)', Japanese *inu* 'dog(s)'). It is a form of a noun that has number,
      unlike a noncountable noun, which lacks the contrast ([grimm-2018],
      `Studies/Grimm2018.lean`). -/
  | general
  /-- The singular denotes exactly one individual, `[+atomic, +minimal]`. -/
  | singular
  /-- The dual denotes exactly two, `[−atomic, +minimal]`. -/
  | dual
  /-- The trial denotes exactly three, recursive `[+minimal]` on the plural region. -/
  | trial
  /-- The paucal denotes a few, with an indeterminate boundary, `[−additive]`. -/
  | paucal
  /-- The plural denotes more than one, the residual value, `[−atomic]` or `[+additive]`. -/
  | plural
  /-- The greater paucal is indeterminate and larger than the paucal, `[−additive +additive]`,
      a second bounded region above the paucal. -/
  | greaterPaucal
  /-- The greater plural denotes abundance, `[+additive]` above a high cut. -/
  | greaterPlural
  /-- The minimal is `[+minimal]` without `[±atomic]`, covering atoms and minimal non-atoms
      alike, unlike the singular. -/
  | minimal
  /-- The augmented is `[−minimal]` without `[±atomic]`, the complement of the minimal. -/
  | augmented
  /-- The unit augmented is recursive `[+minimal]` on the augmented region, the minimal
      non-minimal, unlike the dual. -/
  | unitAugmented
  /-- The global plural denotes every instance in the domain of discourse, the cut of
      `[±additive]` at the top of the lattice, tentative in [harbour-2014]. -/
  | globalPlural
  deriving DecidableEq, Repr, Fintype

namespace Number

/-! ### Classification predicates -/

/-- A number value is determinate when its cardinality boundary is fixed. The minimal and unit
augmented are not, since they depend on the composition of the group. -/
def isDeterminate : Number → Prop
  | .singular | .dual | .trial => True
  | _ => False

instance : DecidablePred isDeterminate := fun n => by
  cases n <;> unfold isDeterminate <;> infer_instance

/-- A number value participates in the number system (is not general). -/
def isInSystem : Number → Prop
  | .general => False
  | _ => True

instance : DecidablePred isInSystem := fun n => by
  cases n <;> unfold isInSystem <;> infer_instance

/-- A determinate value's referent has an exact cardinality, one for the singular, two for the
dual and three for the trial; the other values have none. -/
def exactCard : Number → Option Nat
  | .singular => some 1
  | .dual     => some 2
  | .trial    => some 3
  | _         => none

/-- `fromCard n` is the determinate value of cardinality `n`, and the residual plural from
four on, the greater plural being a value of abundance rather than of four or more. -/
def fromCard : Nat → Number
  | 1 => .singular
  | 2 => .dual
  | 3 => .trial
  | _ => .plural

/-! ### The markedness order

`a ≤ b` means b presupposes a: every number system containing b also
contains a — the implicational hierarchy of [greenberg-1963] and
[corbett-2000] §2.3. The number system of every legitimate parameter setting
of [harbour-2014] is a lower set of this order except those of
`{±additive(*), ±minimal*}`, whose unit augmented lacks the augmented
(`Harbour2014.isLowerSet_values_iff`).

Three independent branches:
```
[±atomic] branch:    trial    greaterPlural
                       |        /
                      dual     /
                       |      /
                   singular  /
                       |    /
                    plural

[±minimal] branch:       unitAugmented
                              |
                          augmented
                              |
                           minimal

Approximative branch:    greaterPaucal    globalPlural
                              |               |
                            paucal          plural
```
The `[±atomic]` branch and `[±minimal]` branch are independent: singular
and minimal never cooccur. Plural spans both. `general` is isolated
(incomparable with all in-system values).

This *typological* order is one of three markedness notions on number and
must not be conflated with the others: the *specification* order on the
Harbour decomposition (the size of a `Number.Features` bundle: sg > du > pl,
linear) and *semantic* markedness ([sauerland-2003], which rides on
specification). On the sg/pl pair the two orders disagree — here sg and pl
are incomparable; under specification sg > pl. -/

/-- `markednessLE a b` holds when every number system with `b` has `a`. -/
def markednessLE (a b : Number) : Prop :=
  a = b ∨ match a, b with
  -- [±atomic] branch ([harbour-2014] Table 1: TR → DU, DU → SG, SG → PL):
  -- plural ≤ singular ≤ dual ≤ trial; greaterPlural requires singular and
  -- plural but NOT dual (Table 1: GR.PL → PL/AUG; Fula is sg/pl/grpl)
  | .singular, .dual | .singular, .trial => True
  | .plural, .singular | .plural, .dual | .plural, .trial => True
  | .plural, .greaterPlural => True
  | .dual, .trial => True
  -- Approximative branch: plural ≤ paucal ≤ greaterPaucal
  | .plural, .paucal | .plural, .greaterPaucal => True
  | .paucal, .greaterPaucal => True
  -- [±minimal] branch: minimal ≤ augmented ≤ unitAugmented
  | .minimal, .augmented | .minimal, .unitAugmented => True
  | .augmented, .unitAugmented => True
  -- globalPlural: plural ≤ globalPlural
  | .plural, .globalPlural => True
  | _, _ => False

instance : ∀ a b : Number, Decidable (markednessLE a b) := fun a b => by
  unfold markednessLE; cases a <;> cases b <;> exact inferInstance

instance : LE Number := ⟨markednessLE⟩

instance : DecidableRel ((· ≤ ·) : Number → Number → Prop) :=
  fun a b => inferInstanceAs (Decidable (markednessLE a b))

instance instPartialOrder : PartialOrder Number where
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide

/-! ### Number opposition stages ([cysouw-2003], Fig 10.8) -/

/-- The number opposition stages of [cysouw-2003] (Fig 10.8) coarsen the number values into
four steps of typological richness, from no number marking (N1) to marking of restricted and
small groups (N3, N4). -/
inductive Stage where
  /-- N1 leaves number unmarked, the singular undistinguished from a group. -/
  | N1
  /-- N2 opposes the singular to a group, the basic number opposition. -/
  | N2
  /-- N3 also distinguishes a restricted group (the dual, and the inclusive trial of
      unit-augmented paradigms) from an unrestricted one. -/
  | N3
  /-- N4 also distinguishes a small group, the paucal. -/
  | N4
  deriving DecidableEq, Repr

namespace Stage

/-- `toNat` embeds the stages into `ℕ` in order of richness. -/
def toNat : Stage → Nat
  | .N1 => 0
  | .N2 => 1
  | .N3 => 2
  | .N4 => 3

instance : LinearOrder Stage :=
  LinearOrder.lift' toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [toNat])

/-- The order on `Stage` is the `toNat` order. -/
theorem toNat_le_toNat {a b : Stage} : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

end Stage

/-! ### Number systems ([corbett-2000] §2.3) -/

/-- A number system records the values available in a language, which of them are
facultative, and whether the language has general number ([corbett-2000] §2.3). -/
structure System where
  name : String
  /-- The values available within the number system. -/
  values : List Number
  /-- Whether the language has general number, a form outside the system. -/
  hasGeneral : Bool := false
  /-- The facultative values, whose use is optional. -/
  facultative : List Number := []
  deriving DecidableEq

namespace System

/-- The size of a system is its number of values. -/
def size (ns : System) : Nat := ns.values.length

/-- A value is obligatory in a system that has it and does not make it facultative. -/
def IsObligatory (ns : System) (v : Number) : Prop :=
  v ∈ ns.values ∧ v ∉ ns.facultative

instance (ns : System) (v : Number) : Decidable (ns.IsObligatory v) := by
  unfold System.IsObligatory; infer_instance

/-! #### Implicational universals ([greenberg-1963], [corbett-2000] §2.3.1) -/

/-- Trial implies dual, TR → DU in [harbour-2014] Table 1. -/
def TrialImpliesDual (ns : System) : Prop :=
  .trial ∈ ns.values → .dual ∈ ns.values

/-- Dual implies singular, DU → SG in [harbour-2014] Table 1. -/
def DualImpliesSingular (ns : System) : Prop :=
  .dual ∈ ns.values → .singular ∈ ns.values

/-- Singular implies plural, SG → PL in [harbour-2014] Table 1. -/
def SingularImpliesPlural (ns : System) : Prop :=
  .singular ∈ ns.values → .plural ∈ ns.values

/-- Dual implies plural ([greenberg-1966], [corbett-2000] §2.3.1), the composition of
DU → SG and SG → PL. -/
def DualImpliesPlural (ns : System) : Prop :=
  .dual ∈ ns.values → .plural ∈ ns.values

/-- Minimal implies augmented or plural, MIN → AUG/PL in [harbour-2014] Table 1. -/
def MinimalImpliesAugmentedOrPlural (ns : System) : Prop :=
  .minimal ∈ ns.values → .augmented ∈ ns.values ∨ .plural ∈ ns.values

/-- Paucal implies plural, PC → PL in [harbour-2014] Table 1. -/
def PaucalImpliesPlural (ns : System) : Prop :=
  .paucal ∈ ns.values → .plural ∈ ns.values

/-- Greater paucal implies paucal, GR.PC → PC in [harbour-2014] Table 1. -/
def GreaterPaucalImpliesPaucal (ns : System) : Prop :=
  .greaterPaucal ∈ ns.values → .paucal ∈ ns.values

/-- Greater plural implies plural or augmented, GR.PL → PL/AUG in [harbour-2014] Table 1, a
disjunction and so a predicate of systems rather than an edge of the markedness order. -/
def GreaterPluralImpliesPluralOrAugmented (ns : System) : Prop :=
  .greaterPlural ∈ ns.values → .plural ∈ ns.values ∨ .augmented ∈ ns.values

/-- Plural implies singular or minimal, PL → SG/MIN in [harbour-2014] Table 1, the plural
needing a base value, the singular of `[±atomic]` or the minimal of `[±minimal]`. -/
def PluralImpliesSingularOrMinimal (ns : System) : Prop :=
  .plural ∈ ns.values → .singular ∈ ns.values ∨ .minimal ∈ ns.values

/-- Augmented implies minimal, AUG → MIN in [harbour-2014] Table 1. -/
def AugmentedImpliesMinimal (ns : System) : Prop :=
  .augmented ∈ ns.values → .minimal ∈ ns.values

/-- Unit augmented implies augmented, U.AUG → AUG in [harbour-2014] Table 1. -/
def UnitAugImpliesAugmented (ns : System) : Prop :=
  .unitAugmented ∈ ns.values → .augmented ∈ ns.values

instance (ns : System) : Decidable ns.TrialImpliesDual := by
  unfold TrialImpliesDual; infer_instance
instance (ns : System) : Decidable ns.DualImpliesSingular := by
  unfold DualImpliesSingular; infer_instance
instance (ns : System) : Decidable ns.SingularImpliesPlural := by
  unfold SingularImpliesPlural; infer_instance
instance (ns : System) : Decidable ns.DualImpliesPlural := by
  unfold DualImpliesPlural; infer_instance
instance (ns : System) : Decidable ns.MinimalImpliesAugmentedOrPlural := by
  unfold MinimalImpliesAugmentedOrPlural; infer_instance
instance (ns : System) : Decidable ns.PaucalImpliesPlural := by
  unfold PaucalImpliesPlural; infer_instance
instance (ns : System) : Decidable ns.GreaterPaucalImpliesPaucal := by
  unfold GreaterPaucalImpliesPaucal; infer_instance
instance (ns : System) : Decidable ns.GreaterPluralImpliesPluralOrAugmented := by
  unfold GreaterPluralImpliesPluralOrAugmented; infer_instance
instance (ns : System) : Decidable ns.PluralImpliesSingularOrMinimal := by
  unfold PluralImpliesSingularOrMinimal; infer_instance
instance (ns : System) : Decidable ns.AugmentedImpliesMinimal := by
  unfold AugmentedImpliesMinimal; infer_instance
instance (ns : System) : Decidable ns.UnitAugImpliesAugmented := by
  unfold UnitAugImpliesAugmented; infer_instance

/-- A well-formed number system satisfies all the implicational universals of
[harbour-2014] Table 1. -/
def WellFormed (ns : System) : Prop :=
  ns.TrialImpliesDual ∧ ns.DualImpliesSingular ∧ ns.SingularImpliesPlural ∧
  ns.DualImpliesPlural ∧ ns.PluralImpliesSingularOrMinimal ∧
  ns.MinimalImpliesAugmentedOrPlural ∧ ns.AugmentedImpliesMinimal ∧
  ns.UnitAugImpliesAugmented ∧ ns.PaucalImpliesPlural ∧
  ns.GreaterPaucalImpliesPaucal ∧ ns.GreaterPluralImpliesPluralOrAugmented

instance (ns : System) : Decidable ns.WellFormed := by
  unfold WellFormed; infer_instance

/-- A system realizes the [cysouw-2003] stage its number of values fixes, N1 for at most one
value, N2 for two, N3 for three and N4 for more. -/
def toStage (ns : System) : Stage :=
  match ns.size with
  | 0 | 1 => .N1
  | 2 => .N2
  | 3 => .N3
  | _ => .N4

end System

end Number
