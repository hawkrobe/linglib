import Mathlib.Order.Nat
import Mathlib.Tactic.DeriveFintype
import Linglib.Data.UD.Basic

/-!
# Grammatical number — the canonical value space
[corbett-2000] [harbour-2014] [greenberg-1963] [cysouw-2009]

`Number` is the canonical grammatical-number type: [corbett-2000]'s analytical
inventory of number values, the vocabulary in which systems, agreement,
resolution, and semantics are stated. The UD tagset (`UD.Number`) is the
*realization vocabulary* — the surface morphology a value projects to via
`Number.toUD` (the analogue of `Pronoun.toWord`) and is ingested from via
`Number.fromUD` at the corpus boundary. Values UD cannot tag (`general`,
`minimal`, `augmented`, `unitAugmented`) realize as `none`; conversely
`UD.Number.Inv`/`.Coll`/`.Count` are morphological form-categories that are
not values of the count-number system, and have no `Number` preimage.
The quadral is deliberately excluded: [corbett-2000] reanalyzes apparent
quadrals (Sursurunga, Tangga) as paucals.

Values are classified along two orthogonal dimensions ([corbett-2000]):

- **System membership**: `general` is *outside* the number system (a form
  non-committal to cardinality); all others are within it.
- **Determinacy**: values whose cardinality boundary is fixed (singular=1,
  dual=2, trial=3) vs those whose boundary varies by context (paucal ≈ 2–6,
  greater plural ≈ abundance).

## Main declarations

* `Number` — the analytical value inventory ([corbett-2000] Ch 2).
* `Number.toUD` / `Number.fromUD` — realization to / ingestion from `UD.Number`.
* `Number.instPartialOrder` — the markedness order: `a ≤ b` iff every system
  containing `b` also contains `a` (the implicational hierarchy of
  [greenberg-1963] and [corbett-2000] §2.3, derived as a lower-set theorem
  from [harbour-2014]'s feature geometry in `Syntax/Minimalist/Phi/Recursion.lean`).
* `Number.System` — a language's number-value inventory ([corbett-2000] §2.3),
  with the implicational universals as decidable predicates and their
  conjunction `System.WellFormed`.
* `Number.Stage` — [cysouw-2009]'s N1–N4 number-opposition stages, a
  `LinearOrder`.

## Implementation notes

The [harbour-2014] feature decomposition and its lattice grounding live in
`Features/Number/Decomposition.lean`; coordinate resolution in
`Features/Number/Resolve.lean`; the `HasNumber` capability mixin in
`Features/Number/Capabilities.lean`.
-/

set_option autoImplicit false

/-- Grammatical number: [corbett-2000]'s analytical inventory of number values.
    The canonical type — `UD.Number` is its surface realization vocabulary
    (`Number.toUD`/`Number.fromUD`). -/
inductive Number where
  /-- Non-committal to cardinality; *outside* the number system
      (Bayso *lúban* 'lion(s)', Japanese *inu* 'dog(s)'). Not to be
      conflated with non-countability: a general form is a
      value-noncommittal form of a noun that *has* number, whereas a
      non-countable noun lacks the contrast altogether — a countability-class
      fact, not a number value ([grimm-2018]; `Studies/Grimm2018.lean`). -/
  | general
  /-- Exactly one (`[+atomic, +minimal]`). -/
  | singular
  /-- Exactly two (`[−atomic, +minimal]`). -/
  | dual
  /-- Exactly three (recursive `[+minimal]` on the plural region). -/
  | trial
  /-- A few — indeterminate boundary (`[−additive]`). -/
  | paucal
  /-- More than one — the residual value (`[−atomic]` or `[+additive]`). -/
  | plural
  /-- Indeterminate, larger than paucal (recursive `[−additive]`). -/
  | greaterPaucal
  /-- Abundance / totality (recursive `[−minimal]` on the plural region). -/
  | greaterPlural
  /-- `[+minimal]` without `[±atomic]` — atoms *and* minimal non-atoms;
      distinct from singular. -/
  | minimal
  /-- `[−minimal]` without `[±atomic]` — the complement of minimal. -/
  | augmented
  /-- Recursive `[+minimal]` on the augmented region — minimal non-minimal;
      distinct from dual. -/
  | unitAugmented
  /-- Recursive `[+additive]` on a `[+additive]` region (tentative in
      [harbour-2014]). -/
  | globalPlural
  deriving DecidableEq, Repr, Fintype

namespace Number

/-! ### Classification predicates -/

/-- A number value is determinate iff its cardinality boundary is fixed.
    Minimal and unit augmented are indeterminate: they depend on the
    composition of the group, not a fixed cardinality. -/
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

/-- Exact referent-set cardinality for determinate number values.

    Singular denotes exactly 1 individual (atom), dual exactly 2 (pair),
    trial exactly 3 (triple). All other values have indeterminate or
    context-dependent cardinality and return `none`.

    Used by `Number.resolve` to derive coordinate resolution from
    cardinality addition: |A ⊔ B| = |A| + |B| for disjoint sets. -/
def exactCard : Number → Option Nat
  | .singular => some 1
  | .dual     => some 2
  | .trial    => some 3
  | _         => none

/-- Whether a value belongs to the `[±minimal]` number system (without
    `[±atomic]`). In such systems, minimal = atoms ∪ minimal non-atoms,
    and augmented = everything else. -/
def isMinAug : Number → Prop
  | .minimal | .augmented => True
  | _ => False

instance : DecidablePred isMinAug := fun n => by
  cases n <;> unfold isMinAug <;> infer_instance

/-- Map a referent-set cardinality back to the finest determinate value.
    1 → singular, 2 → dual, 3 → trial; sums of 4+ have no determinate value
    and fall to the residual plural (greater plural is an *abundance* value
    in [corbett-2000]'s sense, not "four or more"). -/
def fromCard : Nat → Number
  | 1 => .singular
  | 2 => .dual
  | 3 => .trial
  | _ => .plural

/-- `fromCard` inverts `exactCard` for determinate values. -/
theorem fromCard_singular : fromCard 1 = .singular := rfl
theorem fromCard_dual : fromCard 2 = .dual := rfl
theorem fromCard_trial : fromCard 3 = .trial := rfl

/-! ### Realization: the UD bridge -/

/-- Realize a number value as a UD morphological tag (general has no UD
    equivalent; minimal, augmented, and unit augmented cannot be tagged). -/
def toUD : Number → Option UD.Number
  | .general        => none
  | .singular       => some .Sing
  | .dual           => some .Dual
  | .trial          => some .Tri
  | .paucal         => some .Pauc
  | .plural         => some .Plur
  | .greaterPaucal  => some .Grpa
  | .greaterPlural  => some .Grpl
  | .minimal        => none
  | .augmented      => none
  | .unitAugmented  => none
  | .globalPlural   => none

/-- Ingest a UD morphological tag as a number value (partial).

    Seven core values round-trip cleanly. Three UD tags have no analytical
    equivalent:
    - `Inv` (inverse number): marks the *unexpected* number for a given noun —
      plural for some nouns, singular for others. Not a fixed cardinality.
    - `Coll` (collective): denotes a group-as-unit (Russian *листва* 'foliage'),
      distinct from general number, which is non-committal to cardinality.
    - `Count` (count form): a special form after numerals (Hungarian, Welsh),
      not equivalent to singular (exactly one). -/
def fromUD : UD.Number → Option Number
  | .Sing  => some .singular
  | .Plur  => some .plural
  | .Dual  => some .dual
  | .Tri   => some .trial
  | .Pauc  => some .paucal
  | .Grpa  => some .greaterPaucal
  | .Grpl  => some .greaterPlural
  | .Inv   => none
  | .Coll  => none
  | .Count => none

/-- Round-trip: `fromUD ∘ toUD = id` for all in-system values with a UD tag. -/
theorem roundtrip_fromUD_toUD :
    ∀ v ∈ [Number.singular, .dual, .trial, .paucal, .plural,
           .greaterPaucal, .greaterPlural],
      v.toUD.bind fromUD = some v := by decide

/-! ### The markedness order

`a ≤ b` means b presupposes a: every number system containing b also
contains a — the implicational hierarchy of [greenberg-1963] and
[corbett-2000] §2.3. The order is *derived*, not stipulated: the values
generated by any well-formed Harbour configuration form a lower set in
this order (`Minimalist.Phi.Recursion.categories_isLowerSet`, from
[harbour-2014]'s feature geometry).

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
Harbour decomposition (`Features.ContainmentPair.specLevel`: sg > du > pl,
linear) and *semantic* markedness ([sauerland-2003], which rides on
specification). On the sg/pl pair the two orders disagree — here sg and pl
are incomparable; under specification sg > pl. -/

/-- The markedness ordering on number values. -/
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

/-! ### Number opposition stages ([cysouw-2009], Fig 10.8) -/

/-- Number opposition stages ([cysouw-2009], Fig 10.8): a coarsening of the
    number values into a four-step hierarchy of typological richness, from no
    number marking (N1) to full number marking with restricted groups (N3/N4).
    Linearly ordered by richness. -/
inductive Stage where
  /-- Undifferentiated number marking (singular = group unmarked). -/
  | N1
  /-- Singular vs group (basic number opposition). -/
  | N2
  /-- Restricted group (dual/trial) distinguished from unrestricted. -/
  | N3
  /-- Small group (paucal) additionally distinguished. -/
  | N4
  deriving DecidableEq, Repr

namespace Stage

/-- Numeric embedding into ℕ preserving the richness order. -/
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

/-- A number system: the values available in a language, which are
    obligatory vs facultative, and whether general number exists
    ([corbett-2000] §2.3). Per-language instances live with the studies
    and Fragments that record them. -/
structure System where
  name : String
  /-- Values available within the number system. -/
  values : List Number
  /-- Whether the language has general number (a form outside the system). -/
  hasGeneral : Bool := false
  /-- Values whose use is optional (facultative). -/
  facultative : List Number := []
  deriving DecidableEq

namespace System

/-- Number of values in the system. -/
def size (ns : System) : Nat := ns.values.length

/-- Whether a value is obligatory (present and not facultative). -/
def IsObligatory (ns : System) (v : Number) : Prop :=
  v ∈ ns.values ∧ v ∉ ns.facultative

instance (ns : System) (v : Number) : Decidable (ns.IsObligatory v) := by
  unfold System.IsObligatory; infer_instance

/-! #### Implicational universals ([greenberg-1963], [corbett-2000] §2.3.1) -/

/-- Trial implies dual ([harbour-2014] Table 1: TR → DU). -/
def TrialImpliesDual (ns : System) : Prop :=
  .trial ∈ ns.values → .dual ∈ ns.values

/-- Dual implies singular ([harbour-2014] Table 1: DU → SG). -/
def DualImpliesSingular (ns : System) : Prop :=
  .dual ∈ ns.values → .singular ∈ ns.values

/-- Singular implies plural ([harbour-2014] Table 1: SG → PL). -/
def SingularImpliesPlural (ns : System) : Prop :=
  .singular ∈ ns.values → .plural ∈ ns.values

/-- Dual implies plural ([greenberg-1966], [corbett-2000] §2.3.1; the
    composition of DU → SG and SG → PL). -/
def DualImpliesPlural (ns : System) : Prop :=
  .dual ∈ ns.values → .plural ∈ ns.values

/-- Minimal implies augmented or plural ([harbour-2014] Table 1:
    MIN → AUG/PL). -/
def MinimalImpliesAugmentedOrPlural (ns : System) : Prop :=
  .minimal ∈ ns.values → .augmented ∈ ns.values ∨ .plural ∈ ns.values

/-- Paucal implies plural ([harbour-2014] Table 1: PC → PL). -/
def PaucalImpliesPlural (ns : System) : Prop :=
  .paucal ∈ ns.values → .plural ∈ ns.values

/-- Greater paucal implies paucal ([harbour-2014] Table 1: GR.PC → PC). -/
def GreaterPaucalImpliesPaucal (ns : System) : Prop :=
  .greaterPaucal ∈ ns.values → .paucal ∈ ns.values

/-- Greater plural implies plural or augmented ([harbour-2014] Table 1:
    GR.PL → PL/AUG) — disjunctive, so it is a `System` predicate, not a
    markedness-order edge. -/
def GreaterPluralImpliesPluralOrAugmented (ns : System) : Prop :=
  .greaterPlural ∈ ns.values → .plural ∈ ns.values ∨ .augmented ∈ ns.values

/-- Plural implies singular or minimal ([harbour-2014] Table 1:
    PL → SG/MIN). Plural requires a "base" value — either singular
    (from `[±atomic]`) or minimal (from `[±minimal]`). -/
def PluralImpliesSingularOrMinimal (ns : System) : Prop :=
  .plural ∈ ns.values → .singular ∈ ns.values ∨ .minimal ∈ ns.values

/-- Augmented implies minimal ([harbour-2014] Table 1: AUG → MIN). -/
def AugmentedImpliesMinimal (ns : System) : Prop :=
  .augmented ∈ ns.values → .minimal ∈ ns.values

/-- Unit augmented implies augmented ([harbour-2014] Table 1:
    U.AUG → AUG). -/
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

/-- A well-formed number system satisfies all implicational universals
    ([harbour-2014] Table 1). Any Fragment-recorded system discharges this
    by `decide`. -/
def WellFormed (ns : System) : Prop :=
  ns.TrialImpliesDual ∧ ns.DualImpliesSingular ∧ ns.SingularImpliesPlural ∧
  ns.DualImpliesPlural ∧ ns.PluralImpliesSingularOrMinimal ∧
  ns.MinimalImpliesAugmentedOrPlural ∧ ns.AugmentedImpliesMinimal ∧
  ns.UnitAugImpliesAugmented ∧ ns.PaucalImpliesPlural ∧
  ns.GreaterPaucalImpliesPaucal ∧ ns.GreaterPluralImpliesPluralOrAugmented

instance (ns : System) : Decidable ns.WellFormed := by
  unfold WellFormed; infer_instance

/-- The [cysouw-2009] stage a system realizes, by value count:
    0–1 values → N1 (undifferentiated), 2 → N2 (basic opposition),
    3 → N3 (restricted group), 4+ → N4 (paucal additionally). -/
def toStage (ns : System) : Stage :=
  match ns.size with
  | 0 | 1 => .N1
  | 2 => .N2
  | 3 => .N3
  | _ => .N4

end System

end Number
