import Linglib.Semantics.Plurality.MassCount
import Linglib.Syntax.Category.Determiner.Basic

/-!
# The Nominal Mapping Parameter

This file defines the Nominal Mapping Parameter of [chierchia-1998], which sets what a
language's nouns can denote: kinds, so that they are arguments ([+arg]), or properties, so that
they are predicates ([+pred]), or either. A setting is the set of denotation types nouns take.
The setting and the language's determiners then decide which bare nominals can be arguments. A
covert type shift is blocked when a determiner lexicalizes it, the Blocking Principle, and kind
formation ∩ is defined only for mass nouns and plurals, so a [+arg, +pred] language with
articles admits bare plurals and bare mass nouns but no bare singular count nouns, while a
[+arg, −pred] language admits every bare nominal and a [−arg, +pred] language none.

## Main definitions

* `NominalMapping` — a setting of the parameter, with the three attested settings `argOnly`,
  `argAndPred` and `predOnly`, and `CanDenoteKind` and `CanDenoteProperty`
* `CovertShift`, `Determiner.Inventory.Blocks` — the covert type shifts and the Blocking
  Principle
* `DownDefined`, `NominalMapping.LicensesBare` — where ∩ is defined, and which bare nominals a
  language admits as arguments

## Main results

* `NominalMapping.licensesBare_iff_downDefined` — with ι and ∃ blocked, a [+arg, +pred]
  language admits exactly the bare nominals ∩ is defined for
* `NominalMapping.exists_licensesBare_iff` — a language admits some bare argument iff it is
  [+arg]

## References

* [chierchia-1998]
* [dayal-2004]
* [moroney-2021]
-/

namespace Genericity

/-- What a noun denotes: a kind, of type e, or a property, of type ⟨e,t⟩. -/
inductive NominalDenotation where
  | kind
  | property
  deriving DecidableEq, Repr, Fintype

/-- A setting of the Nominal Mapping Parameter: the denotation types a language's nouns can
take. The language is [+arg] when `.kind` is in the setting and [+pred] when `.property` is; the
empty setting, [−arg, −pred], leaves nouns nothing to denote and is excluded by the paper. -/
def NominalMapping := Finset NominalDenotation

namespace NominalMapping

instance : Membership NominalDenotation NominalMapping :=
  inferInstanceAs (Membership NominalDenotation (Finset NominalDenotation))

instance : DecidableEq NominalMapping := inferInstanceAs (DecidableEq (Finset NominalDenotation))

instance (d : NominalDenotation) (m : NominalMapping) : Decidable (d ∈ m) :=
  Finset.decidableMem d m

/-- [+arg, −pred]: nouns denote kinds (Mandarin, Japanese). -/
def argOnly : NominalMapping := ({.kind} : Finset NominalDenotation)

/-- [+arg, +pred]: nouns denote kinds or properties (English, Germanic). -/
def argAndPred : NominalMapping := ({.kind, .property} : Finset NominalDenotation)

/-- [−arg, +pred]: nouns denote properties (Romance, Greek). -/
def predOnly : NominalMapping := ({.property} : Finset NominalDenotation)

@[simp] theorem mem_argOnly {d : NominalDenotation} : d ∈ argOnly ↔ d = .kind := by
  cases d <;> decide

@[simp] theorem mem_argAndPred {d : NominalDenotation} : d ∈ argAndPred := by cases d <;> decide

@[simp] theorem mem_predOnly {d : NominalDenotation} : d ∈ predOnly ↔ d = .property := by
  cases d <;> decide

/-- A nominal can denote a kind outright in a [+arg] language, and otherwise under an overt
determiner. -/
def CanDenoteKind (m : NominalMapping) (hasD : Prop) : Prop := .kind ∈ m ∨ hasD

instance (m : NominalMapping) (hasD : Prop) [Decidable hasD] :
    Decidable (m.CanDenoteKind hasD) := by
  unfold CanDenoteKind; infer_instance

/-- A nominal can denote a property in a [+pred] language. -/
def CanDenoteProperty (m : NominalMapping) : Prop := .property ∈ m

instance (m : NominalMapping) : Decidable m.CanDenoteProperty := by
  unfold CanDenoteProperty; infer_instance

end NominalMapping

/-! ### Covert type shifts -/

/-- The covert type shifts: kind formation ∩, the definite ι and the existential ∃ of
[chierchia-1998], and the anaphoric definite ι^x of [dayal-2004] and [moroney-2021]. -/
inductive CovertShift where
  | down
  | iota
  | iotaAnaphoric
  | exists
  deriving DecidableEq, Repr, Fintype

/-- Kind formation is defined for a mass noun and for a plural, whose instances form a
plurality; a singular count property cannot supply the plurality of instances a kind needs. -/
def DownDefined (nt : MassCount) (num : Number) : Prop := nt = .mass ∨ num = .plural

instance (nt : MassCount) (num : Number) : Decidable (DownDefined nt num) := by
  unfold DownDefined; infer_instance

end Genericity

/-! ### The Blocking Principle -/

namespace Determiner.Inventory

open Genericity (CovertShift)

/-- The Blocking Principle of [chierchia-1998]: a covert shift is blocked when a determiner of
the inventory lexicalizes it. A definite article is ι and an indefinite article ∃; a determiner
that obligatorily expones anaphoric definiteness is ι^x ([moroney-2021]); no determiner is ∩. -/
def Blocks (ds : Inventory) : CovertShift → Prop
  | .down => False
  | .iota => ∃ e ∈ ds, e.kind = .article .definite
  | .iotaAnaphoric => ds.Marks .familiarity
  | .exists => ∃ e ∈ ds, e.kind = .article .indefinite

instance (ds : Inventory) : DecidablePred ds.Blocks := λ τ => by
  cases τ <;> unfold Blocks <;> infer_instance

/-- Kind formation is never blocked. -/
theorem not_blocks_down (ds : Inventory) : ¬ ds.Blocks .down := nofun

/-- ∃ is blocked exactly when the inventory realizes indefinites. -/
theorem blocks_exists_iff (ds : Inventory) : ds.Blocks .exists ↔ ds.Realizes .indefinite :=
  Iff.rfl

/-- ι^x is blocked exactly when the inventory realizes anaphoric definites. -/
theorem blocks_iotaAnaphoric_iff (ds : Inventory) :
    ds.Blocks .iotaAnaphoric ↔ ds.Realizes .anaphoric :=
  Iff.rfl

end Determiner.Inventory

namespace Genericity.NominalMapping

/-! ### Bare arguments -/

/-- A language with the setting `m` and the determiners `ds` admits a bare nominal of
countability `nt` and number `num` as an argument: it must be [+arg], and if also [+pred], so
that count nouns are predicates, the nominal needs ∩ to be defined for it or ι or ∃ unblocked. -/
def LicensesBare (m : NominalMapping) (ds : Determiner.Inventory) (nt : MassCount)
    (num : Number) : Prop :=
  .kind ∈ m ∧ (.property ∉ m ∨ DownDefined nt num ∨ ¬ ds.Blocks .iota ∨ ¬ ds.Blocks .exists)

instance (m : NominalMapping) (ds : Determiner.Inventory) (nt : MassCount) (num : Number) :
    Decidable (m.LicensesBare ds nt num) := by
  unfold LicensesBare; infer_instance

variable {ds : Determiner.Inventory} {nt : MassCount} {num : Number}

/-- With ι and ∃ blocked, a [+arg, +pred] language admits exactly the bare nominals ∩ is
defined for: plurals and mass nouns, not singular count nouns. -/
theorem licensesBare_iff_downDefined (hι : ds.Blocks .iota) (hex : ds.Blocks .exists) :
    argAndPred.LicensesBare ds nt num ↔ DownDefined nt num := by
  simp [LicensesBare, hι, hex]

/-- A [+arg, +pred] language admits bare singular count nouns iff it lacks a definite or an
indefinite article. -/
theorem licensesBare_singular_iff :
    argAndPred.LicensesBare ds .count .singular ↔ ¬ ds.Blocks .iota ∨ ¬ ds.Blocks .exists := by
  simp [LicensesBare, DownDefined]

/-- A language admits some bare argument iff it is [+arg]. -/
theorem exists_licensesBare_iff (m : NominalMapping) :
    (∃ nt num, m.LicensesBare ds nt num) ↔ .kind ∈ m :=
  ⟨λ ⟨_, _, h, _⟩ => h, λ h => ⟨.mass, .singular, h, .inr (.inl (.inl rfl))⟩⟩

end Genericity.NominalMapping
