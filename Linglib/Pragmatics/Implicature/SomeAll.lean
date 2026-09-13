import Mathlib.Tactic.DeriveFintype

/-!
# The canonical *some*/*all* world model

The minimal scenario type for evaluating the *some*/*all* scalar
contrast ([horn-1972]): three worlds covering "no entity has the
property" / "at least one but not all do" / "all do", with the literal
*some*/*all* meanings and the canonical implicature as decidable
predicates.

Consumed as a model input by the implicature study files
([geurts-pouscoulous-2009], [chemla-spector-2011]) and as a component
of richer scenario types (belief worlds, picture cells).

## Main declarations

* `SomeAllWorld` — the 3-world scenario type.
* `SomeAllWorld.atLeastOne` / `SomeAllWorld.universal` — literal *some*
  and *all* meanings.
* `SomeAllWorld.notUniversal` — the canonical scalar implicature of
  *some*, defined as the negation of `universal`.
* `SomeAllWorld.everySome`, `SomeAllWorld.everyAll`,
  `SomeAllWorld.everySomeNotAll` — *some* in the scope of a universal
  over a domain of individuals: the literal reading, its stronger
  alternative, and the reading with the implicature computed locally.
-/

/-- The minimal scenario type for evaluating the *some*/*all* scalar
contrast. Three worlds, parameterized by an implicit entity-set whose
property-holders are being counted: zero (`none`), at least one but not
all (`someNotAll`), or all (`all`). -/
inductive SomeAllWorld where
  | none
  | someNotAll
  | all
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace SomeAllWorld

/-- Literal *some* meaning: at least one entity has the property. -/
def atLeastOne : SomeAllWorld → Prop
  | .none => False
  | _ => True

/-- Literal *all* meaning: every entity has the property. -/
def universal : SomeAllWorld → Prop
  | .all => True
  | _ => False

/-- The canonical scalar implicature of *some*: not all. Defined as the
negation of `universal`. -/
def notUniversal (w : SomeAllWorld) : Prop := ¬ universal w

instance : DecidablePred atLeastOne
  | .none => isFalse not_false
  | .someNotAll => isTrue trivial
  | .all => isTrue trivial

instance : DecidablePred universal
  | .none => isFalse not_false
  | .someNotAll => isFalse not_false
  | .all => isTrue trivial

instance (w : SomeAllWorld) : Decidable (notUniversal w) :=
  inferInstanceAs (Decidable (¬ universal w))

/-- *all* asymmetrically entails *some*: this is the structural source of
the *some*/*all* scalar contrast. -/
theorem universal_imp_atLeastOne {w : SomeAllWorld} (h : universal w) :
    atLeastOne w := by
  cases w <;> simp_all [universal, atLeastOne]

/-- The SI of *some* is exactly the complement of *all*. -/
theorem notUniversal_iff_not_universal {w : SomeAllWorld} :
    notUniversal w ↔ ¬ universal w := Iff.rfl

/-- The middle world is the one verifying *some* and falsifying *all*. -/
theorem eq_someNotAll_iff {w : SomeAllWorld} :
    w = .someNotAll ↔ atLeastOne w ∧ ¬ universal w := by
  cases w <;> simp [atLeastOne, universal]

/-! ### Under a universal quantifier

*Every N V some* over a domain `ι` assigns each individual a `SomeAllWorld`. The readings the
embedded-implicature literature crosses are the literal one, the literal one with the stronger
alternative *every N V all* denied, and the one with the implicature computed in the scope of
the universal, *every N V some but not all*. -/

section Universal

variable {ι : Type*} (m : ι → SomeAllWorld)

/-- *Every N V some*: every individual has the property for at least one entity. -/
def everySome : Prop := ∀ i, atLeastOne (m i)

/-- *Every N V all*: the stronger alternative of `everySome`. -/
def everyAll : Prop := ∀ i, universal (m i)

/-- *Every N V some but not all*: the implicature computed in the scope of the universal. -/
def everySomeNotAll : Prop := ∀ i, m i = .someNotAll

instance [Fintype ι] : Decidable (everySome m) := inferInstanceAs (Decidable (∀ _, _))

instance [Fintype ι] : Decidable (everyAll m) := inferInstanceAs (Decidable (∀ _, _))

instance [Fintype ι] : Decidable (everySomeNotAll m) := inferInstanceAs (Decidable (∀ _, _))

variable {m}

theorem everyAll.everySome (h : everyAll m) : everySome m :=
  λ i => universal_imp_atLeastOne (h i)

/-- The local reading is the literal one with *all* denied of every individual. -/
theorem everySomeNotAll_iff : everySomeNotAll m ↔ everySome m ∧ ∀ i, ¬ universal (m i) := by
  simp only [everySomeNotAll, everySome, eq_someNotAll_iff, forall_and]

theorem everySomeNotAll.everySome (h : everySomeNotAll m) : everySome m :=
  (everySomeNotAll_iff.1 h).1

/-- *No N V all* entails *not every N V all* on a nonempty domain. -/
theorem not_everyAll_of_forall_not [Nonempty ι] (h : ∀ i, ¬ universal (m i)) : ¬ everyAll m :=
  λ h' => h (Classical.arbitrary ι) (h' _)

theorem everySomeNotAll.not_everyAll [Nonempty ι] (h : everySomeNotAll m) : ¬ everyAll m :=
  not_everyAll_of_forall_not (everySomeNotAll_iff.1 h).2

end Universal

end SomeAllWorld
