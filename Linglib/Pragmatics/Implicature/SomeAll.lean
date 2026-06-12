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

end SomeAllWorld
