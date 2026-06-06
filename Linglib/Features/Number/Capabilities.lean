import Linglib.Core.Order.Flat
import Linglib.Features.Number.Basic

/-!
# HasNumber — the number-bearing capability
[corbett-2000]

The typeclass mixin for carriers that bear grammatical number — the number
axis of the capability tower over lexical carriers (cf. `Proform`/`Bound`/
`Clusive` in `Syntax/Pronoun/Capabilities.lean`). A consumer (agreement
checker, resolution, semantics) requires `[HasNumber α]` and works over any
representation: a UD feature bundle, a `Word`, a `Pronoun`, an agreement
paradigm cell.

The accessor is `Option`-valued because underspecification is the
typologically normal case ([corbett-2000]): a carrier with no number marking
is a wildcard for agreement, not a default singular.

Instances live with their carriers (mathlib-style): `UD.MorphFeatures` here
(its type is below this file); `Word` in `Morphology/Word.lean`; `Pronoun`/
`PersonalPronoun` in `Syntax/Pronoun/Capabilities.lean`; paradigm `Cell` in
`Syntax/Agreement/Paradigm.lean`.

Named `HasNumber`, not `Numbered`: the bare name is taken by the carrier
type itself, the situation where Lean retains the `Has` prefix
(`HasEquiv`, `HasSubset`, `HasQuotient`), and the scheme scales across the
φ-inventory (`HasPerson`, `HasGender`) where adjectival forms do not.

The Minimalist probe/goal inventory (`Minimalist.PhiFeature.number`) is the
other number-bearing route in the library; it carries `UD.Number` and
relates to this one by `Number.fromUD`.
-/

set_option autoImplicit false

/-- A carrier that bears grammatical number. `none` = unmarked or
    underspecified (a wildcard for agreement, not a default value). -/
class HasNumber (α : Type*) where
  /-- The canonical number value the carrier bears. -/
  numberOf : α → Option Number

/-- A UD morphology bundle bears the number its `number` tag ingests
    (`Number.fromUD`); tags with no analytical equivalent (`Inv`/`Coll`/
    `Count`) leave the carrier unvalued. -/
instance : HasNumber UD.MorphFeatures :=
  ⟨fun f => f.number.bind Number.fromUD⟩

namespace HasNumber

variable {α : Type*} {β : Type*} [HasNumber α] [HasNumber β]

/-- Number compatibility between two (possibly heterogeneous) carriers:
    the slot values are compatible in the flat information order (`Compat`)
    — valued numbers must coincide; an unvalued carrier is a wildcard.
    The number axis of φ-agreement (`UD.MorphFeatures.compatible`). -/
def Compatible (a : α) (b : β) : Prop :=
  Compat (α := Flat Number) (numberOf a) (numberOf b)

instance (a : α) (b : β) : Decidable (Compatible a b) := by
  unfold Compatible; infer_instance

theorem compatible_comm {a : α} {b : β} (h : Compatible a b) :
    Compatible b a :=
  h.symm

/-- An unvalued carrier is compatible with everything. -/
theorem compatible_of_none {a : α} (h : numberOf a = none) (b : β) :
    Compatible a b := by
  unfold Compatible
  rw [h]
  exact bot_compat _

end HasNumber

/-- φ-compatibility entails number compatibility: the `HasNumber` mixin never
    diverges from the unification-based agreement engine
    (`UD.MorphFeatures.compatible`). -/
theorem UD.MorphFeatures.compatible_hasNumber {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasNumber.Compatible f1 f2 := by
  unfold HasNumber.Compatible
  rw [Flat.compat_iff]
  intro na ha nb hb
  have hn : (f1.number.isNone || f2.number.isNone || f1.number == f2.number)
      = true := by
    unfold UD.MorphFeatures.compatible at h
    simp only [Bool.and_eq_true] at h
    tauto
  simp only [HasNumber.numberOf] at ha hb
  rcases h1 : f1.number with _ | u1
  · rw [h1] at ha
    exact absurd ha (Option.not_mem_none _)
  · rcases h2 : f2.number with _ | u2
    · rw [h2] at hb
      exact absurd hb (Option.not_mem_none _)
    · rw [h1] at ha
      rw [h2] at hb
      rw [h1, h2] at hn
      simp only [Option.isNone_some, Bool.false_or, beq_iff_eq,
                 Option.some.injEq] at hn
      subst hn
      simp only [Option.bind] at ha hb
      rw [ha] at hb
      exact Option.some.inj hb
