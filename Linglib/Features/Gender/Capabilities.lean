import Linglib.Features.Gender.Basic

/-!
# HasGender — the gender-bearing capability
[corbett-1991]

The typeclass mixin for carriers that bear grammatical gender — the gender
axis of the capability tower over lexical carriers, the analogue of
`HasNumber` (`Features/Number/Capabilities.lean`) and `HasPerson`
(`Features/Person/Capabilities.lean`). A consumer (agreement checker,
resolution, semantics) requires `[HasGender α]` and works over any
representation: a UD feature bundle, a `Word`, a `Pronoun`.

The accessor is **label-valued** (`Option Gender`, the comparative-concept
vocabulary), because the mixin is the cross-linguistic interface:
language-particular fine-grained access goes through the language's
`Gender.System` carrier, not through this class. It is `Option`-valued
because underspecification is the typologically normal case: a carrier with
no gender marking is a wildcard for agreement, and most languages have no
gender at all ([corbett-1991]).

Instances live with their carriers (mathlib-style): `UD.MorphFeatures` here
(its type is upstream of this file); downstream carriers (`Word`, `Pronoun`)
declare theirs where they are defined.
-/

set_option autoImplicit false

/-- A carrier that bears grammatical gender. `none` = unmarked or
    underspecified (a wildcard for agreement, not a default value). -/
class HasGender (α : Type*) where
  /-- The comparative gender label the carrier bears. -/
  genderOf : α → Option Gender

/-- A UD morphology bundle bears the label its `gender` tag ingests
    (`Gender.fromUD`, total on UD genders). -/
instance : HasGender UD.MorphFeatures :=
  ⟨fun f => f.gender.map Gender.fromUD⟩

namespace HasGender

variable {α : Type*} {β : Type*} [HasGender α] [HasGender β]

/-- Gender compatibility between two (possibly heterogeneous) carriers:
    valued genders must coincide; an unvalued carrier is a wildcard.
    The gender axis of φ-agreement (`UD.MorphFeatures.compatible`). -/
def Compatible (a : α) (b : β) : Prop :=
  ∀ ga ∈ genderOf a, ∀ gb ∈ genderOf b, ga = gb

instance (a : α) (b : β) : Decidable (Compatible a b) := by
  unfold Compatible; infer_instance

theorem compatible_comm {a : α} {b : β} (h : Compatible a b) :
    Compatible b a :=
  fun gb hb ga ha => (h ga ha gb hb).symm

/-- An unvalued carrier is compatible with everything. -/
theorem compatible_of_none {a : α} (h : genderOf a = none) (b : β) :
    Compatible a b := by
  intro ga ha
  rw [h] at ha
  exact absurd ha (Option.not_mem_none _)

end HasGender

/-- φ-compatibility entails gender compatibility: the `HasGender` mixin never
    diverges from the unification-based agreement engine
    (`UD.MorphFeatures.compatible`). -/
theorem UD.MorphFeatures.compatible_hasGender {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasGender.Compatible f1 f2 := by
  intro ga ha gb hb
  have hg : (f1.gender.isNone || f2.gender.isNone || f1.gender == f2.gender)
      = true := by
    unfold UD.MorphFeatures.compatible at h
    simp only [Bool.and_eq_true] at h
    tauto
  simp only [HasGender.genderOf, Option.mem_def] at ha hb
  rcases h1 : f1.gender with _ | u1
  · rw [h1] at ha
    exact absurd ha (Option.not_mem_none _)
  · rcases h2 : f2.gender with _ | u2
    · rw [h2] at hb
      exact absurd hb (Option.not_mem_none _)
    · rw [h1] at ha
      rw [h2] at hb
      rw [h1, h2] at hg
      simp only [Option.isNone_some, Bool.false_or, beq_iff_eq,
                 Option.some.injEq] at hg
      subst hg
      have ha' : Gender.fromUD u1 = ga := Option.some.inj ha
      have hb' : Gender.fromUD u1 = gb := Option.some.inj hb
      rw [← ha', ← hb']
