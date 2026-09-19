import Linglib.Fragments.Yoruba.Relativization
import Linglib.Semantics.Focus.Marking
import Linglib.Syntax.Category.Particle.Basic
import Linglib.Syntax.Reflex

/-!
# Yoruba focus

Yorùbá focuses a constituent either in place, with no marking of any kind, or by fronting it
to the beginning of the clause, where a focus particle accompanies it: asked *what did Adé
buy?*, a speaker answers *Adé ra bàtà* as it stands or *Bàtà ni Adé rà* 'Adé bought A SHOE'.
A focused subject must front, and the vacated subject position is then filled by the
high-tone *ó*: *Adé ni ó rà bàtà* 'ADÉ bought a shoe', never *Adé rà bàtà* as an answer to
*who bought a shoe?*. A fronted object or adjunct leaves its position empty, as under
relativization. The dialects differ in where the particle stands. Standard (Ọ̀yọ́) Yorùbá
places *ni* immediately after the fronted constituent, as in Awobuluyi's *Omi mímu ni mo lọ
pọn* 'It was drinking water that I went to fetch'; the south-eastern dialect Ìkálẹ̀ places
*rín* at the end of the clause whatever has been fronted, *Adé ó jẹ ejíjẹ nẹ̀ rín* 'ADÉ ate
the food' and *Tolú Adé rí rín* 'Adé saw TOLÚ', against in-place *Adé rí Tolú* with no
particle. Aremu describes the standard dialect in the dissertation and Ìkálẹ̀ in the chapter.

## Main declarations

* `Yoruba.Dialect`, `Yoruba.Dialect.focusParticle`: the two dialects and each one's particle,
  a `Particle` positioned after its host or clause-finally.
* `Yoruba.Focused`: the focusable constituents; `WithTop Focused` hosts the reflexes, the
  clause on top of them.
* `Yoruba.FocusConfig`, `Yoruba.FocusConfig.Licensed`, `Yoruba.FocusConfig.reflexes`: a
  dialect, a focused constituent and a strategy; subject focus is only ex situ; the overt
  reflexes of a configuration in the `Reflex` vocabulary.
* `Yoruba.piedPipes_iff`: the particle is hosted above its focus exactly when it is
  clause-final, so Ìkálẹ̀ marks focus in the pied-piping configuration and the standard dialect
  on the focus itself.
* `Yoruba.refutes_perceptibility`: in-place focus has no reflex, the Yorùbá side of the
  Tangale and Hausa counterexamples to universal overt focus marking.
* `Yoruba.npRel_eq_relative`: a fronted focus vacates its position as relativization does.

## References

* [aremu-2025a]
* [aremu-2025b]
* [awobuluyi-1978]
-/

namespace Yoruba

open Reflex

/-! ### Dialects and their particles -/

/-- The two dialects whose focus marking is recorded here, the standard (Ọ̀yọ́) dialect and
the south-eastern dialect Ìkálẹ̀. -/
inductive Dialect where
  | standard
  | ikale
  deriving DecidableEq, Repr, Fintype

/-- Standard Yorùbá *ni*, immediately after the fronted constituent. -/
def ni : Particle := { form := "ni", position := some .postHost }

/-- Ìkálẹ̀ *rín*, at the end of the clause. -/
def rin : Particle := { form := "rín", position := some .clauseFinal }

/-- Each dialect's focus particle. -/
def Dialect.focusParticle : Dialect → Particle
  | .standard => ni
  | .ikale => rin

/-- The high-tone *ó* filling the subject position of a clause whose subject has been fronted. -/
def o : Morphology.Morph := .free "ó"

/-! ### Focusable constituents and hosts -/

/-- A focus construction fronts the subject, the object, or an adjunct. -/
inductive Focused where
  | subject
  | object
  | adjunct
  deriving DecidableEq, Repr, Fintype

/-- Distinct focusable constituents contain neither one the other, so the reflex hosts
`WithTop Focused` are the focusable constituents with the clause containing all of them. -/
instance : PartialOrder Focused where
  le := (· = ·)
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

instance : DecidableLE Focused := fun a b ↦ inferInstanceAs (Decidable (a = b))

instance : DecidableLT Focused := fun a b ↦ inferInstanceAs (Decidable (a = b ∧ ¬ b = a))

/-- The relativizable position a focused constituent occupies. -/
def Focused.relativePosition : Focused → Option RelativeClause.Position
  | .subject => some .subject
  | .object => some .directObject
  | .adjunct => none

/-- A fronted subject leaves the high-tone *ó* in its position; a fronted object or adjunct
leaves it empty. -/
def Focused.npRel : Focused → RelativeClause.NPRel
  | .subject => .resumptive
  | .object | .adjunct => .gap

/-- A clause-final particle is hosted by the clause, any other particle by the fronted
constituent it accompanies. -/
def particleHost (p : Particle) (f : Focused) : WithTop Focused :=
  if p.position = some .clauseFinal then ⊤ else f

/-! ### Configurations and their reflexes -/

/-- A focus configuration pairs a dialect and a focused constituent with whether it stays in
place or fronts. -/
structure FocusConfig where
  dialect : Dialect
  focused : Focused
  strategy : Focus.Strategy
  deriving DecidableEq, Repr

namespace FocusConfig

variable (c : FocusConfig)

/-- A focused subject fronts; in place it is no answer to *who bought a shoe?*. -/
def Licensed : Prop := c.focused = .subject → c.strategy = .exSitu

instance : Decidable c.Licensed := inferInstanceAs (Decidable (_ → _))

/-- The overt reflexes of a configuration. In place there are none; fronted, they are the
displaced constituent, the dialect's particle at its host, and *ó* in a vacated subject
position. -/
def reflexes : Finset (Reflex (WithTop Focused)) :=
  match c.strategy with
  | .inSitu => ∅
  | .exSitu =>
    {.displacement ↑c.focused,
      .morpheme (particleHost c.dialect.focusParticle c.focused)
        [.free c.dialect.focusParticle.form]}
      ∪ if c.focused.npRel = .resumptive then {.morpheme ↑c.focused [o]} else ∅

end FocusConfig

/-- In place, a focus has no reflex in any channel, so *Adé ra bàtà* answers *what did Adé
buy?* with neither particle nor prominence. -/
theorem reflexes_inSitu (d : Dialect) (f : Focused) :
    (FocusConfig.mk d f .inSitu).reflexes = ∅ := rfl

/-- A subject in place is not focused, so *Adé rà bàtà* does not answer *who bought a
shoe?*. -/
theorem not_licensed_inSitu_subject (d : Dialect) :
    ¬ (FocusConfig.mk d .subject .inSitu).Licensed :=
  fun h ↦ nomatch h rfl

/-- In *Adé ni ó rà bàtà* 'ADÉ bought a shoe' the subject fronts, *ni* follows it and *ó*
fills its position. -/
theorem reflexes_standard_subject :
    (FocusConfig.mk .standard .subject .exSitu).reflexes =
      {.displacement ↑Focused.subject, .morpheme ↑Focused.subject [.free ni.form],
        .morpheme ↑Focused.subject [o]} := by
  decide

/-- In *Adé ó jẹ ejíjẹ nẹ̀ rín* 'ADÉ ate the food' the subject fronts, *ó* fills its
position and *rín* closes the clause. -/
theorem reflexes_ikale_subject :
    (FocusConfig.mk .ikale .subject .exSitu).reflexes =
      {.displacement ↑Focused.subject, .morpheme ⊤ [.free rin.form],
        .morpheme ↑Focused.subject [o]} := by
  decide

/-- In *Tolú Adé rí rín* 'Adé saw TOLÚ' the fronted object leaves its position empty. -/
theorem reflexes_ikale_object :
    (FocusConfig.mk .ikale .object .exSitu).reflexes =
      {.displacement ↑Focused.object, .morpheme ⊤ [.free rin.form]} := by
  decide

/-- Yorùbá joins Tangale and Hausa against the claim that every focus receives an overt
reflex: object focus in place, licensed, has none. -/
theorem refutes_perceptibility : ¬ ∀ c : FocusConfig, c.Licensed → c.reflexes.Nonempty :=
  fun h ↦ Finset.not_nonempty_empty (h ⟨.standard, .object, .inSitu⟩ nofun)

/-! ### Where the particle sits -/

/-- The particle is hosted by a constituent properly containing the focus exactly when the
focus is fronted and the dialect's particle is clause-final: Ìkálẹ̀ marks focus in the
pied-piping configuration, the standard dialect on the focus itself. -/
theorem piedPipes_iff (c : FocusConfig) :
    PiedPipes c.reflexes ↑c.focused ↔
      c.strategy = .exSitu ∧ c.dialect.focusParticle.position = some .clauseFinal := by
  obtain ⟨d, f, s⟩ := c
  cases d <;> cases f <;> cases s <;> decide

/-- Whatever Ìkálẹ̀ fronts, *rín* is hosted by the clause above it. -/
theorem ikale_piedPipes (f : Focused) :
    PiedPipes (FocusConfig.mk .ikale f .exSitu).reflexes ↑f :=
  (piedPipes_iff _).2 ⟨rfl, rfl⟩

/-- Every reflex of a standard-dialect focus sits on the fronted constituent itself. -/
theorem standard_exactlyTargets (f : Focused) :
    ExactlyTargets (FocusConfig.mk .standard f .exSitu).reflexes ↑f := by
  cases f <;> decide

/-- A fronted focus vacates its position as relativization does, the subject resumed by *ó*
and the object left empty under both constructions. -/
theorem npRel_eq_relative :
    ∀ f : Focused, ∀ m ∈ relMarkers, ∀ p ∈ m.positions,
      f.relativePosition = some p → f.npRel = m.npRel := by
  decide

end Yoruba
