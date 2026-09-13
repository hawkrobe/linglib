import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Verb–complementizer compatibility

The hom between the `Verb` and `Complementizer` entry APIs: which
clause-typers a predicate takes. A clausal position and a clause-typer
each record a bundle of partial axis values (`Complement.Axes`, the
[noonan-2007] coding and the illocutionary force) in the flat order, and
a position takes a typer when the two bundles unify (`Compat`) with some
axis actually agreeing (a non-`⊥` meet). One relation, lifted twice: a
frame or verb takes a typer when some position or frame does. All
decidable. Non-clausal positions record no axes, so positive evidence
already excludes them; the subject-requirement axis
(`Complement.Position.embeddedSubject?`) is object-side and not matched:
typers record no subject requirement.

## Main definitions

- `Complementizer.axes` — the typer's bundle
- `Complement.Position.Takes`, `Frame.Takes`, `Verb.takes` — the
  relation and its lifts
- `Verb.typers` — the typers of a verb within an inventory

## Main results

- `Complement.Position.takes_iff` — the relation axis by axis
- `Complement.Position.not_takes_of_blank`,
  `Complement.Position.blank_not_takes` — matching needs positive
  evidence on both sides
- `Frame.smallClause_not_takes` — small clauses take no typer
- `Frame.finiteClause_takes` — the positive witness
- `Frame.Takes.mono` — monotone under frame extension

Consistency checks against Fragment data live in Studies
(e.g. `Bondarenko2022.hanaxa_typers`).
-/

/-- The axes a clause-typer records. -/
def Complementizer.axes (z : Complementizer) : Complement.Axes
  | .coding => z.coding
  | .force => z.force

namespace Complement.Position

variable {p : Complement.Position} {z : Complementizer}

/-- The position takes clause-typer `z`: the two bundles unify and some
    axis agrees. Matching needs positive evidence, so a typer or position
    recording nothing — in particular any non-clausal position — takes
    nothing. -/
def Takes (p : Complement.Position) (z : Complementizer) : Prop :=
  Compat p.axes z.axes ∧ p.axes ⊓ z.axes ≠ ⊥

/-- The relation axis by axis: every axis compatible, some axis agreeing. -/
theorem takes_iff :
    p.Takes z ↔
      (∀ a, Compat (p.axes a) (z.axes a)) ∧ ∃ a, p.axes a ⊓ z.axes a ≠ ⊥ := by
  rw [Takes, compat_pi_iff]
  simp only [ne_eq, funext_iff, Pi.inf_apply, Pi.bot_apply, not_forall]

instance : Decidable (p.Takes z) := decidable_of_iff _ takes_iff.symm

/-- A typer recording neither axis takes nothing. -/
theorem not_takes_of_blank (hc : z.coding = none) (hf : z.force = none) : ¬ p.Takes z := by
  rw [takes_iff]
  rintro ⟨-, a, ha⟩
  cases a <;> simp [Complementizer.axes, hc, hf, Flat.none_eq_bot] at ha

/-- A position recording neither axis takes nothing: matching needs
    positive evidence. -/
theorem blank_not_takes {e : Option Clause.EmbeddedSubject} :
    ¬ (Complement.Position.clausal none none e).Takes z := by
  rw [takes_iff]
  rintro ⟨-, a, ha⟩
  cases a <;> simp [axes, coding?, force?, Flat.none_eq_bot] at ha

end Complement.Position

/-- The frame takes `z`: some position does. -/
def Frame.Takes (fr : Frame) (z : Complementizer) : Prop :=
  ∃ p ∈ fr, p.Takes z

instance (fr : Frame) (z : Complementizer) : Decidable (fr.Takes z) :=
  inferInstanceAs (Decidable (∃ p ∈ fr, _))

/-- Taking is monotone under frame extension. -/
theorem Frame.Takes.mono {fr fr' : Frame} {z : Complementizer}
    (h : fr.Takes z) (hsub : fr ⊆ fr') : fr'.Takes z :=
  let ⟨p, hp, ht⟩ := h
  ⟨p, hsub hp, ht⟩

/-- Small clauses take no clause-typer. -/
theorem Frame.smallClause_not_takes (z : Complementizer) :
    ¬ Frame.smallClause.Takes z := by
  rintro ⟨p, hp, ht⟩
  rw [Frame.smallClause, List.mem_singleton] at hp
  subst hp
  exact Complement.Position.blank_not_takes ht

/-- An indicative typer with declarative or unrecorded force takes the
    finite-clause frame. -/
theorem Frame.finiteClause_takes {z : Complementizer}
    (hc : z.coding = some .indicative)
    (hf : z.force = none ∨ z.force = some .declarative) :
    Frame.finiteClause.Takes z := by
  refine ⟨_, List.mem_singleton_self _,
    Complement.Position.takes_iff.mpr ⟨λ a => ?_, .coding, ?_⟩⟩
  · rcases hf with hf | hf <;> cases a <;>
      simp only [Complement.Position.axes, Complementizer.axes, Complement.Position.coding?,
        Complement.Position.force?, hc, hf, Flat.none_eq_bot] <;>
      first | exact compat_self _ | exact compat_bot _
  · simp [Complement.Position.axes, Complementizer.axes, Complement.Position.coding?, hc,
      Flat.some_eq_coe]

/-- The verb takes `z`: some frame does. -/
def Verb.takes (v : Verb) (z : Complementizer) : Prop :=
  ∃ fr ∈ v.frames, fr.Takes z

instance (v : Verb) (z : Complementizer) : Decidable (v.takes z) :=
  inferInstanceAs (Decidable (∃ fr ∈ v.frames, _))

/-- The typers of `v` within a language's complementizer inventory. -/
def Verb.typers (v : Verb) (inv : List Complementizer) :
    List Complementizer :=
  inv.filter (λ c => decide (v.takes c))
