import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Verb–complementizer compatibility

The hom between the `Verb` and `Complementizer` entry APIs: which
clause-typers a predicate takes. A complement position and a clause-typer
each record a bundle of partial axis values (`Frame.Position.Axes`) in the
flat order, and a position takes a typer when the two bundles unify
(`Compat`) with some axis actually agreeing (a non-`⊥` meet). One
relation, lifted twice: a frame or verb takes a typer when some
complement or frame does. All decidable. A typer records only the
[noonan-2007] coding and the illocutionary force, so matching needs
positive evidence on one of those: a non-clausal position takes nothing,
and the subject-requirement axis is object-side and never matched.

## Main definitions

- `Complementizer.axes` — the typer's bundle
- `Frame.Position.Takes`, `Frame.Takes`, `Verb.takes` — the relation
  and its lifts
- `Verb.typers` — the typers of a verb within an inventory

## Main results

- `Frame.Position.takes_iff` — the relation axis by axis
- `Frame.Position.not_takes_of_blank`, `Frame.Position.blank_not_takes`,
  `Frame.Position.not_takes_of_not_clausal` — matching needs positive
  evidence on both sides
- `Frame.smallClause_not_takes` — small clauses take no typer
- `Frame.finiteClause_takes` — the positive witness
- `Frame.Takes.mono` — monotone under frame extension

Consistency checks against Fragment data live in Studies
(e.g. `Bondarenko2022.hanaxa_typers`).
-/

/-- The axes a clause-typer records: its coding and force; the other
    axes are a complement position's alone. -/
def Complementizer.axes (z : Complementizer) : Frame.Position.Axes
  | .coding => z.coding
  | .force => z.force
  | .embeddedSubject | .relation | .adposition | .interp => ⊥

namespace Frame.Position

variable {p : Position} {z : Complementizer}

/-- The position takes clause-typer `z`: the two bundles unify and some
    axis agrees. Matching needs positive evidence, so a typer or position
    recording nothing — in particular any non-clausal position — takes
    nothing. -/
def Takes (p : Position) (z : Complementizer) : Prop :=
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
    ¬ (Position.clausal none none e).Takes z := by
  rw [takes_iff]
  rintro ⟨-, a, ha⟩
  cases a <;> simp [axes, coding?, force?, Complementizer.axes, Flat.none_eq_bot] at ha

/-- A non-clausal position takes nothing: it records no axis a typer does. -/
theorem not_takes_of_not_clausal (h : ¬ p.IsClausal) : ¬ p.Takes z := by
  rw [takes_iff]
  rintro ⟨-, a, ha⟩
  cases p <;> cases a <;>
    simp [kind, axes, coding?, force?, Complementizer.axes, Flat.none_eq_bot] at h ha

end Frame.Position

/-- The frame takes `z`: some complement does. -/
def Frame.Takes (fr : Frame) (z : Complementizer) : Prop :=
  ∃ p ∈ fr.complements, p.Takes z

instance (fr : Frame) (z : Complementizer) : Decidable (fr.Takes z) :=
  inferInstanceAs (Decidable (∃ p ∈ fr.complements, _))

/-- Taking is monotone under complement extension. -/
theorem Frame.Takes.mono {fr fr' : Frame} {z : Complementizer}
    (h : fr.Takes z) (hsub : fr.complements ⊆ fr'.complements) : fr'.Takes z :=
  let ⟨p, hp, ht⟩ := h
  ⟨p, hsub hp, ht⟩

/-- Small clauses take no clause-typer. -/
theorem Frame.smallClause_not_takes (z : Complementizer) :
    ¬ Frame.smallClause.Takes z := by
  rintro ⟨p, hp, ht⟩
  rw [List.mem_singleton.1 hp] at ht
  exact Frame.Position.blank_not_takes ht

/-- An indicative typer with declarative or unrecorded force takes the
    finite-clause frame. -/
theorem Frame.finiteClause_takes {z : Complementizer}
    (hc : z.coding = some .indicative)
    (hf : z.force = none ∨ z.force = some .declarative) :
    Frame.finiteClause.Takes z := by
  refine ⟨_, List.mem_singleton_self _,
    Frame.Position.takes_iff.mpr ⟨fun a ↦ ?_, .coding, ?_⟩⟩
  · rcases hf with hf | hf <;> cases a <;>
      simp only [Frame.Position.axes, Complementizer.axes, Frame.Position.coding?,
        Frame.Position.force?, Frame.Position.embeddedSubject?, Frame.Position.relation?,
        Frame.Position.adposition?, Frame.Position.interp?, hc, hf, Flat.none_eq_bot] <;>
      first | exact compat_self _ | exact compat_bot _
  · simp [Frame.Position.axes, Complementizer.axes, Frame.Position.coding?, hc,
      Flat.some_eq_coe]

/-- The verb takes `z`: some frame does. -/
def Verb.takes (v : Verb) (z : Complementizer) : Prop :=
  ∃ fr ∈ v.frames, fr.Takes z

instance (v : Verb) (z : Complementizer) : Decidable (v.takes z) :=
  inferInstanceAs (Decidable (∃ fr ∈ v.frames, _))

/-- The typers of `v` within a language's complementizer inventory. -/
def Verb.typers (v : Verb) (inv : List Complementizer) :
    List Complementizer :=
  inv.filter fun c ↦ decide (v.takes c)
