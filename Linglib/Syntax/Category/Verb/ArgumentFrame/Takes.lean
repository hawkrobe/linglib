import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic
import Mathlib.Order.PropInstances

/-!
# Verb–complementizer selection

The selection relation between the `Verb` and `Complementizer` entry
APIs: which clause-typers a predicate takes. A complement position and a
clause-typer each record a bundle of partial axis values
(`ArgumentFrame.Position.Axes`) in the flat order, and a position takes a
typer when the two bundles are consistent (`Compat`) and overlap
(`¬ Disjoint`): some axis both commit to, with one value. One relation,
lifted twice: a frame or verb takes a typer when some complement or frame
does. All decidable. A typer records only the [noonan-2007] coding, the
illocutionary force and the reality status, so the relation lives on those
three axes (`takes_iff_typer_axes`): matching needs positive evidence on one
of them, a non-clausal position takes nothing, and the subject-requirement
axis is position-side and never matched. The reality axis is what lets one
typer span two codings: Gã *ni* records only `irrealis` and is taken by the
controlled infinitival and the subjunctive frame alike.

## Main definitions

- `Complementizer.axes` — the typer's bundle
- `ArgumentFrame.Position.typedBy`, `ArgumentFrame.typedBy` — the clausal position
  and the frame a typer types, given the subject requirement the predicate adds
- `ArgumentFrame.Position.Takes`, `ArgumentFrame.Takes`, `Verb.Takes` — the
  relation and its lifts
- `Verb.typers` — the typers of a verb within an inventory

## Main results

- `ArgumentFrame.Position.takes_iff` — the relation axis by axis
- `ArgumentFrame.Position.takes_iff_typer_axes` — the relation on the three
  axes a typer records
- `Complementizer.compat_axes_iff`, `Complementizer.disjoint_axes_iff` — a bundle
  meets a typer's on the coding, force and reality axes alone
- `ArgumentFrame.Position.typedBy_takes_iff`, `ArgumentFrame.typedBy_takes_iff` —
  the position or frame one typer types takes another exactly when the two
  bundles are consistent and overlap; `typedBy_takes_self_iff` for the typer
  itself
- `ArgumentFrame.Position.not_takes_of_blank_left`,
  `ArgumentFrame.Position.not_takes_of_blank_right`,
  `ArgumentFrame.Position.not_takes_of_not_isClausal` — matching needs
  positive evidence on both sides
- `ArgumentFrame.Position.takes_of_le` — the positive witness in general
- `ArgumentFrame.Position.Takes.mono_of_compat`,
  `ArgumentFrame.Position.Takes.of_le_of_not_disjoint` — guarded monotonicity
  under refinement, in both directions
- `ArgumentFrame.Position.Takes.isClausal`, `ArgumentFrame.Takes.hasClausal`,
  `Verb.Takes.takesClausal` — taking a typer entails the clausal shape predicates
- `ArgumentFrame.not_takes_smallClause` — small clauses take no typer
- `ArgumentFrame.finiteClause_takes` — the positive witness
- `ArgumentFrame.Takes.mono` — monotone under complement extension
- `Verb.mem_typers` — membership in the typer list

Consistency checks against Fragment data live in Studies
(e.g. `Bondarenko2022.hanaxa_typers`).

## References

- [noonan-2007]
-/

/-- The axes a clause-typer records: its coding, force and reality status;
    the other axes are a complement position's alone. -/
def Complementizer.axes (z : Complementizer) : ArgumentFrame.Position.Axes
  | .coding => z.coding
  | .force => z.force
  | .reality => z.reality
  | .embeddedSubject | .relation | .adposition | .interp => ⊥

namespace Complementizer

variable {z : Complementizer} {f : ArgumentFrame.Position.Axes}

/-- A bundle is consistent with a typer's exactly on the coding, force and
    reality axes. -/
theorem compat_axes_iff (f : ArgumentFrame.Position.Axes) :
    Compat f z.axes ↔
      Compat (f .coding) z.coding ∧ Compat (f .force) z.force ∧
        Compat (f .reality) z.reality := by
  rw [compat_pi_iff]
  exact ⟨fun h ↦ ⟨h _, h _, h _⟩, fun ⟨hc, hf, hr⟩ a ↦ by
    cases a <;> first | exact hc | exact hf | exact hr | exact compat_bot _⟩

/-- A bundle is disjoint from a typer's exactly on the coding, force and
    reality axes. -/
theorem disjoint_axes_iff (f : ArgumentFrame.Position.Axes) :
    Disjoint f z.axes ↔
      Disjoint (f .coding) z.coding ∧ Disjoint (f .force) z.force ∧
        Disjoint (f .reality) z.reality := by
  rw [Pi.disjoint_iff]
  exact ⟨fun h ↦ ⟨h _, h _, h _⟩, fun ⟨hc, hf, hr⟩ a ↦ by
    cases a <;> first | exact hc | exact hf | exact hr | exact disjoint_bot_right⟩

end Complementizer

namespace ArgumentFrame.Position

variable {p q : Position} {z z' : Complementizer} {s : Option Clause.EmbeddedSubject}

/-- The clausal position `z` types: `z`'s coding, force and reality status,
    with the subject requirement `s` the selecting predicate adds. -/
def typedBy (z : Complementizer) (s : Option Clause.EmbeddedSubject := none) : Position :=
  .clausal z.coding z.force s z.reality

@[simp] theorem kind_typedBy : (typedBy z s).kind = .clausal := rfl

@[simp] theorem coding?_typedBy : (typedBy z s).coding? = z.coding := rfl

@[simp] theorem force?_typedBy : (typedBy z s).force? = z.force := rfl

@[simp] theorem reality?_typedBy : (typedBy z s).reality? = z.reality := rfl

@[simp] theorem embeddedSubject?_typedBy : (typedBy z s).embeddedSubject? = s := rfl

@[simp] theorem relation?_typedBy : (typedBy z s).relation? = none := rfl

@[simp] theorem adposition?_typedBy : (typedBy z s).adposition? = none := rfl

@[simp] theorem interp?_typedBy : (typedBy z s).interp? = none := rfl

/-- The position takes clause-typer `z`: the two bundles are consistent and
    overlap, some axis committed on both sides to one value. Matching needs
    positive evidence, so a typer or position recording nothing — in
    particular any non-clausal position — takes nothing. -/
def Takes (p : Position) (z : Complementizer) : Prop :=
  Compat p.axes z.axes ∧ ¬ Disjoint p.axes z.axes

/-- The relation axis by axis: every axis consistent, some axis overlapping. -/
theorem takes_iff :
    p.Takes z ↔
      (∀ a, Compat (p.axes a) (z.axes a)) ∧ ∃ a, ¬ Disjoint (p.axes a) (z.axes a) := by
  simp only [Takes, compat_pi_iff, Pi.disjoint_iff, not_forall]

instance : Decidable (p.Takes z) := decidable_of_iff _ takes_iff.symm

/-- The relation on the three axes a typer records: coding, force and reality
    consistent, one of them overlapping. -/
theorem takes_iff_typer_axes :
    p.Takes z ↔
      (Compat (p.axes .coding) z.coding ∧ Compat (p.axes .force) z.force ∧
          Compat (p.axes .reality) z.reality) ∧
        (¬ Disjoint (p.axes .coding) z.coding ∨ ¬ Disjoint (p.axes .force) z.force ∨
          ¬ Disjoint (p.axes .reality) z.reality) :=
  and_congr (Complementizer.compat_axes_iff _)
    ((Complementizer.disjoint_axes_iff _).not.trans (not_and_or.trans (or_congr_right not_and_or)))

/-- The position `z` types takes `z'` exactly when the two typers' bundles are
    consistent and overlap; the subject requirement plays no part. -/
theorem typedBy_takes_iff :
    (typedBy z s).Takes z' ↔ Compat z.axes z'.axes ∧ ¬ Disjoint z.axes z'.axes := by
  rw [Takes, Complementizer.compat_axes_iff, Complementizer.disjoint_axes_iff,
    Complementizer.compat_axes_iff z.axes, Complementizer.disjoint_axes_iff z.axes]
  exact Iff.rfl

/-- The position `z` types takes `z` itself exactly when `z` records something;
    the `←` direction is `takes_of_le`. -/
theorem typedBy_takes_self_iff : (typedBy z s).Takes z ↔ z.axes ≠ ⊥ :=
  typedBy_takes_iff.trans ((and_iff_right (compat_self _)).trans disjoint_self.not)

/-- A position recording no shared axis takes nothing. -/
theorem not_takes_of_blank_left (hc : p.coding? = none) (hf : p.force? = none)
    (hr : p.reality? = none) : ¬ p.Takes z := by
  simp [takes_iff_typer_axes, axes, hc, hf, hr, Flat.none_eq_bot]

/-- A typer recording no axis takes nothing. -/
theorem not_takes_of_blank_right (hc : z.coding = none) (hf : z.force = none)
    (hr : z.reality = none) : ¬ p.Takes z := by
  simp [takes_iff_typer_axes, hc, hf, hr, Flat.none_eq_bot]

/-- A non-clausal position takes nothing: it records no axis a typer does. -/
theorem not_takes_of_not_isClausal (h : ¬ p.IsClausal) : ¬ p.Takes z := by
  cases p <;> first | exact absurd rfl h | exact not_takes_of_blank_left rfl rfl rfl

/-- A position taking a typer is clausal. -/
theorem Takes.isClausal (h : p.Takes z) : p.IsClausal :=
  of_not_not fun hn ↦ not_takes_of_not_isClausal hn h

/-- A typer whose bundle lies below the position's, and records something,
    is taken: the positive witness in general. -/
theorem takes_of_le (h : z.axes ≤ p.axes) (hz : z.axes ≠ ⊥) : p.Takes z :=
  ⟨Compat.of_le le_rfl h, fun hd ↦ hz (hd.symm.eq_bot_of_le h)⟩

/-- Refining a position keeps a typer it takes, as long as the refinement
    stays consistent with the typer. -/
theorem Takes.mono_of_compat (hpq : p ≤ q) (hc : Compat q.axes z.axes) (h : p.Takes z) :
    q.Takes z :=
  ⟨hc, fun hd ↦ h.2 (hd.mono_left (le_def.1 hpq).2)⟩

/-- Coarsening a position keeps a typer it takes, as long as the coarsening
    still overlaps the typer. -/
theorem Takes.of_le_of_not_disjoint (hpq : p ≤ q) (hd : ¬ Disjoint p.axes z.axes)
    (h : q.Takes z) : p.Takes z :=
  ⟨h.1.mono (le_def.1 hpq).2 le_rfl, hd⟩

end ArgumentFrame.Position

namespace ArgumentFrame

variable {fr fr' : ArgumentFrame} {z z' : Complementizer} {s : Option Clause.EmbeddedSubject}

/-- The frame takes `z`: some complement does. -/
def Takes (fr : ArgumentFrame) (z : Complementizer) : Prop :=
  ∃ p ∈ fr.complements, p.Takes z

instance : Decidable (fr.Takes z) := inferInstanceAs (Decidable (∃ p ∈ fr.complements, _))

/-- Taking is monotone under complement extension. -/
theorem Takes.mono (hsub : fr.complements ⊆ fr'.complements) (h : fr.Takes z) : fr'.Takes z :=
  h.imp fun _ ⟨hp, ht⟩ ↦ ⟨hsub hp, ht⟩

/-- A frame taking a typer has a clausal complement. -/
theorem Takes.hasClausal (h : fr.Takes z) : fr.HasClausal :=
  h.imp fun _ ⟨hp, ht⟩ ↦ ⟨hp, ht.isClausal⟩

/-- Small clauses take no clause-typer. -/
theorem not_takes_smallClause (z : Complementizer) : ¬ smallClause.Takes z := by
  rintro ⟨p, hp, ht⟩
  rw [List.mem_singleton.1 hp] at ht
  exact Position.not_takes_of_blank_left rfl rfl rfl ht

/-- An indicative typer with declarative or unrecorded force takes the
    finite-clause frame. -/
theorem finiteClause_takes (hc : z.coding = some .indicative)
    (hf : z.force = none ∨ z.force = some .declarative) : finiteClause.Takes z := by
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rcases hf with hf | hf <;>
    simp [Position.takes_iff_typer_axes, Position.axes, Position.coding?, Position.force?,
      Position.reality?, hc, hf, Flat.none_eq_bot, Flat.some_eq_coe, compat_bot, bot_compat]

/-! ### The frame a typer types -/

/-- The frame whose one complement is the clause `z` types, with the subject
    requirement `s`: the frame a fragment derives from its complementizer
    entry rather than retyping the typer's axes. -/
def typedBy (z : Complementizer) (s : Option Clause.EmbeddedSubject := none) : ArgumentFrame :=
  ⟨some .nominal, [.typedBy z s]⟩

@[simp] theorem complements_typedBy : (typedBy z s).complements = [.typedBy z s] := rfl

/-- The frame `z` types takes `z'` exactly when the two typers' bundles are
    consistent and overlap. -/
theorem typedBy_takes_iff :
    (typedBy z s).Takes z' ↔ Compat z.axes z'.axes ∧ ¬ Disjoint z.axes z'.axes := by
  simp only [Takes, complements_typedBy, List.mem_singleton, exists_eq_left,
    Position.typedBy_takes_iff]

/-- The frame `z` types takes `z` exactly when `z` records something. -/
theorem typedBy_takes_self_iff : (typedBy z s).Takes z ↔ z.axes ≠ ⊥ :=
  typedBy_takes_iff.trans ((and_iff_right (compat_self _)).trans disjoint_self.not)

end ArgumentFrame

namespace Verb

variable {v : Verb} {z : Complementizer} {inv : List Complementizer}

/-- The verb takes `z`: some frame does. -/
def Takes (v : Verb) (z : Complementizer) : Prop :=
  ∃ fr ∈ v.frames, fr.Takes z

instance : Decidable (v.Takes z) := inferInstanceAs (Decidable (∃ fr ∈ v.frames, _))

/-- A verb taking a typer takes a clausal complement. -/
theorem Takes.takesClausal (h : v.Takes z) : v.TakesClausal :=
  h.imp fun _ ⟨hf, ht⟩ ↦ ⟨hf, ht.hasClausal⟩

/-- The typers of `v` within a language's complementizer inventory. -/
def typers (v : Verb) (inv : List Complementizer) : List Complementizer :=
  inv.filter (v.Takes ·)

@[simp] theorem mem_typers : z ∈ v.typers inv ↔ z ∈ inv ∧ v.Takes z := by
  simp [typers]

end Verb
