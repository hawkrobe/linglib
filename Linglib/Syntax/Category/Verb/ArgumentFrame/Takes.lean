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
does. All decidable. A typer records only the [noonan-2007] coding and
the illocutionary force, so the relation lives on those two axes
(`takes_iff_coding_force`): matching needs positive evidence on one of
them, a non-clausal position takes nothing, and the subject-requirement
axis is position-side and never matched.

## Main definitions

- `Complementizer.axes` — the typer's bundle
- `ArgumentFrame.Position.Takes`, `ArgumentFrame.Takes`, `Verb.Takes` — the
  relation and its lifts
- `Verb.typers` — the typers of a verb within an inventory

## Main results

- `ArgumentFrame.Position.takes_iff` — the relation axis by axis
- `ArgumentFrame.Position.takes_iff_coding_force` — the relation on the two
  axes a typer records
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

/-- The axes a clause-typer records: its coding and force; the other
    axes are a complement position's alone. -/
def Complementizer.axes (z : Complementizer) : ArgumentFrame.Position.Axes
  | .coding => z.coding
  | .force => z.force
  | .embeddedSubject | .relation | .adposition | .interp => ⊥

namespace ArgumentFrame.Position

variable {p q : Position} {z : Complementizer}

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

/-- The relation on the two axes a typer records: coding and force
    consistent, one of them overlapping. -/
theorem takes_iff_coding_force :
    p.Takes z ↔
      (Compat (p.axes .coding) (z.axes .coding) ∧ Compat (p.axes .force) (z.axes .force)) ∧
        (¬ Disjoint (p.axes .coding) (z.axes .coding) ∨
          ¬ Disjoint (p.axes .force) (z.axes .force)) := by
  rw [takes_iff]
  constructor
  · rintro ⟨hc, a, ha⟩
    refine ⟨⟨hc .coding, hc .force⟩, ?_⟩
    cases a <;> simp_all [Complementizer.axes]
  · rintro ⟨⟨hc, hf⟩, h⟩
    refine ⟨fun a ↦ ?_, ?_⟩
    · cases a <;> first | exact hc | exact hf | exact compat_bot _
    · rcases h with h | h
      exacts [⟨.coding, h⟩, ⟨.force, h⟩]

/-- A position recording neither shared axis takes nothing. -/
theorem not_takes_of_blank_left (hc : p.coding? = none) (hf : p.force? = none) :
    ¬ p.Takes z := by
  simp [takes_iff_coding_force, axes, hc, hf, Flat.none_eq_bot]

/-- A typer recording neither axis takes nothing. -/
theorem not_takes_of_blank_right (hc : z.coding = none) (hf : z.force = none) :
    ¬ p.Takes z := by
  simp [takes_iff_coding_force, Complementizer.axes, hc, hf, Flat.none_eq_bot]

/-- A non-clausal position takes nothing: it records no axis a typer does. -/
theorem not_takes_of_not_isClausal (h : ¬ p.IsClausal) : ¬ p.Takes z := by
  cases p <;> first | exact absurd rfl h | exact not_takes_of_blank_left rfl rfl

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

variable {fr fr' : ArgumentFrame} {z : Complementizer}

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
  exact Position.not_takes_of_blank_left rfl rfl ht

/-- An indicative typer with declarative or unrecorded force takes the
    finite-clause frame. -/
theorem finiteClause_takes (hc : z.coding = some .indicative)
    (hf : z.force = none ∨ z.force = some .declarative) : finiteClause.Takes z := by
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rcases hf with hf | hf <;>
    simp [Position.takes_iff_coding_force, Position.axes, Position.coding?, Position.force?,
      Complementizer.axes, hc, hf, Flat.none_eq_bot, Flat.some_eq_coe]

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
