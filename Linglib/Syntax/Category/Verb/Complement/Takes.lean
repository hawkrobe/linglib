import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic
import Linglib.Core.Data.Option.Compatible

/-!
# Verb–complementizer compatibility

The hom between the `Verb` and `Complementizer` entry APIs: which
clause-typers a predicate takes. One relation, lifted twice: a position
takes a typer when their recorded axes — [noonan-2007]'s coding axis
and the force axis — are `Option.Compatible` throughout and
`Option.Agrees` somewhere; a frame or verb takes a typer when some
position or frame does. All decidable. Non-clausal positions record no
axes, so positive evidence already excludes them; the
subject-requirement axis (`Complement.Position.embeddedSubject?`) is
object-side and not matched: typers record no subject requirement.

## Main definitions

- `Complement.Position.Takes`, `Frame.Takes`, `Verb.takes` — the
  relation and its lifts
- `Verb.typers` — the typers of a verb within an inventory

## Main results

- `Complement.Position.not_takes_of_blank`,
  `Complement.Position.blank_not_takes` — matching needs positive
  evidence on both sides
- `Frame.smallClause_not_takes` — small clauses take no typer
- `Frame.finiteClause_takes` — the positive witness
- `Frame.Takes.mono` — monotone under frame extension

Consistency checks against Fragment data live in Studies
(e.g. `Bondarenko2022.hanaxa_typers`).
-/

/-- The position takes clause-typer `z`: every recorded axis
    compatible, some axis agreeing. Matching needs positive evidence,
    so a typer or position recording nothing — in particular any
    non-clausal position — takes nothing. -/
def Complement.Position.Takes (p : Complement.Position)
    (z : Complementizer) : Prop :=
  p.coding?.Compatible z.coding ∧ p.force?.Compatible z.force ∧
    (p.coding?.Agrees z.coding ∨ p.force?.Agrees z.force)

instance (p : Complement.Position) (z : Complementizer) :
    Decidable (p.Takes z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A typer recording neither axis takes nothing. -/
theorem Complement.Position.not_takes_of_blank
    {p : Complement.Position} {z : Complementizer}
    (hc : z.coding = none) (hf : z.force = none) : ¬ p.Takes z := by
  simp [Position.Takes, hc, hf]

/-- A position recording neither axis takes nothing: matching needs
    positive evidence. -/
theorem Complement.Position.blank_not_takes {z : Complementizer}
    {e : Option Clause.EmbeddedSubject} :
    ¬ (Complement.Position.clausal none none e).Takes z := by
  simp [Position.Takes, Position.coding?, Position.force?]

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
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rcases hf with hf | hf <;>
    simp [Complement.Position.Takes, Complement.Position.coding?,
      Complement.Position.force?, hc, hf]

/-- The verb takes `z`: some frame does. -/
def Verb.takes (v : Verb) (z : Complementizer) : Prop :=
  ∃ fr ∈ v.frames, fr.Takes z

instance (v : Verb) (z : Complementizer) : Decidable (v.takes z) :=
  inferInstanceAs (Decidable (∃ fr ∈ v.frames, _))

/-- The typers of `v` within a language's complementizer inventory. -/
def Verb.typers (v : Verb) (inv : List Complementizer) :
    List Complementizer :=
  inv.filter (λ c => decide (v.takes c))
