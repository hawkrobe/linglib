import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Verb–complementizer selection

The hom between the `Verb` and `Complementizer` entry APIs: which
clause-typers can head a predicate's complements. The core relation is
axis-wise compatibility between a clausal position's recorded axes and
a clause-typer's — [noonan-2007]'s coding axis and the clause-form
axis — with no conflicting axis and at least one positively agreeing
one. Frame- and verb-level relations are derived lifts, all decidable.
`Complement.Position.SatisfiedBy` is the object-side counterpart: the
recorded axes checked against any `Clause` carrier.

## Main definitions

- `Complement.Position.TypedBy` — the axis-matching core
- `Complement.Position.SatisfiedBy` — satisfaction by a `Clause` object
- `Frame.RealizedBy`, `Verb.realizes` — the derived lifts
- `Verb.typers` — the typers of a verb within an inventory

Consistency checks against Fragment data live in Studies
(e.g. `Bondarenko2022.hanaxa_frames_realized`).
-/

/-- Clause-typer `z` types the clausal position: no axis both sides
    record conflicts, and at least one recorded axis agrees (matching
    needs positive evidence — a typer recording nothing types nothing).
    Non-clausal positions are typed by nothing. -/
def Complement.Position.TypedBy : Complement.Position →
    Complementizer → Prop
  | .clausal coding form _, z =>
      (coding = none ∨ z.coding = none ∨ coding = z.coding) ∧
        (form = none ∨ z.clauseForm = none ∨ form = z.clauseForm) ∧
        ((coding ≠ none ∧ coding = z.coding) ∨
          (form ≠ none ∧ form = z.clauseForm))
  | _, _ => False

instance : (p : Complement.Position) → (z : Complementizer) →
    Decidable (p.TypedBy z)
  | .clausal _ _ _, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .nominal, _ => inferInstanceAs (Decidable False)
  | .adpositional, _ => inferInstanceAs (Decidable False)

/-- A `Clause` object satisfies the clausal position: every axis the
    position records, the object determines and agrees on. A position
    recording nothing is satisfied by every clause object; non-clausal
    positions by none. -/
def Complement.Position.SatisfiedBy {C : Type*} [Clause C] :
    Complement.Position → C → Prop
  | .clausal coding form _, c =>
      (coding = none ∨ Clause.coding? c = coding) ∧
        (form = none ∨ Clause.form? c = form)
  | _, _ => False

instance {C : Type*} [Clause C] : (p : Complement.Position) → (c : C) →
    Decidable (p.SatisfiedBy c)
  | .clausal _ _ _, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .nominal, _ => inferInstanceAs (Decidable False)
  | .adpositional, _ => inferInstanceAs (Decidable False)

/-- Some position of the frame is typed by `c`. -/
def Frame.RealizedBy (fr : Frame) (c : Complementizer) : Prop :=
  ∃ p ∈ fr, p.TypedBy c

instance (fr : Frame) (c : Complementizer) : Decidable (fr.RealizedBy c) :=
  inferInstanceAs (Decidable (∃ p ∈ fr, _))

/-- Some frame of `v` is realized by clause-typer `c`. -/
def Verb.realizes (v : Verb) (c : Complementizer) : Prop :=
  ∃ fr ∈ v.frames, fr.RealizedBy c

instance (v : Verb) (c : Complementizer) : Decidable (v.realizes c) :=
  inferInstanceAs (Decidable (∃ fr ∈ v.frames, _))

/-- The typers of `v` within a language's complementizer inventory. -/
def Verb.typers (v : Verb) (inv : List Complementizer) :
    List Complementizer :=
  inv.filter (λ c => decide (v.realizes c))
