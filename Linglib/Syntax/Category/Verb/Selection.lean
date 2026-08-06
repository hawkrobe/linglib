import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Verb–complementizer selection

The hom between the `Verb` and `Complementizer` entry APIs: which
clause-typers can head a predicate's complements. The core relation is
axis-wise compatibility between a `Clause` description's recorded axes
and a clause-typer's — [noonan-2007]'s coding axis and the clause-form
axis — with no conflicting axis and at least one positively agreeing
one. Position-, frame- and verb-level relations are derived lifts, all
decidable.

## Main definitions

- `Clause.TypedBy` — the axis-matching core
- `Complement.Position.TypedBy`, `Frame.RealizedBy`, `Verb.realizes` —
  the derived lifts
- `Verb.typers` — the typers of a verb within an inventory

Consistency checks against Fragment data live in Studies
(e.g. `Bondarenko2022.hanaxa_frames_realized`).
-/

/-- Clause-typer `z` types clause `c`: no axis both sides record
    conflicts, and at least one recorded axis agrees (matching needs
    positive evidence — a typer recording nothing types nothing). -/
def Clause.TypedBy (c : Clause) (z : Complementizer) : Prop :=
  (c.coding = none ∨ z.coding = none ∨ c.coding = z.coding) ∧
    (c.clauseForm = none ∨ z.clauseForm = none ∨
      c.clauseForm = z.clauseForm) ∧
    ((c.coding ≠ none ∧ c.coding = z.coding) ∨
      (c.clauseForm ≠ none ∧ c.clauseForm = z.clauseForm))

instance (c : Clause) (z : Complementizer) : Decidable (c.TypedBy z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A clausal position is typed by `z` iff its clause is. -/
def Complement.Position.TypedBy : Complement.Position →
    Complementizer → Prop
  | .clausal c, z => c.TypedBy z
  | _, _ => False

instance : (p : Complement.Position) → (z : Complementizer) →
    Decidable (p.TypedBy z)
  | .clausal c, z => inferInstanceAs (Decidable (c.TypedBy z))
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
  inv.filter (fun c => decide (v.realizes c))
