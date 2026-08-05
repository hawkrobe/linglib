import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Verb–complementizer selection

The hom between the `Verb` and `Complementizer` entry APIs: which
clause-typers can head a predicate's complements. The core relation is
axis-wise compatibility between a complement position's recorded
clausal axes and a clause-typer's — [noonan-2007]'s coding axis and the
clause-form axis — with no conflicting axis and at least one positively
agreeing one (matching needs positive evidence: a typer recording
nothing types nothing). Frame- and verb-level relations are derived
`∃`-lifts, all decidable.

## Main definitions

- `Complement.Position.TypedBy` — the axis-matching core
- `Frame.RealizedBy`, `Verb.realizes` — the derived lifts
- `Verb.typers` — the typers of a verb within an inventory

Consistency checks against Fragment data live in Studies
(e.g. `Bondarenko2022.hanaxa_frames_realized`).
-/

/-- Clause-typer `c` types complement position `p`: the position is
    clausal, no axis both sides record conflicts, and at least one
    recorded axis agrees. -/
def Complement.Position.TypedBy (p : Complement.Position)
    (c : Complementizer) : Prop :=
  p.cat = .clausal ∧
    (p.coding = none ∨ c.coding = none ∨ p.coding = c.coding) ∧
    (p.clauseForm = none ∨ c.clauseForm = none ∨
      p.clauseForm = c.clauseForm) ∧
    ((p.coding ≠ none ∧ p.coding = c.coding) ∨
      (p.clauseForm ≠ none ∧ p.clauseForm = c.clauseForm))

instance (p : Complement.Position) (c : Complementizer) :
    Decidable (p.TypedBy c) :=
  inferInstanceAs (Decidable (_ ∧ _))

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
