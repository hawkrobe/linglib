import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Verb–complementizer compatibility

The hom between the `Verb` and `Complementizer` entry APIs: which
clause-typers a predicate takes. The core relation is
axis-wise compatibility between a clausal position's recorded axes and
a clause-typer's — [noonan-2007]'s coding axis and the force
axis — with no conflicting axis and at least one positively agreeing
one. Frame- and verb-level relations are derived lifts, all decidable.
The subject-requirement axis (`Complement.Position.embeddedSubject?`)
is object-side and not matched: typers record no subject requirement.

## Main definitions

- `Complement.Position.TypedBy` — the axis-matching core
- `Frame.RealizedBy`, `Verb.takes` — the derived lifts
- `Verb.typers` — the typers of a verb within an inventory

## Main results

- `Complement.Position.not_typedBy_of_blank`,
  `Complement.Position.blank_not_typedBy` — matching needs positive
  evidence on both sides
- `Frame.smallClause_not_realizedBy` — small clauses take no typer
- `Frame.finiteClause_realizedBy` — the positive witness
- `Frame.RealizedBy.mono` — realization is monotone under frame
  extension

Consistency checks against Fragment data live in Studies
(e.g. `Bondarenko2022.hanaxa_frames_realized`).
-/

/-- Clause-typer `z` types the clausal position: no axis both sides
    record conflicts, and at least one recorded axis agrees (matching
    needs positive evidence — a typer recording nothing types nothing).
    Non-clausal positions are typed by nothing. -/
def Complement.Position.TypedBy : Complement.Position →
    Complementizer → Prop
  | .clausal coding force _, z =>
      (coding = none ∨ z.coding = none ∨ coding = z.coding) ∧
        (force = none ∨ z.force = none ∨ force = z.force) ∧
        ((coding ≠ none ∧ coding = z.coding) ∨
          (force ≠ none ∧ force = z.force))
  | _, _ => False

instance : (p : Complement.Position) → (z : Complementizer) →
    Decidable (p.TypedBy z)
  | .clausal _ _ _, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .nominal, _ => inferInstanceAs (Decidable False)
  | .adpositional, _ => inferInstanceAs (Decidable False)

/-- A typer recording neither axis types nothing. -/
theorem Complement.Position.not_typedBy_of_blank
    {p : Complement.Position} {z : Complementizer}
    (hc : z.coding = none) (hf : z.force = none) : ¬ p.TypedBy z := by
  cases p with
  | clausal c f e =>
      rintro ⟨-, -, ⟨hne, heq⟩ | ⟨hne, heq⟩⟩
      · exact hne (heq.trans hc)
      · exact hne (heq.trans hf)
  | nominal => exact id
  | adpositional => exact id

/-- A position recording neither axis is typed by nothing: matching
    needs positive evidence. -/
theorem Complement.Position.blank_not_typedBy {z : Complementizer}
    {e : Option Clause.EmbeddedSubject} :
    ¬ (Complement.Position.clausal none none e).TypedBy z := by
  rintro ⟨-, -, ⟨hne, -⟩ | ⟨hne, -⟩⟩ <;> exact hne rfl

/-- Some position of the frame is typed by `c`. -/
def Frame.RealizedBy (fr : Frame) (c : Complementizer) : Prop :=
  ∃ p ∈ fr, p.TypedBy c

instance (fr : Frame) (c : Complementizer) : Decidable (fr.RealizedBy c) :=
  inferInstanceAs (Decidable (∃ p ∈ fr, _))

/-- Realization is monotone under frame extension. -/
theorem Frame.RealizedBy.mono {fr fr' : Frame} {z : Complementizer}
    (h : fr.RealizedBy z) (hsub : fr ⊆ fr') : fr'.RealizedBy z :=
  let ⟨p, hp, ht⟩ := h
  ⟨p, hsub hp, ht⟩

/-- Small clauses take no clause-typer. -/
theorem Frame.smallClause_not_realizedBy (z : Complementizer) :
    ¬ Frame.smallClause.RealizedBy z := by
  rintro ⟨p, hp, ht⟩
  rw [Frame.smallClause, List.mem_singleton] at hp
  subst hp
  exact Complement.Position.blank_not_typedBy ht

/-- An indicative typer with declarative or unrecorded force realizes
    the finite-clause frame. -/
theorem Frame.finiteClause_realizedBy {z : Complementizer}
    (hc : z.coding = some .indicative)
    (hf : z.force = none ∨ z.force = some .declarative) :
    Frame.finiteClause.RealizedBy z :=
  ⟨_, List.mem_singleton_self _,
    ⟨.inr (.inr hc.symm),
     hf.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h.symm)),
     .inl ⟨Option.some_ne_none _, hc.symm⟩⟩⟩

/-- Some frame of `v` is realized by clause-typer `c`. -/
def Verb.takes (v : Verb) (c : Complementizer) : Prop :=
  ∃ fr ∈ v.frames, fr.RealizedBy c

instance (v : Verb) (c : Complementizer) : Decidable (v.takes c) :=
  inferInstanceAs (Decidable (∃ fr ∈ v.frames, _))

/-- The typers of `v` within a language's complementizer inventory. -/
def Verb.typers (v : Verb) (inv : List Complementizer) :
    List Complementizer :=
  inv.filter (λ c => decide (v.takes c))
