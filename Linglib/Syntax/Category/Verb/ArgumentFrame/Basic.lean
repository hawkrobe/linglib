module

public import Linglib.Syntax.Clause.Basic
public import Linglib.Syntax.Clause.Complementation
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Category.Adposition.Basic
public import Linglib.Semantics.Mood.Defs
public import Linglib.Core.Order.Flat
public import Linglib.Core.Data.List.Forall2

/-! # Argument frames

A predicate's argument frame: its external argument, if any, and its
complement positions in order. A position is nominal, adpositional,
clausal, implicit or expletive, and carries the axes the predicate
selects for: the relation and adposition of an adpositional position,
the [noonan-2007] coding, sentence types and subject requirement of
a clausal one, the interpretation of an implicit one. Positions and
frames are partially ordered by refinement, so a schematic frame lies
below every frame instantiating it.

## Main definitions

* `ImplicitInterp` — the interpretation of an unexpressed argument
* `ArgumentFrame.Position` — one argument position, with its selectional axes
* `ArgumentFrame.Position.Kind`, `Position.kind`, `IsNominal`, `IsAdpositional`,
  `IsClausal`, `IsExpressed` — the category of a position
* `ArgumentFrame.Position.Axis`, `Axes`, `Position.axes` — the axes a position
  records, as a bundle of partial values in the flat order
* `ArgumentFrame` — external argument and complements, with the refinement order
* `ArgumentFrame.Slot`, `ArgumentFrame.get?`, `ArgumentFrame.slots`, `ArgumentFrame.coreSlots`,
  `ArgumentFrame.valency`, `ArgumentFrame.IsTransitive`, `ArgumentFrame.codingRole` — the
  argument slots of a frame and their comparative S/A/P/R/T classification
* `ArgumentFrame.IsIntransitive`, `ArgumentFrame.IsUnaccusative`, `ArgumentFrame.HasNominal`,
  `ArgumentFrame.HasAdpositional`, `ArgumentFrame.HasClausal`, `ArgumentFrame.HasFinite`,
  `ArgumentFrame.HasImplicit` — shape predicates
* `ArgumentFrame.intransitive`, `ArgumentFrame.np`, `ArgumentFrame.finiteClause`, … — smart
  constructors

## Main results

* `ArgumentFrame.Position.le_def`, `ArgumentFrame.le_def` — the refinement orders

## Implementation notes

A position refines another within its kind: `p ≤ q` when the two are of
one kind and every axis `p` records, `q` records with the same value. A
frame's order fixes the external argument and refines the complements
pointwise (`List.Forall₂`). The external argument is an `Option`: `none`
is the unaccusative and impersonal case. Role labels are derived from
the frame (`ArgumentFrame.codingRole`), never stored. Complement-taking is
cross-categorial ([noonan-2007]'s CTPs include adjectives and nouns),
so `ArgumentFrame` is not under `Verb`. Frame-conditioned readings (attitude,
opacity, control) live on `Verb.Reading`
(`Syntax/Category/Verb/Defs.lean`); the selection relation between
frames and clause-typers (`Verb.Takes`) in
`Syntax/Category/Verb/ArgumentFrame/Takes.lean`. [deal-2026]'s CP-external
shell inventory lives with its consumer in `Studies/Deal2026.lean`.

## References

* [bruening-2021]
* [comrie-1978]
* [fillmore-1986]
* [levin-1993]
* [noonan-2007]
-/

@[expose] public section

/-- The interpretation of an unexpressed argument ([fillmore-1986],
[bruening-2021]; the understood-object alternations of [levin-1993]). -/
inductive ImplicitInterp where
  /-- Existentially bound: an unspecified someone or something. -/
  | indef
  /-- A pragmatically recoverable definite. -/
  | def
  /-- Understood as the subject itself (*Mary dressed*). -/
  | reflexive
  /-- Understood as the subject's members, each of the other (*Anne and Cathy met*). -/
  | reciprocal
  /-- Understood as a body part of the subject (*Mary waved*). -/
  | bodyPart
  deriving DecidableEq, Repr

namespace ArgumentFrame

/-- An argument position of a frame is nominal; adpositional, recording the
    relation and the adposition selected; clausal, recording the
    [noonan-2007] coding, the sentence types and the subject requirement
    selected; implicit, an unexpressed argument with its interpretation;
    or expletive. Every axis is optional, and `none` or `⊥` is unselective. -/
inductive Position where
  | nominal
  | adpositional (relation : Option Adposition.RelationType := none)
      (adposition : Option Adposition := none)
  | clausal (coding : Option Complement.Coding := none)
      (types : Clause.Selection := ⊥)
      (embeddedSubject : Option Clause.EmbeddedSubject := none)
  | implicit (interp : Option ImplicitInterp := none)
  | expletive
  deriving DecidableEq, Repr

namespace Position

/-- The adpositional position selecting `p`. -/
def adposition (p : Adposition) : Position := .adpositional (some p.relation) (some p)

/-- The position's recorded [noonan-2007] coding, if clausal. -/
def coding? : Position → Option Complement.Coding
  | clausal c _ _ => c
  | _ => none

/-- The sentence types the position selects, if clausal; nothing otherwise. -/
def types : Position → Clause.Selection
  | clausal _ t _ => t
  | _ => ⊥

/-- The position's recorded subject requirement, if clausal. -/
def embeddedSubject? : Position → Option Clause.EmbeddedSubject
  | clausal _ _ e => e
  | _ => none

/-- The position's recorded relation, if adpositional. -/
def relation? : Position → Option Adposition.RelationType
  | adpositional r _ => r
  | _ => none

/-- The position's recorded adposition, if adpositional. -/
def adposition? : Position → Option Adposition
  | adpositional _ p => p
  | _ => none

/-- The position's recorded interpretation, if implicit. -/
def interp? : Position → Option ImplicitInterp
  | implicit i => i
  | _ => none

/-! ### Kind -/

/-- The category of a position. -/
inductive Kind where
  | nominal
  | adpositional
  | clausal
  | implicit
  | expletive
  deriving DecidableEq, Repr

/-- The category of the position. -/
def kind : Position → Kind
  | nominal => .nominal
  | adpositional .. => .adpositional
  | clausal .. => .clausal
  | implicit _ => .implicit
  | expletive => .expletive

/-- The position is nominal, the core case. -/
abbrev IsNominal (p : Position) : Prop := p.kind = .nominal

/-- The position is adpositional. -/
abbrev IsAdpositional (p : Position) : Prop := p.kind = .adpositional

/-- The position is clausal. -/
abbrev IsClausal (p : Position) : Prop := p.kind = .clausal

/-- The position is expressed when it is nominal, adpositional or clausal. -/
abbrev IsExpressed (p : Position) : Prop := p.IsNominal ∨ p.IsAdpositional ∨ p.IsClausal

/-- The position is a finite clause when its coding is finite. -/
def IsFinite (p : Position) : Prop := ∃ c ∈ p.coding?, c.IsFinite

instance : DecidablePred IsFinite := fun p ↦ inferInstanceAs (Decidable (∃ c ∈ p.coding?, _))

/-! ### Axes and the refinement order -/

/-- The selectional axes a position records. A clausal position and a
    clause-typer share `coding` and `types` (`Complementizer.axes`). -/
inductive Axis where
  | coding
  | types
  | embeddedSubject
  | relation
  | adposition
  | interp
  deriving DecidableEq, Fintype, Repr

/-- The carrier of an axis is a flat slot over the values of an enumerated axis, and a
    selection of sentence types for the `types` axis. -/
def Axis.Carrier : Axis → Type
  | coding => Flat Complement.Coding
  | types => Clause.Selection
  | embeddedSubject => Flat Clause.EmbeddedSubject
  | relation => Flat Adposition.RelationType
  | adposition => Flat Adposition
  | interp => Flat ImplicitInterp

instance : ∀ a : Axis, PartialOrder a.Carrier
  | .coding => inferInstanceAs (PartialOrder (Flat Complement.Coding))
  | .types => inferInstanceAs (PartialOrder Clause.Selection)
  | .embeddedSubject => inferInstanceAs (PartialOrder (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (PartialOrder (Flat Adposition.RelationType))
  | .adposition => inferInstanceAs (PartialOrder (Flat Adposition))
  | .interp => inferInstanceAs (PartialOrder (Flat ImplicitInterp))

instance : ∀ a : Axis, OrderBot a.Carrier
  | .coding => inferInstanceAs (OrderBot (Flat Complement.Coding))
  | .types => inferInstanceAs (OrderBot Clause.Selection)
  | .embeddedSubject => inferInstanceAs (OrderBot (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (OrderBot (Flat Adposition.RelationType))
  | .adposition => inferInstanceAs (OrderBot (Flat Adposition))
  | .interp => inferInstanceAs (OrderBot (Flat ImplicitInterp))

instance : ∀ a : Axis, PartialUnify a.Carrier
  | .coding => inferInstanceAs (PartialUnify (Flat Complement.Coding))
  | .types => inferInstanceAs (PartialUnify Clause.Selection)
  | .embeddedSubject => inferInstanceAs (PartialUnify (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (PartialUnify (Flat Adposition.RelationType))
  | .adposition => inferInstanceAs (PartialUnify (Flat Adposition))
  | .interp => inferInstanceAs (PartialUnify (Flat ImplicitInterp))

instance : ∀ a : Axis, DecidableEq a.Carrier
  | .coding => inferInstanceAs (DecidableEq (Flat Complement.Coding))
  | .types => inferInstanceAs (DecidableEq Clause.Selection)
  | .embeddedSubject => inferInstanceAs (DecidableEq (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (DecidableEq (Flat Adposition.RelationType))
  | .adposition => inferInstanceAs (DecidableEq (Flat Adposition))
  | .interp => inferInstanceAs (DecidableEq (Flat ImplicitInterp))

instance : ∀ a : Axis, DecidableLE a.Carrier
  | .coding => inferInstanceAs (DecidableLE (Flat Complement.Coding))
  | .types => inferInstanceAs (DecidableLE Clause.Selection)
  | .embeddedSubject => inferInstanceAs (DecidableLE (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (DecidableLE (Flat Adposition.RelationType))
  | .adposition => inferInstanceAs (DecidableLE (Flat Adposition))
  | .interp => inferInstanceAs (DecidableLE (Flat ImplicitInterp))

/-- A bundle of partial axis values, ordered pointwise by extension:
    unification is `PartialUnify.unify`, consistency is `Compat`. -/
abbrev Axes := ∀ a : Axis, a.Carrier

/-- The axes the position records. -/
def axes (p : Position) : Axes
  | .coding => p.coding?
  | .types => p.types
  | .embeddedSubject => p.embeddedSubject?
  | .relation => p.relation?
  | .adposition => p.adposition?
  | .interp => p.interp?

/-- A position is its kind and its axes. -/
theorem eq_of_kind_eq_of_axes_eq {p q : Position} (hk : p.kind = q.kind)
    (ha : p.axes = q.axes) : p = q := by
  have h := fun a ↦ congrFun ha a
  have hc := h .coding
  have hf := h .types
  have he := h .embeddedSubject
  have hr := h .relation
  have hp := h .adposition
  have hi := h .interp
  cases p <;> cases q <;>
    simp_all [kind, axes, coding?, types, embeddedSubject?, relation?, adposition?, interp?]

/-- A position refines another, `p ≤ q`, when the two are of one kind and every axis `p`
    records, `q` records with the same value. -/
instance : PartialOrder Position where
  le p q := p.kind = q.kind ∧ p.axes ≤ q.axes
  le_refl _ := ⟨rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := eq_of_kind_eq_of_axes_eq h₁.1 (h₁.2.antisymm h₂.2)

theorem le_def {p q : Position} : p ≤ q ↔ p.kind = q.kind ∧ p.axes ≤ q.axes := Iff.rfl

instance : DecidableLE Position := fun p q ↦
  inferInstanceAs (Decidable (p.kind = q.kind ∧ ∀ a, p.axes a ≤ q.axes a))

end Position

end ArgumentFrame

/-- An argument frame is the external argument, if any, and the complement positions in
    order. -/
@[ext]
structure ArgumentFrame where
  /-- The external argument; `none` for an unaccusative or impersonal frame. -/
  external : Option ArgumentFrame.Position := some .nominal
  /-- The complement positions in order. -/
  complements : List ArgumentFrame.Position
  deriving DecidableEq, Repr

namespace ArgumentFrame

/-- A frame refines another when it has the same external argument and complements refined
    pointwise. -/
instance : PartialOrder ArgumentFrame where
  le f g := f.external = g.external ∧ List.Forall₂ (· ≤ ·) f.complements g.complements
  le_refl _ := ⟨rfl, List.forall₂_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ArgumentFrame.ext h₁.1 (h₁.2.antisymm h₂.2)

theorem le_def {f g : ArgumentFrame} : f ≤ g ↔
    f.external = g.external ∧ List.Forall₂ (· ≤ ·) f.complements g.complements := Iff.rfl

instance : DecidableLE ArgumentFrame := fun f g ↦
  inferInstanceAs (Decidable (f.external = g.external ∧ List.Forall₂ _ _ _))

/-! ### Slots -/

/-- An argument slot of a frame is the external argument or the `i`-th complement. -/
inductive Slot where
  | external
  | complement (i : ℕ)
  deriving DecidableEq, Repr

variable (fr : ArgumentFrame)

/-- The position at a slot. -/
def get? : Slot → Option Position
  | .external => fr.external
  | .complement i => fr.complements[i]?

/-- The filled slots, external first. -/
def slots : List Slot :=
  (fr.external.map fun _ ↦ Slot.external).toList ++
    (List.range fr.complements.length).map .complement

/-- The core argument slots are those realized as nominals ([comrie-1978]). -/
def coreSlots : List Slot :=
  fr.slots.filter fun s ↦ (fr.get? s).any fun p ↦ decide p.IsNominal

/-- The number of core arguments. -/
def valency : ℕ := fr.coreSlots.length

/-- A frame is transitive when it has two or more core arguments. -/
def IsTransitive : Prop := 2 ≤ fr.valency

instance : Decidable fr.IsTransitive := inferInstanceAs (Decidable (_ ≤ _))

/-- The comparative classification of a core slot ([comrie-1978]): the
    sole core argument of a one-place frame is S; a two-place frame has A
    and P; a three-place frame A, R and T. A function of the frame's
    shape, never a stored feature; `Clause.Arguments.codingRole` is the
    classification of a clause token. -/
def codingRole (s : Slot) : Option ArgumentRole :=
  (fr.coreSlots.idxOf? s).bind fun i ↦
    match fr.valency, i with
    | 1, 0 => some .S
    | _, 0 => some .A
    | 2, 1 => some .P
    | _, 1 => some .R
    | _, 2 => some .T
    | _, _ => none

/-- The slot object entailments sit on is the last core complement, the sole
    object of a monotransitive and the second object of a double-object
    frame. -/
def objectSlot? : Option Slot := (fr.coreSlots.filter (· != Slot.external)).getLast?

/-! ### Shape predicates -/

/-- The frame has no complement. -/
def IsIntransitive : Prop := fr.complements = []

instance : Decidable fr.IsIntransitive := inferInstanceAs (Decidable (_ = _))

/-- Some complement of the frame is nominal. -/
def HasNominal : Prop := ∃ p ∈ fr.complements, p.IsNominal

instance : Decidable fr.HasNominal := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- Some complement of the frame is adpositional. -/
def HasAdpositional : Prop := ∃ p ∈ fr.complements, p.IsAdpositional

instance : Decidable fr.HasAdpositional := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- Some complement of the frame is clausal. -/
def HasClausal : Prop := ∃ p ∈ fr.complements, p.IsClausal

instance : Decidable fr.HasClausal := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- Some complement of the frame is a finite clause. -/
def HasFinite : Prop := ∃ p ∈ fr.complements, p.IsFinite

instance : Decidable fr.HasFinite := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- Some complement of the frame is implicit, an argument left unexpressed. -/
def HasImplicit : Prop := ∃ p ∈ fr.complements, p.kind = .implicit

instance : Decidable fr.HasImplicit := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- A frame is unaccusative when it has no external argument and an expressed
    complement, the underlying object or clause that surfaces as subject. -/
def IsUnaccusative : Prop := fr.external = none ∧ ∃ p ∈ fr.complements, p.IsExpressed

instance : Decidable fr.IsUnaccusative := inferInstanceAs (Decidable (_ ∧ ∃ p ∈ _, _))

/-- The [noonan-2007] codings recorded across the frame's complements. -/
def codings : List Complement.Coding := fr.complements.filterMap (·.coding?)

/-- Some complement of the frame selects the sentence type `t`. -/
def hasType (t : Clause.SentenceType) : Prop := ∃ p ∈ fr.complements, t ∈ p.types

instance (t : Clause.SentenceType) : Decidable (fr.hasType t) :=
  inferInstanceAs (Decidable (∃ p ∈ _, _))

/-! ### Smart constructors -/

/-- The intransitive frame has an external argument and no complement. -/
def intransitive : ArgumentFrame := ⟨some .nominal, []⟩

/-- The unaccusative frame has a single nominal argument, internal. -/
def unaccusative : ArgumentFrame := ⟨none, [.nominal]⟩

/-- The impersonal frame has an expletive subject and no complement. -/
def impersonal : ArgumentFrame := ⟨some .expletive, []⟩

/-- The object-drop frame leaves the object unexpressed, with interpretation `i`. -/
def objectDrop (i : Option ImplicitInterp := none) : ArgumentFrame :=
  ⟨some .nominal, [.implicit i]⟩

/-- The transitive frame has one nominal complement. -/
def np : ArgumentFrame := ⟨some .nominal, [.nominal]⟩

/-- The double-object frame has two nominal complements. -/
def np_np : ArgumentFrame := ⟨some .nominal, [.nominal, .nominal]⟩

/-- The PP frame has one adpositional complement, selecting `p` when given. -/
def pp (p : Option Adposition := none) : ArgumentFrame :=
  ⟨some .nominal, [.adpositional (p.map (·.relation)) p]⟩

/-- The NP + PP frame has a nominal plus an adpositional complement, selecting `p`
    when given. -/
def np_pp (p : Option Adposition := none) : ArgumentFrame :=
  ⟨some .nominal, [.nominal, .adpositional (p.map (·.relation)) p]⟩

/-- Finite declarative clause. -/
def finiteClause : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .indicative) (types := .only .declarative)]⟩

/-- Finite declarative clause in the subjunctive. -/
def subjunctiveClause : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .subjunctive) (types := .only .declarative)]⟩

/-- Infinitival clause. The embedded-subject requirement varies by verb
    (equi-deletion, raising, or adposition-marked overt subjects,
    [noonan-2007] §1.3.4), so it lives on the verb's reading, not here. -/
def infinitival : ArgumentFrame := ⟨some .nominal, [.clausal (coding := some .infinitive)]⟩

/-- The raising frame has an infinitival clause and no external argument. -/
def raising : ArgumentFrame := ⟨none, [.clausal (coding := some .infinitive)]⟩

/-- Gerund / nominalized clause. -/
def gerund : ArgumentFrame := ⟨some .nominal, [.clausal (coding := some .nominalized)]⟩

/-- Small clause (*consider X happy*; causative *make X leave*). Outside
    [noonan-2007]'s coding inventory, which classifies complements by
    the part of speech of their predicate, so the position records
    nothing. -/
def smallClause : ArgumentFrame := ⟨some .nominal, [.clausal]⟩

/-- The frame of an embedded question. The sentence type is orthogonal to the
    [noonan-2007] coding, so `coding` stays `none`. -/
def question : ArgumentFrame := ⟨some .nominal, [.clausal (types := .interrogatives)]⟩

end ArgumentFrame
