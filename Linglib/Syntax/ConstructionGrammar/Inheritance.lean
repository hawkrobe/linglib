import Mathlib.Data.List.Dedup

/-!
# Construction Grammar: Inheritance Modes

Computational content for the two modes of constructional inheritance
distinguished by [goldberg-1995] §3.3.1 (the `InheritanceMode` enum in
`ConstructionGrammar.Basic`), following [diessel-2023]'s Table 2: in the
**complete mode**, "high- and low-level representations are fully
compatible with each other" — the unification-based regime [kay-fillmore-1999]
built their formal CxG on and [sag-2012]'s SBCG inherits from HPSG — while
in the **default mode** "low-level representations override high-level
representations if there is a conflict", with formal semantics in the
default-unification tradition ([lascarides-copestake-1999]). Complete mode
is defined exactly on `IsCompatible` inputs; default mode (`inheritField`)
lets the child win, and under **multiple inheritance** (a child with two or
more schematic parents, [diessel-2023] §2.2.2) leaves a field unspecified
when the parents conflict and the child does not legislate
(`ResolvesField`).

[diessel-2023]'s other axis — impoverished vs. full *entry model*, i.e.
whether shared information is stored once or redundantly at every level —
is a storage claim orthogonal to the inheritance algebra and is not
formalized here.

## Main declarations

- `IsCompatible`: two partial field values can strictly unify
- `HasConflict`, `inheritField`, `ResolvesField`: normal-mode field semantics
- `CxnSpec`: a partial constructional specification (bar level, modifier position, stress locus, self-embedding)
- `CxnSpec.inherit`, `CxnSpec.IsCompatible`, `CxnSpec.Resolves`: componentwise lifts
- `inheritField_of_isCompatible`: the two modes agree absent conflict
-/

namespace ConstructionGrammar

/-! ### Field algebra

A specification field is an `Option`-valued partial value: `none` is
"unspecified", and inheritance fills unspecified fields from parents. -/

section FieldAlgebra

variable {α : Type*} [DecidableEq α]

/-- Two partial field values are compatible — able to strictly unify: at
most one is defined, or both agree. Complete-mode inheritance
([diessel-2023] Table 2: representations "fully compatible with each
other") is defined exactly on compatible values. -/
def IsCompatible (p q : Option α) : Prop :=
  p = none ∨ q = none ∨ p = q

instance (p q : Option α) : Decidable (IsCompatible p q) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The distinct values a family of parents determines for a field. -/
def determinedValues (parents : List (Option α)) : List α :=
  (parents.filterMap id).dedup

/-- A parent family conflicts on a field when it determines two or more
distinct values. -/
def HasConflict (parents : List (Option α)) : Prop :=
  1 < (determinedValues parents).length

instance (parents : List (Option α)) : Decidable (HasConflict parents) :=
  inferInstanceAs (Decidable (_ < _))

/-- Normal-mode (default) inheritance for one field ([goldberg-1995]
§3.3.1; [diessel-2023] Table 2: "low-level representations override
high-level representations if there is a conflict";
[lascarides-copestake-1999]): the inheriting construction's own value wins;
an unspecified field takes the unique value its parents agree on; a
parental conflict the child does not legislate leaves the field
unspecified. -/
def inheritField (own : Option α) (parents : List (Option α)) : Option α :=
  match own, determinedValues parents with
  | some x, _ => some x
  | none, [x] => some x
  | none, _ => none

/-- The child legislates wherever its parents conflict — [goldberg-1995]'s
normal mode: "conflicts are addressed by the inheriting construction, which
specifies its own constraints". -/
def ResolvesField (own : Option α) (parents : List (Option α)) : Prop :=
  HasConflict parents → own ≠ none

instance (own : Option α) (parents : List (Option α)) :
    Decidable (ResolvesField own parents) := by
  unfold ResolvesField; infer_instance

@[simp]
theorem inheritField_some (x : α) (parents : List (Option α)) :
    inheritField (some x) parents = some x := rfl

@[simp]
theorem inheritField_nil (own : Option α) : inheritField own [] = own := by
  cases own <;> rfl

/-- Absent conflict, normal-mode inheritance agrees with strict
(complete-mode) unification: with compatible parents the inherited value is
the priority union of child and parents. Normal mode departs from complete
inheritance only at genuine conflicts. -/
theorem inheritField_of_isCompatible (own : Option α) {p q : Option α}
    (h : IsCompatible p q) :
    inheritField own [p, q] = (own.or p).or q := by
  rcases h with h | h | h
  · subst h; cases own <;> cases q <;> rfl
  · subst h; cases own <;> cases p <;> rfl
  · subst h
    cases own <;> cases p <;>
      simp [inheritField, determinedValues, List.dedup_cons_of_mem,
        List.dedup_cons_of_notMem]

/-- Compatible parents impose no resolution burden on the child. -/
theorem resolvesField_of_isCompatible (own : Option α) {p q : Option α}
    (h : IsCompatible p q) : ResolvesField own [p, q] := by
  intro hc
  rcases h with h | h | h <;> subst h <;>
    first
      | (cases q <;>
          simp [HasConflict, determinedValues, List.dedup_cons_of_notMem] at hc)
      | (cases p <;>
          simp [HasConflict, determinedValues, List.dedup_cons_of_notMem] at hc)

end FieldAlgebra

/-! ### Constructional specification vocabulary

Typed values for the inheritable form-side properties at issue in
nominal-modification networks ([goldberg-1995] §3.3;
[goldberg-shirtz-2025] §6). -/

/-- X-bar level of a construction's output category. -/
inductive BarLevel where
  | zero    -- X⁰
  | bar     -- X′
  | phrase  -- XP
  deriving DecidableEq, Repr

/-- Locus of primary stress in a modification construction: compound
stress falls within the modifier (*BLACKbird*), phrasal modification
stresses the head (*black BIRD*). -/
inductive StressLocus where
  | modifier
  | head
  deriving DecidableEq, Repr

/-- Position of the modifier slot relative to the head. -/
inductive ModPosition where
  | prenominal
  | postnominal
  deriving DecidableEq, Repr

/-- Whether a construction's output can recur inside the construction's own
open slot. -/
inductive SelfEmbedding where
  | allowed
  | banned
  deriving DecidableEq, Repr

/-- A partial constructional specification: the inheritable form-side
properties of a (nominal-modification) construction. `none` means the
construction does not legislate the field; inheritance fills unspecified
fields from parents. -/
structure CxnSpec where
  /-- X-bar level of the construction's output -/
  level : Option BarLevel := none
  /-- Position of the modifier slot -/
  modPosition : Option ModPosition := none
  /-- Locus of primary stress -/
  stress : Option StressLocus := none
  /-- Whether the construction self-embeds -/
  selfEmbedding : Option SelfEmbedding := none
  deriving DecidableEq, Repr

namespace CxnSpec

/-- Componentwise compatibility: complete-mode inheritance
([goldberg-1995]'s complete mode; the regime of [sag-2012]'s type
hierarchy) is defined exactly on compatible specifications. -/
def IsCompatible (p q : CxnSpec) : Prop :=
  ConstructionGrammar.IsCompatible p.level q.level ∧
  ConstructionGrammar.IsCompatible p.modPosition q.modPosition ∧
  ConstructionGrammar.IsCompatible p.stress q.stress ∧
  ConstructionGrammar.IsCompatible p.selfEmbedding q.selfEmbedding

instance (p q : CxnSpec) : Decidable (IsCompatible p q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Normal-mode inheritance from a family of parent specifications,
componentwise. -/
def inherit (own : CxnSpec) (parents : List CxnSpec) : CxnSpec :=
  { level := inheritField own.level (parents.map (·.level))
  , modPosition := inheritField own.modPosition (parents.map (·.modPosition))
  , stress := inheritField own.stress (parents.map (·.stress))
  , selfEmbedding := inheritField own.selfEmbedding (parents.map (·.selfEmbedding)) }

/-- The child's own specification legislates every field its parents
conflict on — well-formedness of a normal-mode multi-mother node. -/
def Resolves (own : CxnSpec) (parents : List CxnSpec) : Prop :=
  ResolvesField own.level (parents.map (·.level)) ∧
  ResolvesField own.modPosition (parents.map (·.modPosition)) ∧
  ResolvesField own.stress (parents.map (·.stress)) ∧
  ResolvesField own.selfEmbedding (parents.map (·.selfEmbedding))

instance (own : CxnSpec) (parents : List CxnSpec) :
    Decidable (Resolves own parents) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

@[simp]
theorem inherit_nil (own : CxnSpec) : own.inherit [] = own := by
  simp [inherit]

/-- Compatible parents impose no resolution burden: any child — including
one with no constraints of its own — is well-formed below them. Normal
mode only demands child-side legislation at genuine conflicts. -/
theorem resolves_of_isCompatible (own : CxnSpec) {p q : CxnSpec}
    (h : IsCompatible p q) : Resolves own [p, q] :=
  ⟨resolvesField_of_isCompatible _ h.1, resolvesField_of_isCompatible _ h.2.1,
   resolvesField_of_isCompatible _ h.2.2.1, resolvesField_of_isCompatible _ h.2.2.2⟩

end CxnSpec

end ConstructionGrammar
