import Linglib.Theories.Semantics.Dynamic.Core.Update

/-!
# File Change Semantics
@cite{heim-1982} @cite{heim-1983}

Heim's File Change Semantics, the pioneering dynamic semantic framework
that treats sentence meanings as context change potentials (FCPs) operating
on *files* — structured information states tracking which discourse
referents are active.

## Heim's File Metaphor (Ch III)

A file F = ⟨Dom(F), Sat(F)⟩ is a pair:
- `Dom(F)`: a set of variable indices — the "file cards" currently open
- `Sat(F)`: a set of ⟨world, assignment⟩ sequences satisfying the file

Sentences denote *file change potentials*: partial functions from files
to files. Partiality is essential — it models presupposition as
definedness:
- **Novelty**: indefinites require their index NOT in Dom(F)
- **Familiarity**: definites require their index IN Dom(F)

When a precondition fails, the FCP is *undefined*, not empty.

## FCP Rules (@cite{heim-1982}, Ch III §1.5)

| Connective | FCP |
|------------|-----|
| Atomic P(x₁,...,xₙ) | Filter Sat(F) by the predicate |
| φ ∧ ψ | (F + φ) + ψ (sequential update) |
| ¬φ | {s ∈ Sat(F) \| s ∉ Sat(F + φ)} |
| if φ then ψ | F + ¬(φ ∧ ¬ψ) |
| ∃x.φ (indefinite) | Extend Dom by x, widen Sat, then update with φ |

## Truth (@cite{heim-1982}, Ch III §3)

φ is true in F iff F + φ = F (truth as idempotency of update).

## Relation to Core Infrastructure

| This Module | `Semantics.Dynamic.Core` |
|-------------|------------------------|
| `HeimFile` | `Context W E` (enriched with dom/sat structure) |
| `FCP` (partial) | `CCP` (total) |
| novelty guard | `InfoState.novelAt` |
| familiarity guard | `InfoState.definedAt` |
-/

namespace Semantics.Dynamic.FileChangeSemantics

open Semantics.Dynamic.Core
open Classical

-- ════════════════════════════════════════════════════
-- § 1. Files (@cite{heim-1982}, Ch III)
-- ════════════════════════════════════════════════════

/-- A Heim File: ⟨Dom(F), Sat(F)⟩.

`Dom(F)` is the set of discourse referent indices currently active.
`Sat(F)` is the set of ⟨world, assignment⟩ possibilities satisfying
the file's conditions.

This captures @cite{heim-1982}'s formal definition of a file as a
structured pair, not merely a flat set of possibilities. The domain
tracks which variables carry information — the key structural
innovation over bare info states. -/
structure HeimFile (W : Type*) (E : Type*) where
  /-- Domain: the set of active discourse referent indices. -/
  dom : Set Nat
  /-- Satisfaction set: possibilities consistent with the file. -/
  sat : InfoState W E

/-- A File Change Potential: a partial function from files to files.

@cite{heim-1982}'s central semantic type. Partiality (modeled via
`Option`) captures presupposition-as-definedness: when a novelty or
familiarity precondition fails, the FCP returns `none` rather than
an empty file. -/
def FCP (W : Type*) (E : Type*) := HeimFile W E → Option (HeimFile W E)

namespace HeimFile

variable {W E : Type*}

/-- The empty file: no discourse referents, all possibilities. -/
def empty : HeimFile W E where
  dom := ∅
  sat := Set.univ

/-- The absurd file: no possibilities. -/
def absurd (dom : Set Nat) : HeimFile W E where
  dom := dom
  sat := ∅

/-- Variable x is NOVEL in file F iff x ∉ Dom(F).

@cite{heim-1982}'s Novelty Condition: an indefinite NP with index x
is felicitous only if x has not yet been used. -/
def novel (F : HeimFile W E) (x : Nat) : Prop :=
  x ∉ F.dom

/-- Variable x is FAMILIAR in file F iff x ∈ Dom(F).

@cite{heim-1982}'s Familiarity Condition: a definite NP with index x
is felicitous only if x is already in the domain. -/
def familiar (F : HeimFile W E) (x : Nat) : Prop :=
  x ∈ F.dom

/-- A file is consistent (non-absurd) iff its satisfaction set is non-empty. -/
def consistent (F : HeimFile W E) : Prop :=
  F.sat.Nonempty

/-- Project to the underlying `InfoState`. -/
def toInfoState (F : HeimFile W E) : InfoState W E := F.sat

/-- Build a `HeimFile` from a `Context`. -/
def ofContext (c : Context W E) : HeimFile W E where
  dom := c.definedVars
  sat := c.state

/-- Novelty and familiarity are complementary. -/
theorem novel_iff_not_familiar (F : HeimFile W E) (x : Nat) :
    F.novel x ↔ ¬F.familiar x := Iff.rfl

end HeimFile

-- ════════════════════════════════════════════════════
-- § 2. File Change Potentials (@cite{heim-1982}, Ch III §1.5)
-- ════════════════════════════════════════════════════

namespace FCP

variable {W E : Type*}

/-- Atomic predicate update: filter satisfaction set by predicate.

F + [P(x₁,...,xₙ)] = ⟨Dom(F), {s ∈ Sat(F) | P holds of s}⟩

Domain is unchanged; only the satisfaction set shrinks. -/
def atom (pred : Possibility W E → Prop) : FCP W E :=
  λ F => some { dom := F.dom, sat := { p ∈ F.sat | pred p } }

/-- Atomic predicate on world only. -/
def atomW (pred : W → Prop) : FCP W E :=
  atom (λ p => pred p.world)

/-- Atomic predicate on assignment at variable x. -/
def atomVar (pred : E → Prop) (x : Nat) : FCP W E :=
  atom (λ p => pred (p.assignment x))

/-- Binary predicate on two variables. -/
def atomVar2 (pred : E → E → Prop) (x y : Nat) : FCP W E :=
  atom (λ p => pred (p.assignment x) (p.assignment y))

/-- Sequential composition (conjunction): F + [φ ∧ ψ] = (F + φ) + ψ.

@cite{heim-1982}'s successive file change. If either step is
undefined (presupposition failure), the whole is undefined. -/
def seq (φ ψ : FCP W E) : FCP W E :=
  λ F => (φ F).bind ψ

infixl:70 " +> " => seq

/-- Negation: F + [¬φ] = ⟨Dom(F), {s ∈ Sat(F) | s ∉ Sat(F + φ)}⟩.

@cite{heim-1982}'s per-element negation: keep assignments from Sat(F)
that do NOT survive the update with φ. The domain is preserved —
negation is a test that doesn't introduce new drefs.

If φ is undefined on F (presupposition failure in the scope of
negation), the negation is also undefined. -/
noncomputable def neg (φ : FCP W E) : FCP W E :=
  λ F => match φ F with
    | none => none
    | some F' => some { dom := F.dom
                      , sat := { p ∈ F.sat | p ∉ F'.sat } }

/-- Conditional: F + [if φ then ψ] = F + [¬(φ ∧ ¬ψ)].

@cite{heim-1982}'s analysis of conditionals as negated conjunctions
of the antecedent with the negated consequent. -/
noncomputable def cond (φ ψ : FCP W E) : FCP W E :=
  neg (seq φ (neg ψ))

/-- Indefinite introduction: F + [∃x.φ].

Defined only if x is NOVEL in F (the Novelty Condition). When
defined:
1. Extend Dom(F) by x
2. Widen Sat(F) to all re-assignments of x (random assignment)
3. Update with the body φ

This is Heim's key innovation: indefinites don't quantify, they
*change the file structure* by opening a new file card. -/
noncomputable def indef (x : Nat) (body : FCP W E) : FCP W E :=
  λ F => if F.novel x then
    let F' : HeimFile W E :=
      { dom := F.dom ∪ {x}
      , sat := F.sat.randomAssignFull x }
    body F'
  else
    none

/-- Definite reference: F + [the x. φ].

Defined only if x is FAMILIAR in F (the Familiarity Condition).
When defined, updates with the body φ without changing the domain
structure — the dref is already established.

@cite{heim-1982}'s familiarity theory of definiteness. -/
noncomputable def def_ (x : Nat) (body : FCP W E) : FCP W E :=
  λ F => if F.familiar x then body F else none

/-- Identity FCP: no change. -/
def id : FCP W E := λ F => some F

/-- Absurd FCP: always undefined (total presupposition failure). -/
def fail : FCP W E := λ _ => none

end FCP

-- ════════════════════════════════════════════════════
-- § 3. Truth and Entailment (@cite{heim-1982}, Ch III §3)
-- ════════════════════════════════════════════════════

section Truth

variable {W E : Type*}

/-- φ is true in F iff F + φ is defined and equals F.

@cite{heim-1982}'s truth definition: truth is idempotency of
update. A file already "knows" φ iff updating with φ changes
nothing. -/
def trueIn (F : HeimFile W E) (φ : FCP W E) : Prop :=
  φ F = some F

/-- φ is satisfiable in F iff F + φ is defined and consistent. -/
def satisfiable (F : HeimFile W E) (φ : FCP W E) : Prop :=
  ∃ F', φ F = some F' ∧ F'.consistent

/-- F entails φ iff F + φ = F (same as truth). -/
def fileEntails (F : HeimFile W E) (φ : FCP W E) : Prop :=
  trueIn F φ

/-- φ semantically entails ψ iff for all files F, if F + φ is defined
then F + φ + ψ = F + φ. -/
def fcpEntails (φ ψ : FCP W E) : Prop :=
  ∀ F : HeimFile W E, ∀ F' : HeimFile W E,
    φ F = some F' → FCP.seq φ ψ F = φ F

end Truth

-- ════════════════════════════════════════════════════
-- § 4. Theorems
-- ════════════════════════════════════════════════════

section Theorems

variable {W E : Type*}

/-- Sequential composition is associative. -/
theorem seq_assoc (φ ψ χ : FCP W E) :
    FCP.seq (FCP.seq φ ψ) χ = FCP.seq φ (FCP.seq ψ χ) := by
  funext F
  simp only [FCP.seq]
  cases φ F <;> rfl

/-- Identity is left unit for sequential composition. -/
theorem id_seq (φ : FCP W E) : FCP.seq FCP.id φ = φ := by
  funext F; simp [FCP.seq, FCP.id, Option.bind]

/-- Identity is right unit for sequential composition. -/
theorem seq_id (φ : FCP W E) : FCP.seq φ FCP.id = φ := by
  funext F; simp [FCP.seq]
  cases φ F <;> rfl

/-- Atomic updates preserve the domain. -/
theorem atom_preserves_dom (pred : Possibility W E → Prop) (F : HeimFile W E) :
    (FCP.atom pred F).map (·.dom) = some F.dom := by
  simp [FCP.atom]

/-- Negation preserves the domain. -/
theorem neg_preserves_dom (φ : FCP W E) (F F' : HeimFile W E)
    (h : FCP.neg φ F = some F') : F'.dom = F.dom := by
  simp only [FCP.neg] at h
  split at h
  · exact absurd h (by simp)
  · rename_i F'' _
    simp at h
    rw [← h]

/-- Indefinite is undefined when variable is familiar (not novel). -/
theorem indef_familiar_none (x : Nat) (body : FCP W E) (F : HeimFile W E)
    (h : F.familiar x) : FCP.indef x body F = none :=
  if_neg (show ¬F.novel x from fun hn => hn h)

/-- Definite is undefined when variable is novel (not familiar). -/
theorem def_novel_none (x : Nat) (body : FCP W E) (F : HeimFile W E)
    (h : F.novel x) : FCP.def_ x body F = none :=
  if_neg (show ¬F.familiar x from h)

/-- The intermediate file passed to the body of an indefinite
has x in its domain. -/
theorem indef_intermediate_has_x (x : Nat) (F : HeimFile W E) :
    x ∈ (HeimFile.mk (F.dom ∪ {x}) (F.sat.randomAssignFull x) : HeimFile W E).dom :=
  Set.mem_union_right _ rfl

/-- Conditional is definable from negation and conjunction. -/
theorem cond_eq (φ ψ : FCP W E) :
    FCP.cond φ ψ = FCP.neg (FCP.seq φ (FCP.neg ψ)) := rfl

/-- Atomic update is eliminative: Sat(F + P) ⊆ Sat(F). -/
theorem atom_eliminative (pred : Possibility W E → Prop)
    (F : HeimFile W E) (F' : HeimFile W E)
    (h : FCP.atom pred F = some F') :
    F'.sat ⊆ F.sat := by
  simp [FCP.atom] at h
  intro p hp
  rw [← h] at hp
  exact hp.1

/-- Truth is idempotency: if φ is true in F, then updating again
does nothing. -/
theorem true_idempotent (F : HeimFile W E) (φ : FCP W E)
    (h : trueIn F φ) : FCP.seq φ φ F = φ F := by
  simp only [FCP.seq, trueIn] at *
  rw [h]
  simp [h]

end Theorems

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Core Infrastructure
-- ════════════════════════════════════════════════════

section Bridge

variable {W E : Type*}

/-- Lift a total CCP to a (total) FCP that preserves domain. -/
def liftCCP (u : CCP (Possibility W E)) : FCP W E :=
  λ F => some { dom := F.dom, sat := u F.sat }

/-- Lift preserves sequential composition. -/
theorem liftCCP_seq (u v : CCP (Possibility W E)) :
    liftCCP (CCP.seq u v) = FCP.seq (liftCCP u) (liftCCP v) := by
  funext F
  simp [liftCCP, FCP.seq, CCP.seq]

/-- Extract the satisfaction set from the result of an FCP. -/
def resultSat (φ : FCP W E) (F : HeimFile W E) : Option (InfoState W E) :=
  (φ F).map (·.sat)

end Bridge

end Semantics.Dynamic.FileChangeSemantics
