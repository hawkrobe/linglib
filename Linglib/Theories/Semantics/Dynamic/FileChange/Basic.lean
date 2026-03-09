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

## FCP Rules (@cite{heim-1982}, Ch III §2.1)

| Connective | FCP |
|------------|-----|
| Atomic P(x₁,...,xₙ) | Filter Sat(F) by the predicate |
| φ ∧ ψ | (F + φ) + ψ (sequential update) |
| ¬φ | {s ∈ Sat(F) \| s ∉ Sat(F + φ)} |
| if φ then ψ | F + ¬(φ ∧ ¬ψ) |
| ∃x.φ (indefinite) | Extend Dom by x, widen Sat, then update with φ |

**Design note on atomic domain expansion.** @cite{heim-1982}'s rule (i'')
specifies that atomic updates *expand* the domain: Dom(F + φ) = Dom(F) ∪
{i₁,...,iₙ}. We follow the modern convention (shared by DRT and DPL) where
domain expansion is handled solely by the indefinite operator (`indef`),
and atomic predicates preserve the domain. This simplifies the algebra
without affecting truth conditions, since in practice every variable
mentioned in an atomic predicate has already been introduced by an
indefinite or a definite.

## Truth (@cite{heim-1982}, Ch III §3.2, criterion (C))

φ is true w.r.t. F iff F + φ is defined and Sat(F + φ) is nonempty.
This is *not* idempotency — it is a weaker condition that builds
existential quantification into the notion of truth itself.

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
@[ext]
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

/-- A file is consistent (non-absurd) iff its satisfaction set is non-empty.

File truth in @cite{heim-1982} (Ch III §1.2): "F is true iff there
is at least one sequence a_N such that a_N ∈ Sat(F)." -/
def consistent (F : HeimFile W E) : Prop :=
  F.sat.Nonempty

/-- Card i in F refers to entity x iff every satisfying sequence
assigns x to position i.

@cite{heim-1982} (Ch III §2.3, p. 207): "Card i in F refers to x
iff, for all a_N ∈ Sat(F), a_i = x." -/
def refersTo (F : HeimFile W E) (i : Nat) (x : E) : Prop :=
  ∀ p ∈ F.sat, p.assignment i = x

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
-- § 2. File Change Potentials (@cite{heim-1982}, Ch III §2.1)
-- ════════════════════════════════════════════════════

namespace FCP

variable {W E : Type*}

/-- Atomic predicate update: filter satisfaction set by predicate.

F + [P(x₁,...,xₙ)] = ⟨Dom(F), {s ∈ Sat(F) | P holds of s}⟩

Domain is unchanged; only the satisfaction set shrinks.

**Note:** @cite{heim-1982}'s rule (i'') on p. 198 specifies that atomic
updates also expand the domain: Dom(F + φ) = Dom(F) ∪ {i₁,...,iₙ}.
We follow the modern convention where domain expansion is handled
by `indef` only. This is equivalent in practice because every variable
in an atomic predicate has been previously introduced. -/
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

/-- φ is true w.r.t. F iff F + φ is defined and the result is
a consistent (true) file.

This is @cite{heim-1982}'s truth criterion (C) (Ch III §3.2, p. 214):
"A formula φ is true w.r.t. a file F if F + φ is true" — where a file
is true iff Sat(F) ≠ ∅. Existential quantification is built into the
notion of truth itself: indefinites need not be explicitly bound by ∃. -/
def trueIn (F : HeimFile W E) (φ : FCP W E) : Prop :=
  ∃ F', φ F = some F' ∧ F'.consistent

/-- φ is false w.r.t. F iff F + φ is defined but the result is
an inconsistent (absurd) file.

@cite{heim-1982}'s criterion (C): "false w.r.t. F if F + φ is false." -/
def falseIn (F : HeimFile W E) (φ : FCP W E) : Prop :=
  ∃ F', φ F = some F' ∧ ¬F'.consistent

/-- F supports φ iff F + φ = F (idempotency of update).

This is the dynamic notion of entailment/support: F already "knows" φ
iff updating with φ changes nothing. This is stronger than truth —
support implies truth (when F is consistent) but not vice versa.

Note: this is sometimes called "truth as idempotency" in the update
semantics literature (@cite{veltman-1996}), but it is NOT
@cite{heim-1982}'s truth definition, which is the weaker `trueIn`. -/
def supports (F : HeimFile W E) (φ : FCP W E) : Prop :=
  φ F = some F

/-- F entails φ iff F supports φ (F + φ = F). -/
def fileEntails (F : HeimFile W E) (φ : FCP W E) : Prop :=
  supports F φ

/-- φ semantically entails ψ iff for all files F, if F + φ is defined
then F + φ supports ψ. -/
def fcpEntails (φ ψ : FCP W E) : Prop :=
  ∀ F : HeimFile W E, ∀ F' : HeimFile W E,
    φ F = some F' → supports F' ψ

/-- φ is defined on F (the update doesn't trigger presupposition failure). -/
def definedOn (F : HeimFile W E) (φ : FCP W E) : Prop :=
  ∃ F', φ F = some F'

/-- Truth implies definedness. -/
theorem trueIn_definedOn (F : HeimFile W E) (φ : FCP W E)
    (h : trueIn F φ) : definedOn F φ :=
  ⟨h.choose, h.choose_spec.1⟩

/-- Support implies truth for consistent files. -/
theorem supports_trueIn (F : HeimFile W E) (φ : FCP W E)
    (hsup : supports F φ) (hcons : F.consistent) : trueIn F φ :=
  ⟨F, hsup, hcons⟩

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

/-- Atomic update is eliminative: Sat(F + P) ⊆ Sat(F).

This is @cite{heim-1982}'s Principle (A): information only grows
(possibilities only decrease). -/
theorem atom_eliminative (pred : Possibility W E → Prop)
    (F : HeimFile W E) (F' : HeimFile W E)
    (h : FCP.atom pred F = some F') :
    F'.sat ⊆ F.sat := by
  simp [FCP.atom] at h
  intro p hp
  rw [← h] at hp
  exact hp.1

/-- Negation is eliminative: Sat(F + ¬φ) ⊆ Sat(F). -/
theorem neg_eliminative (φ : FCP W E) (F F' : HeimFile W E)
    (h : FCP.neg φ F = some F') :
    F'.sat ⊆ F.sat := by
  simp only [FCP.neg] at h
  split at h
  · exact absurd h (by simp)
  · rename_i F'' _
    simp at h
    intro p hp
    rw [← h] at hp
    exact hp.1

/-- Sequential composition of eliminative FCPs is eliminative. -/
theorem seq_eliminative (φ ψ : FCP W E)
    (hφ : ∀ F F', φ F = some F' → F'.sat ⊆ F.sat)
    (hψ : ∀ F F', ψ F = some F' → F'.sat ⊆ F.sat)
    (F F' : HeimFile W E) (h : FCP.seq φ ψ F = some F') :
    F'.sat ⊆ F.sat := by
  simp only [FCP.seq, Option.bind] at h
  cases hφF : φ F with
  | none => rw [hφF] at h; exact absurd h (by simp)
  | some F₁ =>
    rw [hφF] at h
    simp at h
    intro p hp
    exact hφ F F₁ hφF (hψ F₁ F' h hp)

/-- Domain monotonicity for definite updates: when the body preserves
the domain, so does the definite FCP. -/
theorem def_preserves_dom (x : Nat) (body : FCP W E)
    (hbody : ∀ G G', body G = some G' → G'.dom = G.dom)
    (F F' : HeimFile W E) (h : FCP.def_ x body F = some F') :
    F'.dom = F.dom := by
  simp only [FCP.def_] at h
  split at h
  · exact hbody F F' h
  · exact absurd h (by simp)

/-- Support is idempotent: if F supports φ, then updating twice is
the same as once. -/
theorem supports_idempotent (F : HeimFile W E) (φ : FCP W E)
    (h : supports F φ) : FCP.seq φ φ F = φ F := by
  simp only [FCP.seq, supports] at *
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

/-- Lifted CCPs are always defined (total). -/
theorem liftCCP_definedOn (u : CCP (Possibility W E)) (F : HeimFile W E) :
    definedOn F (liftCCP u) :=
  ⟨{ dom := F.dom, sat := u F.sat }, rfl⟩

/-- Extract the satisfaction set from the result of an FCP. -/
def resultSat (φ : FCP W E) (F : HeimFile W E) : Option (InfoState W E) :=
  (φ F).map (·.sat)

-- ─── DynProp bridge ───

/-- Lift a DRS (relational meaning) to an FCP via the relational image.

This connects @cite{heim-1982}'s FCPs to the relational algebra
in `Core.DynProp`. The resulting FCP preserves domain and is always
defined (total). -/
def liftDRS (R : DynProp.DRS (Possibility W E)) : FCP W E :=
  liftCCP (lift R)

/-- `liftDRS` preserves sequential composition: lifting a relational
sequence equals sequencing lifted FCPs.

This shows the FCS algebra homomorphically embeds the DynProp
algebra — the unification underlying @cite{muskens-1996}. -/
theorem liftDRS_seq (R₁ R₂ : DynProp.DRS (Possibility W E)) :
    liftDRS (DynProp.dseq R₁ R₂) = FCP.seq (liftDRS R₁) (liftDRS R₂) := by
  simp only [liftDRS]
  rw [lift_dseq]
  exact liftCCP_seq (lift R₁) (lift R₂)

set_option linter.unusedSimpArgs false in
/-- Atomic FCP equals lifting a test from DynProp.

FCS's `atom pred` = lifting `DynProp.test (λ p => pred p)`. This
shows atomic FCPs are exactly the relational tests, connecting
@cite{heim-1982}'s Principle (A) to the DynProp algebra. -/
theorem atom_eq_liftDRS_test (pred : Possibility W E → Prop) :
    FCP.atom pred = liftDRS (DynProp.test pred) := by
  funext F
  simp only [FCP.atom, liftDRS, liftCCP, lift, DynProp.test]
  congr 1
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, hpred⟩; exact ⟨p, hp, rfl, hpred⟩
  · rintro ⟨i, hi, rfl, hpred⟩; exact ⟨hi, hpred⟩

end Bridge

end Semantics.Dynamic.FileChangeSemantics
