import Mathlib.Data.List.Chain
import Linglib.Theories.Semantics.Plurality.Basic
import Linglib.Theories.Semantics.Plurality.Cumulativity

/-!
# Reciprocal Predicates

Substrate for the reciprocal-meaning typology. The six interpretation
schemes originate in @cite{langendoen-1978} (Strong Reciprocity SR,
Intermediate Reciprocity IR, Weak Reciprocity WR), Kański 1987 (bib
entry pending; Inclusive Alternative Ordering IAO), Fiengo & Lasnik
1973 (bib entry pending; Partitioned Strong Reciprocity PartSR), and
@cite{dalrymple-et-al-1998} (the **Alternative** variants SAR/IAR plus
One-way Weak Reciprocity OWR as a methodological waypoint between WR
and IAO). DKMPK 1998 organises them along two axes — **quantification
strength** (∀∀ / ∃-chain / ∃∃) and **directionality** (one-way vs
alternative `R x y ∨ R y x`) — and proposes the **Strongest Meaning
Hypothesis** (SMH): interpretation selects the strongest scheme
consistent with context. The substrate here exposes the six schemes,
the entailment lattice between the bivalent versions, and a bridge to
`Cumulativity.Cumulative` for WR. SMH itself is left as a Todo.

## Main declarations

* `ReciprocalScheme` — the six-cell typology, named.
* `StrongReciprocity` — every distinct pair satisfies `R`.
* `PartitionedStrongReciprocity` — there is a partition of `X` such
  that SR holds within each cell.
* `IntermediateReciprocity` — every distinct pair is connected by an
  `R`-chain.
* `WeakReciprocity` — every member is `R`-related to a distinct other
  *in both directions*.
* `OneWayWeakReciprocity` — only the first direction of WR.
* `InclusiveAlternativeOrdering` — every member participates in `R`
  either as subject or as object of a distinct other.
* `strong_imp_weak`, `weak_imp_oneWay`, `oneWay_imp_inclusiveAlternative`,
  `strong_imp_inclusiveAlternative` — the entailment lattice
  (@cite{beck-2001} eq 28 right-hand spine).
* `weakReciprocity_iff_cumulative_strict` — WR factors through
  `Cumulative` of the strict-distinct relation (Beck eq 120 /
  @cite{sternefeld-1998} eq 26b, bivalent collapse).

## Implementation notes

The standard DKMPK / Langendoen 1978 form of WR requires both
`∃y ∈ X. y ≠ x ∧ R x y` AND `∃y ∈ X. y ≠ x ∧ R y x` for each
`x ∈ X` — i.e., each member must be both an `R`-subject and an
`R`-object of some distinct other. The single-conjunct version (here:
`OneWayWeakReciprocity`) is empirically too weak; it's named after
Sabato & Winter 2005's terminology.

`IntermediateReciprocity` uses `List.IsChain` on a list of atoms in `X`
to express "connected by an `R`-chain"; `PartitionedStrongReciprocity`
uses `Finset (Finset α)` for the partition witness.

## Todo

* Strong/Weak/Intermediate **Alternative** schemes (`R y x ∨ R x y`
  variants): SAR, IAR.
* Strongest Meaning Hypothesis as an interpretation operator selecting
  among schemes given context.
* Add bib entries: Kański 1987, Fiengo & Lasnik 1973, Sabato & Winter
  2005.
-/

namespace Semantics.Plurality.Reciprocal

open Semantics.Plurality
open Semantics.Plurality.Cumulativity

variable {A : Type*}

/-- The six reciprocal interpretation schemes. SR/IR/WR originate in
    @cite{langendoen-1978}; IAO in Kański 1987 (bib entry pending);
    Partitioned SR in Fiengo & Lasnik 1973 (bib entry pending); the
    **Alternative** variants (SAR, IAR) in @cite{dalrymple-et-al-1998}. -/
inductive ReciprocalScheme where
  | strong                  -- Strong Reciprocity (SR)
  | partitionedStrong       -- Partitioned Strong Reciprocity (PartSR)
  | intermediate            -- Intermediate Reciprocity (IR)
  | weak                    -- Weak Reciprocity (WR)
  | oneWayWeak              -- One-way Weak Reciprocity (OWR)
  | inclusiveAlternative    -- Inclusive Alternative Ordering (IAO)
  deriving DecidableEq, Repr

/-! ### Strong Reciprocity -/

/-- **Strong Reciprocity**: every distinct pair in `X` satisfies `R`.
    "The students all know each other": every student knows every
    other student. -/
def StrongReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, y ≠ x → R x y

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (StrongReciprocity R X) := by
  unfold StrongReciprocity; infer_instance

/-! ### Partitioned Strong Reciprocity -/

/-- **Partitioned Strong Reciprocity** (Fiengo & Lasnik 1973, bib entry
    pending): there is a partition of `X` such that SR holds within
    each cell. "The men are hitting each other" can be true if the men
    team up in pairs that stand in the hit-relation. -/
def PartitionedStrongReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ PART : Finset (Finset A),
    (∀ Y ∈ PART, Y ⊆ X) ∧
    (∀ a ∈ X, ∃ Y ∈ PART, a ∈ Y) ∧
    (∀ Y ∈ PART, ∀ x ∈ Y, ∀ y ∈ Y, y ≠ x → R x y)

/-! ### Intermediate Reciprocity -/

/-- **Intermediate Reciprocity** (Langendoen 1978): any two distinct
    members of `X` are connected by an `R`-chain through `X`. "Five
    Boston pitchers sat alongside each other": each pitcher has an
    `R`-chain to every other pitcher.

    Uses `List.Chain'` over a non-empty list of `X`-elements whose head
    is `x` and whose last element is `y`. -/
def IntermediateReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, y ≠ x →
    ∃ chain : List A, chain.head? = some x ∧ chain.getLast? = some y ∧
      (∀ z ∈ chain, z ∈ X) ∧ chain.IsChain R

/-! ### Weak Reciprocity -/

/-- **Weak Reciprocity** (Langendoen 1978; DKMPK 1998): every member of
    `X` is `R`-related to at least one distinct other member **in both
    directions** — as `R`-subject and as `R`-object. "The boys are
    stacked on top of each other": each boy has *some* other boy on
    top of him AND is on top of *some* other boy.

    Definitionally identical to `Cumulative (R ∧ ≠) X X` (see
    `weakReciprocity_iff_cumulative_strict`). -/
def WeakReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  (∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y) ∧ (∀ y ∈ X, ∃ x ∈ X, R x y ∧ x ≠ y)

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (WeakReciprocity R X) := by
  unfold WeakReciprocity; infer_instance

/-! ### One-way Weak Reciprocity -/

/-- **One-way Weak Reciprocity** (Sabato & Winter 2005 terminology):
    only the first direction of WR is required. "The pirates are
    staring at each other" — pirate 6 is not stared at by anybody, but
    everyone stares at someone. -/
def OneWayWeakReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (OneWayWeakReciprocity R X) := by
  unfold OneWayWeakReciprocity; infer_instance

/-! ### Inclusive Alternative Ordering -/

/-- **Inclusive Alternative Ordering** (Kański 1987, bib entry pending):
    each member of `X` participates in `R` as either first or second
    argument of a distinct other. "The plates are stacked on top of
    each other" — each plate is on top of one or has one on top of
    itself. -/
def InclusiveAlternativeOrdering (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∃ y ∈ X, x ≠ y ∧ (R x y ∨ R y x)

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (InclusiveAlternativeOrdering R X) := by
  unfold InclusiveAlternativeOrdering; infer_instance

/-! ### Entailment lattice (Beck 2001 eq 28, right-hand spine) -/

/-- Strong Reciprocity entails Weak Reciprocity, on pluralities of
    cardinality ≥ 2 (so a distinct witness exists). -/
theorem strong_imp_weak [DecidableEq A]
    (R : A → A → Prop) (X : Finset A)
    (hcard : 2 ≤ X.card) (hSR : StrongReciprocity R X) :
    WeakReciprocity R X := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    exact ⟨y, hy, hSR x hx y hy hyx, hyx.symm⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    exact ⟨y, hy, hSR y hy x hx hyx.symm, hyx⟩

/-- Weak Reciprocity entails One-way Weak Reciprocity (projection on
    the first conjunct). -/
theorem weak_imp_oneWay (R : A → A → Prop) (X : Finset A)
    (hWR : WeakReciprocity R X) : OneWayWeakReciprocity R X :=
  hWR.1

/-- One-way Weak Reciprocity entails Inclusive Alternative Ordering. -/
theorem oneWay_imp_inclusiveAlternative (R : A → A → Prop) (X : Finset A)
    (hOWR : OneWayWeakReciprocity R X) :
    InclusiveAlternativeOrdering R X := by
  intro x hx
  obtain ⟨y, hy, hRxy, hxy⟩ := hOWR x hx
  exact ⟨y, hy, hxy, Or.inl hRxy⟩

/-- Composition: SR entails IAO via the right-hand spine
    `SR → WR → OWR → IAO`. -/
theorem strong_imp_inclusiveAlternative [DecidableEq A]
    (R : A → A → Prop) (X : Finset A) (hcard : 2 ≤ X.card)
    (hSR : StrongReciprocity R X) :
    InclusiveAlternativeOrdering R X :=
  oneWay_imp_inclusiveAlternative R X
    (weak_imp_oneWay R X (strong_imp_weak R X hcard hSR))

/-! ### Cumulativity bridge -/

/-- **Weak Reciprocity factors through `Cumulative`**: Beck-Sauerland's
    `**` applied to the strict-distinct verb relation
    `λ a b. R a b ∧ a ≠ b` on `(X, X)` recovers Weak Reciprocity
    definitionally. This is the substrate-level form of
    @cite{beck-2001} eq 120 / @cite{sternefeld-1998} eq 26b (bivalent
    collapse). The Beck/Sternefeld trivalent disagreement is invisible
    here — both reduce to the same proposition under bivalent
    encoding. -/
theorem weakReciprocity_iff_cumulative_strict
    (R : A → A → Prop) (X : Finset A) :
    WeakReciprocity R X ↔
    Cumulative (fun a b => R a b ∧ a ≠ b) X X := Iff.rfl

/-- Forward weakening: WR truth conditions entail bare
    `Cumulative R X X` (dropping the strict-distinct conjunct). This
    is *strictly weaker* than either Beck eq 120 or Sternefeld eq 26b,
    both of which keep the distinctness clause inside the relation
    argument. -/
theorem weakReciprocity_imp_cumulative
    (R : A → A → Prop) (X : Finset A)
    (hWR : WeakReciprocity R X) :
    Cumulative R X X := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hRxy, _⟩ := hWR.1 x hx
    exact ⟨y, hy, hRxy⟩
  · intro y hy
    obtain ⟨x, hx, hRxy, _⟩ := hWR.2 y hy
    exact ⟨x, hx, hRxy⟩

end Semantics.Plurality.Reciprocal
