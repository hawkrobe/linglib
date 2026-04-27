import Linglib.Core.Question.Basic
import Linglib.Theories.Semantics.Questions.Resolution
import Linglib.Theories.Semantics.Questions.Exhaustivity

/-!
# @cite{fox-2018}: Partition by Exhaustification: Comments on Dayal 1996
@cite{dayal-1996} @cite{heim-1994} @cite{groenendijk-stokhof-1984} @cite{spector-2008}

Single-paper formalisation of @cite{fox-2018}, "Partition by
Exhaustification: Comments on Dayal 1996" (ZAS Papers in Linguistics
60 / Sinn und Bedeutung 22). Fox derives Dayal's maximality
presupposition from the demand that question denotations *partition*
the Stalnakerian context-set via point-wise exhaustification of the
question's Hamblin members.

## Substrate identifications

Fox's central operator is the `Exh`-derived **cell identifier**: the
set of worlds where a given proposition `p` is the maximally
informative true Hamblin alternative.

| @cite{fox-2018}                        | substrate                         |
|----------------------------------------|-----------------------------------|
| `Exh(Q,p) = λw. w∈p ∧ ∀q∈Q[w∈q → p⊆q]` (eq 11) | `{w | IsStrongestTrueAnswer Q w p}` |
| `Max_inf(Q,w)` (eq 9b)                 | the unique `p` with `IsStrongestTrueAnswer Q w p` (when EP holds) |
| `Partition_L(Q)` (eq 3)                | logical partition by `strongAnswer`-equivalence |
| `Partition_C(Q,A)` (eq 10)             | contextual partition (A-restricted) |
| Dayal's `Ans_D` presupposition         | `IsExhaustivelyResolvable` (Exhaustivity.lean) |
| **Cell Identification (CI)** (eq 19)   | `CellIdentification` defined here |
| **Non-Vacuity (NV)** (eq 20b)          | `NonVacuity` defined here         |
| **Question Partition Matching (QPM)** (eq 20) | `QPM = CI ∧ NV`              |

## Section coverage

* **§1.1** Question duality (partition vs Hamblin set) — captured by
  the substrate's `Question W = LowerSet (Set W)` (Hamblin shape) and
  `strongAnswer Q w` (the partition view as equivalence classes).
* **§1.2** Dayal's solution — `IsExhaustivelyResolvable` is already
  the substrate's predicate; `Exh` here connects it to Fox's
  partition-by-exhaustification view.
* **§1.3** Empirical evidence (singular *wh* inferences, negative
  islands) — paper-anchored prose; substrate captures the
  uniqueness/existence inferences via `IsStrongestTrueAnswer`.
* **§1.4** Interim summary — defines `CI` and `QPM`; both are formalised
  here.
* **§2.1** Mention-some challenge — `Ans_D` over-restricts;
  `IsExhaustivelyResolvable` fails for MS questions (`where can I
  get gas in Cambridge`).
* **§2.2** Higher-order quantification (Spector 2008) — requires
  generalised-quantifier *wh*-restrictors over UE quantifiers;
  deferred to a future Spector 2008 study file.
* **§3** Over-generation + QPM — formalised here.
* **§4** Alternative `Exh` definition (Bar-Lev & Fox 2017 free-choice
  conjunctive `Exh`) — requires free-choice machinery; deferred.

## What this file does NOT cover

* The Free-Choice / scalar-implicature interpretation of `Exh` (Krifka
  1995 / Bar-Lev & Fox 2017): the substrate's `Exh` here is the
  *strongest-true-answer* set, not the formula-level FC operator.
* Negative islands as Maximality Failure (Fox & Hackl 2006; Abrusán
  2007/2014): require degree-question / dense-domain machinery.
* The §6 type-shift and §7 MS-distribution predictions: paper-internal
  empirical claims about distribution of higher-order interpretations.
-/

namespace Phenomena.Questions.Studies.Fox2018

open Core Core.Question Semantics.Questions.Resolution
open Semantics.Questions.Exhaustivity

variable {W : Type*}

/-! ### §1 Exh-derived cells (eq 11) — substrate-level primitives

Fox's `Exh(Q,p)` and `Partition_L(Q)` are substrate primitives now —
see `Theories/Semantics/Questions/Exhaustivity.lean::exhCell` and
`exhaustifiedPartition`. We re-export them here under Fox's names for
paper-faithfulness, and define the paper-specific contextual variant
locally. -/

/-- @cite{fox-2018} (11): the **Exh-cell** of proposition `p` in
    question `Q`. Substrate primitive `exhCell` re-exported under
    Fox's notation. -/
abbrev Exh (Q : Question W) (p : Set W) : Set W := exhCell Q p

/-! ### §1.1 Logical and contextual partitions (eq 3, eq 10) -/

/-- @cite{fox-2018} (3): the **Logical Partition** of `Q`. Substrate
    primitive `exhaustifiedPartition` re-exported under Fox's notation. -/
abbrev LogicalPartition (Q : Question W) : Set (Set W) :=
  exhaustifiedPartition Q

/-- @cite{fox-2018} (10): the **Contextual Partition** of `Q` over
    context-set `A` — the Logical Partition cells intersected with `A`.
    Paper-specific variant; the substrate primitive `exhaustifiedPartition`
    is the unrestricted form. -/
def ContextualPartition (Q : Question W) (A : Set W) : Set (Set W) :=
  {C | ∃ w ∈ A, C = strongAnswer Q w ∩ A}

theorem mem_ContextualPartition (Q : Question W) (A : Set W) (C : Set W) :
    C ∈ ContextualPartition Q A ↔ ∃ w ∈ A, C = strongAnswer Q w ∩ A :=
  Iff.rfl

/-! ### §1.4 Cell Identification, Non-Vacuity, QPM (eq 19, eq 20) -/

/-- @cite{fox-2018} (19): **Cell Identification (CI)** — every cell
    in `Partition_C(Q, A)` is identifiable by some `Exh(Q, p)`
    intersected with `A`. -/
def CellIdentification (Q : Question W) (A : Set W) : Prop :=
  ∀ C ∈ ContextualPartition Q A, ∃ p ∈ alt Q, C = Exh Q p ∩ A

/-- @cite{fox-2018} (20b): **Non-Vacuity (NV)** — every alternative
    `p ∈ alt Q` identifies *some* cell of `Partition_C(Q, A)`. -/
def NonVacuity (Q : Question W) (A : Set W) : Prop :=
  ∀ p ∈ alt Q, Exh Q p ∩ A ≠ ∅ → ∃ C ∈ ContextualPartition Q A, C = Exh Q p ∩ A

/-- @cite{fox-2018} (20): **Question Partition Matching (QPM)** —
    `Q` and the context-set `A` jointly satisfy CI and NV. -/
def QPM (Q : Question W) (A : Set W) : Prop :=
  CellIdentification Q A ∧ NonVacuity Q A

/-! ### §1.2 Dayal's EP ↔ CI (the central bridge)

Fox's central claim (eq 11–12): when Dayal's maximality presupposition
is met (i.e., every world in `A` has a maximally informative true
answer), the contextual partition is exactly the image of `Exh`.
The substrate-level form of this connection: `IsExhaustivelyResolvable
Q w` for every `w ∈ A` implies `CellIdentification Q A`. -/

/-- @cite{fox-2018} eq (11)→(12): if every world in the context-set
    has a maximally informative true answer, every cell of the
    contextual partition is `Exh`-identifiable. The substrate
    counterpart of the Dayal-EP-implies-CI direction. -/
theorem cellIdentification_of_isExhaustivelyResolvable
    (Q : Question W) (A : Set W)
    (hEP : ∀ w ∈ A, IsExhaustivelyResolvable Q w) :
    CellIdentification Q A := by
  intro C hC
  obtain ⟨w, hwA, rfl⟩ := hC
  obtain ⟨p, hpStrongest⟩ := hEP w hwA
  refine ⟨p, hpStrongest.1, ?_⟩
  ext v
  refine ⟨?_, ?_⟩
  · rintro ⟨hvSA, hvA⟩
    refine ⟨?_, hvA⟩
    -- v ∈ strongAnswer Q w means v decides every alt like w; w ∈ p
    -- with p the strongest true answer; so v ∈ p and p is also
    -- v's strongest true answer (since v ~ w on alts).
    refine ⟨hpStrongest.1, ?_, ?_⟩
    · -- v ∈ p: w ∈ p, v decides p like w
      exact (hvSA p hpStrongest.1).mp hpStrongest.2.1
    · intro q hq hvq
      -- v ∈ q means w ∈ q (by hvSA); then p ⊆ q from w-side.
      have hwq : w ∈ q := (hvSA q hq).mpr hvq
      exact hpStrongest.2.2 q hq hwq
  · rintro ⟨hvSTA, hvA⟩
    refine ⟨?_, hvA⟩
    intro q hq
    refine ⟨?_, ?_⟩
    · -- w ∈ q → v ∈ q: both have p as strongest true answer, so they
      -- agree on every alt.
      intro hwq
      -- w ∈ q ⇒ p ⊆ q (from w-side); also v ∈ p (from v-side); so v ∈ q
      have hpq : p ⊆ q := hpStrongest.2.2 q hq hwq
      exact hpq hvSTA.2.1
    · intro hvq
      have hpq : p ⊆ q := hvSTA.2.2 q hq hvq
      exact hpq hpStrongest.2.1

/-! ### §2.1 Mention-some challenge

@cite{fox-2018} §2.1 (21): "Mary knows where we can get gas in
Cambridge" has an MS reading not derivable from `Ans_D` (which
demands the maximally informative answer). The substrate mirror:
some questions have `¬ IsExhaustivelyResolvable Q w` at the
evaluation world even though they are perfectly answerable in the MS
sense (`Resolves σ Q` succeeds for some non-maximal `p`). -/

/-- A question can fail Dayal's EP at world `w` while still being
    `Resolves`-supported there. The substrate-level distinction
    underlying Fox §2.1's MS challenge. The hypothesis `hp₁p₂ : ¬ p₁ ⊆
    p₂` together with maximality of both alts witnesses the
    incomparability that defeats EP. -/
theorem resolves_can_succeed_when_EP_fails
    (Q : Question W) (w : W) (σ p₁ p₂ : Set W)
    (hp₁ : p₁ ∈ alt Q) (hp₂ : p₂ ∈ alt Q)
    (hwp₁ : w ∈ p₁) (hwp₂ : w ∈ p₂)
    (hp₁p₂ : ¬ p₁ ⊆ p₂)
    (hσp₁ : σ ⊆ p₁) :
    Resolves σ Q ∧ ¬ IsExhaustivelyResolvable Q w := by
  refine ⟨⟨p₁, hp₁, hσp₁⟩, ?_⟩
  rintro ⟨q, hqAlt, hwq, hMin⟩
  have hq_sub_p₁ : q ⊆ p₁ := hMin p₁ hp₁ hwp₁
  have hq_sub_p₂ : q ⊆ p₂ := hMin p₂ hp₂ hwp₂
  have hq_max := hqAlt.2
  have hqp₁ : q = p₁ := hq_max p₁ (alt_subset_props _ hp₁) hq_sub_p₁
  have hqp₂ : q = p₂ := hq_max p₂ (alt_subset_props _ hp₂) hq_sub_p₂
  apply hp₁p₂
  rw [← hqp₁, hqp₂]

end Phenomena.Questions.Studies.Fox2018
