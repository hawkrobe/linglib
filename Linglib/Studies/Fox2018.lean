import Linglib.Semantics.Questions.Basic
import Linglib.Semantics.Questions.Resolution
import Linglib.Semantics.Questions.Exhaustivity

/-!
# [fox-2018]: Partition by Exhaustification: Comments on Dayal 1996
[dayal-1996] [heim-1994] [groenendijk-stokhof-1984] [spector-2008]

Single-paper formalisation of [fox-2018], "Partition by
Exhaustification: Comments on Dayal 1996" (ZAS Papers in Linguistics
60 / Sinn und Bedeutung 22). Fox derives Dayal's maximality
presupposition from the demand that question denotations *partition*
the Stalnakerian context-set via point-wise exhaustification of the
question's Hamblin members.

## Substrate identifications

Fox's central operator is the `Exh`-derived **cell identifier**: the
set of worlds where a given proposition `p` is the maximally
informative true Hamblin alternative.

| [fox-2018]                        | substrate                         |
|----------------------------------------|-----------------------------------|
| `Exh(Q,p) = λw. w∈p ∧ ∀q∈Q[w∈q → p⊆q]` (eq 11) | `exhCell (alt Q) p` |
| `Max_inf(Q,w)` (eq 9b)                 | the unique `p` with `IsStrongestTrueAnswer (alt Q) w p` (when EP holds) |
| `Partition_L(Q)` (eq 3)                | logical partition by `strongAnswer`-equivalence |
| `Partition_C(Q,A)` (eq 10)             | contextual partition (A-restricted) |
| Dayal's `Ans_D` presupposition         | `IsExhaustivelyResolvable` (Exhaustivity.lean) |
| **Cell Identification (CI)** (eq 19)   | `CellIdentification` defined here |
| **Non-Vacuity (NV)** (eq 20b)          | `NonVacuity` defined here         |
| **Question Partition Matching (QPM)** (eq 20) | `QPM = CI ∧ NV`              |

## Section coverage

* **§1.1** Question duality (partition vs Hamblin set) — captured by
  the substrate's `Question W = LowerSet (Set W)` (Hamblin shape) and
  `strongAnswer (alt Q) w` (the partition view as equivalence classes).
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

namespace Fox2018

open Question
open Questions

variable {W : Type*}

/-! ### §1 Exh-derived cells (eq 11) — substrate-level primitives

Fox's `Exh(Q,p)` and `Partition_L(Q)` are substrate primitives now —
see `Semantics/Questions/Exhaustivity.lean::exhCell` and
`exhaustifiedPartition`. We re-export them here under Fox's names for
paper-faithfulness, and define the paper-specific contextual variant
locally. -/

/-- [fox-2018] (11): the **Exh-cell** of proposition `p` in
    question `Q`. Substrate primitive `exhCell` re-exported under
    Fox's notation. -/
abbrev Exh (Q : Question W) (p : Set W) : Set W := exhCell (alt Q) p

/-! ### §1.1 Logical and contextual partitions (eq 3, eq 10) -/

/-- [fox-2018] (3): the **Logical Partition** of `Q`. Substrate
    primitive `exhaustifiedPartition` re-exported under Fox's notation. -/
abbrev LogicalPartition (Q : Question W) : Set (Set W) :=
  exhaustifiedPartition (alt Q)

/-- [fox-2018] (10): the **Contextual Partition** of `Q` over
    context-set `A` — the Logical Partition cells intersected with `A`.
    Paper-specific variant; the substrate primitive `exhaustifiedPartition`
    is the unrestricted form. -/
def ContextualPartition (Q : Question W) (A : Set W) : Set (Set W) :=
  {C | ∃ w ∈ A, C = strongAnswer (alt Q) w ∩ A}

theorem mem_ContextualPartition (Q : Question W) (A : Set W) (C : Set W) :
    C ∈ ContextualPartition Q A ↔ ∃ w ∈ A, C = strongAnswer (alt Q) w ∩ A :=
  Iff.rfl

/-! ### §1.4 Cell Identification, Non-Vacuity, QPM (eq 19, eq 20) -/

/-- [fox-2018] (19): **Cell Identification (CI)** — every cell
    in `Partition_C(Q, A)` is identifiable by some `Exh(Q, p)`
    intersected with `A`. -/
def CellIdentification (Q : Question W) (A : Set W) : Prop :=
  ∀ C ∈ ContextualPartition Q A, ∃ p ∈ alt Q, C = Exh Q p ∩ A

/-- [fox-2018] (20b): **Non-Vacuity (NV)** — every alternative
    `p ∈ alt Q` identifies *some* cell of `Partition_C(Q, A)`. -/
def NonVacuity (Q : Question W) (A : Set W) : Prop :=
  ∀ p ∈ alt Q, Exh Q p ∩ A ≠ ∅ → ∃ C ∈ ContextualPartition Q A, C = Exh Q p ∩ A

/-- [fox-2018] (20): **Question Partition Matching (QPM)** —
    `Q` and the context-set `A` jointly satisfy CI and NV. -/
def QPM (Q : Question W) (A : Set W) : Prop :=
  CellIdentification Q A ∧ NonVacuity Q A

/-! ### §1.2 Dayal's EP ↔ CI (the central bridge)

Fox's central claim (eq 11–12): when Dayal's maximality presupposition
is met (i.e., every world in `A` has a maximally informative true
answer), the contextual partition is exactly the image of `Exh`.
The substrate-level form of this connection: `IsExhaustivelyResolvable
(alt Q) w` for every `w ∈ A` implies `CellIdentification Q A`. -/

/-- [fox-2018] eq (11)→(12): if every world in the context-set
    has a maximally informative true answer, every cell of the
    contextual partition is `Exh`-identifiable. The substrate
    counterpart of the Dayal-EP-implies-CI direction. -/
theorem cellIdentification_of_isExhaustivelyResolvable
    (Q : Question W) (A : Set W)
    (hEP : ∀ w ∈ A, IsExhaustivelyResolvable (alt Q) w) :
    CellIdentification Q A := by
  rintro C ⟨w, hwA, rfl⟩
  obtain ⟨p, hp⟩ := hEP w hwA
  exact ⟨p, hp.1.1, congrArg (· ∩ A) (exhCell_eq_strongAnswer _ w hp).symm⟩

/-! ### §2.1 Mention-some challenge

[fox-2018] §2.1 (21): "Mary knows where we can get gas in
Cambridge" has an MS reading not derivable from `Ans_D` (which
demands the maximally informative answer). The substrate mirror:
some questions have `¬ IsExhaustivelyResolvable (alt Q) w` at the
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
    Resolves σ Q ∧ ¬ IsExhaustivelyResolvable (alt Q) w := by
  refine ⟨⟨p₁, hp₁, hσp₁⟩, fun ⟨q, hq⟩ => ?_⟩
  rw [isStrongestTrueAnswer_alt_iff] at hq
  have h₁ : p₁ = q := Set.mem_singleton_iff.1 (hq ▸ (⟨hp₁, hwp₁⟩ : p₁ ∈ trueAnswers (alt Q) w))
  have h₂ : p₂ = q := Set.mem_singleton_iff.1 (hq ▸ (⟨hp₂, hwp₂⟩ : p₂ ∈ trueAnswers (alt Q) w))
  exact hp₁p₂ (by rw [h₁, h₂])

end Fox2018
