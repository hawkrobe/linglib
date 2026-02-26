/-!
# Exhaustivity Presuppositions for Questions @cite{xiang-2022}

Formalizes Dayal's Exhaustivity Presupposition (EP, definition 90) and Xiang's
Relativized Exhaustivity (RelExh, definition 91) from:

Xiang, Yimei (2022). Relativized Exhaustivity: mention-some and uniqueness.
*Natural Language Semantics* 30:311–362.

## Key Definitions

- `dayalEP`: Dayal (1996)'s Exhaustivity Presupposition — the question
  presupposes that there exists a strongest true answer (one whose proposition
  entails all other true answers' propositions).
- `relExh`: Xiang's Relativized Exhaustivity — EP is evaluated relative to
  *singleton* modal bases. For each accessible world v, restrict the modal base
  to {v} and check EP there. This weakens EP just enough to license
  mention-some for ability-*can* questions while preserving mention-all for
  non-modal and other modal questions.
- `foQDen`: First-order question denotation (◇φ_x interpretation) — the
  building block for can-questions where the wh-trace scopes below the modal.

## Design

All definitions are polymorphic in `W` (worlds) and `P` (individuals/answers),
taking explicit `List W` universe parameters for decidable computation via
`native_decide`. No imports beyond basic Lean — this is pure theory.
-/

namespace Theories.Semantics.Questions.Exhaustivity

/-! ### Propositional Entailment -/

/-- Propositional entailment as Bool: `p ⊆ q` over a finite universe.
`propEntails p q worlds = true` iff every world where `p` holds also has `q`. -/
def propEntails {W : Type _} (p q : W → Bool) (worlds : List W) : Bool :=
  worlds.all (λ v => !p v || q v)

/-! ### True Answers -/

/-- The answers whose denotation is true at world `w` under modal base `mb`. -/
def trueAnswers {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (w : W) : List P :=
  answers.filter (λ α => qden mb α w)

/-! ### First-Order Question Denotation -/

/-- First-order question denotation: ◇φ_x interpretation.

`foQDen pred mb α w = true` iff there exists an accessible world `v ∈ mb(w)`
where `pred(v, α)` holds. This is the denotation for can-questions where the
wh-trace takes scope below the modal:
  ⟦who can VP⟧(mb)(α)(w) = ∃v ∈ mb(w). VP(v)(α) -/
def foQDen {W P : Type _} (pred : W → P → Bool)
    (mb : W → List W) (α : P) (w : W) : Bool :=
  (mb w).any (λ v => pred v α)

/-! ### Dayal's Exhaustivity Presupposition -/

/-- Dayal's Exhaustivity Presupposition (Dayal 1996; Xiang 2022, definition 90).

EP holds at `w` iff there exists a true answer α whose proposition entails the
proposition of every other true answer β:
  ∃α ∈ True(w). ∀β ∈ True(w). ⟦α⟧ ⊆ ⟦β⟧

When EP holds, α is the *strongest true answer* — the exhaustive answer to the
question. When EP fails, no single answer subsumes all others, so the question
has no well-defined exhaustive reading. -/
def dayalEP {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W) : Bool :=
  let trueAt := trueAnswers qden mb answers w
  trueAt.any (λ α =>
    trueAt.all (λ β =>
      propEntails (qden mb α) (qden mb β) worlds))

/-! ### Relativized Exhaustivity -/

/-- Relativized Exhaustivity (Xiang 2022, definition 91).

RelExh holds at `w` iff for every singleton modal base {v} where v ∈ mb(w),
if {v} makes some answer relevant (both true under {v} and true under the full
mb), then EP holds for {v}:
  ∀v ∈ mb(w). [∃α. qden({v})(α)(w) ∧ qden(mb)(α)(w)] → EP({v})(w)

The key insight: under a singleton modal base {v}, each individual α either
determinately can or determinately cannot VP at v. So for each v, there IS a
strongest true answer (trivially — the answers don't overlap when the modal
base is a singleton). This means RelExh passes for ability-*can* questions
even when the full EP fails due to overlapping answer propositions. -/
def relExh {W P : Type _}
    (qden : (W → List W) → P → W → Bool)
    (mb : W → List W) (answers : List P) (worlds : List W) (w : W) : Bool :=
  (mb w).all (λ v =>
    let singletonMB : W → List W := λ _ => [v]
    let hasRelevant := answers.any (λ α =>
      qden singletonMB α w && qden mb α w)
    !hasRelevant || dayalEP qden singletonMB answers worlds w)

/-! ### Fox 2018: Partition by Exhaustification @cite{fox-2018}

Fox (2018) "Partition by Exhaustification" derives Dayal's EP from the
exhaustification operator Exh. The key insight: a question partitions
the logical space iff every world has exactly one exhaustified true answer.

The definitions below are Bool-valued analogues of the Prop-valued MC-set/IE
machinery in `NeoGricean.Exhaustivity.Basic`, specialized to question cells
for decidable computation via `native_decide`.

- `cellMCSets` mirrors `isMCSet` from NeoGricean.Exhaustivity
- `cellIE` mirrors `IE` from NeoGricean.Exhaustivity
- `foxExh` mirrors `exhIE` from NeoGricean.Exhaustivity
- `foxQPM` implements Fox 2018, definition 34 (CI + NV)
-/

/-- All sublists (power set) of a list, preserving order.
Used to enumerate candidate MC-sets of cell indices. -/
def sublists : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs =>
    let rest := sublists xs
    rest ++ rest.map (x :: ·)

/-- Safe cell accessor: returns the cell at index `i`, or (λ _ => false) for OOB. -/
def getCell {W : Type _} (cells : List (W → Bool)) (i : Nat) : W → Bool :=
  cells.getD i (λ _ => false)

/-- Negation consistency: can cells at `excluded` indices be simultaneously
negated while cell `pIdx` stays true?

`negConsistent cells pIdx excluded worlds = true` iff
∃w ∈ worlds. cells[pIdx](w) ∧ ∀j ∈ excluded. ¬cells[j](w)

This is the Bool analogue of `SetConsistent` in NeoGricean.Exhaustivity,
specialized to the pattern φ ∧ ⋀{¬a : a ∈ excluded}. -/
def negConsistent {W : Type _} (cells : List (W → Bool)) (pIdx : Nat)
    (excluded : List Nat) (worlds : List W) : Bool :=
  worlds.any (λ w =>
    getCell cells pIdx w &&
    excluded.all (λ j => !getCell cells j w))

/-- MC-sets (maximal consistent sets) of cell indices for cell `pIdx`.

A subset `S` of alternative indices (excluding `pIdx`) is an MC-set iff:
1. Negating all cells in `S` is consistent with `pIdx` being true
2. No proper superset of `S` is also consistent

Bool analogue of `isMCSet` in NeoGricean.Exhaustivity.Basic. -/
def cellMCSets {W : Type _} (cells : List (W → Bool)) (pIdx : Nat)
    (worlds : List W) : List (List Nat) :=
  let altIdxs := (List.range cells.length).filter (· != pIdx)
  let allSubs := sublists altIdxs
  let consistent := allSubs.filter (negConsistent cells pIdx · worlds)
  -- Keep only maximal: S is maximal iff no consistent T ⊃ S
  consistent.filter (λ s =>
    !consistent.any (λ t =>
      t.length > s.length && s.all (t.contains ·)))

/-- Innocently excludable alternatives for cell `pIdx`: the indices
that appear in *every* MC-set (intersection of all MC-sets).

Bool analogue of `IE` in NeoGricean.Exhaustivity.Basic:
  IE_(ALT,φ) = {ψ : ψ belongs to every MC_(ALT,φ)-set} -/
def cellIE {W : Type _} (cells : List (W → Bool)) (pIdx : Nat)
    (worlds : List W) : List Nat :=
  let mcs := cellMCSets cells pIdx worlds
  match mcs with
  | [] => []
  | first :: rest =>
    first.filter (λ i => rest.all (·.contains i))

/-- Fox's exhaustified cell: Exh(Q)(p)(w) = cells[pIdx](w) ∧ ∀j ∈ IE. ¬cells[j](w).

The exhaustified meaning of answer p negates all innocently excludable
alternatives. Bool analogue of `exhIE` in NeoGricean.Exhaustivity.Basic. -/
def foxExh {W : Type _} (cells : List (W → Bool)) (pIdx : Nat)
    (worlds : List W) : W → Bool :=
  λ w => getCell cells pIdx w &&
    (cellIE cells pIdx worlds).all (λ j => !getCell cells j w)

/-- Non-vacuity: Exh(Q)(p) is satisfiable (true at some world).
Fox 2018 requires non-vacuity for QPM. -/
def foxNV {W : Type _} (cells : List (W → Bool)) (pIdx : Nat)
    (worlds : List W) : Bool :=
  worlds.any (foxExh cells pIdx worlds)

/-- Count of Exh-true cells at world `w`: the number of cells whose
exhaustified meaning holds at `w`. This is NOT Fox's |Ans| (Definition 35)
but a simpler diagnostic: how many exclusive readings are true at `w`.
When = 0, no cell exclusively holds (overlap); when = 1, one cell
dominates; when > 1, multiple exclusive readings coexist. -/
def exhTrueCount {W : Type _} (cells : List (W → Bool))
    (worlds : List W) (w : W) : Nat :=
  (List.range cells.length).filter (λ i => foxExh cells i worlds w) |>.length

/-- Pointwise non-vacuity: every cell true at `w` has a satisfiable
exhaustified version. This is a necessary condition for Fox's QPM
(Definition 34) but weaker — it checks NV for true cells at a single
world, while Fox's QPM requires both CI and NV globally over the
partition induced by Q. -/
def pointwiseNV {W : Type _} (cells : List (W → Bool))
    (worlds : List W) (w : W) : Bool :=
  (List.range cells.length).all (λ i =>
    !getCell cells i w || foxNV cells i worlds)

/-- Fox's answer operator (Definition 35). At world `w`, finds the unique
cell-identifier (the unique `j` where `foxExh(cells, j, worlds)(w) = true`)
and returns the count of Q-members that are true at `w` AND whose
denotation entails the cell-identifier's exhaustified meaning.

Returns 0 if no unique cell-identifier exists (zero or multiple Exh-true
cells at `w`). When `foxAns > 1`, Fox predicts mention-some (the
cell-identifier is weaker than individual true answers). When `= 1`,
mention-all (the cell-identifier is the strongest true answer). -/
def foxAns {W : Type _} (cells : List (W → Bool))
    (worlds : List W) (w : W) : Nat :=
  let exhTrue := (List.range cells.length).filter (λ j => foxExh cells j worlds w)
  match exhTrue with
  | [j] =>
    let cellId := foxExh cells j worlds
    (List.range cells.length).filter (λ i =>
      getCell cells i w && propEntails (getCell cells i) cellId worlds) |>.length
  | _ => 0

/-- Schwarzschild's partition test (Fox 2018, (38)): do the exhaustified
cells {Exh(Q)(p) : p ∈ Q} partition the world set? Holds iff every world
has exactly one Exh-true cell. When this holds, Fox's QPM (Definition 34)
is satisfied and `foxAns` is well-defined at every world. -/
def foxPartition {W : Type _} (cells : List (W → Bool))
    (worlds : List W) : Bool :=
  worlds.all (λ (w : W) =>
    let n := (List.range cells.length).filter (λ i => foxExh cells i worlds w) |>.length
    n == 1)

end Theories.Semantics.Questions.Exhaustivity
