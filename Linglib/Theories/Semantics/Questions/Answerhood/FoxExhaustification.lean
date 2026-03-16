import Linglib.Theories.Semantics.Questions.Answerhood.Exhaustivity

/-! ### @cite{fox-2018}: Partition by Exhaustification @cite{fox-2018}

@cite{fox-2018} "Partition by Exhaustification" derives Dayal's EP from the
exhaustification operator Exh. The key insight: a question partitions
the logical space iff every world has exactly one exhaustified true answer.

The definitions below are Bool-valued analogues of the Prop-valued MC-set/IE
machinery in `Exhaustification.Operators`, specialized to question cells
for decidable computation via `native_decide`.

- `cellMCSets` mirrors `isMCSet` from Exhaustification
- `cellIE` mirrors `IE` from Exhaustification
- `foxExh` mirrors `exhIE` from Exhaustification
- `foxAns` implements @cite{fox-2018}'s answer operator (definition 35)
- `foxPartition` implements the partition condition from
  @cite{fox-2018}'s restated Ans operator (presupposition of (38))
-/

namespace Theories.Semantics.Questions.Exhaustivity

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

This is the Bool analogue of `SetConsistent` in Exhaustification,
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

Bool analogue of `isMCSet` in Exhaustification.Operators. -/
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

Bool analogue of `IE` in Exhaustification.Operators:
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
alternatives. Bool analogue of `exhIE` in Exhaustification.Operators. -/
def foxExh {W : Type _} (cells : List (W → Bool)) (pIdx : Nat)
    (worlds : List W) : W → Bool :=
  λ w => getCell cells pIdx w &&
    (cellIE cells pIdx worlds).all (λ j => !getCell cells j w)

/-- Non-vacuity: Exh(Q)(p) is satisfiable (true at some world).
@cite{fox-2018} requires non-vacuity for QPM. -/
def foxNV {W : Type _} (cells : List (W → Bool)) (pIdx : Nat)
    (worlds : List W) : Bool :=
  worlds.any (foxExh cells pIdx worlds)

/-- Count of Exh-true cells at world `w`: the number of cells whose
exhaustified meaning holds at `w`. This is NOT Fox's |Ans|
but a simpler diagnostic: how many exclusive readings are true at `w`.
When = 0, no cell exclusively holds (overlap); when = 1, one cell
dominates; when > 1, multiple exclusive readings coexist. -/
def exhTrueCount {W : Type _} (cells : List (W → Bool))
    (worlds : List W) (w : W) : Nat :=
  (List.range cells.length).filter (λ i => foxExh cells i worlds w) |>.length

/-- Pointwise non-vacuity: every cell true at `w` has a satisfiable
exhaustified version. This is a necessary condition for Fox's QPM
but weaker — it checks NV for true cells at a single
world, while Fox's QPM requires both CI and NV globally over the
partition induced by Q. -/
def pointwiseNV {W : Type _} (cells : List (W → Bool))
    (worlds : List W) (w : W) : Bool :=
  (List.range cells.length).all (λ i =>
    !getCell cells i w || foxNV cells i worlds)

/-- Fox's answer operator. At world `w`, finds the unique
cell-identifier (the unique `j` where `foxExh(cells, j, worlds)(w) = true`)
and returns the count of Q-members that are true at `w` AND whose
denotation entails the cell-identifier *proposition* `cells[j]`.

@cite{fox-2018}, definition 35:
Ans(Q)(w) = {q∈Q : w∈q ∧ q ⊆ (ιp∈Q)[Exh(Q,p,w)=1]}
The ι picks the unique proposition p whose exhaustification is true at w;
the entailment check is q ⊆ p (q entails the proposition p, not Exh(p)).

Returns 0 if no unique cell-identifier exists (zero or multiple Exh-true
cells at `w`). When `foxAns > 1`, Fox predicts mention-some (the
cell-identifier is weaker than individual true answers). When `= 1`,
mention-all (the cell-identifier is the strongest true answer). -/
def foxAns {W : Type _} (cells : List (W → Bool))
    (worlds : List W) (w : W) : Nat :=
  let exhTrue := (List.range cells.length).filter (λ j => foxExh cells j worlds w)
  match exhTrue with
  | [j] =>
    let cellId := getCell cells j
    (List.range cells.length).filter (λ i =>
      getCell cells i w && propEntails (getCell cells i) cellId worlds) |>.length
  | _ => 0

/-- Schwarzschild's partition test: do the exhaustified
cells {Exh(Q)(p) : p ∈ Q} partition the world set? Holds iff every world
has exactly one Exh-true cell.

This is the partition condition that appears as the presupposition of
@cite{fox-2018}'s restated Ans operator (38): Ans is defined only when
pointwise exhaustification of Q is a partition of the context set. -/
def foxPartition {W : Type _} (cells : List (W → Bool))
    (worlds : List W) : Bool :=
  worlds.all (λ (w : W) =>
    let n := (List.range cells.length).filter (λ i => foxExh cells i worlds w) |>.length
    n == 1)

end Theories.Semantics.Questions.Exhaustivity
