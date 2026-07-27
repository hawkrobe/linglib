import Linglib.Core.Computability.NonContextFree.BlockWitness
import Linglib.Core.Computability.NonContextFree.AnBnCn
import Linglib.Core.Computability.ContextFreeGrammar.Closure

/-!
# `{aⁿbⁿcⁿdⁿ}`: a four-symbol non-context-free witness

The single-parameter four-symbol witness `anbncndn = {aⁿbⁿcⁿdⁿ | n ≥ 0}`.

Non-context-freeness is **derived by closure, not re-proved by pumping**: the erasing
homomorphism `dropD : d ↦ ε` maps `anbncndn` exactly onto the counting core
`anbnc = {aⁿbⁿcⁿ}`, so `anbncndn_not_contextFree` follows from `anbnc_not_contextFree` through
`Language.IsContextFree.stringMap`. `aⁿbⁿcⁿdⁿ` is the *nested*-counting case; the genuinely
*crossing* witness is the two-parameter `ambncmdn` sibling, which does not reduce by
single-symbol erasure.

This file also hosts the `FourSymbol` substrate shared with `NonContextFree.AmBnCmDn`: the
alphabet, the witness-form bridge to `BlockWitness`, and the two adjacency consequences.

## Main definitions

* `FourSymbol`, `FourString`: the shared four-letter alphabet and its words.
* `makeString_anbncndn n`: the witness word `aⁿbⁿcⁿdⁿ`.
* `anbncndn`: the language `{aⁿbⁿcⁿdⁿ | n ≥ 0}`, as the range of `makeString_anbncndn`.
* `dropD`: the erasing homomorphism `d ↦ ε` witnessing the reduction to `anbnc`.

## Main results

* `not_a_and_c_in_vxy` / `not_b_and_d_in_vxy`: a window of length `≤ p` cannot meet two
  blocks that are not adjacent.
* `stringMap_dropD_anbncndn`: `dropD` maps `anbncndn` onto `anbnc`.
* `anbncndn_not_contextFree`: `anbncndn` is not context-free.
-/

/-- Alphabet for the four-symbol counting witness languages. -/
inductive FourSymbol where
  | a | b | c | d
  deriving DecidableEq, Repr

/-- Words over the four-symbol alphabet. -/
abbrev FourString := List FourSymbol

/-- The witness word `aⁿbⁿcⁿdⁿ`. -/
def makeString_anbncndn (n : ℕ) : FourString :=
  List.replicate n .a ++ List.replicate n .b ++
  List.replicate n .c ++ List.replicate n .d

/-- The language `{aⁿbⁿcⁿdⁿ | n ≥ 0}`, as the range of `makeString_anbncndn`. -/
def anbncndn : Language FourSymbol := {w | ∃ n, w = makeString_anbncndn n}

/-- Membership characterization: every string in `anbncndn` is `makeString_anbncndn n` for
some `n`. -/
theorem mem_anbncndn_iff (w : FourString) :
    w ∈ anbncndn ↔ ∃ n, w = makeString_anbncndn n := Iff.rfl

theorem makeString_in_language (n : ℕ) : makeString_anbncndn n ∈ anbncndn := ⟨n, rfl⟩

/-- Each of the four symbols occurs exactly `n` times in the witness. Shared with `AmBnCmDn`,
which pumps over the same diagonal witness. -/
@[simp] theorem count_makeString_anbncndn (n : ℕ) (s : FourSymbol) :
    (makeString_anbncndn n).count s = n := by
  cases s <;> simp [makeString_anbncndn, List.count_replicate]

@[simp] theorem length_makeString_anbncndn (n : ℕ) :
    (makeString_anbncndn n).length = 4 * n := by
  simp [makeString_anbncndn]; omega

/-- The four symbol counts of a word sum to its length. -/
theorem fourSymbol_count_total (l : FourString) :
    l.count .a + l.count .b + l.count .c + l.count .d = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => cases h <;> simp <;> omega

/-- The four-symbol witness is structurally `BlockWitness [a, b, c, d] n`. -/
theorem makeString_anbncndn_eq_blockwitness (n : ℕ) :
    makeString_anbncndn n =
      BlockWitness ([FourSymbol.a, .b, .c, .d] : List FourSymbol) n := by
  simp [makeString_anbncndn, BlockWitness, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]

/-- Adjacency in the `FourSymbol` witness via the unified `BlockWitness.not_both_in_vxy`:
each instance is a one-line invocation parameterized by symbol indices. -/
private theorem not_both_in_vxy_FourSymbol {s t : FourSymbol} {i j : ℕ}
    (hi : ([FourSymbol.a, .b, .c, .d] : List FourSymbol)[i]? = some s)
    (hj : ([FourSymbol.a, .b, .c, .d] : List FourSymbol)[j]? = some t)
    (hij : j ≥ i + 2) (p : ℕ) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬ (s ∈ vxy ∧ t ∈ vxy) :=
  BlockWitness.not_both_in_vxy
    (by decide : ([FourSymbol.a, .b, .c, .d] : List FourSymbol).Nodup)
    hi hj hij (makeString_anbncndn_eq_blockwitness p ▸ hw) hvxy

theorem not_a_and_c_in_vxy (p : ℕ) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(FourSymbol.a ∈ vxy ∧ FourSymbol.c ∈ vxy) :=
  not_both_in_vxy_FourSymbol (i := 0) (j := 2) rfl rfl (by decide) p u vxy z hw hvxy

theorem not_b_and_d_in_vxy (p : ℕ) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(FourSymbol.b ∈ vxy ∧ FourSymbol.d ∈ vxy) :=
  not_both_in_vxy_FourSymbol (i := 1) (j := 3) rfl rfl (by decide) p u vxy z hw hvxy

/-! ### Non-context-freeness by homomorphic reduction to `{aⁿbⁿcⁿ}` -/

/-- The erasing homomorphism `d ↦ ε` (a per-symbol map; the string action is
`List.flatMap dropD`, the free-monoid lift), relabelling the surviving `a`/`b`/`c` into the
`ThreeSymbol` alphabet. -/
def dropD : FourSymbol → List ThreeSymbol
  | FourSymbol.a => [ThreeSymbol.a]
  | FourSymbol.b => [ThreeSymbol.b]
  | FourSymbol.c => [ThreeSymbol.c]
  | FourSymbol.d => []

private theorem flatten_replicate_singleton {α : Type*} (n : ℕ) (x : α) :
    (List.replicate n [x]).flatten = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

private theorem flatten_replicate_nil {α : Type*} (n : ℕ) :
    (List.replicate n ([] : List α)).flatten = [] := by
  induction n with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

private theorem dropD_replicate (n : ℕ) (s : FourSymbol) :
    List.flatMap dropD (List.replicate n s) =
      List.flatten (List.replicate n (dropD s)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, List.replicate_succ, List.flatten_cons]

/-- `dropD` erases the `dⁿ` block and relabels, sending the witness to `makeString_anbnc n`. -/
@[simp] theorem dropD_makeString (n : ℕ) :
    List.flatMap dropD (makeString_anbncndn n) = makeString_anbnc n := by
  simp only [makeString_anbncndn, List.flatMap_append, dropD_replicate, dropD,
             flatten_replicate_singleton, flatten_replicate_nil, List.append_nil, makeString_anbnc]

/-- `dropD` maps `anbncndn` exactly onto the counting core `anbnc`. This image equality is what
powers the closure reduction. -/
theorem stringMap_dropD_anbncndn : Language.stringMap dropD anbncndn = anbnc := by
  ext w
  rw [Language.mem_stringMap]
  constructor
  · rintro ⟨v, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, (dropD_makeString n).symm ▸ rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨makeString_anbncndn n, makeString_in_language n, dropD_makeString n⟩

/-- `{aⁿbⁿcⁿdⁿ}` is not context-free — derived by closure from `anbnc_not_contextFree` via the
erasing homomorphism `dropD`, rather than re-proved by pumping. -/
theorem anbncndn_not_contextFree : ¬ Language.IsContextFree anbncndn :=
  Language.not_isContextFree_of_stringMap_not dropD
    (by rw [stringMap_dropD_anbncndn]; exact anbnc_not_contextFree)
