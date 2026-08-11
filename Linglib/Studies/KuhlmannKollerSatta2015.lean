import Linglib.Syntax.CCG.Grammar
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

/-!
# Target-restricted CCG generates a non-context-free language

Formalisation of the construction in [kuhlmann-koller-satta-2015], Example 2: a
target-restricted combinatory categorial grammar — the formalism of
[vijay-shanker-weir-1994] and [weir-joshi-1988], "VW-CCG" in the paper's
terminology — that generates the non-context-free language `aⁿbⁿcⁿ`.

The point is theoretical. [kuhlmann-koller-satta-2015] show that the CCG≡TAG weak
equivalence holds for *target-restricted* CCG, where combinatory rules may be restricted per
grammar (here, via the target restriction modelled in `Syntax/CCG/Grammar`: every rule
fires only when the *target* of its primary input category is `S`). For lexicalized CCG
*without* target restrictions they prove the power is strictly below TAG: such a CCG that
covers `aⁿbⁿcⁿ` also admits extra permuted strings, so it cannot generate the language
*exactly*. `Syntax/CCG/Derivation`'s `CCG.Derivation` models a (rule-inventory) fragment of that
unrestricted variant, so this construction genuinely needs the restricted model
`CCG.Grammar`.

Atoms follow the paper (`A, B, C, S`) as the study's own atom type — `CCG.Cat` is
parameterized over its atoms, so the construction needs no proxy inventory.

## Main definitions

- `exampleGrammar` — the grammar `G₁` of Example 2: six lexical entries, target
  restriction and start at `S`, degree bound 2.

## Main statements

- `cluster_derives` — the `b`-cluster: `G₁` derives `bⁿ` at category `S/Cⁿ`.
- `peel_derives` — peeling: each `C` argument is discharged by crossed-composing a
  `c` and backward-applying an `a`, wrapping the string as `a … c`.
- `ccg_generates_anbnc` — `anbncStrings ⊆ exampleGrammar.language`.

## Implementation notes

These are the *completeness* direction (`anbncStrings ⊆ exampleGrammar.language`).
The converse *soundness* (`exampleGrammar.language ⊆ anbncStrings`, an induction on
`Grammar.Derives`) is stateable but not formalised here; with it, relabelling
`{"a","b","c"} → ThreeSymbol` and `AnBnCn.anbnc_not_contextFree` would establish that
the grammar's language is itself non-context-free.
-/

namespace KuhlmannKollerSatta2015

open CCG

/-- The atomic categories of the paper's Example 2 grammar. -/
inductive Atom where
  | A
  | B
  | C
  /-- The distinguished atom the target restriction is stated at. -/
  | S
  deriving Repr, DecidableEq

abbrev Acat : Cat Atom := .atom .A
abbrev Bcat : Cat Atom := .atom .B
abbrev Ccat : Cat Atom := .atom .C
abbrev Scat : Cat Atom := .atom .S

/-- The grammar `G₁` of Example 2: the six lexical entries, target restriction and
start at `S`, degree bound 2 — an instance of the modern capacity object
([schiffer-maletti-2021]: ε-free, degree at most 2). -/
def exampleGrammar : Grammar Atom :=
  .targetRestricted
    [("a", Acat), ("c", Ccat \ Acat),
     ("b", (Scat / Ccat) / Bcat), ("b", (Bcat / Ccat) / Bcat),
     ("b", Scat / Ccat), ("b", Bcat / Ccat)]
    .S 2

/-- The cluster category `S/C/…/C` with `n` forward `C`-arguments. -/
def clusterCat : Nat → Cat Atom
  | 0 => Scat
  | n + 1 => (clusterCat n) / Ccat

/-- The cluster category always has target `S`. -/
theorem target_clusterCat (n : Nat) : (clusterCat n).target = Atom.S := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [clusterCat] using ih

/-! ### The construction, as `Derives` inductions -/

/-- Chain of degree-2 compositions: `b₁ = S/C/B` composed with `j` copies of
`B/C/B` derives `bʲ⁺¹` at `S/Cʲ⁺¹/B`. -/
theorem fc2Chain_derives (j : Nat) :
    exampleGrammar.Derives ((clusterCat (j + 1)).rslash .dot Bcat)
      (List.replicate (j + 1) "b") := by
  induction j with
  | zero => exact .lex (by decide)
  | succ j ih =>
      have h : exampleGrammar.Derives ((clusterCat (j + 2)).rslash .dot Bcat)
          (List.replicate (j + 1) "b" ++ ["b"]) :=
        .fc 2 ih (.lex (c := (Bcat / Ccat) / Bcat) (by decide))
          ⟨by decide, by simp [target_clusterCat]⟩ rfl
      simpa [List.replicate_succ'] using h

/-- The `b`-cluster: `G₁` derives `bⁿ` at category `clusterCat n`, for `n ≥ 1`. -/
theorem cluster_derives : ∀ {n : Nat}, 1 ≤ n →
    exampleGrammar.Derives (clusterCat n) (List.replicate n "b")
  | 1, _ => .lex (by decide)
  | n + 2, _ => by
      have h : exampleGrammar.Derives (clusterCat (n + 2))
          (List.replicate (n + 1) "b" ++ ["b"]) :=
        .fc 1 (fc2Chain_derives n) (.lex (c := Bcat / Ccat) (by decide))
          ⟨by decide, by simp [target_clusterCat]⟩ rfl
      simpa [List.replicate_succ'] using h

private theorem replicate_cons_comm {α : Type*} (k : Nat) (a : α) (X : List α) :
    List.replicate k a ++ (a :: X) = a :: (List.replicate k a ++ X) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, List.cons_append, ih]

/-- Peeling: from a derivation of `w` at `clusterCat k`, crossed-composing a `c` and
backward-applying an `a` `k` times derives `aᵏ w cᵏ` at `S`. -/
theorem peel_derives : ∀ (k : Nat) {w : List String},
    exampleGrammar.Derives (clusterCat k) w →
    exampleGrammar.Derives Scat
      (List.replicate k "a" ++ w ++ List.replicate k "c")
  | 0, w, h => by simpa [clusterCat] using h
  | k + 1, w, h => by
      have hstep : exampleGrammar.Derives (clusterCat k) ("a" :: (w ++ ["c"])) :=
        .bc 0 (.lex (c := Acat) (by decide))
          (.fc 1 h (.lex (c := Ccat \ Acat) (by decide))
            ⟨by decide, by simp [target_clusterCat]⟩ rfl)
          ⟨by decide, by simp [target_clusterCat]⟩ rfl
      have hrec := peel_derives k hstep
      simpa [List.replicate_succ, List.cons_append, List.append_assoc,
        replicate_cons_comm] using hrec

/-! ### Generative-capacity result -/

/-- The string language `aⁿbⁿcⁿ` (`n ≥ 1`) over `{"a","b","c"}`. -/
def anbncStrings : Set (List String) :=
  {w | ∃ n, 1 ≤ n ∧ w = List.replicate n "a" ++ List.replicate n "b" ++ List.replicate n "c"}

/-- **`G₁` generates `aⁿbⁿcⁿ`** ([kuhlmann-koller-satta-2015], Ex. 2): every string
in the non-context-free language is in the grammar's language. This is the
completeness half of CCG ⊋ CFG; the language `anbnc` it covers is not context-free
(`AnBnCn.anbnc_not_contextFree`). -/
theorem ccg_generates_anbnc : anbncStrings ⊆ exampleGrammar.language := by
  rintro w ⟨n, hn, rfl⟩
  exact peel_derives n (cluster_derives hn)

end KuhlmannKollerSatta2015
