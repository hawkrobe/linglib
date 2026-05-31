import Linglib.Syntax.CCG.Classical
import Linglib.Core.Computability.NonContextFree.AnBnCn

/-!
# Classical CCG generates a non-context-free language

Formalisation of the construction in @cite{kuhlmann-koller-satta-2015}, Example 2: a
rule-restricted combinatory categorial grammar — the classical formalism of
@cite{vijay-shanker-weir-1994} and @cite{weir-joshi-1988} — that generates the
non-context-free language `aⁿbⁿcⁿ`.

The point is theoretical. @cite{kuhlmann-koller-satta-2015} show that the CCG≡TAG weak
equivalence holds for *classical* CCG, where combinatory rules may be restricted per
grammar (here, via the target restriction modelled in `Syntax/CCG/Classical`: every rule
fires only when the *target* of its primary input category is `S`). Modern universal-rule
CCG — `Syntax/CCG/Basic`'s `CCG.DerivStep` — is strictly weaker (they prove pure CCG
without target restrictions is properly below TAG). So this construction genuinely needs
the restricted model `CCG.Classical`.

Atoms follow the paper (`A, B, C, S`); we realise them with the project's `CCG.Cat` atoms
as `A = NP`, `B = N`, `C = PP`, `S = S` — abstract placeholders, the content is generative
capacity, not syntax.

## Main definitions

- `build` — the `n`-indexed `CCG.Classical.Derivation` of `aⁿbⁿcⁿ` (cluster of degree-2
  compositions, peeled to `S` by crossed-composition with `c` and backward-application
  with `a`).

## Main statements

- `build_cat` — `(build n).cat = some S` for `n ≥ 1`.
- `build_yield` — `(build n).yield = aⁿbⁿcⁿ`.
- `ccg_generates_anbnc` — every `aⁿbⁿcⁿ` string is generated.

## Implementation notes

These are the *completeness* direction (every target string is generated). The converse
*soundness* (the target-restricted rules generate *only* count-matched strings) is an
all-derivations induction not formalised here; with it, relabelling
`{"a","b","c"} → ThreeSymbol` and `AnBnCn.anbnc_not_contextFree` would establish that the
grammar's language is itself non-context-free.
-/

namespace KuhlmannKollerSatta2015

open CCG
open CCG.Classical

/-- Abstract atom `A`, realised as `NP`. -/
abbrev Acat : Cat := NP
/-- Abstract atom `B`, realised as `N`. -/
abbrev Bcat : Cat := N
/-- Abstract atom `C`, realised as `PP`. -/
abbrev Ccat : Cat := PP

/-! ### The grammar `G₁` of Example 2 -/

/-- `a := A`. -/
def aLex : Derivation := .lex Acat "a"
/-- `c := C\A`. -/
def cLex : Derivation := .lex (Ccat \ Acat) "c"

/-- The cluster category `S/C/…/C` with `n` forward `C`-arguments. -/
def clusterCat : Nat → Cat
  | 0 => S
  | n + 1 => (clusterCat n) / Ccat

/-- Chain of degree-2 compositions: `b₁ = S/C/B` composed with `j` copies of
`B/C/B`, giving `S/Cʲ⁺¹/B` and yield `bʲ⁺¹`. -/
def fc2Chain : Nat → Derivation
  | 0 => .lex ((S / Ccat) / Bcat) "b"
  | j + 1 => .fc2 (fc2Chain j) (.lex ((Bcat / Ccat) / Bcat) "b")

/-- The `b`-cluster derivation for `n ≥ 1`, with category `clusterCat n`, yield `bⁿ`. -/
def clusterDeriv : Nat → Derivation
  | 0 => .lex S "b"            -- unused (the construction starts at n = 1)
  | 1 => .lex (S / Ccat) "b"
  | n + 2 => .fc1 (fc2Chain n) (.lex (Bcat / Ccat) "b")

/-- One peel: crossed-compose with a `c` on the right, then backward-apply an `a` on the
left — wrapping the yield with `a … c` and removing one `C` argument. -/
def peelStep (d : Derivation) : Derivation := .ba aLex (.fcx1 d cLex)

/-- Peel `k` times. -/
def peel : Nat → Derivation → Derivation
  | 0, d => d
  | k + 1, d => peel k (peelStep d)

/-- The full derivation of `aⁿbⁿcⁿ`. -/
def build (n : Nat) : Derivation := peel n (clusterDeriv n)

/-! ### Target invariant -/

/-- The cluster category always has target `S`. -/
theorem targetIsS_clusterCat (n : Nat) : targetIsS (clusterCat n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [clusterCat] using ih

/-! ### Category of the construction (completeness, part 1) -/

/-- The degree-2 chain composes to `S/Cʲ⁺¹/B`. -/
theorem fc2Chain_cat (j : Nat) :
    (fc2Chain j).cat = some ((clusterCat (j + 1)).rslash Bcat) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp [fc2Chain, Derivation.cat, ih, fcomp2, targetIsS_clusterCat, clusterCat]

/-- The cluster derivation has category `clusterCat n` for `n ≥ 1`. -/
theorem clusterDeriv_cat : ∀ {n : Nat}, 1 ≤ n → (clusterDeriv n).cat = some (clusterCat n)
  | 1, _ => rfl
  | n + 2, _ => by
    simp [clusterDeriv, Derivation.cat, fc2Chain_cat, fcomp1, targetIsS_clusterCat, clusterCat]

/-- One peel removes one `C` argument from a cluster. -/
theorem peelStep_cat {d : Derivation} {k : Nat} (h : d.cat = some (clusterCat (k + 1))) :
    (peelStep d).cat = some (clusterCat k) := by
  simp [peelStep, Derivation.cat, aLex, cLex, h, fcompX1, bapp, clusterCat, targetIsS_clusterCat]

/-- Peeling `k` times turns a `clusterCat k` derivation into one of category `S`. -/
theorem peel_cat : ∀ (k : Nat) (d : Derivation), d.cat = some (clusterCat k) →
    (peel k d).cat = some S
  | 0, d, h => by simpa [peel, clusterCat] using h
  | k + 1, d, h => by
    simp only [peel]
    exact peel_cat k (peelStep d) (peelStep_cat h)

/-- **Completeness, category part.** The construction derives `S` for every `n ≥ 1`. -/
theorem build_cat {n : Nat} (hn : 1 ≤ n) : (build n).cat = some S :=
  peel_cat n (clusterDeriv n) (clusterDeriv_cat hn)

/-! ### Yield of the construction (completeness, part 2) -/

private theorem replicate_cons_comm {α : Type*} (k : Nat) (a : α) (X : List α) :
    List.replicate k a ++ (a :: X) = a :: (List.replicate k a ++ X) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, List.cons_append, ih]

theorem fc2Chain_yield (j : Nat) : (fc2Chain j).yield = List.replicate (j + 1) "b" := by
  induction j with
  | zero => rfl
  | succ j ih => simp [fc2Chain, Derivation.yield, ih, List.replicate_succ']

theorem clusterDeriv_yield : ∀ {n : Nat}, 1 ≤ n →
    (clusterDeriv n).yield = List.replicate n "b"
  | 1, _ => rfl
  | n + 2, _ => by simp [clusterDeriv, Derivation.yield, fc2Chain_yield, List.replicate_succ']

theorem peel_yield : ∀ (k : Nat) (d : Derivation),
    (peel k d).yield = List.replicate k "a" ++ d.yield ++ List.replicate k "c"
  | 0, d => by simp [peel]
  | k + 1, d => by
    simp only [peel]
    rw [peel_yield k (peelStep d)]
    have hy : (peelStep d).yield = "a" :: (d.yield ++ ["c"]) := by
      simp [peelStep, Derivation.yield, aLex, cLex]
    rw [hy, List.replicate_succ, List.replicate_succ]
    simp only [List.cons_append, List.append_assoc, List.singleton_append]
    exact replicate_cons_comm k "a" _

/-- **Completeness, yield part.** The construction spells out `aⁿbⁿcⁿ`. -/
theorem build_yield {n : Nat} (hn : 1 ≤ n) :
    (build n).yield = List.replicate n "a" ++ List.replicate n "b" ++ List.replicate n "c" := by
  simp [build, peel_yield, clusterDeriv_yield hn, List.append_assoc]

/-! ### Generative-capacity result -/

/-- The string language `aⁿbⁿcⁿ` (`n ≥ 1`) over `{"a","b","c"}`. -/
def anbncStrings : Set (List String) :=
  {w | ∃ n, 1 ≤ n ∧ w = List.replicate n "a" ++ List.replicate n "b" ++ List.replicate n "c"}

/-- **The construction generates `aⁿbⁿcⁿ`** (@cite{kuhlmann-koller-satta-2015}, Ex. 2):
every string in the non-context-free language is the yield of a well-formed (target-
restricted) CCG derivation. This is the completeness half of CCG ⊋ CFG; the language
`anbnc` it covers is not context-free (`AnBnCn.anbnc_not_contextFree`). -/
theorem ccg_generates_anbnc (w : List String) (hw : w ∈ anbncStrings) :
    ∃ d : Derivation, d.cat = some S ∧ d.yield = w := by
  obtain ⟨n, hn, rfl⟩ := hw
  exact ⟨build n, build_cat hn, build_yield hn⟩

end KuhlmannKollerSatta2015
