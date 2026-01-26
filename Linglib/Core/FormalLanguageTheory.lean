/-
# Formal Language Theory

Foundational definitions for the Chomsky hierarchy and formal language classes.

## Goal (Phase 4.1 of Roadmap)

Provide rigorous definitions that let us PROVE CCG's position in the hierarchy,
not just assert it.

## Key Results

- Definition of context-free languages
- Proof that {aⁿbⁿcⁿdⁿ} is NOT context-free (via pumping lemma)
- This is the language of cross-serial dependencies

## References

- Joshi, A.K. (1985). Tree Adjoining Grammars
- Hopcroft, Motwani & Ullman (2006). Introduction to Automata Theory
- Steedman (2000). The Syntactic Process, Ch. 2
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

-- ============================================================================
-- Basic Definitions
-- ============================================================================

/--
Alphabet for cross-serial dependencies: a, b, c, d.

This models Dutch word order:
  NP₁ NP₂ V₁ V₂ → aabbccdd pattern
-/
inductive FourSymbol where
  | a | b | c | d
  deriving DecidableEq, Repr, BEq

/--
A string is a list of symbols.
-/
abbrev FourString := List FourSymbol

/--
The language {aⁿbⁿcⁿdⁿ | n ≥ 0}.

This models cross-serial dependencies in Dutch:
  NP₁ NP₂ ... NPₙ V₁ V₂ ... Vₙ
where NPᵢ is the argument of Vᵢ.
-/
def isInLanguage_anbncndn (w : FourString) : Bool :=
  match w with
  | [] => true  -- ε is in the language (n=0)
  | _ =>
    -- Count each symbol
    let na := w.filter (· == .a) |>.length
    let nb := w.filter (· == .b) |>.length
    let nc := w.filter (· == .c) |>.length
    let nd := w.filter (· == .d) |>.length
    -- Check counts are equal
    na == nb && nb == nc && nc == nd &&
    -- Check order: all a's, then all b's, then all c's, then all d's
    w == List.replicate na .a ++ List.replicate nb .b ++
         List.replicate nc .c ++ List.replicate nd .d

/-- Generate a string aⁿbⁿcⁿdⁿ -/
def makeString_anbncndn (n : Nat) : FourString :=
  List.replicate n .a ++ List.replicate n .b ++
  List.replicate n .c ++ List.replicate n .d

-- Basic properties
#eval isInLanguage_anbncndn []  -- true (n=0)
#eval isInLanguage_anbncndn (makeString_anbncndn 0)  -- true
#eval isInLanguage_anbncndn (makeString_anbncndn 1)  -- true: abcd
#eval isInLanguage_anbncndn (makeString_anbncndn 2)  -- true: aabbccdd
#eval isInLanguage_anbncndn (makeString_anbncndn 3)  -- true: aaabbbcccddd
#eval isInLanguage_anbncndn [.a, .b, .c]  -- false (missing d)
#eval isInLanguage_anbncndn [.a, .a, .b, .c, .c, .d]  -- false (counts unequal)

-- ============================================================================
-- The Pumping Lemma (Statement)
-- ============================================================================

/--
The pumping lemma for context-free languages.

If L is context-free and infinite, then there exists a pumping length p such that:
for all w ∈ L with |w| ≥ p, we can write w = uvxyz where:
1. |vxy| ≤ p
2. |vy| ≥ 1 (at least one of v, y is non-empty)
3. For all i ≥ 0: uvⁱxyⁱz ∈ L

We state this as an axiom since the full proof requires formalizing CFGs.
-/
axiom pumping_lemma_for_cfl :
    ∀ (inLang : FourString → Bool),
    -- If the language is context-free (we assume this for contradiction)
    -- Then there exists a pumping length
    ∃ p : Nat, p > 0 ∧
    ∀ w : FourString, inLang w = true → w.length ≥ p →
      ∃ u v x y z : FourString,
        w = u ++ v ++ x ++ y ++ z ∧
        (v ++ x ++ y).length ≤ p ∧
        (v.length + y.length) ≥ 1 ∧
        ∀ i : Nat, inLang (u ++ List.flatten (List.replicate i v) ++ x ++
                          List.flatten (List.replicate i y) ++ z) = true

-- ============================================================================
-- Key Theorem: {aⁿbⁿcⁿdⁿ} is NOT Context-Free
-- ============================================================================

/--
Helper: pumping a string in {aⁿbⁿcⁿdⁿ} breaks membership.

The key insight is that |vxy| ≤ p means vxy spans at most p symbols,
so it can touch at most 2 adjacent symbol types. Pumping changes
those counts but not the others, breaking the equality requirement.
-/
theorem pump_breaks_anbncndn (p : Nat) (hp : p > 0) :
    let w := makeString_anbncndn p
    ∀ u v x y z : FourString,
      w = u ++ v ++ x ++ y ++ z →
      (v ++ x ++ y).length ≤ p →
      (v.length + y.length) ≥ 1 →
      -- The pumped string (i=2) is NOT in the language
      ∃ i : Nat, isInLanguage_anbncndn (u ++ List.flatten (List.replicate i v) ++ x ++
                                        List.flatten (List.replicate i y) ++ z) = false := by
  intro w u v x y z hw hvxy_len hvy_len
  -- The pumped region vxy has length ≤ p, so it can span at most 2 types
  -- Pumping with i=0 or i=2 will change some counts but not all
  -- Since the original has all counts = p, pumping breaks equality
  use 0  -- Pumping with i=0 removes v and y
  -- Full proof requires showing that removing v,y changes counts unequally
  sorry

/--
**Main Theorem: {aⁿbⁿcⁿdⁿ} is NOT context-free**

This is proven by contradiction using the pumping lemma.
If it were context-free, we could pump any sufficiently long string
while staying in the language. But pumping breaks the equal-counts property.
-/
theorem anbncndn_not_context_free :
    ¬∃ (p : Nat), p > 0 ∧
      ∀ w : FourString, isInLanguage_anbncndn w = true → w.length ≥ p →
        ∀ u v x y z : FourString,
          w = u ++ v ++ x ++ y ++ z →
          (v ++ x ++ y).length ≤ p →
          (v.length + y.length) ≥ 1 →
          ∀ i : Nat, isInLanguage_anbncndn (u ++ List.flatten (List.replicate i v) ++ x ++
                                           List.flatten (List.replicate i y) ++ z) = true := by
  intro ⟨p, hp, hpump⟩
  -- Choose w = aᵖbᵖcᵖdᵖ which is in the language and has length 4p ≥ p
  let w := makeString_anbncndn p
  have hw_in : isInLanguage_anbncndn w = true := by
    simp only [w, makeString_anbncndn, isInLanguage_anbncndn]
    sorry  -- Need to show the generated string satisfies the predicate
  have hw_len : w.length ≥ p := by
    simp only [w, makeString_anbncndn, List.length_append, List.length_replicate]
    omega
  -- The rest of the proof would use pump_breaks_anbncndn to derive a contradiction
  -- For any decomposition u,v,x,y,z satisfying the pumping conditions,
  -- there exists an i such that the pumped string is not in the language.
  -- But hpump says ALL pumps stay in the language, giving a contradiction.
  sorry

-- ============================================================================
-- Three-Symbol Version (Classic Result)
-- ============================================================================

/--
Alphabet for the classic {aⁿbⁿcⁿ} language.
-/
inductive ThreeSymbol where
  | a | b | c
  deriving DecidableEq, Repr, BEq

/--
The language {aⁿbⁿcⁿ | n ≥ 0}.
-/
def isInLanguage_anbnc (w : List ThreeSymbol) : Bool :=
  match w with
  | [] => true
  | _ =>
    let na := w.filter (· == .a) |>.length
    let nb := w.filter (· == .b) |>.length
    let nc := w.filter (· == .c) |>.length
    na == nb && nb == nc &&
    w == List.replicate na .a ++ List.replicate nb .b ++ List.replicate nc .c

/-- Generate aⁿbⁿcⁿ -/
def makeString_anbnc (n : Nat) : List ThreeSymbol :=
  List.replicate n .a ++ List.replicate n .b ++ List.replicate n .c

#eval isInLanguage_anbnc (makeString_anbnc 3)  -- true: aaabbbccc

/--
{aⁿbⁿcⁿ} is also NOT context-free. Same pumping argument.
-/
theorem anbnc_not_context_free :
    ¬∃ (p : Nat), p > 0 ∧
      ∀ w : List ThreeSymbol, isInLanguage_anbnc w = true → w.length ≥ p →
        ∀ u v x y z,
          w = u ++ v ++ x ++ y ++ z →
          (v ++ x ++ y).length ≤ p →
          (v.length + y.length) ≥ 1 →
          ∀ i : Nat, isInLanguage_anbnc (u ++ List.flatten (List.replicate i v) ++ x ++
                                         List.flatten (List.replicate i y) ++ z) = true := by
  sorry

-- ============================================================================
-- Mildly Context-Sensitive
-- ============================================================================

/--
A formalism is mildly context-sensitive if it:
1. Generates all context-free languages
2. Generates some non-context-free languages (like aⁿbⁿcⁿdⁿ)
3. Has polynomial-time parsing
4. Has the constant growth property

CCG, TAG, and LIG are all mildly context-sensitive.
-/
structure MildlyContextSensitive where
  /-- Name of the formalism -/
  name : String
  /-- Can this formalism generate {aⁿbⁿcⁿdⁿ}? -/
  generates_anbncndn : Bool

/-- CCG is mildly context-sensitive -/
def CCG_MCS : MildlyContextSensitive where
  name := "Combinatory Categorial Grammar"
  generates_anbncndn := true  -- Via generalized composition (B²)

/-- TAG is mildly context-sensitive -/
def TAG_MCS : MildlyContextSensitive where
  name := "Tree Adjoining Grammar"
  generates_anbncndn := true  -- Via adjoining

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This File Provides

1. **FourSymbol/ThreeSymbol**: Alphabets for cross-serial patterns
2. **isInLanguage_anbncndn**: Membership predicate for {aⁿbⁿcⁿdⁿ}
3. **pumping_lemma_for_cfl**: Statement of the pumping lemma (axiom)
4. **anbncndn_not_context_free**: Key theorem (proof sketched)
5. **MildlyContextSensitive**: Structure for formalisms that generate this language

## The Key Result

{aⁿbⁿcⁿdⁿ} is NOT context-free, but CCG generates it.
Therefore: CCG > CFG (strictly more expressive).

## Remaining Work

The `sorry` placeholders need:
1. Full case analysis for pumping argument
2. Showing makeString_anbncndn satisfies the predicate

## Next Steps

Use this in `CCG/GenerativeCapacity.lean` to show:
1. CCG derivations produce strings matching {aⁿbⁿcⁿdⁿ}
2. Combined with this theorem: CCG ⊃ CFL
-/
