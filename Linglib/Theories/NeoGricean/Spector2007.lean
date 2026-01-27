/-
# Scalar Implicatures: Exhaustivity and Gricean Reasoning

Formalization of Spector (2007) "Scalar implicatures: exhaustivity and Gricean reasoning"
Proceedings of the ESSLLI 2003 Student Session (revised 2007).

## Main Result

**Theorem**: For any positive proposition P, Max(P) = {Exhaust(P)}.

This shows that exhaustive interpretation is derivable from Gricean maxims:
- The speaker chose P over alternatives (Quantity)
- The speaker believes P (Quality)
- Assuming maximal informativeness → exhaustive reading

## Key Concepts

1. **Valuations**: Assignments of truth values to atoms (modeled as sets of true atoms)
2. **Propositions**: Sets of valuations
3. **Favoring**: P favors literal L iff flipping L can change P's truth value
4. **Positive propositions**: Favor only positive literals (equivalent to negation-free)
5. **Exhaustification**: Keep only minimal valuations
6. **Gricean reasoning**: I(P) = states making P optimal; Max(P) = most informed such states

## References

- Spector (2007). Scalar implicatures: exhaustivity and Gricean reasoning.
- Groenendijk & Stokhof (1984). Studies on the semantics of questions.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Finite.Basic

namespace NeoGricean.Spector2007

-- ============================================================================
-- PART 1: Propositional Framework (Appendix, Section 1)
-- ============================================================================

/-
"A valuation is uniquely defined by the values it assigns to the positive literals.
Hereafter, we treat valuations as functions from atoms to {0, 1}."

For simplicity, we model valuations as Finsets of atoms (the atoms that are true).
This matches Spector's later convention: "We now represent a valuation as the set
of atoms it makes true."
-/

variable (Atom : Type*) [DecidableEq Atom]

/--
A valuation assigns truth values to atoms.
We represent it as the set of atoms that are TRUE.
-/
abbrev Valuation := Finset Atom

/--
A proposition is a set of valuations (the valuations that make it true).
-/
abbrev Proposition := Set (Valuation Atom)

/--
A literal is either an atom (positive) or its negation (negative).
-/
inductive Literal (Atom : Type*)
  | pos : Atom → Literal Atom  -- [p]
  | neg : Atom → Literal Atom  -- [¬p]
  deriving DecidableEq, Repr

namespace Literal

variable {α : Type*} [DecidableEq α]

/-- The atom of a literal. -/
def atom : Literal α → α
  | pos a => a
  | neg a => a

/-- Whether a literal is positive. -/
def isPositive : Literal α → Bool
  | pos _ => true
  | neg _ => false

/-- The negation of a literal. -/
def negate : Literal α → Literal α
  | pos a => neg a
  | neg a => pos a

/-- A valuation satisfies a literal. -/
def satisfies (L : Literal α) (V : Finset α) : Bool :=
  match L with
  | pos a => a ∈ V
  | neg a => a ∉ V

end Literal

-- ============================================================================
-- PART 2: Favoring and Polarity (Appendix, Section 2)
-- ============================================================================

/-
"Def 2 (favoring): Let F be a formula and L be a literal distinct from ⊥, ⊤.
Then F favors L if there exists a valuation V such that V(F) = V(L) = 1 and
such that V_{-L}(F) = 0"

This is the key concept: P favors L iff there's a valuation where both P and L
are true, but flipping L makes P false.
-/

/--
V_{-L}: The valuation identical to V except over the atom of L.
If L = [p], then V_{-L} has p ∉ V_{-L} iff p ∈ V.
If L = [¬p], then V_{-L} has p ∈ V_{-L} iff p ∉ V.
-/
def flipLiteral (V : Valuation Atom) (L : Literal Atom) : Valuation Atom :=
  let a := L.atom
  if h : a ∈ V then V.erase a else V.cons a h

/--
**Definition 2 (Favoring)**: A proposition P favors a literal L if there exists
a valuation V such that:
1. V ∈ P (V makes P true)
2. L.satisfies V = true (V makes L true)
3. flipLiteral V L ∉ P (flipping L makes P false)
-/
def favors (P : Proposition Atom) (L : Literal Atom) : Prop :=
  ∃ V : Valuation Atom, V ∈ P ∧ L.satisfies V ∧ flipLiteral Atom V L ∉ P

/--
**Definition 4 (Positive Proposition)**: A proposition is positive if it favors
at least one positive literal and no negative literal.

"A positive proposition is a proposition that favors no negative literal and
is distinct from ⊥ and ⊤."
-/
def isPositive (P : Proposition Atom) : Prop :=
  (∃ a : Atom, favors Atom P (.pos a)) ∧ (∀ a : Atom, ¬favors Atom P (.neg a))

/--
A proposition is negative if it favors at least one negative literal and no
positive literal.
-/
def isNegative (P : Proposition Atom) : Prop :=
  (∃ a : Atom, favors Atom P (.neg a)) ∧ (∀ a : Atom, ¬favors Atom P (.pos a))

-- ============================================================================
-- PART 3: Exhaustification (Section 3.3.2, Appendix)
-- ============================================================================

/-
"Exhaustification:
Let P be any non-negative proposition, then the function Exhaust is defined as:
Exhaust(P) = {V | V ∈ P and there is no valuation V' in P such that V' ⊂ V}"

This is the propositional counterpart of Groenendijk & Stokhof's exhaustivity
operator - keep only the minimal valuations.
-/

/--
V' is a proper subset of V (as sets of true atoms).
-/
def properSubset (V' V : Valuation Atom) : Prop :=
  V' ⊂ V

/--
**Definition 6 (Exhaustification)**: The set of minimal valuations in P.

Exhaust(P) = {V ∈ P | ¬∃V' ∈ P, V' ⊂ V}
-/
def Exhaust (P : Proposition Atom) : Proposition Atom :=
  {V | V ∈ P ∧ ∀ V' ∈ P, ¬(V' ⊂ V)}

/--
**Definition 5 (Positive Extension)**: The upward closure of P.

Pos(P) = {V | ∃V' ∈ P, V' ⊆ V}

"For any non-negative proposition P, there is a unique positive proposition Q
such that P entails Q and Q entails all other positive propositions that P entails."
-/
def Pos (P : Proposition Atom) : Proposition Atom :=
  {V | ∃ V' ∈ P, V' ⊆ V}

-- Basic properties

omit [DecidableEq Atom] in
theorem Exhaust_subset (P : Proposition Atom) : Exhaust Atom P ⊆ P :=
  fun _ hV => hV.1

omit [DecidableEq Atom] in
/--
Helper lemma: Every element of P has a minimal element below it in P.
Uses strong induction on Finset cardinality.
-/
lemma exists_minimal (P : Set (Valuation Atom)) (s : Valuation Atom) (hs : s ∈ P) :
    ∃ t ∈ P, t ⊆ s ∧ ∀ u ∈ P, ¬(u ⊂ t) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hmin : ∀ u ∈ P, ¬(u ⊂ s)
    · exact ⟨s, hs, Finset.Subset.refl s, hmin⟩
    · simp only [not_forall, not_not] at hmin
      obtain ⟨u, huP, husub⟩ := hmin
      obtain ⟨t, htP, htub, htmin⟩ := ih u husub huP
      exact ⟨t, htP, htub.trans husub.subset, htmin⟩

/--
Helper: If P is positive and W ∈ P and a ∉ W, then W ∪ {a} ∈ P.
(Otherwise P would favor [¬a].)
-/
lemma positive_upward_closed (P : Proposition Atom) (hpos : isPositive Atom P)
    (W : Valuation Atom) (hWP : W ∈ P) (a : Atom) (ha_not_W : a ∉ W) :
    W.cons a ha_not_W ∈ P := by
  -- If W ∪ {a} ∉ P, then P favors [¬a], contradicting positivity
  by_contra h_not_P
  -- P favors [¬a]: W ∈ P, [¬a].satisfies W = true, flipLiteral W [¬a] ∉ P
  have hfavors : favors Atom P (.neg a) := by
    use W
    refine ⟨hWP, ?_, ?_⟩
    · -- [¬a].satisfies W = (a ∉ W) = true
      simp [Literal.satisfies, ha_not_W]
    · -- flipLiteral W [¬a] = W ∪ {a} ∉ P
      simp only [flipLiteral, Literal.atom, dif_neg ha_not_W]
      exact h_not_P
  -- But hpos says P doesn't favor any negative literal
  exact hpos.2 a hfavors

-- Remove extra lemma marker if needed

/--
Helper: Positive propositions are upward closed (if V' ⊆ V and V' ∈ P, then V ∈ P).
Proved by strong induction on |V \ V'| (the "gap" between V' and V).
-/
lemma positive_superset_mem (P : Proposition Atom) (hpos : isPositive Atom P)
    (V' V : Valuation Atom) (hV'P : V' ∈ P) (hV'_sub : V' ⊆ V) : V ∈ P := by
  -- Induction on the cardinality of V \ V'
  generalize hn : V.card - V'.card = n
  induction n using Nat.strong_induction_on generalizing V' with
  | _ n ih =>
    -- Either V' = V or V' ⊂ V
    rcases eq_or_ssubset_of_subset hV'_sub with heq | hsub
    · -- V' = V: trivial
      rw [← heq]; exact hV'P
    · -- V' ⊂ V: there exists a ∈ V \ V'
      obtain ⟨a, ha_V, ha_not_V'⟩ := Finset.exists_of_ssubset hsub
      -- V'.cons a ∈ P by upward closure
      have hcons_P : V'.cons a ha_not_V' ∈ P := positive_upward_closed Atom P hpos V' hV'P a ha_not_V'
      -- V'.cons a ⊆ V
      have hcons_sub : V'.cons a ha_not_V' ⊆ V := by
        intro x hx
        simp only [Finset.mem_cons] at hx
        cases hx with
        | inl heq => rw [heq]; exact ha_V
        | inr hxV' => exact hV'_sub hxV'
      -- The gap shrinks: |V| - |V'.cons a| < |V| - |V'|
      have hcard_V' : V'.card < V.card := Finset.card_lt_card hsub
      have hcard_cons : (V'.cons a ha_not_V').card = V'.card + 1 := Finset.card_cons ha_not_V'
      have hgap_lt : V.card - (V'.cons a ha_not_V').card < n := by omega
      -- Apply IH with V'.cons a
      exact ih (V.card - (V'.cons a ha_not_V').card) hgap_lt (V'.cons a ha_not_V') hcons_P hcons_sub rfl

omit [DecidableEq Atom] in
theorem P_subset_Pos (P : Proposition Atom) : P ⊆ Pos Atom P :=
  fun V hV => ⟨V, hV, Finset.Subset.refl V⟩

/--
**Fact 1**: If P is positive, then Pos(P) = P.

"If P is positive, Pos(P) = P"
-/
theorem Pos_of_positive (P : Proposition Atom) (hpos : isPositive Atom P) :
    Pos Atom P = P := by
  ext V
  constructor
  · -- Pos(P) ⊆ P for positive P
    intro ⟨V', hV'P, hV'_sub⟩
    -- Since P is positive, it's upward closed: V' ∈ P and V' ⊆ V implies V ∈ P
    exact positive_superset_mem Atom P hpos V' V hV'P hV'_sub
  · -- P ⊆ Pos(P)
    intro hV
    exact P_subset_Pos Atom P hV

omit [DecidableEq Atom] in
/--
**Fact 2**: Pos(Exhaust(P)) = Pos(P).

"Pos(Exhaust(P)) = P" [when P is positive, this is Pos(P)]
-/
theorem Pos_Exhaust_eq_Pos (P : Proposition Atom) :
    Pos Atom (Exhaust Atom P) = Pos Atom P := by
  ext V
  constructor
  · -- Pos(Exhaust(P)) ⊆ Pos(P)
    intro ⟨V', hV'_exh, hV'_sub⟩
    exact ⟨V', hV'_exh.1, hV'_sub⟩
  · -- Pos(P) ⊆ Pos(Exhaust(P))
    intro ⟨V', hV'P, hV'_sub⟩
    -- V' ∈ P, so there's a minimal V'' ⊆ V' in Exhaust(P)
    obtain ⟨V'', hV''P, hV''_sub_V', hV''_min⟩ := exists_minimal Atom P V' hV'P
    -- V'' is in Exhaust(P) since it's minimal
    have hV''_exh : V'' ∈ Exhaust Atom P := ⟨hV''P, hV''_min⟩
    -- V'' ⊆ V' ⊆ V, so V ∈ Pos(Exhaust(P))
    exact ⟨V'', hV''_exh, hV''_sub_V'.trans hV'_sub⟩

-- ============================================================================
-- PART 4: Gricean Information States (Section 2)
-- ============================================================================

/-
"Def 3: I(S, α, Q) = {i | i/Q ⊆ α and ∀α' (α' ∈ S and i/Q ⊆ α') → ¬(α' ⊂ α)}"

Information states where α is the optimal answer: no strictly better alternative
is entailed by the speaker's beliefs.

For simplicity, we work with the case where alternatives = all positive propositions.
-/

/--
An information state is itself a proposition (set of valuations the speaker
considers possible).
-/
abbrev InfoState := Proposition Atom

/--
**Definition 3 (Optimal States)**: I(P) is the set of information states where
P is the strongest positive proposition entailed.

I(P) = {i | Pos(i) = P}

An information state i makes P optimal iff P is the strongest positive proposition
that i entails.
-/
def I (P : Proposition Atom) : Set (InfoState Atom) :=
  {i | Pos Atom i = P}

/--
**Definition 4 (Maximal Optimal States)**: Max(P) is the set of maximal elements
of I(P) - the most informed states that still make P optimal.

"Max(S, α, Q) = {i | i ∈ I(S, α, Q) and ∀i' (i' ∈ I(S, α, Q)) → ¬(i'/Q ⊂ i/Q)}"

In our setting: Max(P) = {i ∈ I(P) | ∀i' ∈ I(P), ¬(i' ⊂ i)}
-/
def Max (P : Proposition Atom) : Set (InfoState Atom) :=
  {i | i ∈ I Atom P ∧ ∀ i' ∈ I Atom P, ¬(i' ⊂ i)}

-- ============================================================================
-- PART 5: Main Theorem (Section 3.3.2)
-- ============================================================================

/-
"Theorem: if P is a positive proposition, then Max(P) = {Exhaust(P)}, and
therefore P implicates Exhaust(P)."

This is the main result: Gricean reasoning leads to exhaustive interpretation.
-/

/--
**Lemma**: Exhaust(P) ∈ I(P) for positive P.

Since Pos(Exhaust(P)) = Pos(P) = P (by Facts 1 and 2), Exhaust(P) is an
information state that makes P optimal.
-/
theorem Exhaust_mem_I (P : Proposition Atom) (hpos : isPositive Atom P) :
    Exhaust Atom P ∈ I Atom P := by
  simp only [I, Set.mem_setOf_eq]
  rw [Pos_Exhaust_eq_Pos, Pos_of_positive Atom P hpos]

/--
**Lemma**: Exhaust(P) entails all members of I(P).

"We want to show that Exhaust(P) entails all the other members of I(P)."
-/
theorem Exhaust_entails_I (P : Proposition Atom) (_hpos : isPositive Atom P) :
    ∀ i ∈ I Atom P, Exhaust Atom P ⊆ i := by
  intro i hi V hV_exh
  -- V is a minimal element of P
  have hV_P : V ∈ P := hV_exh.1
  have hV_min : ∀ V' ∈ P, ¬(V' ⊂ V) := hV_exh.2
  -- Since i ∈ I(P), we have Pos(i) = P
  have hi_pos : Pos Atom i = P := hi
  -- Key fact: i ⊆ P (since for any V' ∈ i, V' ∈ Pos(i) = P by reflexivity)
  have hi_sub_P : i ⊆ P := fun V' hV'i =>
    hi_pos ▸ (P_subset_Pos Atom i hV'i)
  -- We need to show V ∈ i. By contradiction, assume V ∉ i.
  by_contra hV_not_i
  -- Since V ∈ P = Pos(i), there exists V' ∈ i with V' ⊆ V
  have hV_in_Pos_i : V ∈ Pos Atom i := hi_pos ▸ hV_P
  obtain ⟨V', hV'i, hV'_sub⟩ := hV_in_Pos_i
  -- Since V ∉ i and V' ∈ i with V' ⊆ V, we must have V' ≠ V
  have hV'_ne : V' ≠ V := fun h => hV_not_i (h ▸ hV'i)
  -- So V' ⊂ V (proper subset)
  have hV'_ssub : V' ⊂ V := Finset.ssubset_iff_subset_ne.mpr ⟨hV'_sub, hV'_ne⟩
  -- But V' ∈ i ⊆ P, so V' ∈ P with V' ⊂ V, contradicting V's minimality
  exact hV_min V' (hi_sub_P hV'i) hV'_ssub

/--
**MAIN THEOREM** (Spector 2007, Section 3.3.2):

For any positive proposition P, Max(P) = {Exhaust(P)}.

"Theorem: if P is a positive proposition, then Max(P) = {Exhaust(P)}, and
therefore P implicates Exhaust(P)."

This derives exhaustive interpretation from Gricean reasoning:
- The speaker uttered P (Quality: they believe P)
- P was optimal among alternatives (Quantity: no better option)
- Assuming maximal informativeness → the speaker's state is Exhaust(P)
- Therefore P implicates Exhaust(P)
-/
theorem main_theorem (P : Proposition Atom) (hpos : isPositive Atom P) :
    Max Atom P = {Exhaust Atom P} := by
  ext i
  simp only [Max, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- If i ∈ Max(P), then i = Exhaust(P)
    intro ⟨hi_I, hi_max⟩
    -- Exhaust(P) ⊆ i (by Exhaust_entails_I)
    have h1 : Exhaust Atom P ⊆ i := Exhaust_entails_I Atom P hpos i hi_I
    -- i ⊆ Exhaust(P) (by maximality)
    -- If i ⊃ Exhaust(P), then there's V ∈ i \ Exhaust(P)
    -- But Exhaust(P) ∈ I(P), so i can't be a proper superset
    have h2 : i ⊆ Exhaust Atom P := by
      by_contra h
      obtain ⟨V, hVi, hV_not_exh⟩ := Set.not_subset.mp h
      -- V ∈ i but V ∉ Exhaust(P)
      -- Since Exhaust(P) ⊆ i (by h1) but V ∈ i \ Exhaust(P), we have Exhaust(P) ⊂ i
      have hExh_ne : Exhaust Atom P ≠ i := fun heq => hV_not_exh (heq ▸ hVi)
      have hExh_ssub : Exhaust Atom P ⊂ i := Set.ssubset_iff_subset_ne.mpr ⟨h1, hExh_ne⟩
      -- This contradicts hi_max applied to Exhaust(P)
      exact hi_max (Exhaust Atom P) (Exhaust_mem_I Atom P hpos) hExh_ssub
    exact Set.Subset.antisymm h2 h1
  · -- If i = Exhaust(P), then i ∈ Max(P)
    intro heq
    rw [heq]
    constructor
    · exact Exhaust_mem_I Atom P hpos
    · intro i' hi' hsub
      -- Need to show ¬(i' ⊂ Exhaust(P))
      -- i' ∈ I(P) means Pos(i') = P
      -- By Exhaust_entails_I: Exhaust(P) ⊆ i'
      -- If i' ⊂ Exhaust(P), then ¬(Exhaust(P) ⊆ i') by definition of ⊂
      -- Contradiction!
      have h := Exhaust_entails_I Atom P hpos i' hi'
      exact hsub.2 h

-- ============================================================================
-- PART 6: Connection to Scalar Implicatures
-- ============================================================================

/-
The main theorem shows that for positive propositions (like "A or B"), the
Gricean reasoning leads to exhaustive interpretation.

Example: "A or B" has the exhaustive reading "exactly one of A or B"
because Max(A∨B) = {Exhaust(A∨B)} = {{A}, {B}}.
-/

/--
Example: The proposition "A or B" (at least one of A, B is true).
-/
def orProp (A B : Atom) : Proposition Atom :=
  {V | A ∈ V ∨ B ∈ V}

/--
Example: The exhaustification of "A or B" is "exactly A or exactly B".

Note: This is the MINIMAL exclusive disjunction - singletons only.
The more general "A xor B" (A ∈ V ↔ B ∉ V) includes non-minimal sets like {A, C}.
-/
def exclOrProp (A B : Atom) : Proposition Atom :=
  {V | V = {A} ∨ V = {B}}

/--
The exhaustification of "A or B" yields exclusive disjunction (minimal singletons).
-/
theorem exhaust_or_eq_exclOr (A B : Atom) (_hne : A ≠ B) :
    Exhaust Atom (orProp Atom A B) = exclOrProp Atom A B := by
  ext V
  simp only [Exhaust, orProp, exclOrProp, Set.mem_setOf_eq]
  constructor
  · -- Exhaust(A∨B) ⊆ {{A}, {B}}
    intro ⟨hV_or, hV_min⟩
    cases hV_or with
    | inl hA =>
      -- A ∈ V. We claim V = {A}.
      left
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        by_contra hne_x
        -- x ∈ V but x ≠ A. Then V.erase x ⊂ V and A ∈ V.erase x.
        apply hV_min (V.erase x)
        · left; exact Finset.mem_erase.mpr ⟨fun h => hne_x h.symm, hA⟩
        · exact Finset.erase_ssubset hx
      · intro hxa; rw [hxa]; exact hA
    | inr hB =>
      -- B ∈ V. We claim V = {B}.
      right
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        by_contra hne_x
        apply hV_min (V.erase x)
        · right; exact Finset.mem_erase.mpr ⟨fun h => hne_x h.symm, hB⟩
        · exact Finset.erase_ssubset hx
      · intro hxb; rw [hxb]; exact hB
  · -- {{A}, {B}} ⊆ Exhaust(A∨B)
    intro hV
    cases hV with
    | inl heqA =>
      rw [heqA]
      constructor
      · left; exact Finset.mem_singleton_self A
      · intro V' hV' hsub
        -- V' ⊂ {A} means V' = ∅
        have : V' = ∅ := Finset.eq_empty_of_ssubset_singleton hsub
        rw [this] at hV'
        cases hV' with
        | inl hA' => exact Finset.notMem_empty A hA'
        | inr hB' => exact Finset.notMem_empty B hB'
    | inr heqB =>
      rw [heqB]
      constructor
      · right; exact Finset.mem_singleton_self B
      · intro V' hV' hsub
        have : V' = ∅ := Finset.eq_empty_of_ssubset_singleton hsub
        rw [this] at hV'
        cases hV' with
        | inl hA' => exact Finset.notMem_empty A hA'
        | inr hB' => exact Finset.notMem_empty B hB'

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Core Framework
- `Valuation`: Assignments of truth to atoms (as Finsets)
- `Proposition`: Sets of valuations
- `Literal`: Positive or negative atoms
- `favors`: When a proposition "favors" a literal

### Polarity Classification
- `isPositive`: Favors positive literals only
- `isNegative`: Favors negative literals only

### Exhaustification
- `Exhaust`: Minimal valuations in a proposition
- `Pos`: Upward closure (strongest positive entailed)

### Gricean Reasoning
- `I P`: Information states making P optimal
- `Max P`: Maximal such states (most informed)

### Main Result
- `main_theorem`: Max(P) = {Exhaust(P)} for positive P

This shows that exhaustive interpretation is a consequence of Gricean reasoning,
not an arbitrary stipulation.

## Connection to Spector (2016)

The `Exhaust` operator here corresponds to `exhMW` in Exhaustivity.lean.
Spector (2007) shows WHY we exhaustify (Gricean reasoning).
Spector (2016) compares DIFFERENT exhaustivity operators (exhMW vs exhIE).

## Conjectured Connection to RSA

RSA (Rational Speech Acts) is a probabilistic formalization of Gricean reasoning.
The key connection is:

**Spector's Classical Gricean Result:**
```
Max(P) = {Exhaust(P)}   for positive P
```

**RSA Probabilistic Version:**
```
L1(u) ∝ Prior(w) · S1(u | w)
S1(u | w) ∝ L0(w | u)^α
```

**Conjectured Limit Theorem:**
```
lim_{α → ∞} L1(u) concentrates on Exhaust(⟦u⟧)
```

### Intuition

1. **Classical**: Max(P) picks the MOST INFORMATIVE info state consistent with P
2. **RSA**: Higher α makes S1 prefer MORE INFORMATIVE utterances more strongly
3. **Connection**: At α → ∞, S1 becomes deterministic (always picks most informative)
4. **Result**: L1 at high α should converge to exhaustive interpretation

### Formal Statement (Sketch)

Given:
- `S : RSAScenario U W` with Boolean semantics
- `u : U` an utterance
- `⟦u⟧ = {w | φ(u,w) = 1}` the semantic denotation

Define:
- `Exhaust_RSA(u) = minimal worlds in ⟦u⟧`
- `L1_α(u)` = L1 distribution with rationality α

**Conjecture**: For all ε > 0, there exists N such that for all α > N,
```
∑_{w ∈ Exhaust_RSA(u)} L1_α(u)(w) > 1 - ε
```

### Implementation Notes

To formalize this, we would need:
1. Parameterize RSAScenario by α (already done)
2. Define `Exhaust_RSA` matching `Exhaust` from this file
3. Prove monotonicity lemmas about L1 as α increases
4. Use limits or ε-δ formulation for the convergence

This would provide a formal bridge between:
- Classical Gricean pragmatics (this file)
- Probabilistic RSA (Core/RSA.lean)
- Showing RSA generalizes classical reasoning with probabilistic softening
-/

end NeoGricean.Spector2007
