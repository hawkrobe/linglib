import Linglib.Core.Mereology

/-! # Truthmaker Semantics (Fine 2017) @cite{fine-2017}

State-based propositions grounded in `Core/Mereology.lean`. Propositions are
sets of *verifying states*, where states form a join-semilattice (the same
`SemilatticeSup` infrastructure used for events and plural individuals).

## Part I: Unilateral Propositions (§§1–6)

The first part formalizes the unilateral fragment needed by
Bondarenko & Elliott (2026): propositions as sets of verifiers,
conjunction via fusion, content parthood, and attitude distribution.

## Part II: Bilateral Propositions (§§7–13)

The second part formalizes Fine's full bilateral conception: propositions
as *pairs* (V, F) of verifier and falsifier sets, with negation as
the swap operation. The key structural insight is the duality between
conjunction and disjunction at the verification/falsification level:

| Connective | Verified by  | Falsified by |
|------------|-------------|--------------|
| A ∧ B      | fusion (⊔)  | union (∨)    |
| A ∨ B      | union (∨)   | fusion (⊔)   |
| ¬A         | falsifiers  | verifiers    |

## Key ideas

1. **Conjunction via fusion**: p ∧ q is verified by the fusion s₁ ⊔ s₂ of
   verifiers of p and q (not by set intersection). This makes conjunction
   mereologically structured.

2. **Disjunction via union**: p ∨ q is verified by any verifier of either
   p or q. This is purely set-theoretic — no mereological structure.

3. **Content parthood**: q is a content part of p when every verifier of p
   has a part that verifies q. This is strictly weaker than entailment.

4. **Bilateral propositions**: Propositions are (V, F) pairs. Negation swaps
   them; conjunction fuses verifiers but unions falsifiers; disjunction unions
   verifiers but fuses falsifiers.

5. **Exclusivity/Exhaustivity**: No verifier is compatible with a falsifier
   (exclusivity); every possible state is compatible with a verifier or
   falsifier (exhaustivity).

6. **Subject-matter**: σ(A) = the fusion of all verifiers of A. Two sentences
   can be logically equivalent but differ in subject-matter.

## References

- Fine, K. (2017). Truthmaker semantics. In *A Companion to the Philosophy
  of Language* (2nd ed.). Wiley.
- Bondarenko, T. & Elliott, P.D. (2026). Monotonicity via mereology.
  @cite{bondarenko-elliott-2026}
-/

namespace Semantics.Truthmaker

-- ════════════════════════════════════════════════════
-- § 1. State-Based Propositions
-- ════════════════════════════════════════════════════

/-- A truthmaker proposition: a set of verifying states.
    A state s verifies p iff p s holds. -/
abbrev TMProp (S : Type*) := S → Prop

/-- Conjunction via fusion (Bondarenko & Elliott §3.1).
    s verifies p ∧ q iff s = s₁ ⊔ s₂ for some s₁ verifying p and s₂ verifying q.
    This is the key departure from classical conjunction (set intersection). -/
def tmAnd {S : Type*} [SemilatticeSup S] (p q : TMProp S) : TMProp S :=
  λ s => ∃ s₁ s₂, p s₁ ∧ q s₂ ∧ s = s₁ ⊔ s₂

/-- Disjunction via union.
    s verifies p ∨ q iff s verifies p or s verifies q.
    This is set-theoretic — no mereological structure. -/
def tmOr {S : Type*} (p q : TMProp S) : TMProp S :=
  λ s => p s ∨ q s

-- ════════════════════════════════════════════════════
-- § 2. Content Parthood
-- ════════════════════════════════════════════════════

/-- Content parthood (Bondarenko & Elliott Def 3).
    q is a content part of p iff every verifier of p has a part (≤) that
    verifies q. This is strictly weaker than entailment: p entails q
    requires every *world* satisfying p to satisfy q, while content
    parthood only requires every *verifier* of p to have a *part*
    verifying q. -/
def contentPart {S : Type*} [Preorder S] (q p : TMProp S) : Prop :=
  ∀ s, p s → ∃ t, q t ∧ t ≤ s

/-- Content parthood is reflexive: p is a content part of itself. -/
theorem contentPart_refl {S : Type*} [Preorder S] (p : TMProp S) :
    contentPart p p := by
  intro s hp
  exact ⟨s, hp, le_refl s⟩

/-- Content parthood is transitive. -/
theorem contentPart_trans {S : Type*} [Preorder S] (p q r : TMProp S)
    (hpq : contentPart p q) (hqr : contentPart q r) :
    contentPart p r := by
  intro s hr
  obtain ⟨t, hqt, htles⟩ := hqr s hr
  obtain ⟨u, hpu, hulet⟩ := hpq t hqt
  exact ⟨u, hpu, le_trans hulet htles⟩

-- ════════════════════════════════════════════════════
-- § 3. Content Parts of Conjunctions
-- ════════════════════════════════════════════════════

/-- p is a content part of p ∧ q.
    Proof: if s verifies p ∧ q, then s = s₁ ⊔ s₂ with p s₁.
    Since s₁ ≤ s₁ ⊔ s₂ = s (by `le_sup_left`), s₁ is a part of s
    that verifies p. -/
theorem contentPart_and_left {S : Type*} [SemilatticeSup S] (p q : TMProp S) :
    contentPart p (tmAnd p q) := by
  intro s ⟨s₁, _, hp, _, hs⟩
  exact ⟨s₁, hp, hs ▸ le_sup_left⟩

/-- q is a content part of p ∧ q.
    Symmetric to `contentPart_and_left`, using `le_sup_right`. -/
theorem contentPart_and_right {S : Type*} [SemilatticeSup S] (p q : TMProp S) :
    contentPart q (tmAnd p q) := by
  intro s ⟨_, s₂, _, hq, hs⟩
  exact ⟨s₂, hq, hs ▸ le_sup_right⟩

-- ════════════════════════════════════════════════════
-- § 4. Attitude Semantics
-- ════════════════════════════════════════════════════

/-- An attitude holds when the agent's total information state has a
    verifier-part for the proposition.
    σ : E → S maps agents to their total information states.
    attHolds σ p x iff ∃ s ≤ σ(x) such that p(s). -/
def attHolds {S E : Type*} [Preorder S] (σ : E → S) (p : TMProp S) (x : E) : Prop :=
  ∃ s, p s ∧ s ≤ σ x

-- ════════════════════════════════════════════════════
-- § 5. Conjunction Distribution (Bondarenko & Elliott Thm 1)
-- ════════════════════════════════════════════════════

/-- Upward-monotone attitudes distribute over conjunction (forward direction).
    If the agent's state verifies p ∧ q, then it verifies both p and q.

    Proof: p ∧ q is verified by s₁ ⊔ s₂ where p(s₁) and q(s₂).
    Since s₁ ≤ s₁ ⊔ s₂ ≤ σ(x) and s₂ ≤ s₁ ⊔ s₂ ≤ σ(x), we have
    attHolds for both p and q. -/
theorem mono_att_distrib_and {S E : Type*} [SemilatticeSup S]
    (σ : E → S) (p q : TMProp S) (x : E)
    (h : attHolds σ (tmAnd p q) x) :
    attHolds σ p x ∧ attHolds σ q x := by
  obtain ⟨s, ⟨s₁, s₂, hp, hq, hs⟩, hle⟩ := h
  constructor
  · exact ⟨s₁, hp, le_trans (hs ▸ le_sup_left) hle⟩
  · exact ⟨s₂, hq, le_trans (hs ▸ le_sup_right) hle⟩

/-- Conjunction distribution (converse direction).
    If the agent's state has parts verifying both p and q, then their
    fusion verifies p ∧ q and is also a part of σ(x).

    This requires `sup_le`: s₁ ≤ σ(x) ∧ s₂ ≤ σ(x) → s₁ ⊔ s₂ ≤ σ(x). -/
theorem mono_att_distrib_and_conv {S E : Type*} [SemilatticeSup S]
    (σ : E → S) (p q : TMProp S) (x : E)
    (hp : attHolds σ p x) (hq : attHolds σ q x) :
    attHolds σ (tmAnd p q) x := by
  obtain ⟨s₁, hps₁, hle₁⟩ := hp
  obtain ⟨s₂, hqs₂, hle₂⟩ := hq
  exact ⟨s₁ ⊔ s₂, ⟨s₁, s₂, hps₁, hqs₂, rfl⟩, sup_le hle₁ hle₂⟩

/-- Full conjunction distribution iff for upward-monotone attitudes.
    Combines the forward and converse directions. -/
theorem mono_att_distrib_and_iff {S E : Type*} [SemilatticeSup S]
    (σ : E → S) (p q : TMProp S) (x : E) :
    attHolds σ (tmAnd p q) x ↔ attHolds σ p x ∧ attHolds σ q x :=
  ⟨mono_att_distrib_and σ p q x,
   λ ⟨hp, hq⟩ => mono_att_distrib_and_conv σ p q x hp hq⟩

-- ════════════════════════════════════════════════════
-- § 6. Disjunction Does NOT Distribute
-- ════════════════════════════════════════════════════

/-- Disjunction does NOT generally satisfy content parthood.

    In truthmaker semantics, p ∨ q is verified by any verifier of p or
    any verifier of q (set union). But a verifier of p ∨ q that verifies
    only p need not have a part verifying q. So q is not generally a
    content part of p ∨ q.

    We state this as: there exist types and propositions where
    contentPart q (tmOr p q) fails. -/
theorem contentPart_or_not_general :
    ¬ (∀ (S : Type) (_ : SemilatticeSup S) (p q : TMProp S),
       contentPart q (tmOr p q)) := by
  intro h
  -- Use Nat with max as the semilattice (inferred)
  have := h Nat inferInstance (· = 0) (· = 1)
  -- 0 verifies p ∨ q (via left disjunct)
  obtain ⟨t, ht, hle⟩ := this 0 (Or.inl rfl)
  -- t must equal 1 (to verify q) and t ≤ 0
  omega


-- ════════════════════════════════════════════════════════════════════════════
-- PART II: BILATERAL PROPOSITIONS (Fine 2017 §5–6)
-- ════════════════════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════
-- § 7. Bilateral Propositions
-- ════════════════════════════════════════════════════

/-- A bilateral proposition: separate sets of verifiers and falsifiers.

    Fine (2017 §5): "A model M for the bilateral case will be a triple
    (S, ⊑, |·|) in which |p| for each atom p is now a pair (V, F) of
    a verification set V and a falsification set F."

    The unilateral `TMProp` is recovered by `BilProp.ver`. -/
@[ext] structure BilProp (S : Type*) where
  /-- States that verify (make true) the proposition -/
  ver : S → Prop
  /-- States that falsify (make false) the proposition -/
  fal : S → Prop

/-- Project a bilateral proposition to its unilateral (verifier-only) part.
    This recovers the `TMProp` from Part I. -/
def BilProp.toTM {S : Type*} (p : BilProp S) : TMProp S := p.ver

/-- Lift a unilateral proposition to bilateral by leaving falsifiers empty.
    (No state falsifies the proposition — appropriate for atoms in contexts
    where falsification isn't tracked.) -/
def TMProp.toBil {S : Type*} (p : TMProp S) : BilProp S :=
  ⟨p, λ _ => False⟩

-- ════════════════════════════════════════════════════
-- § 8. Bilateral Connectives
-- ════════════════════════════════════════════════════

/-- Negation: swap verifiers and falsifiers (Fine 2017 §5).
    s verifies ¬A iff s falsifies A; s falsifies ¬A iff s verifies A. -/
def bilNot {S : Type*} (p : BilProp S) : BilProp S :=
  ⟨p.fal, p.ver⟩

/-- Conjunction: verified by fusion, falsified by union (Fine 2017 §5).
    - s verifies A ∧ B iff s = s₁ ⊔ s₂ where s₁ verifies A and s₂ verifies B
    - s falsifies A ∧ B iff s falsifies A or s falsifies B

    Defined in terms of `tmAnd`/`tmOr` — the duality is explicit:
    conjunction *fuses* verifiers but *unions* falsifiers. -/
def bilAnd {S : Type*} [SemilatticeSup S] (p q : BilProp S) : BilProp S where
  ver := tmAnd p.ver q.ver
  fal := tmOr p.fal q.fal

/-- Disjunction: verified by union, falsified by fusion (Fine 2017 §5).
    - s verifies A ∨ B iff s verifies A or s verifies B
    - s falsifies A ∨ B iff s = s₁ ⊔ s₂ where s₁ falsifies A and s₂ falsifies B

    Exact dual of `bilAnd`: disjunction *unions* verifiers but *fuses* falsifiers. -/
def bilOr {S : Type*} [SemilatticeSup S] (p q : BilProp S) : BilProp S where
  ver := tmOr p.ver q.ver
  fal := tmAnd p.fal q.fal

-- ════════════════════════════════════════════════════
-- § 9. Double Negation and De Morgan Duality
-- ════════════════════════════════════════════════════

/-- Double negation is the identity. Definitionally true: swapping
    verifiers and falsifiers twice returns to the original. -/
theorem bilNot_involutive {S : Type*} (p : BilProp S) :
    bilNot (bilNot p) = p := rfl

/-- De Morgan: ¬(A ∧ B) has the same verifiers and falsifiers as ¬A ∨ ¬B.

    - Verifiers of ¬(A ∧ B) = falsifiers of A ∧ B = {s | A.fal s ∨ B.fal s}
    - Verifiers of ¬A ∨ ¬B = {s | (¬A).ver s ∨ (¬B).ver s} = {s | A.fal s ∨ B.fal s}

    - Falsifiers of ¬(A ∧ B) = verifiers of A ∧ B = {s | ∃ s₁ s₂, ...}
    - Falsifiers of ¬A ∨ ¬B = {s | ∃ s₁ s₂, (¬A).fal s₁ ∧ (¬B).fal s₂ ∧ ...}
      = {s | ∃ s₁ s₂, A.ver s₁ ∧ B.ver s₂ ∧ ...} -/
theorem deMorgan_and {S : Type*} [SemilatticeSup S] (p q : BilProp S) :
    bilNot (bilAnd p q) = bilOr (bilNot p) (bilNot q) := rfl

/-- De Morgan: ¬(A ∨ B) = ¬A ∧ ¬B. -/
theorem deMorgan_or {S : Type*} [SemilatticeSup S] (p q : BilProp S) :
    bilNot (bilOr p q) = bilAnd (bilNot p) (bilNot q) := rfl

-- ════════════════════════════════════════════════════
-- § 10. Modalized State Space and Compatibility
-- ════════════════════════════════════════════════════

/-- A possibility predicate distinguishes possible from impossible states
    within a state space. Fine (2017 §4): "(S, S⁰, ⊑) where S⁰ ⊆ S is
    the set of possible states and is required to be closed under Part
    (if s ∈ S⁰ and t ⊑ s then t ∈ S⁰)."

    We represent this as a predicate satisfying downward closure. -/
structure Possibility (S : Type*) [Preorder S] where
  /-- Which states are possible -/
  possible : S → Prop
  /-- Possible states are closed under parts (downward closed).
      If s is possible and t ≤ s, then t is possible. -/
  downClosed : ∀ (s t : S), possible s → t ≤ s → possible t

/-- Two states are compatible iff their fusion is possible (Fine 2017 §4).
    Incompatible states represent conflicting information — e.g., a state
    verifying "it's cold" and a state verifying "it's hot" are incompatible
    because their fusion is impossible. -/
def compatible {S : Type*} [SemilatticeSup S] (P : Possibility S) (s t : S) : Prop :=
  P.possible (s ⊔ t)

/-- Compatibility is symmetric. -/
theorem compatible_symm {S : Type*} [SemilatticeSup S] (P : Possibility S)
    (s t : S) : compatible P s t ↔ compatible P t s := by
  simp only [compatible, sup_comm]

-- ════════════════════════════════════════════════════
-- § 11. Exclusivity and Exhaustivity
-- ════════════════════════════════════════════════════

/-- Exclusivity (Fine 2017 §5): no verifier is compatible with a falsifier.
    If s verifies A and t falsifies A, then s ⊔ t is impossible.

    This is one direction of bivalence: verification and falsification are
    mutually incompatible. -/
def Exclusive {S : Type*} [SemilatticeSup S]
    (P : Possibility S) (A : BilProp S) : Prop :=
  ∀ s t, A.ver s → A.fal t → ¬ compatible P s t

/-- Exhaustivity (Fine 2017 §5): every possible state is compatible with
    a verifier or a falsifier.

    This is the other direction of bivalence: no possible state is
    undecided — it must be compatible with evidence for or against A. -/
def Exhaustive {S : Type*} [SemilatticeSup S]
    (P : Possibility S) (A : BilProp S) : Prop :=
  ∀ s, P.possible s →
    (∃ t, A.ver t ∧ compatible P s t) ∨ (∃ t, A.fal t ∧ compatible P s t)

/-- Negation preserves exclusivity: if A is exclusive, so is ¬A.
    (Swap verifiers/falsifiers — the incompatibility is symmetric.) -/
theorem exclusive_bilNot {S : Type*} [SemilatticeSup S]
    (P : Possibility S) (A : BilProp S) (h : Exclusive P A) :
    Exclusive P (bilNot A) := by
  intro s t hs ht hc
  exact h t s ht hs ((compatible_symm P s t).mp hc)

/-- Negation preserves exhaustivity: if A is exhaustive, so is ¬A. -/
theorem exhaustive_bilNot {S : Type*} [SemilatticeSup S]
    (P : Possibility S) (A : BilProp S) (h : Exhaustive P A) :
    Exhaustive P (bilNot A) := by
  intro s hs
  cases h s hs with
  | inl hv => exact Or.inr hv
  | inr hf => exact Or.inl hf

-- ════════════════════════════════════════════════════
-- § 12. Subject-Matter
-- ════════════════════════════════════════════════════

/-- Subject-matter of a proposition: the fusion of all its verifiers
    (Fine 2017 §II.2). Two sentences can be logically equivalent (true
    at the same worlds) but differ in subject-matter. -/
noncomputable def subjectMatter {S : Type*} [SupSet S]
    (A : BilProp S) : S :=
  sSup {s | A.ver s}

/-- A proposition is about another if its subject-matter is part of the
    other's. This gives a mereological account of "aboutness": "It's raining"
    is about the weather; "It's raining and 2+2=4" is about the weather AND
    arithmetic. -/
def isAbout {S : Type*} [Preorder S] [SupSet S]
    (A B : BilProp S) : Prop :=
  subjectMatter A ≤ subjectMatter B

-- ════════════════════════════════════════════════════
-- § 13. Conjunction Exclusivity Propagation
-- ════════════════════════════════════════════════════

/-- If A and B are both exclusive, then A ∧ B is exclusive.

    Proof sketch: if s verifies A ∧ B, then s = s₁ ⊔ s₂ with s₁ verifying A
    and s₂ verifying B. If t falsifies A ∧ B, then t falsifies A or t falsifies B.
    Either way, the fusion includes a verifier-falsifier pair for the same
    atomic proposition, which is impossible by exclusivity of A or B plus
    downward closure of possibility. -/
theorem exclusive_bilAnd {S : Type*} [SemilatticeSup S]
    (P : Possibility S) (A B : BilProp S)
    (hA : Exclusive P A) (hB : Exclusive P B) :
    Exclusive P (bilAnd A B) := by
  intro s t ⟨s₁, s₂, hvA, hvB, hs⟩ hfAB hcompat
  cases hfAB with
  | inl hfA =>
    -- t falsifies A, s₁ verifies A; show s₁ ⊔ t is impossible
    -- (s₁ ⊔ s₂) ⊔ t is possible and s₁ ⊔ t ≤ (s₁ ⊔ s₂) ⊔ t, so downClosed gives us compatible P s₁ t
    have : compatible P s₁ t := by
      unfold compatible at hcompat ⊢
      rw [hs] at hcompat
      exact P.downClosed _ _ hcompat (sup_le_sup_right le_sup_left t)
    exact hA s₁ t hvA hfA this
  | inr hfB =>
    have : compatible P s₂ t := by
      unfold compatible at hcompat ⊢
      rw [hs] at hcompat
      exact P.downClosed _ _ hcompat (sup_le_sup_right le_sup_right t)
    exact hB s₂ t hvB hfB this

end Semantics.Truthmaker
