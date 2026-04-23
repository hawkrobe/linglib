import Linglib.Core.Mereology
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.UpperLower.CompleteLattice

/-! # Truthmaker Semantics @cite{fine-2017} @cite{bondarenko-elliott-2026} @cite{jago-2026}

State-based propositions grounded in `Core/Mereology.lean`. Propositions are
sets of *verifying states*, where states form a join-semilattice (the same
`SemilatticeSup` infrastructure used for events and plural individuals).

## Files in this directory

- `Basic.lean` (this file) — unilateral and bilateral propositions, fusion-based
  connectives, content parthood (Down/Up/full), bilateral pairs with
  exclusivity/exhaustivity, subject-matter.
- `Inexact.lean` — inexact truthmaking and exact/inexact entailment.
- `Closure.lean` — closed/convex/regular closure operators (Jago Def 4),
  built on `Mereology.AlgClosure` and `Mereology.convexClosure`.
- `Entailment.lean` — analytic entailment (AC), FDE-style consequence, bridges.

## Part I: Unilateral propositions

The first part formalizes the unilateral fragment needed by
@cite{bondarenko-elliott-2026}: propositions as sets of verifiers,
conjunction via fusion, content parthood (Down clause), and attitude
distribution. Both halves of Jago's conjunctive parthood are exposed
(`IsSubsumedBy`, `Subserves`, `IsContentPart`).

## Part II: Bilateral propositions

The second part formalizes Fine's full bilateral conception: propositions
as *pairs* (V, F) of verifier and falsifier sets, with negation as
the swap operation. The duality between conjunction and disjunction at
the verification/falsification level:

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

3. **Content parthood (Jago Def 5)**: q is a content part of p when both
   the *Down* clause holds (every verifier of p has a part verifying q)
   AND the *Up* clause holds (every verifier of q is part of some verifier
   of p). The Down-only relation `IsSubsumedBy` is the relation
   @cite{bondarenko-elliott-2026} use for monotonicity arguments.

4. **Bilateral propositions**: Propositions are (V, F) pairs. Negation swaps
   them; conjunction fuses verifiers but unions falsifiers; disjunction unions
   verifiers but fuses falsifiers.

5. **Exclusivity/Exhaustivity**: No verifier is compatible with a falsifier
   (exclusivity); every possible state is compatible with a verifier or
   falsifier (exhaustivity).

6. **Subject-matter**: σ(A) = the fusion of *all* verifiers and falsifiers
   of A. Two sentences can be logically equivalent but differ in
   subject-matter; crucially, σ(¬A) = σ(A) (negation invariance).

## Citation discipline

- The encyclopedia survey @cite{jago-2026} is the entry point; specific
  technical claims trace back to Fine's two-part *Truthmaker Content*
  series (which are in *Journal of Philosophical Logic* 46(6), not the
  Wiley *Companion* chapter `fine-2017`). Section/page numbers internal
  to those papers are flagged `UNVERIFIED` until checked against PDFs.
- @cite{bondarenko-elliott-2026} definitions/theorem numbers are flagged
  `UNVERIFIED` since the manuscript has not been cross-checked.

-/

namespace Semantics.Truthmaker


-- ════════════════════════════════════════════════════
-- § 1. State-Based Propositions
-- ════════════════════════════════════════════════════

/-- A truthmaker proposition: a set of verifying states.
    A state `s` verifies `p` iff `p s` holds. -/
abbrev TMProp (S : Type*) := S → Prop

section Connectives
variable {S : Type*}

/-- Disjunction via union.
    `s` verifies `p ∨ q` iff `s` verifies `p` or `s` verifies `q`.
    Set-theoretic — no mereological structure. -/
def tmOr (p q : TMProp S) : TMProp S :=
  fun s => p s ∨ q s

variable [SemilatticeSup S]

/-- Conjunction via fusion (@cite{fine-2017}; @cite{bondarenko-elliott-2026}).
    `s` verifies `p ∧ q` iff `s = s₁ ⊔ s₂` for some `s₁` verifying `p`
    and `s₂` verifying `q`.
    The key departure from classical conjunction (set intersection). -/
def tmAnd (p q : TMProp S) : TMProp S :=
  fun s => ∃ s₁ s₂, p s₁ ∧ q s₂ ∧ s = s₁ ⊔ s₂

end Connectives

-- ════════════════════════════════════════════════════
-- § 2. Content Parthood (Jago Def 5: Up + Down)
-- ════════════════════════════════════════════════════

/-- **Down clause** of conjunctive parthood (@cite{jago-2026} Def 5;
    @cite{bondarenko-elliott-2026} content parthood):
    every verifier of `p` has a part verifying `q`.

    Re-export of `Mereology.IsSubsumedBy` — the Down clause is a generic
    poset relation, not truthmaker-specific.

    The Down-only relation suffices for @cite{bondarenko-elliott-2026}'s
    monotonicity arguments. -/
abbrev IsSubsumedBy {S : Type*} [Preorder S] (q p : TMProp S) : Prop :=
  Mereology.IsSubsumedBy q p

/-- **Up clause** of conjunctive parthood (@cite{jago-2026} Def 5):
    every verifier of `q` is part of some verifier of `p`.

    Re-export of `Mereology.Subserves`. The Up clause is more delicate:
    `Subserves p (tmAnd p q)` requires `q` to be inhabited (you need a
    witness to fuse with) — a deliberate departure from the Fine
    convention that propositions are nonempty. -/
abbrev Subserves {S : Type*} [Preorder S] (q p : TMProp S) : Prop :=
  Mereology.Subserves q p

/-- Full conjunctive parthood (@cite{jago-2026} Def 5):
    `q` is a content part of `p` iff both the Down and Up clauses hold.

    Re-export of `Mereology.IsContentPart`. Written `q ≤ p` in Jago's
    notation. -/
abbrev IsContentPart {S : Type*} [Preorder S] (q p : TMProp S) : Prop :=
  Mereology.IsContentPart q p

-- ════════════════════════════════════════════════════
-- § 3. Content Parts of Conjunctions
-- ════════════════════════════════════════════════════

section ConjunctionParts
variable {S : Type*} [SemilatticeSup S] (p q : TMProp S)

/-- `p` is subsumed by `p ∧ q` (Down clause).
    If `s` verifies `p ∧ q`, then `s = s₁ ⊔ s₂` with `p s₁`,
    so `s₁ ≤ s` is the required part. -/
theorem IsSubsumedBy.tmAnd_left : IsSubsumedBy p (tmAnd p q) := by
  intro s ⟨s₁, _, hp, _, hs⟩
  exact ⟨s₁, hp, hs ▸ le_sup_left⟩

/-- `q` is subsumed by `p ∧ q` (symmetric to `tmAnd_left`). -/
theorem IsSubsumedBy.tmAnd_right : IsSubsumedBy q (tmAnd p q) := by
  intro s ⟨_, s₂, _, hq, hs⟩
  exact ⟨s₂, hq, hs ▸ le_sup_right⟩

/-- `p` subserves `p ∧ q` provided `q` is inhabited (Up clause).
    Take any `s` verifying `p`; pick a witness `s₂` verifying `q`;
    then `s ⊔ s₂` verifies `p ∧ q` and `s ≤ s ⊔ s₂`. -/
theorem Subserves.tmAnd_left (hq : ∃ s, q s) : Subserves p (tmAnd p q) := by
  intro s hp
  obtain ⟨s₂, hqs₂⟩ := hq
  exact ⟨s ⊔ s₂, ⟨s, s₂, hp, hqs₂, rfl⟩, le_sup_left⟩

/-- `q` subserves `p ∧ q` provided `p` is inhabited. -/
theorem Subserves.tmAnd_right (hp : ∃ s, p s) : Subserves q (tmAnd p q) := by
  intro s hq
  obtain ⟨s₁, hps₁⟩ := hp
  exact ⟨s₁ ⊔ s, ⟨s₁, s, hps₁, hq, rfl⟩, le_sup_right⟩

/-- `p` is a content part of `p ∧ q` whenever `q` is inhabited (full Jago Def 5). -/
theorem IsContentPart.tmAnd_left (hq : ∃ s, q s) :
    IsContentPart p (tmAnd p q) :=
  ⟨IsSubsumedBy.tmAnd_left p q, Subserves.tmAnd_left p q hq⟩

/-- `q` is a content part of `p ∧ q` whenever `p` is inhabited. -/
theorem IsContentPart.tmAnd_right (hp : ∃ s, p s) :
    IsContentPart q (tmAnd p q) :=
  ⟨IsSubsumedBy.tmAnd_right p q, Subserves.tmAnd_right p q hp⟩

end ConjunctionParts

-- ════════════════════════════════════════════════════
-- § 4. Attitude Semantics (@cite{bondarenko-elliott-2026})
-- ════════════════════════════════════════════════════

section Attitudes
variable {S : Type*} {E : Type*}

/-- An attitude holds when the agent's total information state has a
    verifier-part for the proposition.
    `σ : E → S` maps agents to their total information states. -/
def attHolds [Preorder S] (σ : E → S) (p : TMProp S) (x : E) : Prop :=
  ∃ s, p s ∧ s ≤ σ x

variable [SemilatticeSup S] (σ : E → S) (p q : TMProp S) (x : E)

/-- Forward direction of conjunction distribution: if the agent's state
    verifies `p ∧ q`, then it verifies both `p` and `q`. -/
theorem attHolds_tmAnd_imp (h : attHolds σ (tmAnd p q) x) :
    attHolds σ p x ∧ attHolds σ q x := by
  obtain ⟨s, ⟨s₁, s₂, hp, hq, hs⟩, hle⟩ := h
  refine ⟨⟨s₁, hp, ?_⟩, ⟨s₂, hq, ?_⟩⟩
  · exact le_trans (hs ▸ le_sup_left) hle
  · exact le_trans (hs ▸ le_sup_right) hle

/-- Converse direction: if the agent's state has parts verifying both
    `p` and `q`, their fusion verifies `p ∧ q` and is also a part of `σ x`. -/
theorem attHolds_tmAnd_of (hp : attHolds σ p x) (hq : attHolds σ q x) :
    attHolds σ (tmAnd p q) x := by
  obtain ⟨s₁, hps₁, hle₁⟩ := hp
  obtain ⟨s₂, hqs₂, hle₂⟩ := hq
  exact ⟨s₁ ⊔ s₂, ⟨s₁, s₂, hps₁, hqs₂, rfl⟩, sup_le hle₁ hle₂⟩

/-- Full conjunction-distribution biconditional for upward-monotone attitudes
    (@cite{bondarenko-elliott-2026}, monotonicity-via-mereology theorem). -/
theorem attHolds_tmAnd_iff :
    attHolds σ (tmAnd p q) x ↔ attHolds σ p x ∧ attHolds σ q x :=
  ⟨attHolds_tmAnd_imp σ p q x,
   fun ⟨hp, hq⟩ => attHolds_tmAnd_of σ p q x hp hq⟩

end Attitudes

-- ════════════════════════════════════════════════════
-- § 5. Disjunction Does NOT Distribute as Content
-- ════════════════════════════════════════════════════

/-- Disjunction does NOT generally satisfy content parthood.
    `tmOr p q` is verified by any verifier of `p` or `q` (set union).
    A verifier of `p ∨ q` that verifies only `p` need not have a part
    verifying `q` — so `q` is not generally subsumed by `p ∨ q`.

    Concrete witness over `Nat` with `p = (· = 0)` and `q = (· = 1)`. -/
theorem isSubsumedBy_or_not_general :
    ¬ (∀ (S : Type) (_ : SemilatticeSup S) (p q : TMProp S),
       IsSubsumedBy q (tmOr p q)) := by
  intro h
  have := h Nat inferInstance (· = 0) (· = 1)
  obtain ⟨t, ht, hle⟩ := this 0 (Or.inl rfl)
  omega


-- ════════════════════════════════════════════════════════════════════════════
-- PART II: BILATERAL PROPOSITIONS
-- @cite{fine-2017}; cf. @cite{jago-2026} for the bilateral/unilateral choice
-- ════════════════════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════
-- § 6. Bilateral Propositions
-- ════════════════════════════════════════════════════

/-- A bilateral proposition: separate sets of verifiers and falsifiers.

    Per @cite{fine-2017}, a bilateral model assigns each atom a pair
    `(V, F)` of a verification set `V` and a falsification set `F`.
    The unilateral `TMProp` is recovered by `BilProp.toTM`. -/
@[ext] structure BilProp (S : Type*) where
  /-- States that verify (make true) the proposition. -/
  ver : S → Prop
  /-- States that falsify (make false) the proposition. -/
  fal : S → Prop

namespace BilProp

variable {S : Type*}

/-- Project a bilateral proposition to its unilateral (verifier) part. -/
def toTM (p : BilProp S) : TMProp S := p.ver

end BilProp

/-- Lift a unilateral proposition to bilateral with empty falsifier set.
    Appropriate for atoms in contexts where falsification isn't tracked. -/
def TMProp.toBil {S : Type*} (p : TMProp S) : BilProp S :=
  ⟨p, fun _ => False⟩

-- ════════════════════════════════════════════════════
-- § 7. Bilateral Connectives
-- ════════════════════════════════════════════════════

namespace BilProp

variable {S : Type*}

/-- Negation: swap verifiers and falsifiers (@cite{fine-2017}). -/
def neg (p : BilProp S) : BilProp S :=
  ⟨p.fal, p.ver⟩

variable [SemilatticeSup S]

/-- Conjunction: verified by fusion, falsified by union.
    Defined via `tmAnd` / `tmOr` so the duality is structurally explicit:
    conjunction *fuses* verifiers but *unions* falsifiers. -/
def conj (p q : BilProp S) : BilProp S where
  ver := tmAnd p.ver q.ver
  fal := tmOr p.fal q.fal

/-- Disjunction: verified by union, falsified by fusion.
    Exact dual of `conj`. -/
def disj (p q : BilProp S) : BilProp S where
  ver := tmOr p.ver q.ver
  fal := tmAnd p.fal q.fal

end BilProp

-- ════════════════════════════════════════════════════
-- § 8. Double Negation and De Morgan
-- ════════════════════════════════════════════════════

namespace BilProp

variable {S : Type*}

/-- Double negation is the identity (definitional). -/
@[simp] theorem neg_neg (p : BilProp S) : p.neg.neg = p := rfl

/-- Negation is involutive (mathlib-flavored restatement of `neg_neg`). -/
theorem neg_involutive : Function.Involutive (@neg S) := neg_neg

/-- `BilProp S` carries an `InvolutiveNeg` structure — the same mathlib
    abstraction satisfied by `Theories/Semantics/Dynamic/Bilateral/Basic.lean`'s
    `BilateralDen`. The two bilateral frameworks (state-based truthmaker,
    update-based dynamic) are unified at the swap-pair level by being
    instances of `InvolutiveNeg`. -/
instance : InvolutiveNeg (BilProp S) where
  neg := neg
  neg_neg := neg_neg

variable [SemilatticeSup S]

/-- De Morgan: ¬(A ∧ B) = ¬A ∨ ¬B. Definitionally true once the
    duality of `conj` and `disj` (fusion vs. union) is unrolled. -/
@[simp] theorem neg_conj (p q : BilProp S) :
    (p.conj q).neg = p.neg.disj q.neg := rfl

/-- De Morgan: ¬(A ∨ B) = ¬A ∧ ¬B. -/
@[simp] theorem neg_disj (p q : BilProp S) :
    (p.disj q).neg = p.neg.conj q.neg := rfl

end BilProp

-- ════════════════════════════════════════════════════
-- § 9. Modalized State Space and Compatibility
-- ════════════════════════════════════════════════════

/-- The set of *possible* states within a state space, packaged as a
    `LowerSet S` from mathlib: the carrier is a downward-closed set
    (`P.lower : IsLowerSet ↑P`), capturing Fine's requirement that any
    part of a possible state is itself possible.

    `Possibility S = LowerSet S` is just an alias to make the
    truthmaker-semantic role visible. -/
abbrev Possibility (S : Type*) [Preorder S] := LowerSet S

section Possibility
variable {S : Type*} [SemilatticeSup S]

/-- Two states are *compatible* iff their fusion is possible
    (@cite{fine-2017}). Incompatible states represent conflicting
    information — e.g., a state verifying "it's cold" and a state
    verifying "it's hot" are incompatible because their fusion is impossible. -/
def compatible (P : Possibility S) (s t : S) : Prop :=
  s ⊔ t ∈ P

/-- Compatibility is symmetric. -/
theorem compatible_comm {P : Possibility S} (s t : S) :
    compatible P s t ↔ compatible P t s := by
  unfold compatible
  rw [sup_comm]

instance compatible_isSymm (P : Possibility S) :
    Std.Symm (compatible P) :=
  ⟨fun _ _ h => (compatible_comm _ _).mp h⟩

end Possibility

-- ════════════════════════════════════════════════════
-- § 10. Exclusivity and Exhaustivity
-- ════════════════════════════════════════════════════

section ExclEx
variable {S : Type*} [SemilatticeSup S]

/-- **Exclusivity** (@cite{fine-2017}): no verifier is compatible with
    a falsifier. One direction of bivalence: verification and falsification
    are mutually incompatible. -/
def Exclusive (P : Possibility S) (A : BilProp S) : Prop :=
  ∀ s t, A.ver s → A.fal t → ¬ compatible P s t

/-- **Exhaustivity** (@cite{fine-2017}): every possible state is
    compatible with a verifier or a falsifier. The other direction of
    bivalence: no possible state is undecided about A.

    NOTE: this is the compatibility-based formulation in Fine 2017;
    a parthood-based variant ("every possible state is *part of* a
    verifier or falsifier") also appears in the literature and is
    related but not identical — added as `ExhaustivePart` if needed. -/
def Exhaustive (P : Possibility S) (A : BilProp S) : Prop :=
  ∀ s, s ∈ P →
    (∃ t, A.ver t ∧ compatible P s t) ∨ (∃ t, A.fal t ∧ compatible P s t)

/-- Negation preserves exclusivity. -/
theorem exclusive_neg {P : Possibility S} {A : BilProp S}
    (h : Exclusive P A) : Exclusive P A.neg := by
  intro s t hs ht hc
  exact h t s ht hs ((compatible_comm s t).mp hc)

/-- Negation preserves exhaustivity. -/
theorem exhaustive_neg {P : Possibility S} {A : BilProp S}
    (h : Exhaustive P A) : Exhaustive P A.neg := by
  intro s hs
  cases h s hs with
  | inl hv => exact Or.inr hv
  | inr hf => exact Or.inl hf

/-- If `A` and `B` are both exclusive, then `A ∧ B` is exclusive.

    Sketch: if `s` verifies `A ∧ B` then `s = s₁ ⊔ s₂` with
    `A.ver s₁`, `B.ver s₂`. If `t` falsifies `A ∧ B` then `t` falsifies
    `A` or `B`. Either way, the down-closure of possibility under parts
    contradicts exclusivity of `A` (or `B`). -/
theorem exclusive_conj {P : Possibility S} {A B : BilProp S}
    (hA : Exclusive P A) (hB : Exclusive P B) :
    Exclusive P (A.conj B) := by
  intro s t ⟨s₁, s₂, hvA, hvB, hs⟩ hfAB hcompat
  have hbig : (s₁ ⊔ s₂) ⊔ t ∈ P := by
    rw [hs] at hcompat; exact hcompat
  cases hfAB with
  | inl hfA =>
    have : s₁ ⊔ t ∈ P :=
      P.lower (sup_le_sup_right le_sup_left t) hbig
    exact hA s₁ t hvA hfA this
  | inr hfB =>
    have : s₂ ⊔ t ∈ P :=
      P.lower (sup_le_sup_right le_sup_right t) hbig
    exact hB s₂ t hvB hfB this

end ExclEx

-- ════════════════════════════════════════════════════
-- § 11. Subject-Matter
-- ════════════════════════════════════════════════════

section SubjectMatter
variable {S : Type*} [SupSet S]

/-- Subject-matter of a unilateral proposition: the fusion of all its
    verifiers (@cite{jago-2026} p. 5; cf. @cite{fine-2017}'s *Truthmaker
    Content* series in JPL 46(6) for the original presentation). -/
noncomputable def TMProp.subjectMatter (p : TMProp S) : S :=
  sSup {s | p s}

/-- Subject-matter of a bilateral proposition: the fusion of *both*
    verifiers and falsifiers (@cite{jago-2026} p. 5).

    This is the formulation that makes `subjectMatter` invariant under
    negation — the headline structural property that distinguishes
    truthmaker subject-matter from naive verifier-only "thick content".
    See `BilProp.subjectMatter_neg`. -/
noncomputable def BilProp.subjectMatter (A : BilProp S) : S :=
  sSup ({s | A.ver s} ∪ {s | A.fal s})

/-- **Negation invariance** of subject-matter (@cite{jago-2026} p. 5):
    `σ(¬A) = σ(A)`. The headline structural property of bilateral
    subject-matter, falling out structurally because `BilProp.neg`
    swaps `ver` and `fal` and `Set.union_comm` does the rest. -/
@[simp] theorem BilProp.subjectMatter_neg (A : BilProp S) :
    A.neg.subjectMatter = A.subjectMatter := by
  simp only [BilProp.subjectMatter, BilProp.neg, Set.union_comm]

variable [Preorder S]

/-- "A is about B" iff A's subject-matter is a part of B's (@cite{jago-2026}).
    Mereological account of aboutness: "It's raining" is about the weather;
    "It's raining and 2+2=4" is about the weather AND arithmetic. -/
def BilProp.isAbout (A B : BilProp S) : Prop :=
  A.subjectMatter ≤ B.subjectMatter

end SubjectMatter

-- ════════════════════════════════════════════════════
-- § 12. Headline Theorem: truthmaker distinguishes classical equivalents
-- ════════════════════════════════════════════════════

/-- Auxiliary 2-element carrier for the headline-theorem witness. -/
private inductive TwoAtom where
  | a
  | b
  deriving DecidableEq

/-- **The load-bearing claim of the framework** (@cite{jago-2026},
    @cite{fine-2017}). Two bilateral propositions can be *pointwise
    equivalent on verifiers* (= classically equivalent at every world)
    yet have *distinct subject-matters* (= mereologically different content).

    Witness over `Set TwoAtom`: `A` and `B` share the same verifier
    `{a}`, but differ in falsifier — `A` has none, `B` has `{b}`.
    `A.subjectMatter = sSup ({{a}} ∪ ∅) = {a}` while `B.subjectMatter =
    sSup ({{a}} ∪ {{b}}) = {a, b}`. The two are classically equivalent
    on verifiers but truthmaker-distinct in subject-matter — exactly the
    distinction PW semantics cannot make. -/
theorem subjectMatter_distinguishes_classically_equivalent :
    ∃ (A B : BilProp (Set TwoAtom)),
      (∀ s, A.ver s ↔ B.ver s) ∧
      A.subjectMatter ≠ B.subjectMatter := by
  let aSet : Set TwoAtom := {TwoAtom.a}
  let bSet : Set TwoAtom := {TwoAtom.b}
  refine ⟨⟨(· = aSet), fun _ => False⟩,
          ⟨(· = aSet), (· = bSet)⟩,
          fun _ => Iff.rfl, ?_⟩
  intro h
  simp only [BilProp.subjectMatter] at h
  -- h asserts equality of two `sSup`s; show b is in RHS but not LHS.
  have hb_in_rhs : TwoAtom.b ∈
      sSup ({s : Set TwoAtom | s = aSet} ∪ {s : Set TwoAtom | s = bSet}) :=
    ⟨bSet, Or.inr rfl, rfl⟩
  have hb_not_in_lhs : TwoAtom.b ∉
      sSup ({s : Set TwoAtom | s = aSet} ∪ {s : Set TwoAtom | False}) := by
    rintro ⟨t, ht, hbt⟩
    rcases ht with ht | ht
    · rw [ht] at hbt
      -- hbt : b ∈ aSet = {a}, contradiction
      cases hbt
    · exact ht
  exact hb_not_in_lhs (h ▸ hb_in_rhs)

end Semantics.Truthmaker
