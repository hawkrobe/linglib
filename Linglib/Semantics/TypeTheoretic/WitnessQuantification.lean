import Linglib.Semantics.TypeTheoretic.Basic
import Linglib.Semantics.Quantification.Counting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

/-!
# Witness-set quantification

[cooper-2023] [barwise-cooper-1981]

Witness-set semantics for natural-language quantifiers: a quantifier `q(P, Q)`
is witnessed by a finite set `X` of `P`-individuals satisfying a
quantifier-specific cardinality condition, together with evidence that each
member of `X` (or alternatively each member outside `X`) bears `Q`. The
architecture descends from [barwise-cooper-1981]'s notion of *witness
sets*, formulated as type-theoretic predicates in [cooper-2023] Ch. 7.

This file extracts the framework as reusable substrate. It is consumed by
`Studies.Cooper2023.Ch7` (Cooper's own deployment) and
`Studies.LuckingGinzburg2022` (the Referential Transparency Theory of
quantification, which uses witness sets as a comparator for its
refset/compset/maxset framework).

## Main definitions

* `WitnessSet P X` — the base condition `X ⊆ ext(P)` shared by all
  quantifier-specific witness types. Structural conservativity follows.
* `IsExistW`, `IsNoW`, `IsEveryW`, `IsMostW`, `IsManyAbsW`, `IsManyPropW`,
  `IsFewAbsW`, `IsFewPropW`, `IsAFewAbsW`, `IsAFewPropW`, `IsCompFewAbsW`,
  `IsCompFewPropW` — quantifier-specific witness-set conditions.
* `GeneralWC_Incr`, `GeneralWC_Decr` — general witness conditions
  parameterised by an `isWS` predicate (monotone-increasing /
  monotone-decreasing forms).
* `ParticularWC_Exist`, `ParticularWC_No`, `ParticularWC_FewComp` —
  particular (anaphora-exposing) witness conditions.
* `AnaphoraRef`, `QuantName`, `anaphoraAvailable` — per-quantifier
  anaphora-set predictions (REFSET / MAXSET / COMPSET).
* `witnessGQ_exist`, `witnessGQ_every` — induced classical
  generalised-quantifier denotations.

## Main statements

* `witnessGQ_exist_conservative`, `witnessGQ_every_conservative` —
  conservativity follows structurally from the `WitnessSet` subset
  condition, rather than being stipulated as in [barwise-cooper-1981].
* `particular_exist_iff_witnessGQ`, `universal_iff_witnessGQ`,
  `particularWC_to_witnessGQ`, `particularWC_no_to_witnessGQ` — bridges
  between particular witness conditions and the classical GQ denotations.
* `particular_exist_implies_general`, `particular_no_implies_general` —
  every particular condition implies the matching general one.
* `comp_witness_card`, `few_comp_partition` — complement-witness-set
  combinatorics underpinning COMPSET anaphora.
* `generalWC_incr_mono`, `generalWC_decr_mono` — monotonicity of the
  general witness conditions follows from their structural shape.

## Implementation notes

* All witness-set predicates take a `DecidablePred` `P : E → Prop` rather
  than a `Ppty E := E → Type`. This matches [barwise-cooper-1981]'s
  set-theoretic formulation and lets Lean's `decide` close finite
  cardinality goals. `Ppty`-shaped witness conditions
  (`ParticularWC_*`, `GeneralWC_*`) coexist for the Type-valued TTR
  predicates used in compositional semantics.
* Anaphora-availability is encoded as a finite enumeration
  (`anaphoraAvailable : QuantName → List AnaphoraRef`) rather than a
  derived predicate. The list is empirical (Cooper §7.4.1 Table); the
  Lean encoding is for downstream `decide`-based dispatch.
-/

namespace Semantics.TypeTheoretic

/-! ### Extension of a predicate as a `Finset` -/

/-- The extension `[↓P]` of a predicate `P` as a `Finset`. -/
def fullExtFinset {E : Type} [Fintype E] (P : E → Prop) [DecidablePred P] :
    Finset E :=
  Finset.univ.filter P

/-! ### Witness-set predicates -/

variable {E : Type}

/-- Base witness-set condition ([barwise-cooper-1981]): a witness set
for `P` is a subset of `[↓P]`. Every quantifier-specific witness type
extends this condition. -/
structure WitnessSet (P : E → Prop) (X : Finset E) : Prop where
  subset : ∀ a ∈ X, P a

/-- `existʷ(P)`: a singleton witness set. -/
structure IsExistW (P : E → Prop) (X : Finset E) : Prop extends WitnessSet P X where
  card_eq : X.card = 1

/-- `exist_plʷ(P)`: a plural-some witness set, `|X| ≥ 2`. -/
structure IsExistPlW (P : E → Prop) (X : Finset E) : Prop extends WitnessSet P X where
  card_ge : X.card ≥ 2

/-- `noʷ(P)`: the empty witness set. -/
def IsNoW (_P : E → Prop) (X : Finset E) : Prop := X = ∅

/-- `everyʷ(P)`: the full extension. -/
def IsEveryW [Fintype E] (P : E → Prop) [DecidablePred P]
    (X : Finset E) : Prop := X = fullExtFinset P

/-- `mostʷ(P)`: proportional, `|X| / |[↓P]| ≥ θ_num / θ_denom`. Stated
as cross-multiplication. -/
structure IsMostW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≥ θ_num * (fullExtFinset P).card

/-- `many_aʷ(P)`: absolute threshold, `|X| ≥ θ`. -/
structure IsManyAbsW (P : E → Prop) (θ : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  card_ge : X.card ≥ θ

/-- `many_pʷ(P)`: proportional threshold. -/
structure IsManyPropW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≥ θ_num * (fullExtFinset P).card

/-- `few_aʷ(P)`: absolute upper bound, `|X| ≤ θ`. -/
structure IsFewAbsW (P : E → Prop) (θ : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  card_le : X.card ≤ θ

/-- `few_pʷ(P)`: proportional upper bound. -/
structure IsFewPropW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≤ θ_num * (fullExtFinset P).card

/-- `a_few_aʷ(P)`: absolute lower bound (same threshold as `few_a`,
reversed direction). -/
structure IsAFewAbsW (P : E → Prop) (θ : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  card_ge : X.card ≥ θ

/-- `a_few_pʷ(P)`: proportional lower bound. -/
structure IsAFewPropW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≥ θ_num * (fullExtFinset P).card

/-- Complement witness set for `few` (absolute):
`X̄ : few̄ʷ_a(P) iff |X| ≥ |[↓P]| − θ`. Predicts COMPSET anaphora. -/
structure IsCompFewAbsW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  card_ge : X.card ≥ (fullExtFinset P).card - θ

/-- Complement witness set for `few` (proportional). -/
structure IsCompFewPropW [Fintype E] (P : E → Prop) [DecidablePred P]
    (θ_num θ_denom : ℕ) (X : Finset E) : Prop extends WitnessSet P X where
  extPos : (fullExtFinset P).card > 0
  proportion : X.card * θ_denom ≥ (θ_denom - θ_num) * (fullExtFinset P).card

/-- `noʷ` has exactly one witness set: `∅`. -/
theorem isNoW_iff_empty (P : E → Prop) (X : Finset E) :
    IsNoW P X ↔ X = ∅ := Iff.rfl

/-- `everyʷ` has exactly one witness set: the full extension. -/
theorem isEveryW_iff [DecidableEq E] [Fintype E] (P : E → Prop) [DecidablePred P]
    (X : Finset E) : IsEveryW P X ↔ X = fullExtFinset P := Iff.rfl

/-! ### General and particular witness conditions -/

/-- General witness condition for monotone-increasing quantifiers
([cooper-2023] §7.4): a witness set `X` plus a per-element
mapping into `Q`-evidence. -/
structure GeneralWC_Incr (P Q : Ppty E)
    (isWS : Finset E → Prop) [DecidableEq E] where
  X : Finset E
  witnessOK : isWS X
  f : (a : E) → a ∈ X → Q a

/-- General witness condition for monotone-decreasing quantifiers: a
witness set `X` plus universal containment of `P ∩ Q`-entities in `X`. -/
structure GeneralWC_Decr (P Q : Ppty E)
    (isWS : Finset E → Prop) [DecidableEq E] where
  X : Finset E
  witnessOK : isWS X
  f : (a : E) → Nonempty (P a) → Nonempty (Q a) → a ∈ X

/-- Particular witness condition for `exist(P, Q)`: a specific
individual `x` witnessing both `P` and `Q`. The `x`-field enables REFSET
(singular) anaphora ("A dog barked. It heard an intruder."). -/
structure ParticularWC_Exist (P Q : Ppty E) where
  x : E
  pWit : P x
  qWit : Q x

/-- Particular witness condition for `no(P, Q)`: every `P`-entity fails
to bear `Q`. With `everyʷ(P)` as the witness set, predicts MAXSET
anaphora ("No dog barked. They were all asleep."). -/
structure ParticularWC_No (P Q : Ppty E) where
  f : (a : E) → P a → IsEmpty (Q a)

/-- Particular witness condition for `few` with complement: a set of
`P`-entities all lacking `Q`. Predicts COMPSET anaphora ("Few dogs
barked. They slept through."). -/
structure ParticularWC_FewComp (P Q : Ppty E) [DecidableEq E] where
  X : Finset E
  allP : ∀ a ∈ X, Nonempty (P a)
  allNotQ : ∀ a ∈ X, IsEmpty (Q a)

/-- The particular `exist` condition implies the general one with a
singleton witness set. -/
def particular_exist_implies_general [DecidableEq E]
    (P Q : Ppty E) (h : ParticularWC_Exist P Q)
    (Pd : E → Prop) (hPd : ∀ a, Pd a ↔ Nonempty (P a)) :
    GeneralWC_Incr P Q (IsExistW Pd) :=
  ⟨{h.x},
   { subset := λ a ha => by
       rw [Finset.mem_singleton] at ha
       rw [ha]; exact (hPd h.x).mpr ⟨h.pWit⟩
     card_eq := Finset.card_singleton h.x },
   λ a ha => by rw [Finset.mem_singleton] at ha; rw [ha]; exact h.qWit⟩

/-- The particular `no` condition implies the general decreasing one
with the empty witness set. -/
def particular_no_implies_general [DecidableEq E]
    (P Q : Ppty E) (h : ParticularWC_No P Q)
    (Pd : E → Prop) :
    GeneralWC_Decr P Q (IsNoW Pd) :=
  ⟨∅, rfl,
   λ a hP hQ => ((h.f a hP.some).false hQ.some).elim⟩

/-! ### Anaphora-set predictions

The witness-set architecture predicts which anaphora sets each
quantifier makes available ([cooper-2023] §7.4.1, Table). -/

/-- Anaphora-set kinds reachable from a quantified noun phrase. -/
inductive AnaphoraRef where
  /-- REFSET: the witness individual or set ("A dog barked. It heard
  an intruder."). -/
  | refset
  /-- MAXSET: the full extension ("Every dog barked. They heard an
  intruder."). -/
  | maxset
  /-- COMPSET: the complement witness set ("Few dogs barked. They slept
  through."). -/
  | compset
  deriving DecidableEq, Repr

/-- The English fragment's quantifier names. -/
inductive QuantName where
  | exist | existPl | no | every | most | many | few | aFew
  deriving DecidableEq, Repr

/-- Per-quantifier anaphora-set predictions ([cooper-2023] §7.4.1). -/
def anaphoraAvailable : QuantName → List AnaphoraRef
  | .exist   => [.refset]
  | .existPl => [.refset, .maxset]
  | .no      => [.maxset]
  | .every   => [.maxset]
  | .most    => [.maxset]
  | .many    => [.maxset]
  | .few     => [.refset, .maxset, .compset]
  | .aFew    => [.refset, .maxset]

/-! ### Induced classical GQ denotations -/

open Quantification

/-- The GQ induced by existential witness sets:
`exist(A, B)` iff some element bears both `A` and `B`. -/
def witnessGQ_exist : GQ E :=
  λ A B => ∃ x : E, A x ∧ B x

/-- The GQ induced by universal witness sets:
`every(A, B)` iff every `A`-element also bears `B`. -/
def witnessGQ_every : GQ E :=
  λ A B => ∀ x : E, A x → B x

/-- Conservativity of `witnessGQ_exist` follows structurally from the
`WitnessSet` subset condition — not stipulated as in
[barwise-cooper-1981]. -/
theorem witnessGQ_exist_conservative :
    Conservative (α := E) witnessGQ_exist := by
  intro R S
  simp only [witnessGQ_exist]
  exact ⟨λ ⟨x, hR, hS⟩ => ⟨x, hR, hR, hS⟩,
         λ ⟨x, hR, _, hS⟩ => ⟨x, hR, hS⟩⟩

/-- Conservativity of `witnessGQ_every`. -/
theorem witnessGQ_every_conservative :
    Conservative (α := E) witnessGQ_every := by
  intro R S
  simp only [witnessGQ_every]
  exact ⟨λ h x hR => ⟨hR, h x hR⟩,
         λ h x hR => (h x hR).2⟩

/-! ### Bridges between particular witness conditions and GQs -/

/-- The particular existential condition equals the existential GQ
denotation (both unfold to `∃ x, P x ∧ Q x`). -/
theorem particular_exist_iff_witnessGQ (P Q : E → Prop) :
    (∃ x, P x ∧ Q x) ↔ witnessGQ_exist P Q :=
  Iff.rfl

/-- The universal condition equals the universal GQ denotation. -/
theorem universal_iff_witnessGQ (P Q : E → Prop) :
    (∀ x, P x → Q x) ↔ witnessGQ_every P Q :=
  Iff.rfl

/-- `ParticularWC_Exist` constructs a witness for the existential GQ. -/
theorem particularWC_to_witnessGQ [DecidableEq E]
    {P Q : Ppty E} (w : ParticularWC_Exist P Q)
    (Pd Qd : E → Prop)
    (hP : ∀ a, Pd a ↔ Nonempty (P a)) (hQ : ∀ a, Qd a ↔ Nonempty (Q a)) :
    witnessGQ_exist Pd Qd := by
  rw [← particular_exist_iff_witnessGQ]
  exact ⟨w.x, (hP w.x).mpr ⟨w.pWit⟩, (hQ w.x).mpr ⟨w.qWit⟩⟩

/-- `ParticularWC_No` constructs the universal GQ with negated scope. -/
theorem particularWC_no_to_witnessGQ [DecidableEq E]
    {P Q : Ppty E} (w : ParticularWC_No P Q)
    (Pd Qd : E → Prop)
    (hP : ∀ a, Pd a ↔ Nonempty (P a)) (hQ : ∀ a, Qd a ↔ Nonempty (Q a)) :
    witnessGQ_every Pd (λ x => ¬ Qd x) := by
  rw [← universal_iff_witnessGQ]
  intro x hPx hQx
  have hP' := (hP x).mp hPx
  have hQ' := (hQ x).mp hQx
  exact (w.f x hP'.some).false hQ'.some

/-! ### Complement witness sets and the few / a_few contrast -/

/-- The complement of a `few_a` witness set satisfies the complement
cardinality condition. -/
theorem comp_witness_card [DecidableEq E] [Fintype E]
    (P : E → Prop) [DecidablePred P]
    (X : Finset E) (_hSub : ∀ a ∈ X, P a) (θ : ℕ)
    (_hFew : X.card ≤ θ)
    (hXsub : X ⊆ fullExtFinset P) :
    (fullExtFinset P \ X).card ≥ (fullExtFinset P).card - θ := by
  have h := Finset.card_sdiff_of_subset hXsub
  omega

/-- A witness set and its complement partition the extension. -/
theorem few_comp_partition [DecidableEq E] [Fintype E]
    (P : E → Prop) [DecidablePred P]
    (X : Finset E) (hX : X ⊆ fullExtFinset P) :
    X ∪ (fullExtFinset P \ X) = fullExtFinset P :=
  Finset.union_sdiff_of_subset hX

/-! ### Monotonicity from witness-condition shape -/

/-- Upward monotonicity of the increasing general witness condition. -/
def generalWC_incr_mono [DecidableEq E] (P Q Q' : Ppty E)
    (isWS : Finset E → Prop)
    (embed : ∀ a : E, Q a → Q' a)
    (w : GeneralWC_Incr P Q isWS) : GeneralWC_Incr P Q' isWS :=
  ⟨w.X, w.witnessOK, λ a ha => embed a (w.f a ha)⟩

/-- Downward monotonicity of the decreasing general witness condition. -/
def generalWC_decr_mono [DecidableEq E] (P Q Q' : Ppty E)
    (isWS : Finset E → Prop)
    (embed : ∀ a : E, Q' a → Q a)
    (w : GeneralWC_Decr P Q isWS) : GeneralWC_Decr P Q' isWS :=
  ⟨w.X, w.witnessOK, λ a hP hQ' => w.f a hP ⟨embed a hQ'.some⟩⟩

end Semantics.TypeTheoretic
