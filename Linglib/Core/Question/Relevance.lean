import Linglib.Core.Question.Hamblin
import Mathlib.Data.Fintype.Powerset

/-!
# Roberts (2012) QUD relevance — Prop predicates on `Core.Question`
@cite{roberts-2012} @cite{groenendijk-stokhof-1984}

Mathlib-style Prop predicates with `Decidable` instances. Successor of an
earlier Bool/List `partiallyAnswers`/`questionEntails`/`isSubquestion`/
`moveRelevant` API (now removed) that operated on a Hamblin
list-of-alternatives `Question` type.

The predicates operate directly on `Core.Question`, ranging over `alt P`
(the maximal-resolving propositions). For computability, an `Question`
must expose a finite alternative-list witness via `HasAltList`. The
canonical witness for a polar question is `HasAltList.polar`; for an
arbitrary Hamblin issue, define a `HasAltList` instance via the
`ofList` smart constructor (`Core/Question/Hamblin.lean`).

Decidability of `σ ⊆ p` for `σ p : Set W` is *not* automatic in mathlib
(unlike `Finset`). The local instance `Set.decidableSubsetOfFintype` below
plugs the gap: it derives `Decidable (s ⊆ t)` from `[Fintype W]` plus
`DecidablePred (· ∈ s)` and `DecidablePred (· ∈ t)`. Consumers building
`Set W` from `W → Bool` predicates get the per-set `DecidablePred` for
free.

Note that the `[∀ p, Decidable (σ ⊆ p ∨ σ ⊆ pᶜ)]` hypothesis on the
instances below ranges over **all** `p : Set W` — Lean cannot synthesize
this universally because `DecidablePred (· ∈ p)` is not derivable for
arbitrary `p`. Consumers should either supply this hypothesis at the
call site (typically via `decide_partiallyAnswers_polar` for polar
questions) or invoke a specialized decision procedure tied to the
specific alternative list.
-/

namespace Core
namespace Question

universe u
variable {W : Type u}

/-- `σ` partially answers `P`: settles at least one alternative either
    positively (`σ ⊆ p`) or negatively (`σ ⊆ pᶜ`).
    @cite{roberts-2012} Def. 3a. -/
def partiallyAnswers (P : Question W) (σ : Set W) : Prop :=
  ∃ p ∈ alt P, σ ⊆ p ∨ σ ⊆ pᶜ

/-- Question entailment: every alternative of `P` entails some alternative
    of `Q`. @cite{roberts-2012} Def. 8 (after
    @cite{groenendijk-stokhof-1984}). At the partition level this is
    `QUD.refines`: `P` refines `Q` iff knowing `P`'s answer determines
    `Q`'s answer. -/
def questionEntails (P Q : Question W) : Prop :=
  ∀ p ∈ alt P, ∃ q ∈ alt Q, p ⊆ q

/-- `q` is a **subquestion** of `parent`: answering `parent` settles `q`. -/
def isSubquestion (q parent : Question W) : Prop :=
  questionEntails parent q

/-- A discourse move `den` is **relevant** to the QUD if some alternative
    partially answers the QUD or any of the subquestions. The
    QUD-relevance idea traces to @cite{roberts-2012}; the present
    formulation is the one @cite{ippolito-kiss-williams-2025} ex. (16)
    assumption iii uses for discourse *only*'s definedness condition. -/
def moveRelevant (den qud : Question W) (subquestions : List (Question W)) : Prop :=
  ∃ a ∈ alt den,
    partiallyAnswers qud a ∨ ∃ q ∈ subquestions, partiallyAnswers q a

/-- The dual of `questionEntails`: every **nonempty** alternative of
    `Q` is *covered* by a nonempty alternative of `P`.

    On partition questions this is equivalent to `questionEntails P Q`;
    for general inquisitive `Question W`, the two directions are
    independent. The decision-relevance preservation theorem in
    `Theories.Semantics.Questions.DecisionTheoretic` requires this
    dual form, not `questionEntails`. The nonempty clause matches
    `IsDecisionRelevant`'s requirement that witnessing alternatives
    be substantive — without it, `⊥`-style questions trivially
    "cover" anything via the empty set. -/
def CoversAltsOf (P Q : Question W) : Prop :=
  ∀ q ∈ alt Q, q.Nonempty → ∃ p ∈ alt P, p.Nonempty ∧ p ⊆ q

/-! ### Reflexivity / transitivity -/

theorem questionEntails_refl (P : Question W) : questionEntails P P :=
  fun p hp => ⟨p, hp, Set.Subset.refl p⟩

theorem questionEntails_trans {P Q R : Question W}
    (hPQ : questionEntails P Q) (hQR : questionEntails Q R) :
    questionEntails P R := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hPQ p hp
  obtain ⟨r, hr, hqr⟩ := hQR q hq
  exact ⟨r, hr, hpq.trans hqr⟩

/-! ### Lattice → entailment

The workhorse: `P ≤ Q` in the inquisitive lattice (`P.props ⊆ Q.props`)
implies `questionEntails P Q`. Every alternative of `P` resolves `Q`
and therefore extends to a maximal `Q`-resolving proposition. -/

/-- `P ≤ Q` (inquisitive entailment) implies `questionEntails P Q`
    (Roberts question entailment). The bridge from the lattice order
    to the alternative-set quantification. Requires `Q.props.Finite`
    to guarantee maximal extensions exist. -/
theorem questionEntails_of_le {P Q : Question W} (h : P ≤ Q)
    (hQ : Q.props.Finite) : questionEntails P Q := by
  intro p hp
  have hpP : p ∈ P.props := alt_subset_props P hp
  have hpQ : p ∈ Q.props := (le_def.mp h) hpP
  exact exists_alt_above Q hQ hpQ

/-- Variant of `questionEntails_of_le` with `[Fintype W] [DecidableEq W]`
    discharging the finiteness hypothesis (via `Fintype (Set W)` then
    `Set.toFinite`). Convenient for finite-world studies. -/
theorem questionEntails_of_le' [Fintype W] [DecidableEq W]
    {P Q : Question W} (h : P ≤ Q) : questionEntails P Q := by
  haveI : Finite (Set W) := Finite.of_fintype _
  exact questionEntails_of_le h (Set.toFinite Q.props)

theorem isSubquestion_refl (P : Question W) : isSubquestion P P :=
  questionEntails_refl P

theorem isSubquestion_trans {q r s : Question W}
    (hqr : isSubquestion q r) (hrs : isSubquestion r s) :
    isSubquestion q s :=
  questionEntails_trans hrs hqr

/-- A move whose alternative directly partially answers the QUD is
    relevant (no subquestions needed). -/
theorem partiallyAnswers_imp_moveRelevant
    {den qud : Question W} {a : Set W} (ha : a ∈ alt den)
    (h : partiallyAnswers qud a) :
    moveRelevant den qud [] :=
  ⟨a, ha, Or.inl h⟩

/-! ### Generic `Set ⊆ Set` decidability for finite types

Mathlib provides `Set.Subset` decidability only via `Finset`. For `Question`
consumers that build alternatives as `Set W` from `Bool`-valued predicates,
the gap is plugged by deriving from `Fintype W` plus per-set `DecidablePred`
witnesses. -/

instance Set.decidableSubsetOfFintype {α : Type*} [Fintype α]
    (s t : Set α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    Decidable (s ⊆ t) :=
  show Decidable (∀ ⦃a⦄, a ∈ s → a ∈ t) from inferInstance

/-! ### Decidability via `HasAltList` -/

/-- A finite-presentation witness for a `Question`'s alternatives. The
    `altList` is a `List (Set W)` whose elements correspond bijectively
    (modulo set-equality) to `alt P`. -/
class HasAltList (P : Question W) where
  /-- The finite list of alternatives. -/
  altList : List (Set W)
  /-- The list exhausts `alt P`. -/
  mem_altList : ∀ p, p ∈ alt P ↔ p ∈ altList

/-- `partiallyAnswers` decides via the alternative list, given
    decidability of each alternative-subset / complement-subset check. -/
instance partiallyAnswers_decidable
    (P : Question W) [HP : HasAltList P] (σ : Set W)
    [∀ p : Set W, Decidable (σ ⊆ p ∨ σ ⊆ pᶜ)] :
    Decidable (partiallyAnswers P σ) :=
  decidable_of_iff (∃ p ∈ HP.altList, σ ⊆ p ∨ σ ⊆ pᶜ) <| by
    refine ⟨?_, ?_⟩
    · rintro ⟨p, hp, hor⟩
      exact ⟨p, (HP.mem_altList p).mpr hp, hor⟩
    · rintro ⟨p, hp, hor⟩
      exact ⟨p, (HP.mem_altList p).mp hp, hor⟩

/-- `questionEntails` decides via the alternative lists, given
    decidability of pairwise subset checks. -/
instance questionEntails_decidable
    (P Q : Question W) [HP : HasAltList P] [HQ : HasAltList Q]
    [∀ p q : Set W, Decidable (p ⊆ q)] :
    Decidable (questionEntails P Q) :=
  decidable_of_iff (∀ p ∈ HP.altList, ∃ q ∈ HQ.altList, p ⊆ q) <| by
    constructor
    · intro h p hp
      obtain ⟨q, hq, hpq⟩ := h p ((HP.mem_altList p).mp hp)
      exact ⟨q, (HQ.mem_altList q).mpr hq, hpq⟩
    · intro h p hp
      obtain ⟨q, hq, hpq⟩ := h p ((HP.mem_altList p).mpr hp)
      exact ⟨q, (HQ.mem_altList q).mp hq, hpq⟩

instance isSubquestion_decidable
    (q parent : Question W) [HasAltList q] [HasAltList parent]
    [∀ p₁ p₂ : Set W, Decidable (p₁ ⊆ p₂)] :
    Decidable (isSubquestion q parent) :=
  questionEntails_decidable parent q

/-- `moveRelevant` decides via the move's alternative list, given
    decidability of partial answerhood against the QUD and each
    subquestion. -/
instance moveRelevant_decidable
    (den qud : Question W) (subquestions : List (Question W))
    [HD : HasAltList den]
    [∀ a : Set W, Decidable (partiallyAnswers qud a)]
    [∀ q : Question W, ∀ a : Set W, Decidable (partiallyAnswers q a)] :
    Decidable (moveRelevant den qud subquestions) :=
  decidable_of_iff
    (∃ a ∈ HD.altList,
      partiallyAnswers qud a ∨ ∃ q ∈ subquestions, partiallyAnswers q a) <| by
    refine ⟨?_, ?_⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (HD.mem_altList a).mpr ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (HD.mem_altList a).mp ha, h⟩

/-! ### `HasAltList` constructors -/

/-- `HasAltList` witness for a polar question whose proposition is
    non-trivial (neither `∅` nor `Set.univ`). The two alternatives are
    `p` and `pᶜ`. Not an `instance`: nontriviality must be supplied. -/
@[reducible]
def HasAltList.polar (p : Set W) [DecidablePred (· ∈ p)]
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    HasAltList (Question.polar p) where
  altList := [p, pᶜ]
  mem_altList q := by
    rw [alt_polar_of_nontrivial hne hnu]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons,
               List.not_mem_nil, or_false]

/-- `HasAltList` witness for a Hamblin question built from an explicit
    alternative list under pairwise disjointness + nonempty cells.
    The Hamblin construction `Question.ofList L` has `alt = {p | p ∈ L}`
    by `alt_ofList_of_pairwise_disjoint_nonempty`. Not an `instance`:
    the structural hypotheses must be supplied at the call site. -/
@[reducible]
def HasAltList.ofList (L : List (Set W)) (hL : L ≠ [])
    (hdisj : ∀ p₁ ∈ L, ∀ p₂ ∈ L, p₁ ≠ p₂ → Disjoint p₁ p₂)
    (hne : ∀ p ∈ L, p ≠ ∅) :
    HasAltList (Question.ofList L) where
  altList := L
  mem_altList q := by
    rw [alt_ofList_of_pairwise_disjoint_nonempty L hL hdisj hne]
    rfl

/-- `HasAltList` witness for a Hamblin question built from an explicit
    alternative list under the antichain condition (no cell contained
    in another) + nonempty cells. Weaker than `HasAltList.ofList` —
    cells may overlap as long as none is a subset of another distinct
    cell. Useful for Hamblin alternatives whose truth-sets share worlds
    (e.g., two polar question alternatives with overlap). -/
@[reducible]
def HasAltList.ofListAntichain (L : List (Set W)) (hL : L ≠ [])
    (hac : ∀ p₁ ∈ L, ∀ p₂ ∈ L, p₁ ≠ p₂ → ¬ p₁ ⊆ p₂)
    (hne : ∀ p ∈ L, p ≠ ∅) :
    HasAltList (Question.ofList L) where
  altList := L
  mem_altList q := by
    rw [alt_ofList_of_antichain_nonempty L hL hac hne]
    rfl

/-! ### Iff-rewrite lemmas for `polar`

These reduce `partiallyAnswers`/`questionEntails`/`moveRelevant` on
polar questions to plain `Set` operations, so consumers can `rw` and
then `decide` (the residual `Set` subset checks fire from
`Set.decidableSubsetOfFintype` plus per-set `DecidablePred`). -/

theorem partiallyAnswers_polar_iff {p σ : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    partiallyAnswers (Question.polar p) σ ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  unfold partiallyAnswers
  rw [alt_polar_of_nontrivial hne hnu]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨q, (rfl | rfl), hq⟩
    · exact hq
    · rcases hq with h | h
      · exact Or.inr h
      · exact Or.inl (h.trans (compl_compl p).subset)
  · rintro (h | h)
    · exact ⟨p, Or.inl rfl, Or.inl h⟩
    · exact ⟨p, Or.inl rfl, Or.inr h⟩

theorem questionEntails_polar_polar_iff {p q : Set W}
    (hne_p : p ≠ ∅) (hnu_p : p ≠ Set.univ)
    (hne_q : q ≠ ∅) (hnu_q : q ≠ Set.univ) :
    questionEntails (Question.polar p) (Question.polar q) ↔
      (p ⊆ q ∨ p ⊆ qᶜ) ∧ (pᶜ ⊆ q ∨ pᶜ ⊆ qᶜ) := by
  unfold questionEntails
  rw [alt_polar_of_nontrivial hne_p hnu_p,
      alt_polar_of_nontrivial hne_q hnu_q]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨r, (rfl | rfl), hr⟩ := h p (Or.inl rfl)
      · exact Or.inl hr
      · exact Or.inr hr
    · obtain ⟨r, (rfl | rfl), hr⟩ := h pᶜ (Or.inr rfl)
      · exact Or.inl hr
      · exact Or.inr hr
  · rintro ⟨hp, hpc⟩ r (rfl | rfl)
    · rcases hp with h | h
      · exact ⟨q, Or.inl rfl, h⟩
      · exact ⟨qᶜ, Or.inr rfl, h⟩
    · rcases hpc with h | h
      · exact ⟨q, Or.inl rfl, h⟩
      · exact ⟨qᶜ, Or.inr rfl, h⟩

theorem moveRelevant_polar_iff {p : Set W} {qud : Question W}
    {subquestions : List (Question W)}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    moveRelevant (Question.polar p) qud subquestions ↔
      (partiallyAnswers qud p ∨ ∃ Q ∈ subquestions, partiallyAnswers Q p) ∨
      (partiallyAnswers qud pᶜ ∨ ∃ Q ∈ subquestions, partiallyAnswers Q pᶜ) := by
  unfold moveRelevant
  rw [alt_polar_of_nontrivial hne hnu]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, (rfl | rfl), h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨p, Or.inl rfl, h⟩
    · exact ⟨pᶜ, Or.inr rfl, h⟩

end Question
end Core
