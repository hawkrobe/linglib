import Linglib.Semantics.Questions.Hamblin
import Mathlib.Data.Fintype.Powerset

/-!
# Roberts (2012) QUD relevance — Prop predicates on `Question`
[roberts-2012] [groenendijk-stokhof-1984]

Answerhood-based relevance predicates ranging over `alt P` (the
maximal-resolving propositions): `partiallyAnswers`, `questionEntails`,
`isSubquestion`, `moveRelevant`, and the dual `CoversAltsOf`.

`questionEntails` coincides with the inquisitive lattice order under
finiteness (`questionEntails_iff_le`). On polar questions the predicates
reduce to plain `Set` inclusions via the `_polar_iff` lemmas, so consumers
can `rw` and then `decide`; the residual subset checks fire from
`Set.decidableSubsetOfFintype` below.

## Fidelity notes

`partiallyAnswers` is the non-contextual core of [roberts-2012] (3a),
which relativizes both entailments to the common ground. `questionEntails`
matches [groenendijk-stokhof-1984] entailment only where alternatives are
complete answers (partition and polar contents; not mention-some `which`)
— [roberts-2012]'s own caveat. `moveRelevant` is existential answerhood
relevance: the partial-answer clause of Roberts's Relevance (15), weaker
than her strategy clause for interrogative moves; it is the proxy
[ippolito-kiss-williams-2025] use for their relevance assumption (iii),
consumed by the discourse *only* definedness condition in their (16).
These are all answerhood ("aboutness") notions — distinct from
inquisitive-semantics compliance ([ciardelli-groenendijk-roelofsen-2018],
not formalized here) and from decision-theoretic relevance
(`Studies/VanRooy2003.lean`, which consumes `CoversAltsOf`).
-/

/-! ### `Set ⊆ Set` decidability for finite types

Mathlib provides subset decidability only for `Finset`; for `Set` it is
derivable from `Fintype` plus per-set `DecidablePred` membership witnesses.
[UPSTREAM] candidate. -/

instance Set.decidableSubsetOfFintype {α : Type*} [Fintype α]
    (s t : Set α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    Decidable (s ⊆ t) :=
  show Decidable (∀ ⦃a⦄, a ∈ s → a ∈ t) from inferInstance

namespace Question

variable {W : Type*}

/-- `σ` **partially answers** `P`: it settles some alternative positively
    (`σ ⊆ p`) or negatively (`σ ⊆ pᶜ`). [roberts-2012] (3a); `σ = ∅`
    vacuously answers everything, as there. -/
def partiallyAnswers (P : Question W) (σ : Set W) : Prop :=
  ∃ p ∈ alt P, σ ⊆ p ∨ σ ⊆ pᶜ

/-- **Question entailment**: every alternative of `P` entails some
    alternative of `Q`. [roberts-2012] (8), after
    [groenendijk-stokhof-1984]. -/
def questionEntails (P Q : Question W) : Prop :=
  ∀ p ∈ alt P, ∃ q ∈ alt Q, p ⊆ q

/-- `q` is a **subquestion** of `parent`: answering `parent` settles `q`
    ([roberts-2012]). -/
def isSubquestion (q parent : Question W) : Prop :=
  questionEntails parent q

/-- A move `den` is **relevant** to the QUD if some alternative partially
    answers the QUD or one of `subquestions` ([roberts-2012] (15), see
    the fidelity notes above). That `subquestions` really are subquestions
    of the QUD is the caller's obligation. -/
def moveRelevant (den qud : Question W) (subquestions : List (Question W)) : Prop :=
  ∃ a ∈ alt den,
    partiallyAnswers qud a ∨ ∃ q ∈ subquestions, partiallyAnswers q a

/-- Dual of `questionEntails`: every **nonempty** alternative of `Q`
    contains a nonempty alternative of `P`. Equivalent to
    `questionEntails P Q` on partitions, independent in general; the
    nonemptiness bars `⊥`-style vacuous covering, matching
    `VanRooy2003.IsDecisionRelevant`'s substantive witnesses. -/
def CoversAltsOf (P Q : Question W) : Prop :=
  ∀ q ∈ alt Q, q.Nonempty → ∃ p ∈ alt P, p.Nonempty ∧ p ⊆ q

/-! ### Reflexivity / transitivity -/

theorem questionEntails_refl (P : Question W) : questionEntails P P :=
  fun p hp => ⟨p, hp, subset_rfl⟩

theorem questionEntails_trans {P Q R : Question W}
    (hPQ : questionEntails P Q) (hQR : questionEntails Q R) :
    questionEntails P R := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hPQ p hp
  obtain ⟨r, hr, hqr⟩ := hQR q hq
  exact ⟨r, hr, hpq.trans hqr⟩

/-! ### Lattice ↔ entailment -/

/-- Inquisitive entailment `P ≤ Q` implies `questionEntails P Q`.
    `Q.props.Finite` guarantees maximal extensions exist. -/
theorem questionEntails_of_le {P Q : Question W} (h : P ≤ Q)
    (hQ : Q.props.Finite) : questionEntails P Q := by
  intro p hp
  have hpP : p ∈ P.props := alt_subset_props P hp
  have hpQ : p ∈ Q.props := (le_def.mp h) hpP
  exact exists_alt_above Q hQ hpQ

/-- Converse of `questionEntails_of_le`, under finiteness of `P.props`. -/
theorem le_of_questionEntails {P Q : Question W} (hP : P.props.Finite)
    (h : questionEntails P Q) : P ≤ Q := by
  rw [le_def]
  intro s hs
  obtain ⟨p, hp, hsp⟩ := exists_alt_above P hP hs
  obtain ⟨q, hq, hpq⟩ := h p hp
  exact Q.downward_closed q (alt_subset_props Q hq) s (hsp.trans hpq)

/-- Under finiteness, Roberts question entailment and the inquisitive
    lattice order are the same relation. -/
theorem questionEntails_iff_le {P Q : Question W}
    (hP : P.props.Finite) (hQ : Q.props.Finite) :
    questionEntails P Q ↔ P ≤ Q :=
  ⟨le_of_questionEntails hP, (questionEntails_of_le · hQ)⟩

/-- Variant of `questionEntails_of_le` for finite world types. -/
theorem questionEntails_of_le' [Finite W]
    {P Q : Question W} (h : P ≤ Q) : questionEntails P Q :=
  questionEntails_of_le h Q.props.toFinite

theorem isSubquestion_refl (P : Question W) : isSubquestion P P :=
  questionEntails_refl P

theorem isSubquestion_trans {q r s : Question W}
    (hqr : isSubquestion q r) (hrs : isSubquestion r s) :
    isSubquestion q s :=
  questionEntails_trans hrs hqr

/-- A move whose alternative directly partially answers the QUD is
    relevant, with no subquestions needed. -/
theorem moveRelevant_of_partiallyAnswers
    {den qud : Question W} {a : Set W} (ha : a ∈ alt den)
    (h : partiallyAnswers qud a) :
    moveRelevant den qud [] :=
  ⟨a, ha, Or.inl h⟩

/-! ### Iff-rewrite lemmas for `polar`

These reduce the predicates on polar questions to plain `Set` inclusions,
so consumers can `rw` and then `decide` via `Set.decidableSubsetOfFintype`
plus per-set `DecidablePred`. -/

theorem partiallyAnswers_polar_iff {p σ : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    partiallyAnswers (Question.polar p) σ ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  simp only [partiallyAnswers, alt_polar_of_nontrivial hne hnu,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_eq_left, compl_compl]
  tauto

theorem questionEntails_polar_polar_iff {p q : Set W}
    (hne_p : p ≠ ∅) (hnu_p : p ≠ Set.univ)
    (hne_q : q ≠ ∅) (hnu_q : q ≠ Set.univ) :
    questionEntails (Question.polar p) (Question.polar q) ↔
      (p ⊆ q ∨ p ⊆ qᶜ) ∧ (pᶜ ⊆ q ∨ pᶜ ⊆ qᶜ) := by
  simp only [questionEntails, alt_polar_of_nontrivial hne_p hnu_p,
    alt_polar_of_nontrivial hne_q hnu_q, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, exists_eq_or_imp,
    exists_eq_left]

theorem moveRelevant_polar_iff {p : Set W} {qud : Question W}
    {subquestions : List (Question W)}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    moveRelevant (Question.polar p) qud subquestions ↔
      (partiallyAnswers qud p ∨ ∃ Q ∈ subquestions, partiallyAnswers Q p) ∨
      (partiallyAnswers qud pᶜ ∨ ∃ Q ∈ subquestions, partiallyAnswers Q pᶜ) := by
  simp only [moveRelevant, alt_polar_of_nontrivial hne hnu,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_eq_left]

end Question
