import Linglib.Semantics.Questions.Basic
import Linglib.Semantics.Questions.Hamblin

/-!
# Resolution — answerhood predicates on `Question`
[ciardelli-groenendijk-roelofsen-2018] [theiler-etal-2018] [roberts-2012] [groenendijk-stokhof-1984]

Canonical Prop-valued answerhood predicates over the inquisitive
substrate (`Question W`), all in the `Question` namespace with the state
argument first. One topical home for the "what does it mean for a state
σ to answer a question Q?" question, with definitions chosen to match
modern (CGR 2018) formal-semantics consensus rather than the historical
Hamblin/Karttunen/G&S conventions.

## The notions formalised

Given a state `σ : Set W` and a question `Q : Question W`:

- **Resolves**: σ settles at least one alternative — `∃ p ∈ alt Q, σ ⊆ p`.
  This is the standard inquisitive resolution relation
  ([ciardelli-groenendijk-roelofsen-2018], [roelofsen-2013]). It is
  the natural notion of "σ answers Q" — even a singleton state can resolve
  a question by being contained in one of its alternatives.

- **MentionSome**: synonym of `Resolves` — the doctrinal "mention-some"
  reading of [groenendijk-stokhof-1984] Ch. VI §5 is just resolution
  by one alternative. Authors who add an extra "and not all alternatives"
  conjunct (forbidding mention-some answers from also being maximally
  informative) end up ruling out singleton-world states as mention-some
  answers to *Where can I get coffee?* — which is empirically wrong.

- **MentionAll**: σ decides every alternative — `∀ p ∈ alt Q, σ ⊆ p ∨ σ ⊆ pᶜ`.
  Note this is **not** "σ ⊆ p for every p" (which collapses to
  `σ ⊆ ⋂ alt Q` and is incoherent for partition questions whose
  alternatives are disjoint). The "decides each alternative" form is
  what aligns with [groenendijk-stokhof-1984]-style strong
  exhaustivity on partition questions. See `Exhaustivity.lean` for the
  weak / intermediate / strong / relativized exhaustivity ladder
  ([heim-1994], [george-2011], [xiang-2022]).

- **PartiallyAnswers** ([roberts-2012] (3a), its non-contextual core —
  the paper relativizes entailment to the common ground): σ settles at
  least one alternative either positively (`σ ⊆ p`) or negatively
  (`σ ⊆ pᶜ`); `∅` vacuously answers everything, as there. Bridged by
  `Resolves.partiallyAnswers`.

- **CompletelyResolves**: σ entails every alternative —
  `∀ p ∈ alt Q, σ ⊆ p`. The over-strong "intersection" reading; mostly
  vacuous for nontrivial questions. Included for completeness and as a
  comparison point with `MentionAll`.

The four form the quantifier × polarity square of answerhood: `Resolves`
(∃, positive), `PartiallyAnswers` (∃, either), `CompletelyResolves`
(∀, positive), `MentionAll` (∀, either).

## Why this file

A previous draft (deleted `Core/Question/Answerhood.lean`, audited
0.230.378) shipped `isMentionSomeAnswer` with the bad second conjunct
and `isMentionAllAnswer` in the over-strong intersection form. Both
have been corrected here. This file is the canonical home; the G&S
mention-some data lives in `Data.Examples.GroenendijkStokhof1984`
(consumed by `Studies/GroenendijkStokhof1984.lean`), and
`Exhaustivity.lean` (Karttunen / Dayal / Xiang / Fox) specializes
these substrate predicates rather than defining parallel ones.
-/

namespace Question

variable {W : Type*}

/-- `σ` resolves `Q` if it settles at least one alternative. The standard
inquisitive resolution relation ([ciardelli-groenendijk-roelofsen-2018]);
the [groenendijk-stokhof-1984] "mention-some" notion is this same
predicate. -/
def Resolves (σ : Set W) (Q : Question W) : Prop :=
  ∃ p ∈ alt Q, σ ⊆ p

/-- `σ` partially answers `Q` if it settles some alternative positively
(`σ ⊆ p`) or negatively (`σ ⊆ pᶜ`). -/
def PartiallyAnswers (σ : Set W) (Q : Question W) : Prop :=
  ∃ p ∈ alt Q, σ ⊆ p ∨ σ ⊆ pᶜ

/-- `σ` mention-all answers `Q` if it decides every alternative, either
entailing it or ruling it out. -/
def MentionAll (σ : Set W) (Q : Question W) : Prop :=
  ∀ p ∈ alt Q, σ ⊆ p ∨ σ ⊆ pᶜ

/-- `σ` completely resolves `Q` if it entails every alternative
simultaneously; vacuous for questions with disjoint alternatives. -/
def CompletelyResolves (σ : Set W) (Q : Question W) : Prop :=
  ∀ p ∈ alt Q, σ ⊆ p

variable {σ : Set W} {Q : Question W}

/-! ### Basic relationships -/

/-- Resolving implies partially answering: the positive disjunct fires. -/
theorem Resolves.partiallyAnswers (h : Resolves σ Q) :
    PartiallyAnswers σ Q :=
  let ⟨p, hp, hsub⟩ := h
  ⟨p, hp, Or.inl hsub⟩

/-- Completely resolving implies mention-all: the positive disjunct fires
at every alternative. -/
theorem CompletelyResolves.mentionAll (h : CompletelyResolves σ Q) :
    MentionAll σ Q :=
  fun p hp => Or.inl (h p hp)

/-! ### Bridge to `Question.Support`

`Resolves σ Q` (alt-witnessed) and `Support.supports σ Q := σ ∈ Q.props`
(CGR support, downward-closed) are two views on the same intuitive
notion. The CGR side is the foundational definition; `Resolves` is the
alt-witnessed corollary, equivalent under finiteness of `Q.props`. -/

/-- An alt witness is a resolving proposition, so any state below it is
one by downward closure. -/
theorem Resolves.supports (h : Resolves σ Q) : Support.supports σ Q :=
  let ⟨p, hp, hsub⟩ := h
  Q.downward_closed p (alt_subset_props _ hp) σ hsub

/-- Under finiteness of `Q.props`, CGR support yields an alt witness via
`exists_alt_above`. -/
theorem resolves_of_supports (hFin : Q.props.Finite)
    (h : Support.supports σ Q) : Resolves σ Q :=
  exists_alt_above Q hFin h

/-- `Resolves` and `Support.supports` coincide under finiteness. -/
theorem resolves_iff_supports (hFin : Q.props.Finite) :
    Resolves σ Q ↔ Support.supports σ Q :=
  ⟨Resolves.supports, resolves_of_supports hFin⟩

/-! ### Polar reduction

Iff lemmas reducing the square on nontrivial `polar p` to plain `Set`
inclusions — the joints consumer-side study files build on. -/

theorem resolves_polar_iff {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    Resolves σ (polar p) ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  unfold Resolves
  constructor
  · rintro ⟨q, hq, hsub⟩
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact Or.inl hsub
    · exact Or.inr hsub
  · rintro (h | h)
    · exact ⟨p, (mem_alt_polar_of_nontrivial hne hnu p).mpr (Or.inl rfl), h⟩
    · exact ⟨pᶜ, (mem_alt_polar_of_nontrivial hne hnu pᶜ).mpr (Or.inr rfl), h⟩

theorem partiallyAnswers_polar_iff {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    PartiallyAnswers σ (polar p) ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  simp only [PartiallyAnswers, alt_polar_of_nontrivial hne hnu,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
    exists_eq_left, compl_compl]
  tauto

theorem mentionAll_polar_iff {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    MentionAll σ (polar p) ↔ σ ⊆ p ∨ σ ⊆ pᶜ := by
  unfold MentionAll
  constructor
  · intro h
    have hp_mem : p ∈ alt (polar p) :=
      (mem_alt_polar_of_nontrivial hne hnu p).mpr (Or.inl rfl)
    exact h p hp_mem
  · rintro hor q hq
    rcases (mem_alt_polar_of_nontrivial hne hnu q).mp hq with rfl | rfl
    · exact hor
    · rcases hor with h | h
      · right; rw [compl_compl]; exact h
      · left; exact h

/-! ### Decidability for polar questions -/

/-- `Resolves σ (polar p)` is decidable when the two inclusions are. -/
def Resolves.decidable_polar {p σ : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
    [Decidable (σ ⊆ p)] [Decidable (σ ⊆ pᶜ)] :
    Decidable (Resolves σ (polar p)) :=
  decidable_of_iff _ (resolves_polar_iff hne hnu).symm

/-- `MentionAll σ (polar p)` is decidable under the same hypotheses:
on polar questions it coincides with `Resolves`. -/
def MentionAll.decidable_polar {p σ : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
    [Decidable (σ ⊆ p)] [Decidable (σ ⊆ pᶜ)] :
    Decidable (MentionAll σ (polar p)) :=
  decidable_of_iff _ (mentionAll_polar_iff hne hnu).symm

end Question
