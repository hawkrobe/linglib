import Linglib.Theories.Semantics.Questions.Basic
import Linglib.Theories.Semantics.Questions.Hamblin
import Linglib.Theories.Semantics.Questions.Relevance

/-!
# Resolution — answerhood predicates on `Question`
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{theiler-etal-2018} @cite{roberts-2012} @cite{groenendijk-stokhof-1984}

Canonical Prop-valued answerhood predicates over the inquisitive
substrate (`Question W`). One topical home for the "what does it
mean for a state σ to answer a question Q?" question, with definitions
chosen to match modern (CGR 2018) formal-semantics consensus rather
than the historical Hamblin/Karttunen/G&S conventions.

## The notions formalised

Given a state `σ : Set W` and a question `Q : Question W`:

- **Resolves**: σ settles at least one alternative — `∃ p ∈ alt Q, σ ⊆ p`.
  This is the standard inquisitive resolution relation
  (@cite{ciardelli-groenendijk-roelofsen-2018}, @cite{roelofsen-2013}). It is
  the natural notion of "σ answers Q" — even a singleton state can resolve
  a question by being contained in one of its alternatives.

- **MentionSome**: synonym of `Resolves` — the doctrinal "mention-some"
  reading of @cite{groenendijk-stokhof-1984} Ch. VI §5 is just resolution
  by one alternative. Authors who add an extra "and not all alternatives"
  conjunct (forbidding mention-some answers from also being maximally
  informative) end up ruling out singleton-world states as mention-some
  answers to *Where can I get coffee?* — which is empirically wrong.

- **MentionAll**: σ decides every alternative — `∀ p ∈ alt Q, σ ⊆ p ∨ σ ⊆ pᶜ`.
  Note this is **not** "σ ⊆ p for every p" (which collapses to
  `σ ⊆ ⋂ alt Q` and is incoherent for partition questions whose
  alternatives are disjoint). The "decides each alternative" form is
  what aligns with @cite{groenendijk-stokhof-1984}-style strong
  exhaustivity on partition questions. See `Exhaustivity.lean` for the
  weak / intermediate / strong / relativized exhaustivity ladder
  (@cite{heim-1994}, @cite{george-2011}, @cite{xiang-2022}).

- **partiallyResolves**: re-export of `Question.Relevance.partiallyAnswers`
  (@cite{roberts-2012} Def. 3a). σ settles at least one alternative either
  positively (`σ ⊆ p`) or negatively (`σ ⊆ pᶜ`).

- **CompletelyResolves**: σ entails every alternative —
  `∀ p ∈ alt Q, σ ⊆ p`. The over-strong "intersection" reading; mostly
  vacuous for nontrivial questions. Included for completeness and as a
  comparison point with `MentionAll`.

## Why this file

A previous draft (deleted `Core/Question/Answerhood.lean`, audited
0.230.378) shipped `isMentionSomeAnswer` with the bad second conjunct
and `isMentionAllAnswer` in the over-strong intersection form. Both
have been corrected here. This file is the canonical home;
`Theories/Semantics/Questions/MentionSome.lean` (G&S-specific) and the
forthcoming `Exhaustivity.lean` (Karttunen / Dayal / Xiang / Fox)
should be specializations of these substrate predicates rather than
parallel definitions.
-/

namespace Semantics.Questions.Resolution

universe u
variable {W : Type u}

open Question

/-- `σ` **resolves** `Q`: settles at least one alternative.
    The standard inquisitive resolution relation
    (@cite{ciardelli-groenendijk-roelofsen-2018}). The
    @cite{groenendijk-stokhof-1984} Ch. VI §5 "mention-some" notion is
    this same predicate; the literature's `MentionSome` is just
    `Resolves` applied to a singleton-witness. -/
def Resolves (σ : Set W) (Q : Question W) : Prop :=
  ∃ p ∈ alt Q, σ ⊆ p

/-- **Mention-all** answer: σ decides every alternative.
    For each alternative `p`, σ either entails `p` (`σ ⊆ p`) or rules
    `p` out (`σ ⊆ pᶜ`). On partition questions this is equivalent to σ
    being contained in a single cell. -/
def MentionAll (σ : Set W) (Q : Question W) : Prop :=
  ∀ p ∈ alt Q, σ ⊆ p ∨ σ ⊆ pᶜ

/-- **Completely resolves**: σ entails every alternative simultaneously.
    `∀ p ∈ alt Q, σ ⊆ p`, equivalent to `σ ⊆ ⋂ alt Q`. Vacuous for
    questions whose alternatives have empty intersection (most
    interesting questions). Included to make the contrast with
    `MentionAll` explicit. -/
def CompletelyResolves (σ : Set W) (Q : Question W) : Prop :=
  ∀ p ∈ alt Q, σ ⊆ p

/-! ### Basic relationships -/

/-- Resolving implies partially answering the question (the positive
    disjunct of `Question.partiallyAnswers` fires). -/
theorem resolves_imp_partiallyAnswers
    (σ : Set W) (Q : Question W) :
    Resolves σ Q → Question.partiallyAnswers Q σ := by
  rintro ⟨p, hp, hsub⟩
  exact ⟨p, hp, Or.inl hsub⟩

/-- Completely resolving implies mention-all (the positive disjunct fires
    at every alternative). -/
theorem completelyResolves_imp_mentionAll
    (σ : Set W) (Q : Question W) :
    CompletelyResolves σ Q → MentionAll σ Q :=
  fun h p hp => Or.inl (h p hp)

/-! ### Bridge to `Question.Support`

`Resolves σ Q` (alt-witnessed) and `Support.supports σ Q := σ ∈ Q.props`
(CGR support, downward-closed) are two views on the same intuitive
notion. The CGR side is the foundational definition (a state supports
the issue iff it is a resolving proposition); `Resolves` is the
alt-witnessed corollary, equivalent under finiteness of `Q.props`. -/

/-- `Resolves` (alt-witness) implies `Support.supports` (CGR
    membership): an alt is a resolving proposition, so any state below
    an alt is a resolving proposition by `downward_closed`. -/
theorem resolves_imp_supports (σ : Set W) (Q : Question W) :
    Resolves σ Q → Question.Support.supports σ Q := by
  rintro ⟨p, hp, hsub⟩
  exact Q.downward_closed p (Question.alt_subset_props _ hp) σ hsub

/-- Under finiteness of `Q.props`, `Support.supports` (CGR membership)
    yields an alt witness via `Question.exists_alt_above` — recovering
    `Resolves`. The two notions are equivalent when alternatives form
    a finite antichain (the typical empirical case). -/
theorem supports_imp_resolves (σ : Set W) (Q : Question W)
    (hFin : Q.props.Finite) :
    Question.Support.supports σ Q → Resolves σ Q := by
  intro hσ
  exact Question.exists_alt_above Q hFin hσ

/-- Equivalence of `Resolves` and `Support.supports` under finiteness. -/
theorem resolves_iff_supports (σ : Set W) (Q : Question W)
    (hFin : Q.props.Finite) :
    Resolves σ Q ↔ Question.Support.supports σ Q :=
  ⟨resolves_imp_supports σ Q, supports_imp_resolves σ Q hFin⟩

/-! ### Per-constructor characterizations

Iff lemmas for the inquisitive constructors `polar` and `which`. These
are the joints that consumer-side study files build on. -/

/-- `Resolves σ (polar p)`: σ entails `p` or σ entails `pᶜ`. (For
    nontrivial polar; the trivial cases collapse to ⊤.) -/
theorem Resolves_polar_iff_of_nontrivial {p : Set W} (σ : Set W)
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
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

/-- `MentionAll σ (polar p)`: σ decides `p`. (For nontrivial polar.) -/
theorem MentionAll_polar_iff_of_nontrivial {p : Set W} (σ : Set W)
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

/-! ### Decidability for polar questions

Under standard finiteness + decidability hypotheses, the substrate
predicates `Resolves`, `MentionAll`, `CompletelyResolves` for a
nontrivial `polar p` question are all decidable. These reduce to
"`σ ⊆ p ∨ σ ⊆ pᶜ`" via the per-constructor characterizations above. -/

/-- `Resolves σ (polar p)` is decidable when `σ ⊆ p` and `σ ⊆ pᶜ` are
    decidable and `p`'s nontriviality is given. -/
instance Resolves.decidable_polar {p σ : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
    [Decidable (σ ⊆ p)] [Decidable (σ ⊆ pᶜ)] :
    Decidable (Resolves σ (polar p)) :=
  decidable_of_iff _ (Resolves_polar_iff_of_nontrivial σ hne hnu).symm

/-- `MentionAll σ (polar p)` is decidable under the same hypotheses as
    `Resolves`. The two are equivalent on polar questions: deciding
    `p` is the only requirement. -/
instance MentionAll.decidable_polar {p σ : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
    [Decidable (σ ⊆ p)] [Decidable (σ ⊆ pᶜ)] :
    Decidable (MentionAll σ (polar p)) :=
  decidable_of_iff _ (MentionAll_polar_iff_of_nontrivial σ hne hnu).symm

end Semantics.Questions.Resolution
