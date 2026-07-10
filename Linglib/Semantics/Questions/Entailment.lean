import Linglib.Semantics.Questions.Hamblin
import Mathlib.Data.Fintype.Powerset

/-!
# Question entailment
[groenendijk-stokhof-1984] [roberts-2012]

The entailment order on question contents: `P.Entails Q` iff every
alternative of `P` entails some alternative of `Q` ([roberts-2012] (8),
after [groenendijk-stokhof-1984]); `IsSubquestion` is its inverse
reading. The order coincides with the inquisitive lattice order under
finiteness (`entails_iff_le`); the two diverge only where `alt` is
empty.

## Fidelity notes

`Entails` matches [groenendijk-stokhof-1984] entailment only where
alternatives are complete answers (partition and polar contents; not
mention-some `which`) — [roberts-2012]'s own caveat. Polar-question
goals reduce to `Set` inclusions via `entails_polar_polar_iff` and then
`decide`, after activating `Set.decidableSubsetOfFintype`
(`Core/Data/Fintype/Sets.lean`) as a local instance.
-/

namespace Question

variable {W : Type*}

/-- Every alternative of `P` entails some alternative of `Q`. -/
def Entails (P Q : Question W) : Prop :=
  ∀ p ∈ alt P, ∃ q ∈ alt Q, p ⊆ q

/-- `q` is a subquestion of `parent` if answering `parent` settles `q`. -/
def IsSubquestion (q parent : Question W) : Prop :=
  parent.Entails q

variable {P Q R : Question W}

/-! ### Reflexivity / transitivity -/

theorem Entails.refl (P : Question W) : P.Entails P :=
  fun p hp => ⟨p, hp, subset_rfl⟩

theorem Entails.trans (hPQ : P.Entails Q) (hQR : Q.Entails R) :
    P.Entails R := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hPQ p hp
  obtain ⟨r, hr, hqr⟩ := hQR q hq
  exact ⟨r, hr, hpq.trans hqr⟩

theorem IsSubquestion.refl (P : Question W) : IsSubquestion P P :=
  Entails.refl P

theorem IsSubquestion.trans
    (hPQ : IsSubquestion P Q) (hQR : IsSubquestion Q R) :
    IsSubquestion P R :=
  Entails.trans hQR hPQ

/-! ### Lattice ↔ entailment -/

/-- Inquisitive entailment `P ≤ Q` implies `P.Entails Q`; finiteness
supplies maximal extensions. -/
theorem entails_of_le (h : P ≤ Q) (hQ : Q.props.Finite) : P.Entails Q := by
  intro p hp
  have hpP : p ∈ P.props := alt_subset_props P hp
  have hpQ : p ∈ Q.props := (le_def.mp h) hpP
  exact exists_alt_above Q hQ hpQ

/-- Converse of `entails_of_le`, under finiteness of `P.props`. -/
theorem le_of_entails (hP : P.props.Finite) (h : P.Entails Q) : P ≤ Q := by
  rw [le_def]
  intro s hs
  obtain ⟨p, hp, hsp⟩ := exists_alt_above P hP hs
  obtain ⟨q, hq, hpq⟩ := h p hp
  exact Q.downward_closed q (alt_subset_props Q hq) s (hsp.trans hpq)

/-- Question entailment coincides with the inquisitive lattice order
under finiteness. -/
theorem entails_iff_le (hP : P.props.Finite) (hQ : Q.props.Finite) :
    P.Entails Q ↔ P ≤ Q :=
  ⟨le_of_entails hP, (entails_of_le · hQ)⟩

/-- Variant of `entails_of_le` for finite world types. -/
theorem entails_of_le' [Finite W] (h : P ≤ Q) : P.Entails Q :=
  entails_of_le h Q.props.toFinite

/-! ### Polar reduction -/

theorem entails_polar_polar_iff {p q : Set W}
    (hne_p : p ≠ ∅) (hnu_p : p ≠ Set.univ)
    (hne_q : q ≠ ∅) (hnu_q : q ≠ Set.univ) :
    (polar p).Entails (polar q) ↔
      (p ⊆ q ∨ p ⊆ qᶜ) ∧ (pᶜ ⊆ q ∨ pᶜ ⊆ qᶜ) := by
  simp only [Entails, alt_polar_of_nontrivial hne_p hnu_p,
    alt_polar_of_nontrivial hne_q hnu_q, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, exists_eq_or_imp,
    exists_eq_left]

end Question
