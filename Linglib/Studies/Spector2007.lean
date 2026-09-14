import Linglib.Semantics.Questions.Partition.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert

/-!
# Spector (2007): Scalar Implicatures: Exhaustivity and Gricean Reasoning

This file formalizes the Gricean derivation of exhaustivity of [spector-2007]. The
neo-Gricean rules infer from an utterance that the speaker does not believe any stronger
scalar alternative and then, assuming the speaker maximally informed, that the alternative is
false; on multiple disjunctions the second step yields unwanted negations, which the
alternative-expanding repair of [sauerland-2004] avoids only by an ad hoc scale. The paper
replaces the two rules by one reasoning over the question under discussion, a partition
([groenendijk-stokhof-1984]): the speaker's information state, relativized to the question,
entails the answer and no stronger member of the alternative set, and the hearer assumes the
state maximally informed among such states. `IsOptimal`, `optimalStates` and `maximalStates`
state this over any partition question, and `Implicates` what every maximal state entails.

For answers to a question about which atoms hold, states and answers are sets of valuations,
the finest question applies, and the alternative set of a positive answer, one that favors no
negative literal, is the set of positive answers. `isOptimal_iff` derives the paper's
reduction of optimality to "the answer is the strongest positive proposition the state
entails", `Pos i = P`, and `maximalStates_eq` its theorem: the unique maximal state is
`Exhaust P`, the minimal valuations of `P`, so a positive answer implicates its
exhaustification in the sense of Groenendijk and Stokhof. `no_unwanted_negation` checks the
reasoning against the disjunction case: no optimal state for *A or B* decides *A*.

## Implementation notes

Information states are consistent, so the contradiction is not a state; without this the
degenerate case of a single atom would admit the empty state as optimal. Positivity follows
the paper's main text, favoring a positive literal and no negative one, which entails the
appendix's clause that the proposition is neither the tautology nor the contradiction. The
appendix's syntactic theorems, that a proposition favors a literal exactly when every
formula expressing it mentions the literal and that positive propositions are those
expressible without negation, are not formalized, nor are the alternative sets the paper
proposes for negative and quasi-positive answers. The paper's third fact, that removing a
minimal valuation from a positive proposition leaves it positive, is bypassed: the proof of
the theorem here goes through the reduction directly.

## References

* [spector-2007]
* [groenendijk-stokhof-1984]
* [sauerland-2004]
-/

namespace Spector2007

/-! ### The Gricean reasoning over a partition question -/

section Gricean

variable {W : Type*} (Q : Setoid W)

/-- An information state relativized to the question: the union of the cells it meets. -/
def relativize (i : Set W) : Set W := {w | ∃ w' ∈ i, Q w' w}

theorem subset_relativize (i : Set W) : i ⊆ relativize Q i := λ w hw => ⟨w, hw, Q.refl' w⟩

@[simp] theorem relativize_bot (i : Set W) : relativize ⊥ i = i := by
  ext w; simp [relativize]

/-- Strong relevance: the answer excludes a cell and does not cut across cells. -/
def StronglyRelevant (α : Set W) : Prop :=
  (∃ w, Q.cell w ∩ α = ∅) ∧ ∀ w, w ∈ α ↔ Q.cell w ⊆ α

/-- The answer `α` is optimal in state `i` with respect to the alternative set `S`: the
relativized state entails `α` and no member of `S` it entails is stronger. -/
def IsOptimal (S : Set (Set W)) (α i : Set W) : Prop :=
  relativize Q i ⊆ α ∧ ∀ α' ∈ S, relativize Q i ⊆ α' → ¬ α' ⊂ α

/-- The consistent states in which `α` is optimal. -/
def optimalStates (S : Set (Set W)) (α : Set W) : Set (Set W) :=
  {i | i.Nonempty ∧ IsOptimal Q S α i}

/-- The maximally informed optimal states: no other optimal state is relatively stronger. -/
def maximalStates (S : Set (Set W)) (α : Set W) : Set (Set W) :=
  {i | i ∈ optimalStates Q S α ∧ ∀ i' ∈ optimalStates Q S α, ¬ relativize Q i' ⊂ relativize Q i}

/-- An answer implicates what every maximally informed optimal state entails. -/
def Implicates (S : Set (Set W)) (α β : Set W) : Prop := ∀ i ∈ maximalStates Q S α, i ⊆ β

theorem maximalStates_subset (S : Set (Set W)) (α : Set W) :
    maximalStates Q S α ⊆ optimalStates Q S α :=
  λ _ h => h.1

end Gricean

/-! ### Positive propositions -/

/-- A valuation, the set of atoms it makes true. -/
abbrev Valuation (Atom : Type*) := Finset Atom

/-- A proposition, the set of valuations making it true. -/
abbrev Proposition (Atom : Type*) := Set (Valuation Atom)

/-- A literal: an atom or its negation. -/
inductive Literal (Atom : Type*) where
  | pos (a : Atom)
  | neg (a : Atom)
  deriving DecidableEq, Repr

variable {Atom : Type*}

namespace Literal

/-- The atom of a literal. -/
def atom : Literal Atom → Atom
  | pos a => a
  | neg a => a

/-- The literal holds in a valuation. -/
def Holds : Literal Atom → Valuation Atom → Prop
  | pos a, V => a ∈ V
  | neg a, V => a ∉ V

end Literal

/-- Exhaustification: the minimal valuations of `P`. -/
def Exhaust (P : Proposition Atom) : Proposition Atom := {V | V ∈ P ∧ ∀ V' ∈ P, ¬ V' ⊂ V}

/-- The positive extension of `P`: all supersets of its valuations. -/
def Pos (P : Proposition Atom) : Proposition Atom := {V | ∃ V' ∈ P, V' ⊆ V}

theorem Exhaust_subset (P : Proposition Atom) : Exhaust P ⊆ P := λ _ hV => hV.1

theorem subset_Pos (P : Proposition Atom) : P ⊆ Pos P := λ V hV => ⟨V, hV, Finset.Subset.refl V⟩

theorem Pos_mono {P P' : Proposition Atom} (h : P ⊆ P') : Pos P ⊆ Pos P' :=
  λ _ ⟨V', hV', hle⟩ => ⟨V', h hV', hle⟩

/-- Every valuation of `P` lies above a minimal one. -/
theorem exists_minimal (P : Proposition Atom) {s : Valuation Atom} (hs : s ∈ P) :
    ∃ t ∈ P, t ⊆ s ∧ ∀ u ∈ P, ¬ u ⊂ t := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hmin : ∀ u ∈ P, ¬ u ⊂ s
    · exact ⟨s, hs, Finset.Subset.refl s, hmin⟩
    · simp only [not_forall, not_not] at hmin
      obtain ⟨u, huP, husub⟩ := hmin
      obtain ⟨t, htP, htub, htmin⟩ := ih u husub huP
      exact ⟨t, htP, htub.trans husub.subset, htmin⟩

theorem Exhaust_nonempty {P : Proposition Atom} (h : P.Nonempty) : (Exhaust P).Nonempty :=
  let ⟨_, hV⟩ := h
  let ⟨t, htP, _, hmin⟩ := exists_minimal P hV
  ⟨t, htP, hmin⟩

/-- The paper's second fact: exhaustification does not change the positive extension. -/
theorem Pos_Exhaust (P : Proposition Atom) : Pos (Exhaust P) = Pos P := by
  refine Set.Subset.antisymm (Pos_mono (Exhaust_subset P)) λ V ⟨V', hV', hle⟩ => ?_
  obtain ⟨t, htP, hts, hmin⟩ := exists_minimal P hV'
  exact ⟨t, ⟨htP, hmin⟩, hts.trans hle⟩

/-- Exhaustification entails every state in which the answer is optimal. -/
theorem Exhaust_subset_of_Pos_eq {P i : Proposition Atom} (h : Pos i = P) : Exhaust P ⊆ i := by
  rintro V ⟨hVP, hmin⟩
  by_contra hVi
  obtain ⟨V', hV'i, hle⟩ : V ∈ Pos i := h ▸ hVP
  have hV'P : V' ∈ P := h ▸ subset_Pos i hV'i
  exact hmin V' hV'P (Finset.ssubset_iff_subset_ne.2 ⟨hle, λ heq => hVi (heq ▸ hV'i)⟩)

variable [DecidableEq Atom]

/-- The valuation identical to `V` except on the atom of `L`. -/
def flip (V : Valuation Atom) (L : Literal Atom) : Valuation Atom :=
  if h : L.atom ∈ V then V.erase L.atom else V.cons L.atom h

/-- `P` favors `L`: some valuation makes both true and flipping `L` makes `P` false. -/
def Favors (P : Proposition Atom) (L : Literal Atom) : Prop :=
  ∃ V ∈ P, L.Holds V ∧ flip V L ∉ P

/-- A positive proposition favors a positive literal and no negative one. -/
def IsPositive (P : Proposition Atom) : Prop :=
  (∃ a, Favors P (.pos a)) ∧ ∀ a, ¬ Favors P (.neg a)

/-- The positive propositions, the alternative set of a positive answer. -/
def positives : Set (Proposition Atom) := {P | IsPositive P}

/-- A positive proposition contains the valuations extending its valuations by one atom,
since otherwise it would favor the negation of that atom. -/
theorem IsPositive.cons_mem {P : Proposition Atom} (hP : IsPositive P) {V : Valuation Atom}
    (hV : V ∈ P) {a : Atom} (ha : a ∉ V) : V.cons a ha ∈ P := by
  by_contra h
  refine hP.2 a ⟨V, hV, ha, ?_⟩
  simpa [flip, Literal.atom, ha] using h

/-- A positive proposition is closed upward. -/
theorem IsPositive.mem_of_subset {P : Proposition Atom} (hP : IsPositive P)
    {V' V : Valuation Atom} (hV' : V' ∈ P) (hle : V' ⊆ V) : V ∈ P := by
  generalize hn : V.card - V'.card = n
  induction n using Nat.strong_induction_on generalizing V' with
  | _ n ih =>
    rcases eq_or_ssubset_of_subset hle with rfl | hss
    · exact hV'
    · obtain ⟨a, haV, haV'⟩ := Finset.exists_of_ssubset hss
      have hsub : V'.cons a haV' ⊆ V := λ x hx =>
        (Finset.mem_cons.1 hx).elim (λ h => h ▸ haV) (λ h => hle h)
      have hcard : V'.card < V.card := Finset.card_lt_card hss
      exact ih _ (by rw [Finset.card_cons]; omega) (hP.cons_mem hV' haV') hsub rfl

theorem IsPositive.nonempty {P : Proposition Atom} (hP : IsPositive P) : P.Nonempty :=
  let ⟨_, V, hV, _⟩ := hP.1
  ⟨V, hV⟩

theorem IsPositive.ne_univ {P : Proposition Atom} (hP : IsPositive P) : P ≠ Set.univ := by
  rintro rfl
  obtain ⟨_, _, -, -, h⟩ := hP.1
  exact h (Set.mem_univ _)

/-- A nonempty, non-universal, upward-closed proposition is positive: it favors the atoms of
its minimal valuations and no negative literal. -/
theorem isPositive_of_upward {P : Proposition Atom} (hne : P.Nonempty) (hnu : P ≠ Set.univ)
    (hup : ∀ V ∈ P, ∀ V', V ⊆ V' → V' ∈ P) : IsPositive P := by
  refine ⟨?_, λ a ⟨V, hV, haV, hflip⟩ => ?_⟩
  · obtain ⟨V₀, hV₀⟩ := hne
    obtain ⟨V, hVP, -, hmin⟩ := exists_minimal P hV₀
    have hVne : V.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      exact hnu (Set.eq_univ_of_forall λ V' => hup ∅ hVP V' (Finset.empty_subset _))
    obtain ⟨a, ha⟩ := hVne
    refine ⟨a, V, hVP, ha, λ hmem => hmin _ ?_ (Finset.erase_ssubset ha)⟩
    simpa [flip, Literal.atom, ha] using hmem
  · have haV' : a ∉ V := haV
    refine hflip ?_
    simpa [flip, Literal.atom, haV'] using
      hup V hV (V.cons a haV') λ x hx => Finset.mem_cons.2 (Or.inr hx)

/-- The paper's first fact: a positive proposition is its own positive extension. -/
theorem Pos_of_isPositive {P : Proposition Atom} (hP : IsPositive P) : Pos P = P :=
  Set.Subset.antisymm (λ _ ⟨_, hV', hle⟩ => hP.mem_of_subset hV' hle) (subset_Pos P)

/-- The positive extension of a consistent state that does not exclude nothing is positive:
the strongest positive proposition the state entails. -/
theorem Pos_isPositive {i : Proposition Atom} (hi : i.Nonempty) (hnu : Pos i ≠ Set.univ) :
    IsPositive (Pos i) :=
  isPositive_of_upward (hi.mono (subset_Pos i)) hnu
    λ _ ⟨V', hV', hle⟩ _ hle' => ⟨V', hV', hle.trans hle'⟩

/-! ### The reduction and the theorem -/

/-- The paper's reduction: a positive answer is optimal in a consistent state exactly when it
is the strongest positive proposition the state entails. -/
theorem isOptimal_iff {P i : Proposition Atom} (hP : IsPositive P) (hi : i.Nonempty) :
    IsOptimal ⊥ positives P i ↔ Pos i = P := by
  simp only [IsOptimal, relativize_bot, positives, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hiP, hopt⟩
    have hsub : Pos i ⊆ P := λ _ ⟨V', hV', hle⟩ => hP.mem_of_subset (hiP hV') hle
    by_contra hne
    have hnu : Pos i ≠ Set.univ := λ h => hP.ne_univ (Set.eq_univ_of_univ_subset (h ▸ hsub))
    exact hopt (Pos i) (Pos_isPositive hi hnu) (subset_Pos i)
      (Set.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
  · rintro rfl
    exact ⟨subset_Pos i, λ α' hα' hiα' hss =>
      hss.2 ((Pos_mono hiα').trans (Pos_of_isPositive hα').subset)⟩

theorem optimalStates_eq {P : Proposition Atom} (hP : IsPositive P) :
    optimalStates ⊥ positives P = {i | i.Nonempty ∧ Pos i = P} :=
  Set.ext λ _ => and_congr_right (isOptimal_iff hP)

/-- The theorem: for a positive answer the unique maximally informed optimal state is its
exhaustification. -/
theorem maximalStates_eq {P : Proposition Atom} (hP : IsPositive P) :
    maximalStates ⊥ positives P = {Exhaust P} := by
  have hI := optimalStates_eq hP
  have hExh : Exhaust P ∈ optimalStates ⊥ positives P := by
    rw [hI]
    exact ⟨Exhaust_nonempty hP.nonempty, by rw [Pos_Exhaust, Pos_of_isPositive hP]⟩
  have hent : ∀ i ∈ optimalStates ⊥ positives P, Exhaust P ⊆ i := λ i hi => by
    rw [hI] at hi
    exact Exhaust_subset_of_Pos_eq hi.2
  ext i
  simp only [maximalStates, Set.mem_ofPred_eq, Set.mem_singleton_iff, relativize_bot]
  constructor
  · rintro ⟨hi, hmax⟩
    by_contra hne
    exact hmax _ hExh (Set.ssubset_iff_subset_ne.2 ⟨hent i hi, λ h => hne h.symm⟩)
  · rintro rfl
    exact ⟨hExh, λ i' hi' hss => hss.2 (hent i' hi')⟩

/-- A positive answer implicates its exhaustification. -/
theorem implicates_Exhaust {P : Proposition Atom} (hP : IsPositive P) :
    Implicates ⊥ positives P (Exhaust P) := by
  intro i hi
  rw [maximalStates_eq hP, Set.mem_singleton_iff] at hi
  exact hi.subset

/-! ### Disjunction -/

/-- The proposition that `a` holds. -/
def atomProp (a : Atom) : Proposition Atom := {V | a ∈ V}

/-- *A or B*. -/
def orProp (a b : Atom) : Proposition Atom := {V | a ∈ V ∨ b ∈ V}

/-- *Only A or only B*. -/
def exclOr (a b : Atom) : Proposition Atom := {V | V = {a} ∨ V = {b}}

theorem orProp_isPositive (a b : Atom) : IsPositive (orProp a b) := by
  refine isPositive_of_upward ⟨{a}, Or.inl (Finset.mem_singleton_self a)⟩ ?_ ?_
  · intro h
    have : (∅ : Valuation Atom) ∈ orProp a b := by rw [h]; exact Set.mem_univ _
    rcases this with h' | h' <;> exact Finset.notMem_empty _ h'
  · rintro _ hV _ hle
    rcases hV with h | h
    exacts [Or.inl (hle h), Or.inr (hle h)]

/-- The exhaustification of *A or B* is exclusive: only *A* or only *B*. -/
theorem Exhaust_orProp (a b : Atom) : Exhaust (orProp a b) = exclOr a b := by
  ext V
  simp only [Exhaust, orProp, exclOr, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hV, hmin⟩
    have single : ∀ c ∈ V, (∀ x ∈ V, x = c) → V = {c} := λ c hc h =>
      Finset.eq_singleton_iff_unique_mem.2 ⟨hc, h⟩
    rcases hV with ha | hb
    · refine Or.inl (single a ha λ x hx => ?_)
      by_contra hne
      exact hmin (V.erase x) (Or.inl (Finset.mem_erase.2 ⟨λ h => hne h.symm, ha⟩))
        (Finset.erase_ssubset hx)
    · refine Or.inr (single b hb λ x hx => ?_)
      by_contra hne
      exact hmin (V.erase x) (Or.inr (Finset.mem_erase.2 ⟨λ h => hne h.symm, hb⟩))
        (Finset.erase_ssubset hx)
  · rintro (rfl | rfl)
    · refine ⟨Or.inl (Finset.mem_singleton_self a), λ V' hV' hss => ?_⟩
      rw [Finset.eq_empty_of_ssubset_singleton hss] at hV'
      exact hV'.elim (Finset.notMem_empty a) (Finset.notMem_empty b)
    · refine ⟨Or.inr (Finset.mem_singleton_self b), λ V' hV' hss => ?_⟩
      rw [Finset.eq_empty_of_ssubset_singleton hss] at hV'
      exact hV'.elim (Finset.notMem_empty a) (Finset.notMem_empty b)

/-- *A or B* implicates *only A or only B*. -/
theorem orProp_implicates_exclOr (a b : Atom) :
    Implicates ⊥ positives (orProp a b) (exclOr a b) :=
  Exhaust_orProp a b ▸ implicates_Exhaust (orProp_isPositive a b)

/-- No unwanted negation: no state in which *A or B* is optimal decides *A*, since a state
entailing *A* would have *A* as a better answer and one entailing *not A* would have *B*. -/
theorem no_unwanted_negation {a b : Atom} (hab : a ≠ b) {i : Proposition Atom}
    (hi : i ∈ optimalStates ⊥ positives (orProp a b)) :
    ¬ i ⊆ atomProp a ∧ ¬ i ⊆ (atomProp a)ᶜ := by
  rw [optimalStates_eq (orProp_isPositive a b)] at hi
  obtain ⟨-, hPos⟩ := hi
  have hb : ({b} : Valuation Atom) ∈ orProp a b := Or.inr (Finset.mem_singleton_self b)
  have ha : ({a} : Valuation Atom) ∈ orProp a b := Or.inl (Finset.mem_singleton_self a)
  constructor
  · intro h
    have hsub : Pos i ⊆ atomProp a := λ _ ⟨_, hV', hle⟩ => hle (h hV')
    rw [hPos] at hsub
    exact hab (Finset.mem_singleton.1 (hsub hb))
  · intro h
    have hsub : Pos i ⊆ atomProp b := by
      rintro _ ⟨V', hV', hle⟩
      have hV'or : V' ∈ orProp a b := hPos ▸ subset_Pos i hV'
      rcases hV'or with ha' | hb'
      · exact absurd ha' (h hV')
      · exact hle hb'
    rw [hPos] at hsub
    exact hab (Finset.mem_singleton.1 (hsub ha)).symm

end Spector2007
