import Linglib.Fragments.Mandarin.Particles
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Fintype.Prod

/-!
# Wang (2025): Presupposition, Competition, and Coherence

This file formalizes the alternative-competition account of [wang-2025]'s dissertation on the
partial resolution of presuppositions in Mandarin. A presuppositional sentence competes with
its non-presuppositional structural alternative, a [katzir-2007] alternative with the same
assertion, (1)–(2), which exists by deletion of the trigger for the additive, repetitive and
continuative particles, by replacement for the change-of-state and factive triggers, and not
at all for *jiu* 'only' (Table 4.1, `altStructureOf`). Three ranked constraints decide the
competition, (3): Internal Coherence, that the utterance is consistent with the common ground;
Felicity Presupposition, that a presupposition is entailed by the common ground; and Maximize
Presupposition, after [heim-1991], that a form is not used when a presuppositionally stronger
alternative is. Coherence outranks felicity, which outranks Maximize Presupposition
(`Beats`, `ranking`). Utterances and contexts are modelled by the speaker's information
states: an utterance commits the speaker to a set of states (`Candidate`), and a context
admits a set of states, so that coherence is overlap and entailment is inclusion in the
belief set `K`.

Three general facts drive every tableau: a coherent presuppositional sentence beats an
incoherent alternative (`presup_beats_of_incoherent`), a coherent alternative beats a
presuppositional sentence whose presupposition is not entailed (`plain_beats_of_not_entailed`),
and when the presupposition is entailed the presuppositional sentence beats a coherent
alternative (`presup_beats_of_entailed`). The tableaux follow: with the presupposition entailed
the trigger is obligatory, Table 4.2 (`obligatory_of_entailed`); with the context silent the
trigger is dropped, Table 4.3 (`omitted_of_not_entailed`); with positive evidence for the
presupposition and the alternative exhaustified below the speaker's belief operator, the
exhaustive implicature contradicts the context, so the trigger is obligatory, Table 4.4
(`obligatory_of_positive_evidence`); with the presupposition denied the trigger is
incoherent, Table 4.5 (`omitted_of_denied`); and in an ignorance context, with exhaustification
above the belief operator, the presuppositional sentence contradicts the speaker's ignorance,
Table 4.6 (`omitted_of_ignorance`). The exhaustification operator of (24) negates a maximal
consistent subset of the alternatives, and where several maximal subsets exist it yields
several readings (`MaxConsistent`, `exhMx`); the operator of (20) negates only the alternatives
common to all of them (`exhIe`), so the two coincide when the maximal subset is unique
(`exhIe_eq_exhMx_of_unique`), and a disjunction has two maximal subsets, (26)
(`disjunction_two_maxima`), which is how the optionality of the change-of-state triggers
arises, Tables 4.7 and 4.9.

## Implementation notes

* Information states are nonempty sets of worlds; the belief operator `K p` is the set of
  states included in `p`, and possibility and ignorance are the corresponding overlap
  conditions.
* The experiments of Chapters 3 and 5 and the de re and postsupposition analyses of Chapters
  5 and 6 are not represented.
* The fragment's *er* is not among the dissertation's triggers and receives no alternative
  structure.

## References

* [wang-2025]
* [katzir-2007]
* [heim-1991]
-/

namespace Wang2025

open Mandarin.Particles

variable {W : Type*}

/-! ### Information states, commitments and contexts -/

/-- The speaker believes `p`: the nonempty information states included in `p`. -/
def K (p : Set W) : Set (Set W) := {s | s.Nonempty ∧ s ⊆ p}

/-- The speaker holds `p` possible: the states meeting `p`. -/
def Poss (p : Set W) : Set (Set W) := {s | (s ∩ p).Nonempty}

/-- The speaker is ignorant about `p`: `p` and its negation are both possible. -/
def Ignorant (p : Set W) : Set (Set W) := Poss p ∩ Poss pᶜ

/-- An utterance in the competition: the states its use commits the speaker to, and its
presupposition if it has one. -/
structure Candidate (W : Type*) where
  commitment : Set (Set W)
  presup : Option (Set W)

/-- The presuppositional sentence with presupposition `p` and assertion `a`: the speaker
commits to both. -/
def presupSentence (p a : Set W) : Candidate W := ⟨K (p ∩ a), some p⟩

/-- The non-presuppositional alternative asserting `a`, unexhaustified. -/
def plain (a : Set W) : Candidate W := ⟨K a, none⟩

/-- The alternative exhaustified against `q` below the belief operator: the speaker commits
to `a` and to the negation of `q`. -/
def plainExhBelowK (a q : Set W) : Candidate W := ⟨K (a ∩ qᶜ), none⟩

/-- The alternative exhaustified against `q` above the belief operator: the speaker commits to
`a` and does not believe `q`. -/
def plainExhAboveK (a q : Set W) : Candidate W := ⟨K a \ K q, none⟩

/-! ### The constraints and their ranking, (3) -/

/-- Internal Coherence is violated when the commitment excludes every admissible state. -/
def ViolIC (ctx : Set (Set W)) (c : Candidate W) : Prop := Disjoint ctx c.commitment

/-- Felicity Presupposition is violated by a presuppositional sentence whose presupposition
the context does not entail. -/
def ViolFP (ctx : Set (Set W)) (c : Candidate W) : Prop :=
  ∃ p, c.presup = some p ∧ ¬ ctx ⊆ K p

/-- Maximize Presupposition is violated by the non-presuppositional candidate when its rival's
presupposition is entailed by the context. -/
def ViolMP (ctx : Set (Set W)) (rival c : Candidate W) : Prop :=
  c.presup = none ∧ ∃ p, rival.presup = some p ∧ ctx ⊆ K p

/-- Strict-domination comparison along a list of violation predicates: `a` beats `b` at the
first constraint on which they differ. -/
def Beats : List (Candidate W → Prop) → Candidate W → Candidate W → Prop
  | [], _, _ => False
  | C :: cs, a, b => (¬ C a ∧ C b) ∨ ((C a ↔ C b) ∧ Beats cs a b)

/-- The ranking Internal Coherence ≫ Felicity Presupposition ≫ Maximize Presupposition,
evaluated for the competition between `sp` and its alternative. -/
def ranking (ctx : Set (Set W)) (sp : Candidate W) : List (Candidate W → Prop) :=
  [ViolIC ctx, ViolFP ctx, ViolMP ctx sp]

/-! ### The three decisive facts -/

/-- A coherent presuppositional sentence beats an incoherent alternative. -/
theorem presup_beats_of_incoherent {ctx : Set (Set W)} {p a : Set W} {c : Candidate W}
    (hsp : ¬ Disjoint ctx (K (p ∩ a))) (hc : Disjoint ctx c.commitment) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) c :=
  Or.inl ⟨hsp, hc⟩

/-- A coherent alternative beats a presuppositional sentence whose presupposition is not
entailed, when both are coherent. -/
theorem plain_beats_of_not_entailed {ctx : Set (Set W)} {p a : Set W} {c : Candidate W}
    (hc0 : c.presup = none) (hsp : ¬ Disjoint ctx (K (p ∩ a))) (hc : ¬ Disjoint ctx c.commitment)
    (hp : ¬ ctx ⊆ K p) :
    Beats (ranking ctx (presupSentence p a)) c (presupSentence p a) :=
  Or.inr ⟨⟨λ h => absurd h hc, λ h => absurd h hsp⟩,
    Or.inl ⟨λ ⟨q, hq, _⟩ => by simp [hc0] at hq, ⟨p, rfl, hp⟩⟩⟩

/-- A presuppositional sentence whose presupposition is entailed beats a coherent
non-presuppositional alternative. -/
theorem presup_beats_of_entailed {ctx : Set (Set W)} {p a : Set W} {c : Candidate W}
    (hc0 : c.presup = none) (hsp : ¬ Disjoint ctx (K (p ∩ a))) (hc : ¬ Disjoint ctx c.commitment)
    (hp : ctx ⊆ K p) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) c :=
  Or.inr ⟨⟨λ h => absurd h hsp, λ h => absurd h hc⟩,
    Or.inr ⟨⟨λ ⟨q, hq, hnq⟩ => absurd hp (Option.some.inj hq ▸ hnq), λ ⟨q, hq, _⟩ => by
      simp [hc0] at hq⟩,
      Or.inl ⟨λ ⟨h, _⟩ => by simp [presupSentence] at h, ⟨hc0, p, rfl, hp⟩⟩⟩⟩

/-! ### The tableaux -/

private theorem K_inter_subset {p a : Set W} : K (p ∩ a) ⊆ K p :=
  λ _ ⟨hne, hs⟩ => ⟨hne, hs.trans Set.inter_subset_left⟩

/-- Table 4.2: the context entails the presupposition, so the trigger is obligatory. -/
theorem obligatory_of_entailed {ctx : Set (Set W)} {p a : Set W} (hp : ctx ⊆ K p)
    (hwit : ∃ s ∈ ctx, s ⊆ a) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) (plain a) := by
  obtain ⟨s, hs, hsa⟩ := hwit
  have hsp := hp hs
  refine presup_beats_of_entailed rfl ?_ ?_ hp
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hsp.1, Set.subset_inter hsp.2 hsa⟩
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hsp.1, hsa⟩

/-- Table 4.3: the context does not entail the presupposition, so the trigger is dropped. -/
theorem omitted_of_not_entailed {ctx : Set (Set W)} {p a : Set W} (hp : ¬ ctx ⊆ K p)
    (hwit : ∃ s ∈ ctx, s.Nonempty ∧ s ⊆ p ∩ a) :
    Beats (ranking ctx (presupSentence p a)) (plain a) (presupSentence p a) := by
  obtain ⟨s, hs, hne, hsa⟩ := hwit
  refine plain_beats_of_not_entailed rfl ?_ ?_ hp
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hne, hsa⟩
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hne, hsa.trans Set.inter_subset_right⟩

/-- Table 4.4: with positive evidence for the presupposition and the alternative exhaustified
below the belief operator, the exhaustive implicature contradicts the context and the trigger
is obligatory, although its presupposition is not entailed. -/
theorem obligatory_of_positive_evidence {ctx : Set (Set W)} {p a : Set W}
    (hposs : ctx ⊆ Poss p) (hwit : ∃ s ∈ ctx, s.Nonempty ∧ s ⊆ p ∩ a) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) (plainExhBelowK a p) := by
  obtain ⟨s, hs, hne, hsa⟩ := hwit
  refine presup_beats_of_incoherent (Set.not_disjoint_iff.mpr ⟨s, hs, hne, hsa⟩) ?_
  rw [Set.disjoint_left]
  rintro t ht ⟨-, hta⟩
  obtain ⟨w, hw, hwp⟩ := hposs ht
  exact (hta hw).2 hwp

/-- Table 4.5: the context denies the presupposition, so the presuppositional sentence is
incoherent and the alternative wins. -/
theorem omitted_of_denied {ctx : Set (Set W)} {p a : Set W} (hneg : ctx ⊆ K pᶜ)
    (hwit : ∃ s ∈ ctx, s ⊆ a) :
    Beats (ranking ctx (presupSentence p a)) (plainExhBelowK a p) (presupSentence p a) := by
  obtain ⟨s, hs, hsa⟩ := hwit
  have hsn := hneg hs
  refine Or.inl ⟨Set.not_disjoint_iff.mpr ⟨s, hs, hsn.1, Set.subset_inter hsa hsn.2⟩, ?_⟩
  show Disjoint ctx (K (p ∩ a))
  rw [Set.disjoint_left]
  rintro t ht ⟨⟨w, hw⟩, htp⟩
  exact (hneg ht).2 hw (htp hw).1

/-- Table 4.6: in an ignorance context, with the alternative exhaustified above the belief
operator, the presuppositional sentence commits the speaker to the presupposition and so
contradicts the ignorance, while the alternative is coherent; the trigger is dropped. -/
theorem omitted_of_ignorance {ctx : Set (Set W)} {p a : Set W} (hign : ctx ⊆ Ignorant p)
    (hwit : ∃ s ∈ ctx, s ⊆ a) :
    Beats (ranking ctx (presupSentence p a)) (plainExhAboveK a p) (presupSentence p a) := by
  obtain ⟨s, hs, hsa⟩ := hwit
  obtain ⟨⟨w, hw, -⟩, ⟨v, hv, hvp⟩⟩ := hign hs
  refine Or.inl ⟨?_, ?_⟩
  · refine Set.not_disjoint_iff.mpr ⟨s, hs, ⟨⟨w, hw⟩, hsa⟩, λ hsp => ?_⟩
    exact hvp (hsp.2 hv)
  · show Disjoint ctx (K (p ∩ a))
    rw [Set.disjoint_left]
    rintro t ht ⟨-, htp⟩
    obtain ⟨-, ⟨u, hu, hup⟩⟩ := hign ht
    exact hup (htp hu).1

/-! ### Exhaustification by maximal consistent subsets, (20) and (24) -/

variable [DecidableEq W]

/-- `M` is a maximal subset of the alternatives whose joint negation is consistent with `φ`,
the `Max` of (24). -/
def MaxConsistent (φ : Finset W) (alts : Finset (Finset W)) (M : Finset (Finset W)) : Prop :=
  M ⊆ alts ∧ (φ.filter (λ w => ∀ q ∈ M, w ∉ q)).Nonempty ∧
    ∀ M' ∈ alts.powerset, M ⊂ M' → ¬ (φ.filter (λ w => ∀ q ∈ M', w ∉ q)).Nonempty

instance (φ : Finset W) (alts M : Finset (Finset W)) : Decidable (MaxConsistent φ alts M) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ M' ∈ alts.powerset, _))

/-- The reading of (24) for the maximal subset `M`: `φ` with every member of `M` negated. -/
def exhMx (φ : Finset W) (M : Finset (Finset W)) : Finset W :=
  φ.filter (λ w => ∀ q ∈ M, w ∉ q)

/-- The reading of (20): `φ` with every innocently excludable alternative negated, those in
every maximal consistent subset. -/
def exhIe (φ : Finset W) (alts : Finset (Finset W)) : Set W :=
  {w | w ∈ φ ∧ ∀ q ∈ alts, (∀ M, MaxConsistent φ alts M → q ∈ M) → w ∉ q}

/-- When the maximal consistent subset is unique, the two operators agree, (25). -/
theorem exhIe_eq_exhMx_of_unique {φ : Finset W} {alts M₀ : Finset (Finset W)}
    (h₀ : MaxConsistent φ alts M₀) (huniq : ∀ M, MaxConsistent φ alts M → M = M₀) :
    exhIe φ alts = ↑(exhMx φ M₀) := by
  ext w
  simp only [exhIe, exhMx, Set.mem_ofPred_eq, Finset.coe_filter]
  refine and_congr_right λ _ => ⟨λ h q hq => h q (h₀.1 hq) (λ M hM => huniq M hM ▸ hq),
    λ h q _ hall => h q (hall M₀ h₀)⟩

/-- The worlds of the disjunction example (26): the truth values of `p` and `q`. -/
abbrev PQ := Bool × Bool

/-- `p` in (26). -/
def pAlt : Finset PQ := Finset.univ.filter (·.1 = true)

/-- `q` in (26). -/
def qAlt : Finset PQ := Finset.univ.filter (·.2 = true)

/-- The disjunction `p ∨ q` with the alternatives `p`, `q` and `p ∧ q`, (26), has two maximal
consistent subsets, yielding the readings `q ∧ ¬p` and `p ∧ ¬q`. -/
theorem disjunction_two_maxima :
    MaxConsistent (pAlt ∪ qAlt) {pAlt, qAlt, pAlt ∩ qAlt} {pAlt, pAlt ∩ qAlt} ∧
      MaxConsistent (pAlt ∪ qAlt) {pAlt, qAlt, pAlt ∩ qAlt} {qAlt, pAlt ∩ qAlt} ∧
      exhMx (pAlt ∪ qAlt) {pAlt, pAlt ∩ qAlt} = qAlt \ pAlt ∧
      exhMx (pAlt ∪ qAlt) {qAlt, pAlt ∩ qAlt} = pAlt \ qAlt := by
  decide

/-! ### The alternative structure of the triggers, Table 4.1 -/

/-- How a trigger's non-presuppositional alternative is obtained: by deleting the trigger, by
replacing it, or not at all. -/
inductive AltStructure
  | deletion
  | replacement
  | none
  deriving DecidableEq, Repr

/-- Table 4.1 for the fragment's triggers. The additive, repetitive, continuative, inchoative
and contrastive particles delete; the cessative and factive triggers replace, *buzai* by
negation and *zhidao* by *believe*; *jiu* 'only' has no alternative. The fragment's *er* is
not among the dissertation's triggers. -/
def altStructureOf : MandarinTrigger → Option AltStructure
  | .ye => some .deletion
  | .you => some .deletion
  | .reng => some .deletion
  | .kaishi => some .deletion
  | .faner => some .deletion
  | .buzai => some .replacement
  | .zhidao => some .replacement
  | .jiu => some .none
  | .er => Option.none

end Wang2025
