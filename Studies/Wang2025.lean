module

public import Linglib.Fragments.Mandarin.Adverbs
public import Linglib.Fragments.Mandarin.Verbs
public import Linglib.Semantics.Presupposition.Verb
public import Linglib.Semantics.Presupposition.Iterative
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Fintype.Prod
public import Linglib.Semantics.Alternatives.Competition
public import Linglib.Semantics.Exhaustification.Finite

/-!
# Wang (2025): Presupposition, Competition, and Coherence

Wang's dissertation explains when a presupposition trigger of Mandarin is obligatory and when it
is dropped by a competition between the presuppositional sentence and its non-presuppositional
alternative, a sentence with the same assertion that is obtained by deleting or replacing the
trigger. Three constraints decide the competition, ranked in this order. Internal Coherence
requires the utterance to be consistent with the common ground, Felicity Presupposition requires
a presupposition to be entailed by it, and Maximize Presupposition, after Heim, bars a form
where a presuppositionally stronger alternative is usable. An utterance commits the speaker to a
set of information states and a context admits a set of them, so coherence is overlap, and the
context entails a proposition when every state it admits believes the proposition.

## Main statements

* `obligatory_of_entailed`, `omitted_of_not_entailed`: the trigger is obligatory where the
  context entails its presupposition and dropped where the context is silent about it.
* `obligatory_of_positive_evidence`, `omitted_of_denied`, `omitted_of_ignorance`: against the
  exhaustified alternative the trigger is obligatory under positive evidence for the
  presupposition, and dropped where the context denies it or the speaker is ignorant of it.
* `exhIE_eq_exhMx_of_unique`, `disjunction_two_maxima`: exhaustification by a maximal consistent
  subset of the alternatives agrees with innocent exclusion when that subset is unique, and a
  disjunction has two, the source of the optionality of the change-of-state triggers.

## Implementation notes

* Information states are nonempty sets of worlds; the belief operator `K p` is the set of
  states included in `p`, and possibility and ignorance are the corresponding overlap
  conditions.
* The experiments of Chapters 3 and 5 and the de re and postsupposition analyses of Chapters
  5 and 6 are not represented.
* `Trigger` lists the lexical rows of Table 4.1; its cleft row is a construction without a
  lexical entry and is not represented.

## References

* [wang-2025]
* [katzir-2007]
* [heim-1991]
-/

@[expose] public section

namespace Wang2025

variable {W : Type*}

/-! ### Information states, commitments and contexts -/

/-- `K p` is the set of nonempty information states included in `p`, those in which the speaker
believes `p`. -/
def K (p : Set W) : Set (Set W) := {s | s.Nonempty ∧ s ⊆ p}

/-- `Poss p` is the set of states meeting `p`, those in which the speaker holds `p` possible. -/
def Poss (p : Set W) : Set (Set W) := {s | (s ∩ p).Nonempty}

/-- `Ignorant p` is the set of states in which `p` and its negation are both possible. -/
def Ignorant (p : Set W) : Set (Set W) := Poss p ∩ Poss pᶜ

/-- A candidate is an utterance in the competition, given by the states its use commits the
speaker to and by its presupposition if it has one. -/
structure Candidate (W : Type*) where
  commitment : Set (Set W)
  presup : Option (Set W)

/-- The presuppositional sentence with presupposition `p` and assertion `a` commits the speaker
to both. -/
def presupSentence (p a : Set W) : Candidate W := ⟨K (p ∩ a), some p⟩

/-- The unexhaustified non-presuppositional alternative commits the speaker to `a`. -/
def plain (a : Set W) : Candidate W := ⟨K a, none⟩

/-- The alternative exhaustified against `q` below the belief operator commits the speaker to
`a` and to the negation of `q`. -/
def plainExhBelowK (a q : Set W) : Candidate W := ⟨K (a ∩ qᶜ), none⟩

/-- The alternative exhaustified against `q` above the belief operator commits the speaker to
`a` while the speaker does not believe `q`. -/
def plainExhAboveK (a q : Set W) : Candidate W := ⟨K a \ K q, none⟩

/-! ### The constraints and their ranking, (3) -/

/-- Internal Coherence is violated when the commitment excludes every admissible state. -/
def ViolIC (ctx : Set (Set W)) (c : Candidate W) : Prop := Disjoint ctx c.commitment

/-- Felicity Presupposition is violated by a presuppositional sentence whose presupposition
the context does not entail. -/
def ViolFP (ctx : Set (Set W)) (c : Candidate W) : Prop :=
  ∃ p, c.presup = some p ∧ ¬ ctx ⊆ K p

/-- A context admits a candidate when every admissible state believes its presupposition, if it
has one. -/
def Candidate.admits (c : Candidate W) : Set (Set (Set W)) :=
  {ctx | ∀ p, c.presup = some p → ctx ⊆ K p}

theorem Candidate.admits_of_presup_none {c : Candidate W} (h : c.presup = none) :
    c.admits = Set.univ := by
  ext ctx; simp [Candidate.admits, h]

theorem Candidate.admits_of_presup_some {c : Candidate W} {p : Set W} (h : c.presup = some p) :
    c.admits = {ctx | ctx ⊆ K p} := by
  ext ctx; simp [Candidate.admits, h]

/-- A presuppositional candidate is admitted by fewer contexts than a plain one, since the
context `{∅}` admits no presupposition. -/
theorem Candidate.admits_ssubset_univ {c : Candidate W} {p : Set W} (h : c.presup = some p) :
    c.admits ⊂ Set.univ := by
  rw [Candidate.admits_of_presup_some h]
  refine Set.ssubset_univ_iff.2 fun huniv ↦ ?_
  have hmem : ({∅} : Set (Set W)) ∈ {ctx | ctx ⊆ K p} := by rw [huniv]; trivial
  exact (hmem (Set.mem_singleton _)).1.ne_empty rfl

/-- Maximize Presupposition is violated by a candidate without a presupposition at a context
where its rival blocks it, (3c). -/
def ViolMP (ctx : Set (Set W)) (rival c : Candidate W) : Prop :=
  c.presup = none ∧ ctx ∉ Alternatives.unblocked (fun _ ↦ {rival}) Candidate.admits c

/-- A plain candidate violates Maximize Presupposition exactly when the context entails its
rival's presupposition. -/
theorem violMP_iff {ctx : Set (Set W)} {rival c : Candidate W} :
    ViolMP ctx rival c ↔ c.presup = none ∧ ∃ p, rival.presup = some p ∧ ctx ⊆ K p := by
  refine and_congr_right fun hc ↦ ?_
  rw [Alternatives.mem_unblocked_iff, Candidate.admits_of_presup_none hc]
  simp only [Set.mem_univ, true_and, Set.mem_singleton_iff, forall_eq, not_forall, not_not]
  constructor
  · rintro ⟨hctx, hss⟩
    rcases hr : rival.presup with _ | p
    · rw [Candidate.admits_of_presup_none hr] at hss; exact absurd rfl hss.ne
    · exact ⟨p, rfl, by rwa [Candidate.admits_of_presup_some hr] at hctx⟩
  · rintro ⟨p, hp, hctx⟩
    exact ⟨(Candidate.admits_of_presup_some hp).symm ▸ hctx, Candidate.admits_ssubset_univ hp⟩

/-- `Beats cs a b` compares two candidates by strict domination along the list `cs` of violation
predicates, `a` beating `b` at the first constraint on which they differ. -/
def Beats : List (Candidate W → Prop) → Candidate W → Candidate W → Prop
  | [], _, _ => False
  | C :: cs, a, b => (¬ C a ∧ C b) ∨ ((C a ↔ C b) ∧ Beats cs a b)

/-- The ranking Internal Coherence ≫ Felicity Presupposition ≫ Maximize Presupposition,
evaluated for the competition between `sp` and its alternative. -/
def ranking (ctx : Set (Set W)) (sp : Candidate W) : List (Candidate W → Prop) :=
  [ViolIC ctx, ViolFP ctx, ViolMP ctx sp]

/-- A presuppositional sentence violates Felicity Presupposition exactly when the context does
not entail its presupposition. A trigger without an alternative, such as *jiu* 'only', enters no
competition, so this alone bars it from every context short of entailing the presupposition. -/
@[simp] theorem violFP_presupSentence {ctx : Set (Set W)} {p a : Set W} :
    ViolFP ctx (presupSentence p a) ↔ ¬ ctx ⊆ K p :=
  ⟨fun ⟨_, hq, h⟩ ↦ Option.some.inj hq ▸ h, fun h ↦ ⟨p, rfl, h⟩⟩

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
  Or.inr ⟨⟨fun h ↦ absurd h hc, fun h ↦ absurd h hsp⟩,
    Or.inl ⟨fun ⟨q, hq, _⟩ ↦ by simp [hc0] at hq, ⟨p, rfl, hp⟩⟩⟩

/-- A presuppositional sentence whose presupposition is entailed beats a coherent
non-presuppositional alternative. -/
theorem presup_beats_of_entailed {ctx : Set (Set W)} {p a : Set W} {c : Candidate W}
    (hc0 : c.presup = none) (hsp : ¬ Disjoint ctx (K (p ∩ a))) (hc : ¬ Disjoint ctx c.commitment)
    (hp : ctx ⊆ K p) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) c :=
  Or.inr ⟨⟨fun h ↦ absurd h hsp, fun h ↦ absurd h hc⟩,
    Or.inr ⟨⟨fun ⟨q, hq, hnq⟩ ↦ absurd hp (Option.some.inj hq ▸ hnq), fun ⟨q, hq, _⟩ ↦ by
      simp [hc0] at hq⟩,
      Or.inl ⟨fun h ↦ absurd h.1 (by simp [presupSentence]), violMP_iff.2 ⟨hc0, p, rfl, hp⟩⟩⟩⟩

/-! ### The tableaux -/

private theorem K_inter_subset {p a : Set W} : K (p ∩ a) ⊆ K p :=
  fun _ ⟨hne, hs⟩ ↦ ⟨hne, hs.trans Set.inter_subset_left⟩

/-- In Table 4.2 the context entails the presupposition, so the trigger is obligatory. -/
theorem obligatory_of_entailed {ctx : Set (Set W)} {p a : Set W} (hp : ctx ⊆ K p)
    (hwit : ∃ s ∈ ctx, s ⊆ a) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) (plain a) := by
  obtain ⟨s, hs, hsa⟩ := hwit
  have hsp := hp hs
  refine presup_beats_of_entailed rfl ?_ ?_ hp
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hsp.1, Set.subset_inter hsp.2 hsa⟩
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hsp.1, hsa⟩

/-- In Table 4.3 the context does not entail the presupposition, so the trigger is dropped. -/
theorem omitted_of_not_entailed {ctx : Set (Set W)} {p a : Set W} (hp : ¬ ctx ⊆ K p)
    (hwit : ∃ s ∈ ctx, s.Nonempty ∧ s ⊆ p ∩ a) :
    Beats (ranking ctx (presupSentence p a)) (plain a) (presupSentence p a) := by
  obtain ⟨s, hs, hne, hsa⟩ := hwit
  refine plain_beats_of_not_entailed rfl ?_ ?_ hp
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hne, hsa⟩
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hne, hsa.trans Set.inter_subset_right⟩

/-- In Table 4.4, with positive evidence for the presupposition and the alternative exhaustified
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

/-- In Table 4.5 the context denies the presupposition, so the presuppositional sentence is
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

/-- In Table 4.6, an ignorance context with the alternative exhaustified above the belief
operator, the presuppositional sentence commits the speaker to the presupposition and so
contradicts the ignorance, while the alternative is coherent; the trigger is dropped. -/
theorem omitted_of_ignorance {ctx : Set (Set W)} {p a : Set W} (hign : ctx ⊆ Ignorant p)
    (hwit : ∃ s ∈ ctx, s ⊆ a) :
    Beats (ranking ctx (presupSentence p a)) (plainExhAboveK a p) (presupSentence p a) := by
  obtain ⟨s, hs, hsa⟩ := hwit
  obtain ⟨⟨w, hw, -⟩, ⟨v, hv, hvp⟩⟩ := hign hs
  refine Or.inl ⟨?_, ?_⟩
  · refine Set.not_disjoint_iff.mpr ⟨s, hs, ⟨⟨w, hw⟩, hsa⟩, fun hsp ↦ ?_⟩
    exact hvp (hsp.2 hv)
  · show Disjoint ctx (K (p ∩ a))
    rw [Set.disjoint_left]
    rintro t ht ⟨-, htp⟩
    obtain ⟨-, ⟨u, hu, hup⟩⟩ := hign ht
    exact hup (htp hu).1

/-! ### The repetitive adverbs

*You* and *zai* 'again' assert their prejacent, so deleting the adverb leaves a sentence with the
same assertion, the alternative that (1) requires. The tableaux for the presuppositional sentence
and its deletion alternative are then those of Tables 4.2 and 4.3, with the presupposition that
the prejacent held of an earlier eventuality. -/

section Again

open Presupposition ModalLogic

/-- The candidate for a sentence with the partial meaning `φ` commits the speaker to its
presupposition and its assertion. -/
def Candidate.ofPartialProp (φ : PartialProp W) : Candidate W :=
  presupSentence {w | φ.presup w} {w | φ.assertion w}

variable {R : SetRel W W} {P : W → Prop} {ctx : Set (Set W)}

/-- A sentence with *again* is obligatory, against the sentence without it, when the context
entails that its prejacent held before. -/
theorem again_obligatory_of_entailed (hp : ctx ⊆ K {e | ◇[R] P e})
    (hwit : ∃ s ∈ ctx, s ⊆ {e | P e}) :
    Beats (ranking ctx (.ofPartialProp (again R P))) (.ofPartialProp (again R P))
      (plain {e | P e}) :=
  obligatory_of_entailed hp hwit

/-- A sentence with *again* loses to the sentence without it when the context does not entail
that its prejacent held before. -/
theorem again_omitted_of_not_entailed (hp : ¬ ctx ⊆ K {e | ◇[R] P e})
    (hwit : ∃ s ∈ ctx, s.Nonempty ∧ s ⊆ {e | ◇[R] P e} ∩ {e | P e}) :
    Beats (ranking ctx (.ofPartialProp (again R P))) (plain {e | P e})
      (.ofPartialProp (again R P)) :=
  omitted_of_not_entailed hp hwit

end Again

/-! ### Exhaustification by maximal consistent subsets, (20) and (24) -/

variable [DecidableEq W]

/-- The reading of (24) for the maximal subset `M` is `φ` with every member of `M` negated. -/
def exhMx (φ : Finset W) (M : Finset (Finset W)) : Finset W :=
  φ.filter (fun w ↦ ∀ q ∈ M, w ∉ q)

open Exhaustification in
/-- When the maximal consistent subset is unique, innocent exclusion, the operator of (20), and
the operator of (24) agree, (25). -/
theorem exhIE_eq_exhMx_of_unique {φ : Finset W} {alts M₀ : Finset (Finset W)}
    (h₀ : IsMaximalExclusion alts φ M₀) (huniq : ∀ M, IsMaximalExclusion alts φ M → M = M₀) :
    exhIE (asSetOfSets alts) ↑φ = ↑(exhMx φ M₀) := by
  rw [exhIE_eq_sdiff_of_maximal_unique _ _ (isMaximalExclusion_iff.1 h₀) fun X hX ↦ ?_]
  · ext w
    simp [exhMx, mem_asSetOfSets]
  · obtain ⟨M, -, rfl⟩ := exists_asSetOfSets_eq hX.prop.1
    rw [huniq M (isMaximalExclusion_iff.2 hX)]

/-- The worlds of the disjunction example (26) are the pairs of truth values of `p` and `q`. -/
abbrev PQ := Bool × Bool

/-- The alternative `p` of (26). -/
def pAlt : Finset PQ := Finset.univ.filter (·.1 = true)

/-- The alternative `q` of (26). -/
def qAlt : Finset PQ := Finset.univ.filter (·.2 = true)

/-- The disjunction `p ∨ q` with the alternatives `p`, `q` and `p ∧ q`, (26), has two maximal
consistent subsets, yielding the readings `q ∧ ¬p` and `p ∧ ¬q`. -/
theorem disjunction_two_maxima :
    Exhaustification.IsMaximalExclusion {pAlt, qAlt, pAlt ∩ qAlt} (pAlt ∪ qAlt)
        {pAlt, pAlt ∩ qAlt} ∧
      Exhaustification.IsMaximalExclusion {pAlt, qAlt, pAlt ∩ qAlt} (pAlt ∪ qAlt)
        {qAlt, pAlt ∩ qAlt} ∧
      exhMx (pAlt ∪ qAlt) {pAlt, pAlt ∩ qAlt} = qAlt \ pAlt ∧
      exhMx (pAlt ∪ qAlt) {qAlt, pAlt ∩ qAlt} = pAlt \ qAlt := by
  decide

/-! ### The alternative structure of the triggers, Table 4.1 -/

/-- A trigger's non-presuppositional alternative is obtained by deleting the trigger, by
replacing it, or not at all. -/
inductive AltStructure
  | deletion
  | replacement
  | none
  deriving DecidableEq, Repr

/-- The lexical triggers of Table 4.1 are the adverbs *ye* 'also', *fan'er* 'instead', *reng*
'still', *you* and *zai* 'again', *buzai* 'no longer' and *jiu* 'only', and the verbs *kaishi*
'start', *zhidao* 'know' and *houhui* 'regret'. -/
inductive Trigger
  | ye
  | faner
  | reng
  | you
  | zai
  | kaishi
  | buzai
  | zhidao
  | jiu
  | houhui
  deriving DecidableEq, Repr

/-- The fragment entry of a trigger, an adverb or a verb. -/
def Trigger.entry : Trigger → Presupposition.TriggerItem ⊕ Mandarin.Verb
  | .ye => .inl Mandarin.Adverbs.ye
  | .faner => .inl Mandarin.Adverbs.faner
  | .reng => .inl Mandarin.Adverbs.reng
  | .you => .inl Mandarin.Adverbs.you
  | .zai => .inl Mandarin.Adverbs.zai
  | .buzai => .inl Mandarin.Adverbs.buzai
  | .jiu => .inl Mandarin.Adverbs.jiu
  | .kaishi => .inr Mandarin.kaishi
  | .zhidao => .inr Mandarin.zhidao
  | .houhui => .inr Mandarin.houhui

/-- Table 4.1. A trigger whose assertion is its prejacent deletes, as the additive, contrastive,
continuative, repetitive and inchoative ones do. The cessative and the factive replace, *buzai* by
negation and *zhidao* by *renwei* 'believe'. No sequence of deletions and replacements yields a
sentence with the assertion of *jiu* 'only' or of *houhui* 'regret', which have no alternative. -/
def Trigger.altStructure : Trigger → AltStructure
  | .ye | .faner | .reng | .you | .zai | .kaishi => .deletion
  | .buzai | .zhidao => .replacement
  | .jiu | .houhui => .none

/-- The verbal triggers are presupposition triggers by their fragment entries. -/
theorem isTrigger_of_entry {t : Trigger} {v : Mandarin.Verb} (h : t.entry = .inr v) :
    v.IsTrigger := by
  cases t <;> simp only [Trigger.entry, Sum.inr.injEq, reduceCtorEq] at h <;> subst h <;> decide

/-- The replacement for *zhidao* is non-presuppositional, as (1) requires, since *renwei*
'believe' is not a trigger. -/
theorem not_isTrigger_renwei : ¬ Mandarin.renwei.IsTrigger := by decide

end Wang2025
