import Linglib.Semantics.Attitudes.Desire.Preferential
import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Discourse.Commitment.Basic
import Linglib.Data.Examples.CondoravdiLauer2012

/-!
# Condoravdi and Lauer 2012: imperatives as preferential commitments

[condoravdi-lauer-2012] give declaratives and imperatives one kind of conventional effect, a
public commitment of the speaker, differing in the attitude committed to: a declarative commits
the speaker to act as though believing its content, an imperative to act as though the content
were a maximal element of the speaker's effective preference structure, the consistent ranking
of propositions that guides action. The range of uses, from commands to wishes, permissions
and disinterested advice, comes from the context, while the constraints on every use come from
the commitment: successive imperatives are consistent because the maximal elements of a
consistent structure are jointly realizable, the speaker cannot be insincere because the
commitment is self-verifying, and a preference against the content survives a concession but
not disinterested advice, since the addressee's goal enters the adviser's structure at the
bottom by cooperation by default. The paper's formal points against ordering-source
affirmation and, in its discussion of To-Do Lists, against a secondary update of the ordering
source are checked as well.

## Implementation notes

The information state of a preference structure is its world type, so the paper's consistency
is `PreferenceStructure.Consistent Set.univ`; the theorems take an information state `B`, since
the paper's incompatibility is relative to what the speaker believes. A public effective
preference is a commitment of force `.preferential`; the doxastic reduction of a commitment to
one's own preferential commitment, which the paper takes over from [condoravdi-lauer-2011], is a
hypothesis on the world-indexed commitment state. Disinterested advice identifies the content
with the adopted goal, which the paper reaches through a means-end inference, and quantifies
over the effective structure alone where cooperation by default ranges over all of the
adviser's structures.

## TODO

* Informal in the paper and not formalized: the two preconditions and the re-ranking of a
  permission, the second meaning component (36) that limits speaker involvement and excludes
  promises, the two conditions on wish uses behind (37), the conditional preferences of offers
  (41), and the practical reasoning step by which the preliminary semantics (32) is recovered
  from the final (34).

## References

* [C. Condoravdi and S. Lauer, *Imperatives: Meaning and illocutionary force*
  (2012)][condoravdi-lauer-2012]
* [C. Condoravdi and S. Lauer, *Performative verbs and performative acts*
  (2011)][condoravdi-lauer-2011]
* [S. Schmerling, *How imperatives are special, and how they aren't* (1982)][schmerling-1982]
* [M. Schwager, *Interpreting Imperatives* (2006)][schwager-2006]
* [S. Kaufmann and M. Schwager, *A unified analysis of conditional imperatives*
  (2009)][kaufmann-schwager-2009]
* [M. Kaufmann, *Interpreting Imperatives* (2012)][kaufmann-2012]
* [P. Portner, *Imperatives and modals* (2007)][portner-2007]
-/

namespace CondoravdiLauer2012

open Commitment Desire.Preferential Modality.Kratzer Data.Examples

variable {A W : Type*} {P : A → W → PreferenceStructure W} {a : A} {p q : Set W} {w : W}

/-! ### Effective preferences and public commitments

`Want P a p w` is the effective preference `EP_w(a, p)`: `p` is a maximal element of `a`'s
effective preference structure `P a w`, the distinguished consistent structure that determines
`a`'s action choices, (28) and (29). The public commitments of §3.2 are `Commitment`s:
`commit a p` is `PB(a, p)`, to act as though believing `p`, and `commit a p .preferential` is
`PEP(a, p)`, to act as though `p` were a maximal effective preference. -/

variable (P) in
/-- The preferential commitments in `K` are effective preferences at `w`: a speaker commits to
an effective preference only when holding it, condition (iii) of §3.4. -/
def Sincere (K : State A W) (w : W) : Prop :=
  ∀ c ∈ K, c.force = .preferential → c.polarity = .commit → Want P c.committer c.content w

/-! ### The conventions -/

/-- Uttering a declarative, whose propositional denotation falls under the convention (30): the
doxastic context set narrows by the content and the preferential one stays. -/
theorem declarative_contextSets (a : A) (p : Set W) (K : State A W) :
    contextSet (ofForce (insert (commit a p) K) .doxastic) =
        p ∩ contextSet (ofForce K .doxastic) ∧
      contextSet (ofForce (insert (commit a p) K) .preferential) =
        contextSet (ofForce K .preferential) :=
  ⟨contextSet_ofForce_insert_of_eq_of_commit rfl rfl, contextSet_ofForce_insert_of_ne nofun⟩

/-- Uttering an imperative under the imperative convention (47): the preferential context set
narrows by the content and the doxastic one stays, so an imperative never claims its content,
(10). -/
theorem imperative_contextSets (a : A) (p : Set W) (K : State A W) :
    contextSet (ofForce (insert (commit a p .preferential) K) .preferential) =
        p ∩ contextSet (ofForce K .preferential) ∧
      contextSet (ofForce (insert (commit a p .preferential) K) .doxastic) =
        contextSet (ofForce K .doxastic) :=
  ⟨contextSet_ofForce_insert_of_eq_of_commit rfl rfl, contextSet_ofForce_insert_of_ne nofun⟩

/-! ### Self-verification -/

/-- The denotation of `IMP(p)` over a world-indexed commitment state, (34): the worlds at which
the speaker is publicly committed to an effective preference for `p`. -/
def imp (K : W → State A W) (a : A) (p : Set W) : Set W := {w | commit a p .preferential ∈ K w}

/-- Doxastic reduction for preference commitment ([condoravdi-lauer-2011]): a doxastic
commitment to one's own preferential commitment is that preferential commitment. -/
def DoxasticReduction (K : W → State A W) : Prop :=
  ∀ w (c : Commitment A W), c.force = .preferential →
    commit c.committer {v | c ∈ K v} ∈ K w → c ∈ K w

/-- An imperative is self-verifying, §3.3: the doxastic commitment to `IMP(p)` that (30) assigns
to its utterance is true at the world of utterance, so the utterance cannot be insincere and is
not open to the challenges of (23) to (25). The operator implementation of §6 thereby ends in
the commitment the imperative convention (47) assigns to the denotation `p` directly. -/
theorem imp_self_verifying {K : W → State A W} (hK : DoxasticReduction K)
    (h : commit a (imp K a p) ∈ K w) : w ∈ imp K a p :=
  hK w _ rfl h

/-! ### Directive uses -/

/-- The final semantics (34) in a directive context, §3.4: with the speaker committing sincerely,
(iii), and believing the addressee's effective preference for `p` a precondition of `p`, (ii)
under (i), a preferential commitment to `p` is an effective preference satisfied only if the
addressee effectively prefers `p`. The paper reaches the exact-match effective preference for
the addressee's preference, the private counterpart of the preliminary (32), by a step of
practical reasoning it leaves informal; without it, the only-if reading is what follows. -/
theorem directive_want_addressee {K : State A W} {ad : A} (hs : Sincere P K w)
    (hp : commit a p .preferential ∈ K) (hii : p ⊆ {v | Want P ad p v}) :
    WantNecessary P a {v | Want P ad p v} w :=
  (hs _ hp rfl rfl).wantNecessary.mono hii

/-! ### Consistency -/

/-- The preferential commitments of a sincere speaker with consistent effective preferences are
jointly realizable in the information state: successive imperatives are consistent, §2.1. -/
theorem imperatives_consistent {K : State A W} {B : Set W} (hC : (P a w).Consistent B)
    (hs : Sincere P K w) :
    (B ∩ contextSet (ofForce (ofCommitter K a) .preferential)).Nonempty := by
  refine hC.inter_sInter_maxElts_nonempty.mono
    (Set.inter_subset_inter_right _ (Set.sInter_subset_sInter ?_))
  rintro _ ⟨c, ⟨⟨⟨hc, rfl⟩, hf⟩, hp⟩, rfl⟩
  exact hs c hc hf hp

/-- Two imperatives with incompatible contents are not both sincere at one time, (11) and (15):
the second revises the speaker's effective preferences, (12) to (14). -/
theorem imperatives_revise {K : State A W} {B : Set W} (hC : (P a w).Consistent B)
    (hp : commit a p .preferential ∈ K) (hq : commit a q .preferential ∈ K)
    (h : B ∩ (p ∩ q) = ∅) : ¬ Sincere P K w :=
  λ hs => (hC.inter_inter_nonempty_of_mem_maxElts (hs _ hp rfl rfl) (hs _ hq rfl rfl)).ne_empty h

/-! ### Endorsement: advice, permission, concession -/

/-- Disinterested advice, (39) and (40): a goal adopted by cooperation by default, with nothing
ranked below it in the effective structure, is an effective preference only if no preference of
the agent, effective or not, conflicts with it; the follow-ups *but I don't want you to* and
*but I wish you would not* are both out. -/
theorem advice_compatible {S : PreferenceStructure W} {B g : Set W} (hC : S.Consistent B)
    (hb : ∀ r ∈ S.prefs, ¬ S.prec r g) (hg : g ∈ S.maxElts) (hq : q ∈ S.prefs) :
    (B ∩ (g ∩ q)).Nonempty :=
  Set.nonempty_iff_ne_empty.2 λ h => hb q hq (hC.prec_of_mem_maxElts hg hq h)

/-- A concession, (21) and (22): a retained preference against an effective one is ranked
strictly below it, so it survives as a wish but not as an effective preference. The follow-up
*but I don't want you to* is out and *but I wish you would not* is fine. -/
theorem concession_not_want {S : PreferenceStructure W} {B : Set W} (hC : S.Consistent B)
    (hp : p ∈ S.maxElts) (hq : q ∈ S.prefs) (h : B ∩ (p ∩ q) = ∅) : q ∉ S.maxElts :=
  λ hq' => hq'.2 p hp.1 (hC.prec_of_mem_maxElts hp hq h)

/-- The utterances whose follow-ups the paper contrasts. -/
inductive Use
  | assertion | directive | advice | concession
  deriving DecidableEq

/-- What the utterance requires of the speaker's effective preference structure: an effective
preference for the content unless it is an assertion, which incurs no preferential commitment,
`declarative_contextSets`, and nothing below the content for advice, (39). -/
def Use.Holds (u : Use) (S : PreferenceStructure W) (p : Set W) : Prop :=
  (u ≠ .assertion → p ∈ S.maxElts) ∧ (u = .advice → ∀ r ∈ S.prefs, ¬ S.prec r p)

/-- A follow-up's present preference against the content: effective for *I don't want you to*,
mere for *I wish you would not*, and none for a deontic statement or a past desire. -/
inductive Denial
  | want | wish | none
  deriving DecidableEq

/-- The denial's preference against the content: a preference unless there is none, an
effective one for a want. -/
def Denial.Against (d : Denial) (S : PreferenceStructure W) (q : Set W) : Prop :=
  (d ≠ .none → q ∈ S.prefs) ∧ (d = .want → q ∈ S.maxElts)

variable (W) in
/-- A follow-up is coherent when some consistent effective preference structure meets the
utterance's requirement on the content and carries the denial's preference against it. -/
def Coherent (u : Use) (d : Denial) : Prop :=
  ∃ (S : PreferenceStructure W) (p q : Set W),
    S.Consistent Set.univ ∧ u.Holds S p ∧ p ∩ q = ∅ ∧ d.Against S q

/-- One preference. -/
private def single (p : Set W) : PreferenceStructure W where
  prefs := {p}
  prec _ _ := False
  isStrictOrder := { irrefl := λ _ h => h, trans := λ _ _ _ h _ => h }

private theorem single_consistent {p : Set W} (hp : p.Nonempty) :
    (single p).Consistent Set.univ :=
  PreferenceStructure.consistent_of_realistic_of_isChain
    (λ _ hq => by rw [Set.mem_singleton_iff.1 hq, Set.inter_univ]; exact hp.ne_empty)
    (Set.pairwise_singleton _ _) (hp.mono (Set.subset_univ p))

/-- Two preferences, the first ranked strictly above the second. -/
private def pair {p q : Set W} (h : p ≠ q) : PreferenceStructure W where
  prefs := {p, q}
  prec r s := r = q ∧ s = p
  isStrictOrder :=
    { irrefl := λ _ hr => h (hr.2.symm.trans hr.1)
      trans := λ _ _ _ hr hs => absurd (hr.2.symm.trans hs.1) h }

private theorem pair_consistent {p q : Set W} (hp : p.Nonempty) (hq : q.Nonempty) (h : p ≠ q) :
    (pair h).Consistent Set.univ := by
  refine PreferenceStructure.consistent_of_realistic_of_isChain ?_ ?_ (hp.mono (Set.subset_univ p))
  · rintro _ (rfl | rfl)
    · rw [Set.inter_univ]; exact hp.ne_empty
    · rw [Set.inter_univ]; exact hq.ne_empty
  · rintro _ (rfl | rfl) _ (rfl | rfl) hne
    exacts [absurd rfl hne, Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, absurd rfl hne]

/-- A follow-up is coherent unless it denies an effective preference the utterance incurred,
`concession_not_want`, or denies the content of disinterested advice at all,
`advice_compatible`. A directive followed by a wish against its content is thereby predicted
coherent, a case the paper does not discuss. -/
theorem coherent_iff [Nontrivial W] {u : Use} {d : Denial} :
    Coherent W u d ↔ d = .none ∨ u = .assertion ∨ d ≠ .want ∧ u ≠ .advice := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne W
  have hne : ({x} : Set W) ≠ {y} := λ h => hxy (Set.singleton_eq_singleton_iff.1 h)
  have hxy' : ({x} : Set W) ∩ {y} = ∅ :=
    Set.singleton_inter_eq_empty.2 λ h => hxy (Set.mem_singleton_iff.1 h)
  constructor
  · rintro ⟨S, p, q, hC, ⟨hp, hb⟩, hpq, hq, hqm⟩
    by_cases hd : d = .none
    · exact Or.inl hd
    by_cases ha : u = .assertion
    · exact Or.inr (Or.inl ha)
    have hpq' : Set.univ ∩ (p ∩ q) = ∅ := by rw [Set.univ_inter]; exact hpq
    exact Or.inr (Or.inr ⟨λ hw => concession_not_want hC (hp ha) (hq hd) hpq' (hqm hw),
      λ hu => (advice_compatible hC (hb hu) (hp ha) (hq hd)).ne_empty hpq'⟩)
  · rintro (rfl | rfl | ⟨hw, hu⟩)
    · exact ⟨single {x}, {x}, {y}, single_consistent ⟨x, Set.mem_singleton x⟩,
        ⟨λ _ => ⟨Set.mem_singleton _, λ _ _ h => h⟩, λ _ _ _ h => h⟩, hxy', λ h => absurd rfl h,
        nofun⟩
    · exact ⟨single {y}, {x}, {y}, single_consistent ⟨y, Set.mem_singleton y⟩,
        ⟨λ h => absurd rfl h, nofun⟩, hxy', λ _ => Set.mem_singleton _,
        λ _ => ⟨Set.mem_singleton _, λ _ _ h => h⟩⟩
    · exact ⟨pair hne, {x}, {y}, pair_consistent ⟨x, Set.mem_singleton x⟩
        ⟨y, Set.mem_singleton y⟩ hne, ⟨λ _ => ⟨Or.inl rfl, λ _ _ h => hne h.1⟩, λ h => absurd h hu⟩,
        hxy', λ _ => Or.inr rfl, λ h => absurd h hw⟩

/-! ### Ordering-source affirmation -/

/-- [schwager-2006]'s ordering-source affirmation, (19), read as a bouletic necessity of the
content, predicts the consistency requirement: two affirmed contents share a best world. -/
theorem affirmation_consistent {f : ModalBase W} {g : OrderingSource W}
    (hne : (bestWorlds f g w).Nonempty) (hp : necessity f g (· ∈ p) w)
    (hq : necessity f g (· ∈ q) w) : (p ∩ q).Nonempty :=
  let ⟨u, hu⟩ := hne; ⟨u, hp u hu, hq u hu⟩

/-- The weaker affirmation of [kaufmann-schwager-2009], (20), that the negation of the content
not follow from what is optimal, does not: whenever the speaker's wishes leave the content open,
a content and its negation are both weakly affirmed, so (20) admits the incompatible
imperatives of (15). -/
theorem weak_affirmation_compl {f : ModalBase W} {g : OrderingSource W}
    (hp : ∃ u ∈ bestWorlds f g w, u ∈ p) (hq : ∃ u ∈ bestWorlds f g w, u ∉ p) :
    possibility f g (· ∈ p) w ∧ possibility f g (· ∈ pᶜ) w :=
  ⟨hp, hq⟩

/-! ### To-Do Lists -/

/-- [portner-2007]'s secondary update adds the content to the modal ordering source; when the
source already holds a proposition incompatible with the content, a best world verifying it
stays best, so the common ground does not come to entail *must p*, §5.2. -/
theorem todo_not_must {f : ModalBase W} {g : OrderingSource W} {φ ψ : W → Prop} {u : W}
    (hψ : ψ ∈ g w) (hφψ : ∀ v, ψ v → ¬ φ v) (hu : u ∈ bestWorlds f g w) (huψ : ψ u) :
    ¬ necessity f (λ v => φ :: g v) φ w :=
  λ h => hφψ u huψ (h u (mem_bestWorlds_cons hψ hφψ hu huψ))

/-! ### The rows

The uses of (6) to (9), after [schmerling-1982]'s inventory, and the exclusions of (10) are
data; the sequences, follow-ups and challenges instantiate the theorems above. -/

/-- The second utterance of a sequence. -/
inductive Second
  | imperative | assertion
  deriving DecidableEq

/-- Whether the context lets the second utterance revise the first. -/
inductive Continuation
  | revising | conflicting
  deriving DecidableEq

/-- A sequence row: two utterances with incompatible contents. -/
structure Sequence where
  /-- The second utterance. -/
  second : Second
  /-- Whether the context lets it revise the first. -/
  continuation : Continuation

/-- The configuration a sequence row records. -/
def Sequence.ofRow (row : LinguisticExample) : Option Sequence := do
  guard (row.feature? "construction" = some "sequence")
  return ⟨← row.parse? "second" [("imperative", Second.imperative), ("assertion", .assertion)],
    ← row.parse? "continuation"
      [("revising", Continuation.revising), ("conflicting", .conflicting)]⟩

/-- The sequences of (11) to (16): incompatible imperatives are coherent only as a revision,
`imperatives_revise`, while an assertion of incompatible desires reports underlying preferences,
which need not be consistent. -/
theorem sequence_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "sequence" →
    ∃ s ∈ Sequence.ofRow row,
      (row.judgment = .acceptable ↔ s.second = .assertion ∨ s.continuation = .revising) := by
  decide

/-- A follow-up row: the utterance and the denial. -/
structure FollowUp where
  /-- The utterance. -/
  use : Use
  /-- The denial that follows. -/
  denial : Denial

/-- The configuration a follow-up row records. -/
def FollowUp.ofRow (row : LinguisticExample) : Option FollowUp := do
  guard (row.feature? "construction" = some "followUp")
  return ⟨← row.parse? "use" [("assertion", Use.assertion), ("directive", .directive),
      ("advice", .advice), ("concession", .concession)],
    ← row.parse? "denial"
      [("want", Denial.want), ("wish", .wish), ("deontic", .none), ("pastWant", .none)]⟩

/-- The follow-ups of (17), (18), (21), (22) and (40): acceptable exactly when coherent,
`coherent_iff`. -/
theorem followUp_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "followUp" →
    ∃ c ∈ FollowUp.ofRow row, (row.judgment = .acceptable ↔ Coherent Bool c.use c.denial) := by
  simp only [coherent_iff]
  decide

/-- The form of an utterance challenged as a lie or disbelieved. -/
inductive Form
  | imperative | performative | assertion
  deriving DecidableEq

/-- The form a challenge row records. -/
def Form.ofRow (row : LinguisticExample) : Option Form := do
  guard (row.feature? "construction" = some "challenge")
  return ← row.parse? "form"
    [("imperative", Form.imperative), ("performative", .performative), ("assertion", .assertion)]

/-- The challenges of (23) to (25): only the assertion of a desire can be called a lie or
disbelieved; imperatives and explicit performatives are self-verifying, `imp_self_verifying`. -/
theorem challenge_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "challenge" →
    ∃ f ∈ Form.ofRow row, (row.judgment = .acceptable ↔ f = .assertion) := by
  decide

end CondoravdiLauer2012
