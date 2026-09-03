import Linglib.Discourse.Commitment.Space
import Linglib.Discourse.Commitment.State

/-!
# van der Leer 2026: Speech Act Logic

[van-der-leer-2026] is a propositional dynamic logic of speech acts over the commitment states
of `Commitment.State`. Belief `B_a` and commitment `C_{a,b}` are modal operators; an
assertion is the update `c⌈π⌉_{a,b}` that creates a commitment, the performative update of
[krifka-2024a], which Sincerity and Competence pass on to beliefs, the informative update —
keeping common belief and commitment apart, as [bary-2025] demands. The projected discourse is
a commitment space in the sense of [cohen-krifka-2014] and [krifka-2015], a root state together
with its cooperative continuations, which the speech acts of the action language transform: an
assertion narrows the root and keeps the continuations in which the addressee confirms, a
question keeps the root and the continuations in which the addressee answers, a denegation
removes the continuations the denegated act reaches. Cooperativity, admissibility and
possibility of a speech act are the three levels of the thesis's hierarchy of discourse
expectations: a cooperative act is admissible and every act is possible, but not conversely.

## Main definitions

* `sincereRestrict` — the sincere update `c⌈π⌉^sin_{a,b}` (Definition 6), partial as in
  footnote 18.
* `CooperativeContinuation` (`⊏`, Definition 7); a commitment space (Definition 8) is
  `Commitment.Space (State W A)` under the partial order `⊑`.
* `SpeechAct` (Definition 20), `update` (Definitions 10, 19, 21–24).
* `Violation`, `Cooperative`, `Admissible` (Definitions 15–17).

## Main results

* `committed_assert` (Theorem 25) with the acknowledgment corollaries
  `believes_committed_assert` and `committed_committed_assert`; Theorem 26 is
  `State.Sincere.believes_of_committed_of_competent`.
* `committed_believes_of_sincere`, `exists_committed_believes_not_committed` (Theorem 27):
  under Sincerity a commitment entails a commitment to the corresponding belief, but not
  conversely — [krifka-2024b]'s "The buffet is open" is stronger than "I believe the buffet
  is open".
* `root_update_commitment_le` (Lemma 28), `committed_update` (Theorem 30).
* `assert_assert_of_subset` (Theorem 29), `cooperative_assert_of_not_committed` and
  `not_cooperative_assert_compl` (Theorem 31), `violation_assert_empty` (Theorem 33),
  `admissible_of_cooperative` and `exists_admissible_not_cooperative` (Theorem 34),
  `question_assert` (Theorem 35).

## Implementation notes

Propositions are world-sets, so the thesis's side condition that a proposition be
`C_{a,b}`-free holds vacuously, the antecedent of a conditional act holds at the root iff it is
`Set.univ`, and the `⊨_SAL` claims — for every space `C`, member `c` and world — are stated at
the root, `C_c` (Definition 13) being again a space with root `c`. Theorem 32, possibility, is
the totality of `update`.

## TODO

* Theorem 36, the cooperativity of answering a question, and speech act entailment
  (Definition 11) as a relation between acts.
* Report to the author: the witness for Theorem 27(2), `O_{a,b} = B_a ∪ {(w, w)}`, is not
  Euclidean (`buffet` replaces it); Theorem 31(1) needs `a ≠ b`, since for `a = b` the
  confirming assertion is redundant; and the well-definedness of the assertion update, called
  easy, needs the root case of `le_restrictCommitment_of_mem`.

## References

* [T. van der Leer, *Commitments, beliefs and expectations in conversation*
  (2026)][van-der-leer-2026]
* [C. Bary, *Speech acts, common ground and commitments* (2025)][bary-2025]
* [M. Krifka, *Performative updates and the modeling of speech acts* (2024)][krifka-2024a]
* [M. Krifka, *Structure and interpretation of declarative sentences* (2024)][krifka-2024b]
* [A. Cohen and M. Krifka, *Superlative quantifiers and meta-speech acts*
  (2014)][cohen-krifka-2014]
* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
-/

namespace VanDerLeer2026

open Commitment
open ModalLogic (IsSerial IsEuclidean box_D box_four box_five box_restrict not_box)
open ModalLogic.Epistemic (knows everyoneKnows everyoneKnows_iff)
open Relation (ReflGen)

variable {W A : Type*}

/-! ### Beliefs and commitments -/

section States

variable (c : State W A) (a b : A) (π : Set W) (w : W)

/-- Positive introspection of commitment: `C_{a,b} π → C_{a,b} C_{a,b} π`. -/
theorem committed_committed (h : c.Committed a b π w) :
    c.Committed a b {v | c.Committed a b π v} w :=
  box_four h

/-- Negative introspection of commitment: `¬ C_{a,b} π → C_{a,b} ¬ C_{a,b} π`. -/
theorem committed_not_committed (h : ¬ c.Committed a b π w) :
    c.Committed a b {v | ¬ c.Committed a b π v} w :=
  fun v hv => (not_box _ _ _).2 (box_five ((not_box _ _ _).1 h) v hv)

/-- Consistency of belief: no agent believes `⊥`. -/
theorem not_believes_empty : ¬ c.Believes a ∅ w :=
  fun h => let ⟨_, _, hv⟩ := box_D h; hv

/-- `π` is mutually believed at `w` (§2.2): it holds at every world some agent's belief reaches. -/
def MutuallyBelieved : Prop :=
  everyoneKnows c.belief Set.univ (· ∈ π) w

theorem mutuallyBelieved_iff : MutuallyBelieved c π w ↔ ∀ a, c.Believes a π w := by
  simp [MutuallyBelieved, State.Believes, everyoneKnows_iff]

/-- `π` is mutually committed to at `w` (§2.2): it holds at every world some commitment
relation reaches. -/
def MutuallyCommitted : Prop :=
  everyoneKnows (fun p : A × A => c.commitment p.1 p.2) Set.univ (· ∈ π) w

theorem mutuallyCommitted_iff : MutuallyCommitted c π w ↔ ∀ a b, c.Committed a b π w := by
  simp [MutuallyCommitted, State.Committed, knows, everyoneKnows_iff, Prod.forall]

/-- The sincere update `c⌈π⌉^sin_{a,b}` (Definition 6): `c⌈π⌉_{a,b}` with `a`'s belief narrowed
to the new `O_{a,b}`-edges. It is partial (footnote 18): `h` keeps the narrowed belief serial. -/
def sincereRestrict
    (h : ∀ w, ∃ v, c.belief a w v ∧ c.commitment a b w v ∧ v ∈ π) : State W A where
  belief x w v := c.belief x w v ∧ (x = a → (c.restrictCommitment a b π).commitment a b w v)
  commitment := (c.restrictCommitment a b π).commitment
  belief_kd45 x :=
    { serial := fun w => by
        by_cases hx : x = a
        · subst hx
          obtain ⟨v, hb, hc, hv⟩ := h w
          exact ⟨v, hb, fun _ => ⟨hc, fun _ => hv⟩⟩
        · obtain ⟨v, hv⟩ := IsSerial.serial (R := c.belief x) w
          exact ⟨v, hv, fun h' => absurd h' hx⟩
      trans := fun _ _ _ h₁ h₂ =>
        ⟨_root_.trans h₁.1 h₂.1, fun hx => _root_.trans (h₁.2 hx) (h₂.2 hx)⟩
      eucl := fun _ _ _ h₁ h₂ =>
        ⟨IsEuclidean.eucl _ _ _ h₁.1 h₂.1,
          fun hx => IsEuclidean.eucl _ _ _ (h₁.2 hx) (h₂.2 hx)⟩ }
  commitment_k45 := (c.restrictCommitment a b π).commitment_k45

variable {c a b π}

/-- The sincere update preserves Sincerity — the reason Definition 6 exists. -/
theorem sincere_sincereRestrict (hs : c.Sincere)
    (h : ∀ w, ∃ v, c.belief a w v ∧ c.commitment a b w v ∧ v ∈ π) :
    (sincereRestrict c a b π h).Sincere := by
  rintro x y w v ⟨hb, hx⟩
  by_cases hxa : x = a
  · subst hxa
    by_cases hyb : y = b
    · subst hyb
      exact hx rfl
    · exact ⟨hs _ _ _ _ hb, fun h => absurd h.2 hyb⟩
  · exact ⟨hs _ _ _ _ hb, fun h => absurd h.1 hxa⟩

/-- After the sincere update the speaker believes what was asserted. -/
theorem believes_sincereRestrict
    (h : ∀ w, ∃ v, c.belief a w v ∧ c.commitment a b w v ∧ v ∈ π) :
    (sincereRestrict c a b π h).Believes a π w :=
  fun _ hv => (hv.2 rfl).2 ⟨rfl, rfl⟩

/-- Definition 4 alone need not preserve Sincerity. -/
theorem exists_sincere_not_sincere_restrictCommitment :
    ∃ (c : State Bool Unit) (π : Set Bool),
      c.Sincere ∧ ¬ (c.restrictCommitment () () π).Sincere :=
  ⟨default, {true}, fun _ _ _ _ _ => trivial,
    fun h => Bool.false_ne_true ((h () () true false trivial).2 ⟨rfl, rfl⟩)⟩

/-- Theorem 27(1): under Sincerity, `C_{a,b} π → C_{a,b} B_a π`. -/
theorem committed_believes_of_sincere {w : W} (hs : c.Sincere) (h : c.Committed a b π w) :
    c.Committed a b {v | c.Believes a π v} w :=
  fun v hwv u hvu => h u (_root_.trans hwv (hs a b v u hvu))

/-- Both agents believe only `true`, at either world, and are committed to nothing: a sincere
state in which, at `false`, `C_{a,b} B_a {true}` holds but `C_{a,b} {true}` fails. -/
def buffet : State Bool Bool where
  belief _ _ v := v = true
  commitment _ _ _ _ := True
  belief_kd45 _ := { serial := fun _ => ⟨true, rfl⟩
                     trans := fun _ _ _ _ h => h
                     eucl := fun _ _ _ _ h => h }
  commitment_k45 _ _ := { trans := fun _ _ _ _ _ => trivial
                          eucl := fun _ _ _ _ _ => trivial }

/-- Theorem 27(2): `C_{a,b} B_a π → C_{a,b} π` is not valid over sincere states. -/
theorem exists_committed_believes_not_committed :
    ∃ (c : State Bool Bool) (a b : Bool) (π : Set Bool) (w : Bool),
      c.Sincere ∧ c.Committed a b {v | c.Believes a π v} w ∧ ¬ c.Committed a b π w :=
  ⟨buffet, true, false, {true}, false, fun _ _ _ _ _ => trivial, fun _ _ _ hu => hu,
    fun h => Bool.false_ne_true (h false trivial)⟩

end States

/-! ### Commitment spaces -/

/-- `c ⊏ c'`: `c'` is a cooperative continuation of `c` (Definition 7): beliefs and commitments
narrow, every commitment relation of `c'` is non-empty, and some commitment relation narrows
strictly. -/
structure CooperativeContinuation (c c' : State W A) : Prop where
  belief_le : ∀ a, c'.belief a ≤ c.belief a
  commitment_le : ∀ a b, c'.commitment a b ≤ c.commitment a b
  commitment_nonempty : ∀ a b, ∃ w v, c'.commitment a b w v
  commitment_lt : ∃ a b w v, c.commitment a b w v ∧ ¬ c'.commitment a b w v

@[inherit_doc] scoped infix:50 " ⊏ " => CooperativeContinuation

/-- `c ⊑ c'`: `c = c'` or `c ⊏ c'`. -/
scoped infix:50 " ⊑ " => ReflGen CooperativeContinuation

namespace CooperativeContinuation

variable {c c' d : State W A}

theorem ne (h : c ⊏ c') : c ≠ c' :=
  fun e => let ⟨_, _, _, _, h₁, h₂⟩ := h.commitment_lt; h₂ (e ▸ h₁)

/-- Whatever `c` is below, any state above `c` in belief and commitment is below too. -/
theorem of_le (h : c ⊏ c') (hb : ∀ a, c.belief a ≤ d.belief a)
    (hc : ∀ a b, c.commitment a b ≤ d.commitment a b) : d ⊏ c' where
  belief_le a := (h.belief_le a).trans (hb a)
  commitment_le a b := (h.commitment_le a b).trans (hc a b)
  commitment_nonempty := h.commitment_nonempty
  commitment_lt :=
    let ⟨a, b, w, v, h₁, h₂⟩ := h.commitment_lt; ⟨a, b, w, v, hc a b w v h₁, h₂⟩

theorem of_restrictCommitment {a b : A} {π : Set W} (h : c.restrictCommitment a b π ⊏ c') :
    c ⊏ c' :=
  h.of_le (fun _ => le_rfl) (c.restrictCommitment_commitment_le a b π)

instance : IsTrans (State W A) CooperativeContinuation where
  trans _ _ _ h₁ h₂ := h₂.of_le h₁.belief_le h₁.commitment_le

end CooperativeContinuation

section Order

variable {c c' : State W A}

theorem commitment_le_of_le (h : c ⊑ c') (a b : A) : c'.commitment a b ≤ c.commitment a b := by
  rcases h with _ | h
  · exact le_rfl
  · exact h.commitment_le a b

theorem eq_of_le_of_le (h : c ⊑ c') (h' : c' ⊑ c) : c = c' := by
  rcases h with _ | h
  · rfl
  · rcases h' with _ | h'
    · rfl
    · exact absurd rfl (_root_.trans h h').ne

end Order

/-- The cooperative-continuation order on states: `⊑` as `≤`, `⊏` as `<`. A commitment space
(Definition 8) is then a `Commitment.Space (State W A)`. -/
scoped instance : PartialOrder (State W A) where
  le c c' := c ⊑ c'
  lt c c' := c ⊏ c'
  le_refl _ := ReflGen.refl
  le_trans _ _ _ := trans_of (ReflGen CooperativeContinuation)
  le_antisymm _ _ := eq_of_le_of_le
  lt_iff_le_not_ge c c' :=
    ⟨fun h => ⟨.single h, fun h' => h.ne (eq_of_le_of_le (.single h) h')⟩,
      fun ⟨h, h'⟩ => by
        rcases h with _ | h
        · exact absurd ReflGen.refl h'
        · exact h⟩

variable (C : Space (State W A)) {c : State W A} (a b : A) (π : Set W) (w : W)

/-- A restriction `x⌈σ⌉_{d,e}` that belongs to `C` lies above `x` — unless it is the root and
differs from `x`, since the root need not have non-empty commitment relations. -/
theorem le_restrictCommitment_of_mem {x : State W A} {d e : A} {σ : Set W}
    (hmem : x.restrictCommitment d e σ ∈ C.states)
    (hroot : x.restrictCommitment d e σ = C.root → x.restrictCommitment d e σ = x) :
    x ⊑ x.restrictCommitment d e σ := by
  by_cases heq : x.restrictCommitment d e σ = x
  · rw [heq]
  refine ReflGen.single ⟨fun _ => le_rfl, x.restrictCommitment_commitment_le d e σ, ?_, ?_⟩
  · rcases (Relation.reflGen_iff _ _ _).1 (C.root_le hmem) with h | h
    · exact absurd (hroot h) heq
    · exact h.commitment_nonempty
  · by_contra hcon
    push Not at hcon
    exact heq (State.ext rfl (funext fun a' => funext fun b' => funext fun w =>
      funext fun v => propext ⟨(x.restrictCommitment_commitment_le d e σ a' b' w v ·),
        hcon a' b' w v⟩))

/-- `C[assert_{a,b}(π)]` (Definition 10): the root commits `a` to `π` towards `b`; the
continuations are the members of `C` above the state in which `b` has confirmed. -/
def assert : Space (State W A) where
  states := insert (C.root.restrictCommitment a b π)
    {c ∈ C.states | (C.root.restrictCommitment a b π).restrictCommitment b a π ⊑ c}
  root := C.root.restrictCommitment a b π
  isLeast := ⟨Set.mem_insert _ _, by
    rintro c (rfl | ⟨hc, h⟩)
    · rfl
    rcases (Relation.reflGen_iff _ _ _).1 h with rfl | h
    · refine le_restrictCommitment_of_mem C hc fun hroot => ?_
      exact hroot.trans
        ((C.root.restrictCommitment_restrictCommitment_eq_self_iff a b π π b a).1 hroot).1.symm
    · exact ReflGen.single h.of_restrictCommitment⟩

/-- `C[question_{a,b}(π)]` (Definition 19): the root is kept; the continuations are the members
of `C` in which `b` has answered `π` or `¬π`. -/
def question : Space (State W A) :=
  C.propose ({c ∈ C.states | C.root.restrictCommitment b a π ⊑ c} ∪
      {c ∈ C.states | C.root.restrictCommitment b a πᶜ ⊑ c}) <| by
    rintro c (⟨hc, -⟩ | ⟨hc, -⟩) <;> exact C.root_le hc

/-- `C[∼α]` (Definition 22) for `D = C[α]`: `D`'s states are removed, the root is kept. -/
def denegate (D : Space (State W A)) : Space (State W A) :=
  C.propose (C.states \ D.states) fun _ hc => C.root_le hc.1


/-- `V_{a,b}` (Definition 16): `a`'s commitment relation towards `b` is empty — `a` is committed
to a contradiction. -/
def Violation (c : State W A) (a b : A) : Prop :=
  ∀ w v, ¬ c.commitment a b w v

/-- The language of actions (Definition 20): assertion, polar question, the empty act `⊖`,
denegation `∼α`, composition `α;β`, and the conditional `π ↪ α/β`. -/
inductive SpeechAct (W A : Type*)
  | assert (a b : A) (π : Set W)
  | question (a b : A) (π : Set W)
  | empty
  | denegate (α : SpeechAct W A)
  | seq (α β : SpeechAct W A)
  | cond (π : Set W) (α β : SpeechAct W A)

variable (C : Space (State W A)) (a b : A) (π τ : Set W) (w : W) (α : SpeechAct W A)

open scoped Classical in
/-- `C[α]` (Definitions 10, 19, 21–24). The conditional tests its antecedent at the root, where a
world-set holds iff it is `Set.univ`. -/
noncomputable def update : SpeechAct W A → Space (State W A) → Space (State W A)
  | .assert a b π, C => assert C a b π
  | .question a b π, C => question C a b π
  | .empty, C => C
  | .denegate α, C => denegate C (update α C)
  | .seq α β, C => update β (update α C)
  | .cond π α β, C => if π = Set.univ then update α C else update β C

@[simp] theorem update_assert : update (.assert a b π) C = assert C a b π := rfl
@[simp] theorem update_question : update (.question a b π) C = question C a b π := rfl
@[simp] theorem update_empty : update .empty C = C := rfl
@[simp] theorem update_denegate : update (.denegate α) C = denegate C (update α C) := rfl
@[simp] theorem update_seq (β : SpeechAct W A) :
    update (.seq α β) C = update β (update α C) := rfl
@[simp] theorem root_assert : (assert C a b π).root = C.root.restrictCommitment a b π := rfl
@[simp] theorem root_question : (question C a b π).root = C.root := rfl
@[simp] theorem root_denegate (D : Space (State W A)) : (denegate C D).root = C.root := rfl

/-- Lemma 28: no speech act enlarges a commitment relation of the root. -/
theorem root_update_commitment_le :
    (update α C).root.commitment a b ≤ C.root.commitment a b := by
  induction α generalizing C with
  | assert x y π => exact C.root.restrictCommitment_commitment_le x y π a b
  | question => exact le_rfl
  | empty => exact le_rfl
  | denegate => exact le_rfl
  | seq α β ihα ihβ => exact (ihβ _).trans (ihα C)
  | cond π α β ihα ihβ =>
    simp only [update]
    split_ifs
    exacts [ihα C, ihβ C]

/-- Persistence (Theorem 30): a commitment at the root survives every speech act. -/
theorem committed_update (h : C.root.Committed a b π w) : (update α C).root.Committed a b π w :=
  box_restrict _ (root_update_commitment_le C a b α) w h

/-- Theorem 25: after `assert_{a,b}(π)`, `a` is committed towards `b` to `π`. -/
theorem committed_assert : (update (.assert a b π) C).root.Committed a b π w :=
  C.root.committed_restrictCommitment a b π w

/-- Acknowledgment: after `assert_{a,b}(π)`, everyone believes that the commitment was made. -/
theorem believes_committed_assert (x : A) :
    (update (.assert a b π) C).root.Believes x
      {v | (update (.assert a b π) C).root.Committed a b π v} w :=
  fun _ _ => C.root.committed_restrictCommitment a b π _

/-- Acceptance: after `assert_{a,b}(π)`, everyone is committed to the commitment having been
made. -/
theorem committed_committed_assert (x y : A) :
    (update (.assert a b π) C).root.Committed x y
      {v | (update (.assert a b π) C).root.Committed a b π v} w :=
  fun _ _ => C.root.committed_restrictCommitment a b π _

/-- Assertion entailment (Theorem 29): asserting `π` entails asserting any consequence `τ`. -/
theorem assert_assert_of_subset (h : π ⊆ τ) :
    update (.assert a b τ) (update (.assert a b π) C) = update (.assert a b π) C := by
  have hroot : (C.root.restrictCommitment a b π).restrictCommitment a b τ =
      C.root.restrictCommitment a b π := by
    rw [State.restrictCommitment_restrictCommitment, Set.inter_eq_left.2 h]
  refine Space.ext (Set.ext fun c => ?_) hroot
  simp only [update, assert, hroot, Set.mem_insert_iff, Set.mem_ofPred_eq]
  refine ⟨fun hc => hc.elim Or.inl And.left, fun hc => ?_⟩
  rcases hc with rfl | ⟨hc, hle⟩
  · exact Or.inl rfl
  refine Or.inr ⟨Or.inr ⟨hc, hle⟩, ?_⟩
  rcases (Relation.reflGen_iff _ _ _).1 hle with rfl | hlt
  · have hx : ((C.root.restrictCommitment a b π).restrictCommitment b a τ).restrictCommitment
        b a π = (C.root.restrictCommitment a b π).restrictCommitment b a π := by
      rw [State.restrictCommitment_restrictCommitment, Set.inter_eq_right.2 h]
    rw [← hx] at hc ⊢
    refine le_restrictCommitment_of_mem C hc fun e => ?_
    rw [hx] at e ⊢
    obtain ⟨h₁, h₂⟩ :=
      (C.root.restrictCommitment_restrictCommitment_eq_self_iff a b π π b a).1 e
    rw [h₁, h₂, (C.root.restrictCommitment_eq_self b a τ).2
      fun w v hv => h ((C.root.restrictCommitment_eq_self b a π).1 h₂ w v hv)]
  · exact ReflGen.single (hlt.of_le (fun _ => le_rfl)
      ((C.root.restrictCommitment a b π).restrictCommitment_mono b a π τ h))

/-! ### Possibility, admissibility, cooperativity -/

/-- `α` is admissible in `C` (Definition 17): performing it violates no commitment. Every speech
act is *possible* (Theorem 32): `update` is total. -/
def Admissible : Prop :=
  ∀ x y, ¬ Violation (update α C).root x y

/-- `α` is cooperative in `C` (Definition 15): it is not redundant, and its result lies below a
cooperative continuation of the root. -/
def Cooperative : Prop :=
  update α C ≠ C ∧ ∃ c ∈ C.states, C.root ⊏ c ∧ (update α C).root ⊑ c

/-- Inadmissibility of contradictions (Theorem 33). -/
theorem violation_assert_empty : Violation (update (.assert a b ∅) C).root a b :=
  fun _ _ h => h.2 ⟨rfl, rfl⟩

/-- Theorem 34(1): cooperative speech acts are admissible. -/
theorem admissible_of_cooperative (h : Cooperative C α) : Admissible C α := by
  obtain ⟨-, c, -, hlt, hle⟩ := h
  intro x y hV
  obtain ⟨w, v, hwv⟩ := hlt.commitment_nonempty x y
  exact hV w v (commitment_le_of_le hle x y w v hwv)

/-- Theorem 34(3): admissible speech acts need not be cooperative — nothing is cooperative in a
space without continuations. -/
theorem exists_admissible_not_cooperative :
    ∃ (C : Space (State Bool Unit)) (α : SpeechAct Bool Unit),
      Admissible C α ∧ ¬ Cooperative C α :=
  ⟨Space.singleton default, .assert () () {true}, fun _ _ h => h false true ⟨trivial, fun _ => rfl⟩,
    fun ⟨_, _, hc, hlt, _⟩ => hlt.ne hc.symm⟩

/-- Theorem 31(2): after `assert_{a,b}(π)`, `b` denying `π` is not cooperative. -/
theorem not_cooperative_assert_compl :
    ¬ Cooperative (update (.assert a b π) C) (.assert b a πᶜ) := by
  rintro ⟨-, c, hc, hlt, hle⟩
  rcases hc with rfl | ⟨-, hc⟩
  · exact hlt.ne rfl
  obtain ⟨w, v, hwv⟩ := hlt.commitment_nonempty b a
  exact (commitment_le_of_le hle b a w v hwv).2 ⟨rfl, rfl⟩
    ((commitment_le_of_le hc b a w v hwv).2 ⟨rfl, rfl⟩)

/-- Theorem 31(1): after `assert_{a,b}(π)`, `b` confirming `π` is cooperative, provided the
confirmed state is projected in `C` and `b` was not yet committed to `π`. The thesis omits
`a ≠ b`; for `a = b` the confirmation is redundant. -/
theorem cooperative_assert_of_not_committed [Nonempty W] (hab : a ≠ b)
    (hmem : (C.root.restrictCommitment a b π).restrictCommitment b a π ∈ C.states)
    (h : ∀ w, ¬ C.root.Committed b a π w) :
    Cooperative (update (.assert a b π) C) (.assert b a π) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  have h' := h w
  simp only [State.Committed, ModalLogic.box, not_forall] at h'
  obtain ⟨v, hwv, hvπ⟩ := h'
  have h₁ : (C.root.restrictCommitment a b π).commitment b a w v :=
    (C.root.restrictCommitment_other a b π w (fun e => hab e.1.symm) v).2 hwv
  have h₂ : ¬ ((C.root.restrictCommitment a b π).restrictCommitment b a π).commitment b a w v :=
    fun e => hvπ (e.2 ⟨rfl, rfl⟩)
  refine ⟨fun e => h₂ ((congrArg (fun D => D.root.commitment b a w v) e).mpr h₁),
    _, Set.mem_insert_of_mem _ ⟨hmem, ReflGen.refl⟩,
    ⟨fun _ => le_rfl, (C.root.restrictCommitment a b π).restrictCommitment_commitment_le b a π,
      ?_, b, a, w, v, h₁, h₂⟩, ReflGen.refl⟩
  rcases (Relation.reflGen_iff _ _ _).1 (show C.root ⊑ _ from C.root_le hmem) with e | hlt
  · exact absurd ((congrArg (fun s => s.commitment b a w v) e).mpr hwv) h₂
  · exact hlt.commitment_nonempty

/-- Answerhood (Theorem 35): `b` asserting `π` entails `a` having asked whether `π`. -/
theorem question_assert :
    update (.question a b π) (update (.assert b a π) C) = update (.assert b a π) C := by
  refine Space.ext (Set.ext fun c => ?_) rfl
  simp only [update, question, root_assert, State.restrictCommitment_restrictCommitment,
    Set.inter_self]
  refine ⟨fun hc => ?_, fun hc => Or.inr (Or.inl ⟨hc, (assert C b a π).root_le hc⟩)⟩
  rcases hc with rfl | ⟨hc, -⟩ | ⟨hc, -⟩
  · exact (assert C b a π).root_mem
  all_goals exact hc


end VanDerLeer2026
