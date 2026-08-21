import Linglib.Semantics.Dynamic.Partial
import Linglib.Semantics.Presupposition.Trivalent

/-!
# Beaver (2001): Presupposition and Assertion in Dynamic Semantics

[beaver-2001] reviews the theories of presupposition (Part I) and develops a dynamic one
(Part II): **partial update logic**, [veltman-1996]'s update logic — atomic updates
eliminate worlds, *not* removes the worlds the negated sentence keeps, *and* sequences, and
*might*/*must* test the state — with a presupposition operator `∂` whose update is defined
only in contexts that already satisfy its argument (Ch. 6), then extended to the first-order
fragment ABLE (Ch. 7). This file formalizes the propositional core over the substrate's
partial context change potentials: a sentence denotes a partial function on information
states (`Formula.eval : CCP.Partial W`), a state *satisfies* a sentence when it is a fixed
point (D29, `Satisfies`), *admits* it when the update is defined (D30, `CCP.Partial.admits`),
one sentence *presupposes* another when every admitting state satisfies it (D31, D46,
`Presupposes`), and *entails* it when every update with it lands in a satisfying state (D26,
D45, `Entails`). Discourse markers, determiners and accommodation (Chs. 7–9) are outside
the propositional fragment.

Two results from Part I are stated on the static side: under the Strong Kleene connectives
presuppositions are *conditionalised* rather than projected or filtered — *φ ∧ ψ*
presupposes *ψ → π* and *φ ∨ ψ* presupposes *¬ψ → π* when *φ* presupposes *π*, maximally so
when *ψ* is bivalent (Fact 2.1: `andStrong_presup_iff`, `orStrong_presup_iff`). On the
dynamic side: *must* is the dual of *might* (Fact 6.1, `eval_must`); every update is
eliminative (Fact 7.1, `eval_eliminative`); presuppositions project through negation,
conjunction, the conditional and the modals, and compose (Facts 8.1, 8.2, 8.8:
`Presupposes.not`, `.and_left`, `.implies_left`, `.might`, `.must`, `.trans`); a presupposition
of the second conjunct or the consequent projects *conditionalised* on the first conjunct or
the antecedent (Fact 8.3: `Presupposes.and_right`, `.implies_right`) — so *if Spaceman Spiff
lands on Planet X, he will be bothered by the fact that his weight is greater than it would be
on Earth* (E154) presupposes that if he lands there his weight is greater, and not that it is
(`e154`, `e154_not_unconditional`); *might* is a consistency test and *must* a satisfaction
test (D61, Fact 8.5, Lemma 8.6, Fact 8.7). Finally, on the sentences without modals Peters'
trivalent semantics (D70–D71, `tval`: the middle Kleene connectives, `∂φ` undefined unless
`φ` is true) and the update semantics agree world by world (Lemma 10.1, `trueAt_iff`,
`falseAt_iff`), the non-modal updates are distributive (Fact A.2, `mem_eval_iff`), and the
two entailment notions coincide (Lemma 10.2, Fact 10.3: `entails_iff`, `entails_iff_tval`),
whence a non-modal sentence presupposes exactly what both it and its negation entail
(`presupposes_iff`).
-/

namespace Beaver2001

open Semantics.Presupposition DynamicSemantics Classical

variable {W : Type*}

/-! ### Strong Kleene conditionalises presuppositions (Fact 2.1) -/

/-- Under Strong Kleene conjunction, if `φ` presupposes `π` then `φ ∧ ψ` presupposes
`ψ → π`, and when `ψ` is bivalent this is its presupposition. -/
theorem andStrong_presup_iff (p q : PartialProp W) {w : W} (hq : q.presup w) :
    (PartialProp.andStrong p q).presup w ↔ (q.assertion w → p.presup w) := by
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨_, hnq⟩) ha
    exacts [hp, hp, absurd ha hnq]
  · intro h
    by_cases ha : q.assertion w
    · exact Or.inl ⟨h ha, hq⟩
    · exact Or.inr (Or.inr ⟨hq, ha⟩)

/-- Under Strong Kleene disjunction, if `φ` presupposes `π` then `φ ∨ ψ` presupposes
`¬ψ → π`, and when `ψ` is bivalent this is its presupposition. -/
theorem orStrong_presup_iff (p q : PartialProp W) {w : W} (hq : q.presup w) :
    (PartialProp.orStrong p q).presup w ↔ (¬q.assertion w → p.presup w) := by
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨_, ha⟩) hna
    exacts [hp, hp, absurd ha hna]
  · intro h
    by_cases ha : q.assertion w
    · exact Or.inr (Or.inr ⟨hq, ha⟩)
    · exact Or.inl ⟨h ha, hq⟩

/-! ### Partial update logic (Ch. 6) -/

/-- The sentences of partial update logic (D22, D34), with atoms interpreted directly as
sets of worlds. -/
inductive Formula (W : Type*) where
  | atom (p : Set W)
  | not (φ : Formula W)
  | and (φ ψ : Formula W)
  | might (φ : Formula W)
  | must (φ : Formula W)
  | presup (φ : Formula W)

namespace Formula

/-- `φ implies ψ` is `not (φ and not ψ)` (D25). -/
def implies (φ ψ : Formula W) : Formula W := not (and φ (not ψ))

/-- `φ or ψ` is `not (not φ and not ψ)` (D52). -/
def or (φ ψ : Formula W) : Formula W := not (and (not φ) (not ψ))

/-- The update a sentence denotes (D25, D35): a partial function on information states,
defined for `∂φ` only at states that are fixed points of `φ`. -/
noncomputable def eval : Formula W → CCP.Partial W
  | atom p => fun σ => Part.some {w ∈ σ | w ∈ p}
  | not φ => CCP.Partial.neg φ.eval
  | and φ ψ => CCP.Partial.seq φ.eval ψ.eval
  | might φ => fun σ => (φ.eval σ).map fun υ => if υ.Nonempty then σ else ∅
  | must φ => fun σ => (φ.eval σ).map fun υ => if υ = σ then σ else ∅
  | presup φ => fun σ => ⟨σ ∈ φ.eval σ, fun _ => σ⟩

variable {φ ψ χ : Formula W} {σ τ : Set W} {w : W}

theorem mem_eval_atom {p : Set W} : τ ∈ (atom p).eval σ ↔ τ = {w ∈ σ | w ∈ p} :=
  Part.mem_some_iff

theorem mem_eval_not : τ ∈ (not φ).eval σ ↔ ∃ υ ∈ φ.eval σ, σ \ υ = τ :=
  Part.mem_map_iff _

theorem mem_eval_and : τ ∈ (and φ ψ).eval σ ↔ ∃ υ ∈ φ.eval σ, τ ∈ ψ.eval υ :=
  Part.mem_bind_iff

theorem mem_eval_might :
    τ ∈ (might φ).eval σ ↔ ∃ υ ∈ φ.eval σ, (if υ.Nonempty then σ else ∅) = τ :=
  Part.mem_map_iff _

theorem mem_eval_must : τ ∈ (must φ).eval σ ↔ ∃ υ ∈ φ.eval σ, (if υ = σ then σ else ∅) = τ :=
  Part.mem_map_iff _

theorem mem_eval_presup : τ ∈ (presup φ).eval σ ↔ σ ∈ φ.eval σ ∧ τ = σ :=
  Part.mem_mk_iff.trans ⟨fun ⟨h, e⟩ => ⟨h, e.symm⟩, fun ⟨h, e⟩ => ⟨h, e.symm⟩⟩

/-- Every update is eliminative (Fact 7.1, Fact A.1): outputs are subsets of the input. -/
theorem eval_eliminative : ∀ (φ : Formula W) {σ τ : Set W}, τ ∈ φ.eval σ → τ ⊆ σ
  | atom _, _, _, h => mem_eval_atom.1 h ▸ Set.sep_subset _ _
  | not _, _, _, h => CCP.Partial.neg_eliminative _ h
  | and φ ψ, _, _, h =>
    CCP.Partial.seq_eliminative (fun _ _ => eval_eliminative φ) (fun _ _ => eval_eliminative ψ) h
  | might _, _, _, h => by obtain ⟨_, -, rfl⟩ := mem_eval_might.1 h; split_ifs <;> simp
  | must _, _, _, h => by obtain ⟨_, -, rfl⟩ := mem_eval_must.1 h; split_ifs <;> simp
  | presup _, _, _, h => (mem_eval_presup.1 h).2 ▸ le_rfl

/-- The absurd state admits every sentence and is its own update. -/
theorem empty_mem_eval_empty : ∀ φ : Formula W, ∅ ∈ φ.eval ∅
  | atom _ => mem_eval_atom.2 (by ext; simp)
  | not φ => mem_eval_not.2 ⟨∅, empty_mem_eval_empty φ, Set.empty_sdiff _⟩
  | and φ ψ => mem_eval_and.2 ⟨∅, empty_mem_eval_empty φ, empty_mem_eval_empty ψ⟩
  | might φ => mem_eval_might.2 ⟨∅, empty_mem_eval_empty φ, by simp⟩
  | must φ => mem_eval_must.2 ⟨∅, empty_mem_eval_empty φ, by simp⟩
  | presup φ => mem_eval_presup.2 ⟨empty_mem_eval_empty φ, rfl⟩

/-- `σ` satisfies `φ` (D29): `σ[φ]σ`. -/
def Satisfies (σ : Set W) (φ : Formula W) : Prop := σ ∈ φ.eval σ

/-- `φ` presupposes `ψ` (D31, D46): every state admitting `φ` satisfies `ψ`. -/
def Presupposes (φ ψ : Formula W) : Prop := ∀ σ, φ.eval.admits σ → Satisfies σ ψ

/-- `φ` entails `ψ` (D26, D45): every update with `φ` yields a state satisfying `ψ`. -/
def Entails (φ ψ : Formula W) : Prop := ∀ σ τ, τ ∈ φ.eval σ → Satisfies τ ψ

/-- `σ` is consistent with `φ` (MP7): updating does not reach the absurd state. -/
def ConsistentWith (σ : Set W) (φ : Formula W) : Prop := ∃ τ ∈ φ.eval σ, τ.Nonempty

/-- A test (D61): its only outputs are the input and the absurd state. -/
def IsTest (φ : Formula W) : Prop := ∀ σ τ, τ ∈ φ.eval σ → τ = σ ∨ τ = ∅

theorem admits_of_mem (h : τ ∈ φ.eval σ) : φ.eval.admits σ := Part.dom_iff_mem.2 ⟨τ, h⟩

theorem Satisfies.admits (h : Satisfies σ φ) : φ.eval.admits σ := admits_of_mem h

/-- *must* is the dual of *might* (Fact 6.1). -/
theorem eval_must (φ : Formula W) : (must φ).eval = (not (might (not φ))).eval := by
  funext σ
  refine Part.ext fun τ => ?_
  rw [mem_eval_must, mem_eval_not]
  constructor
  · rintro ⟨υ, hυ, rfl⟩
    refine ⟨_, mem_eval_might.2 ⟨σ \ υ, mem_eval_not.2 ⟨υ, hυ, rfl⟩, rfl⟩, ?_⟩
    by_cases h : υ = σ
    · subst h; simp
    · rw [if_neg h, if_pos (Set.sdiff_nonempty.2 fun hσ => h ((eval_eliminative φ hυ).antisymm hσ)),
        Set.sdiff_self]
  · rintro ⟨_, hτ', rfl⟩
    obtain ⟨_, hυ', rfl⟩ := mem_eval_might.1 hτ'
    obtain ⟨υ, hυ, rfl⟩ := mem_eval_not.1 hυ'
    refine ⟨υ, hυ, ?_⟩
    by_cases h : υ = σ
    · subst h; simp
    · rw [if_neg h, if_pos (Set.sdiff_nonempty.2 fun hσ => h ((eval_eliminative φ hυ).antisymm hσ)),
        Set.sdiff_self]

/-! ### Projection (Facts 8.1–8.3, 8.8) -/

theorem Presupposes.not (h : Presupposes φ ψ) : Presupposes (not φ) ψ := fun σ hσ => h σ hσ

theorem Presupposes.and_left (h : Presupposes φ ψ) : Presupposes (and φ χ) ψ :=
  fun σ ⟨hσ, _⟩ => h σ hσ

theorem Presupposes.implies_left (h : Presupposes φ ψ) : Presupposes (implies φ χ) ψ :=
  fun σ ⟨hσ, _⟩ => h σ hσ

theorem Presupposes.might (h : Presupposes φ ψ) : Presupposes (might φ) ψ := fun σ hσ => h σ hσ

theorem Presupposes.must (h : Presupposes φ ψ) : Presupposes (must φ) ψ := fun σ hσ => h σ hσ

/-- Presupposition composes (Fact 8.2). -/
theorem Presupposes.trans (h₁ : Presupposes φ ψ) (h₂ : Presupposes ψ χ) : Presupposes φ χ :=
  fun σ hσ => h₂ σ (h₁ σ hσ).admits

/-- `∂ψ and χ` presupposes `ψ`. -/
theorem presup_and_presupposes (ψ χ : Formula W) : Presupposes (and (presup ψ) χ) ψ :=
  fun _ ⟨hσ, _⟩ => hσ

/-- A presupposition of the second conjunct projects conditionalised on the first
(Fact 8.3). -/
theorem Presupposes.and_right (h : Presupposes φ ψ) : Presupposes (and χ φ) (implies χ ψ) := by
  rintro σ ⟨hχ, hφ⟩
  refine mem_eval_not.2
    ⟨_, mem_eval_and.2 ⟨_, Part.get_mem hχ, mem_eval_not.2 ⟨_, h _ hφ, rfl⟩⟩, ?_⟩
  simp

/-- A presupposition of the consequent projects conditionalised on the antecedent
(Fact 8.3). -/
theorem Presupposes.implies_right (h : Presupposes φ ψ) :
    Presupposes (implies χ φ) (implies χ ψ) := by
  rintro σ ⟨hχ, hφ⟩
  refine mem_eval_not.2
    ⟨_, mem_eval_and.2 ⟨_, Part.get_mem hχ, mem_eval_not.2 ⟨_, h _ hφ, rfl⟩⟩, ?_⟩
  simp

/-- E154: the conditional presupposes that if Spiff lands on Planet X his weight is greater
than on Earth. -/
theorem e154 (lands weight bothered : Set W) :
    Presupposes (implies (atom lands) (and (presup (atom weight)) (atom bothered)))
      (implies (atom lands) (atom weight)) :=
  (presup_and_presupposes _ _).implies_right

/-- E154 does not presuppose that Spiff's weight is greater than on Earth: a state in which he
may be weightless in space admits it. -/
theorem e154_not_unconditional :
    ∃ lands weight bothered : Set Bool,
      ¬Presupposes (implies (atom lands) (and (presup (atom weight)) (atom bothered)))
        (atom weight) := by
  refine ⟨{true}, {true}, Set.univ, fun h => ?_⟩
  have hadm : (implies (atom {true}) (and (presup (atom {true})) (atom Set.univ))).eval.admits
      Set.univ :=
    Part.dom_iff_mem.2 ⟨_, mem_eval_not.2 ⟨_, mem_eval_and.2 ⟨_, mem_eval_atom.2 rfl,
      mem_eval_not.2 ⟨_, mem_eval_and.2 ⟨_, mem_eval_presup.2 ⟨mem_eval_atom.2 (by ext; simp), rfl⟩,
        mem_eval_atom.2 rfl⟩, rfl⟩⟩, rfl⟩⟩
  simpa using congrArg (false ∈ ·) (mem_eval_atom.1 (h _ hadm))

/-! ### Epistemic modality (D61, Facts 8.5–8.7) -/

theorem might_isTest (φ : Formula W) : IsTest (might φ) := fun _ _ h => by
  obtain ⟨_, -, rfl⟩ := mem_eval_might.1 h
  split_ifs <;> simp

theorem must_isTest (φ : Formula W) : IsTest (must φ) := fun _ _ h => by
  obtain ⟨_, -, rfl⟩ := mem_eval_must.1 h
  split_ifs <;> simp

/-- *might* is a consistency test (Fact 8.5): a non-absurd state is a fixed point of
`might φ` iff it is consistent with `φ`. -/
theorem satisfies_might_iff (hσ : σ.Nonempty) : Satisfies σ (might φ) ↔ ConsistentWith σ φ := by
  constructor
  · intro hs
    obtain ⟨υ, hυ, hif⟩ := mem_eval_might.1 hs
    refine ⟨υ, hυ, ?_⟩
    by_contra hne
    rw [if_neg hne] at hif
    exact hσ.ne_empty hif.symm
  · rintro ⟨υ, hυ, hne⟩
    exact mem_eval_might.2 ⟨υ, hυ, if_pos hne⟩

/-- A state admitting `φ` satisfies it iff it is inconsistent with `not φ` (Lemma 8.6). -/
theorem satisfies_iff_not_consistentWith_not (h : φ.eval.admits σ) :
    Satisfies σ φ ↔ ¬ConsistentWith σ (not φ) := by
  constructor
  · rintro hs ⟨_, hτ, hne⟩
    obtain ⟨υ, hυ, rfl⟩ := mem_eval_not.1 hτ
    rw [Part.mem_unique hυ hs, Set.sdiff_self] at hne
    exact Set.not_nonempty_empty hne
  · intro hc
    have hsub : σ ⊆ (φ.eval σ).get h := fun w hw => by_contra fun hw' =>
      hc ⟨_, mem_eval_not.2 ⟨_, Part.get_mem h, rfl⟩, w, hw, hw'⟩
    have hget := Part.get_mem h
    rw [(eval_eliminative φ hget).antisymm hsub] at hget
    exact hget

/-- *must* is a satisfaction test (Fact 8.7): a non-absurd state is a fixed point of `must φ`
iff it satisfies `φ`. -/
theorem satisfies_must_iff (hσ : σ.Nonempty) : Satisfies σ (must φ) ↔ Satisfies σ φ := by
  constructor
  · intro hs
    obtain ⟨υ, hυ, hif⟩ := mem_eval_must.1 hs
    by_cases h : υ = σ
    · exact h ▸ hυ
    · rw [if_neg h] at hif
      exact absurd hif.symm hσ.ne_empty
  · exact fun hs => mem_eval_must.2 ⟨σ, hs, if_pos rfl⟩

/-! ### The trivalent connection (Ch. 10) -/

/-- The non-modal sentences, PL+∂. -/
inductive NonModal : Formula W → Prop
  | atom (p : Set W) : NonModal (atom p)
  | not {φ : Formula W} : NonModal φ → NonModal (not φ)
  | and {φ ψ : Formula W} : NonModal φ → NonModal ψ → NonModal (and φ ψ)
  | presup {φ : Formula W} : NonModal φ → NonModal (presup φ)

/-- Peters' trivalent semantics (D70–D71): bivalent atoms, the middle Kleene connectives,
and `∂φ` true when `φ` is and undefined otherwise. Modal sentences are not covered. -/
noncomputable def tval : Formula W → W → Trivalent
  | atom p, w => if w ∈ p then .true else .false
  | not φ, w => (tval φ w).neg
  | and φ ψ, w => Trivalent.meetMiddle (tval φ w) (tval ψ w)
  | presup φ, w => if tval φ w = .true then .true else .indet
  | might _, _ => .indet
  | must _, _ => .indet

/-- Update truth in a world (D76): `{w}[φ]{w}`. -/
def TrueAt (w : W) (φ : Formula W) : Prop := {w} ∈ φ.eval {w}

/-- Update falsity in a world (D77): `{w}[φ]∅`. -/
def FalseAt (w : W) (φ : Formula W) : Prop := ∅ ∈ φ.eval {w}

theorem eq_singleton_or_eq_empty (h : τ ∈ φ.eval {w}) : τ = {w} ∨ τ = ∅ :=
  (Set.subset_singleton_iff_eq.1 (eval_eliminative φ h)).symm

theorem trueAt_atom {p : Set W} : TrueAt w (atom p) ↔ w ∈ p := by
  rw [TrueAt, mem_eval_atom, Set.sep_mem_eq, eq_comm, Set.inter_eq_left, Set.singleton_subset_iff]

theorem falseAt_atom {p : Set W} : FalseAt w (atom p) ↔ w ∉ p := by
  rw [FalseAt, mem_eval_atom, Set.sep_mem_eq, eq_comm, Set.singleton_inter_eq_empty]

theorem trueAt_not : TrueAt w (not φ) ↔ FalseAt w φ := by
  rw [TrueAt, FalseAt, mem_eval_not]
  constructor
  · rintro ⟨υ, hυ, h⟩
    rcases eq_singleton_or_eq_empty hυ with rfl | rfl
    · exact absurd h (by simp)
    · exact hυ
  · exact fun h => ⟨∅, h, Set.sdiff_empty⟩

theorem falseAt_not : FalseAt w (not φ) ↔ TrueAt w φ := by
  rw [TrueAt, FalseAt, mem_eval_not]
  constructor
  · rintro ⟨υ, hυ, h⟩
    rcases eq_singleton_or_eq_empty hυ with rfl | rfl
    · exact hυ
    · exact absurd h (by simp)
  · exact fun h => ⟨{w}, h, Set.sdiff_self⟩

theorem trueAt_and : TrueAt w (and φ ψ) ↔ TrueAt w φ ∧ TrueAt w ψ := by
  rw [TrueAt, mem_eval_and]
  constructor
  · rintro ⟨υ, hυ, h⟩
    rcases eq_singleton_or_eq_empty hυ with rfl | rfl
    · exact ⟨hυ, h⟩
    · exact absurd (eval_eliminative ψ h) (by simp)
  · exact fun ⟨h₁, h₂⟩ => ⟨{w}, h₁, h₂⟩

theorem falseAt_and : FalseAt w (and φ ψ) ↔ FalseAt w φ ∨ (TrueAt w φ ∧ FalseAt w ψ) := by
  rw [FalseAt, mem_eval_and]
  constructor
  · rintro ⟨υ, hυ, h⟩
    rcases eq_singleton_or_eq_empty hυ with rfl | rfl
    · exact Or.inr ⟨hυ, h⟩
    · exact Or.inl hυ
  · rintro (h | ⟨h₁, h₂⟩)
    · exact ⟨∅, h, empty_mem_eval_empty ψ⟩
    · exact ⟨{w}, h₁, h₂⟩

theorem trueAt_presup : TrueAt w (presup φ) ↔ TrueAt w φ :=
  mem_eval_presup.trans (and_iff_left rfl)

theorem not_falseAt_presup : ¬FalseAt w (presup φ) := fun h =>
  Set.singleton_ne_empty w (mem_eval_presup.1 h).2.symm

/-- A world admitting `φ` makes it true or false. -/
theorem trueAt_or_falseAt (h : φ.eval.admits {w}) : TrueAt w φ ∨ FalseAt w φ := by
  have hget := Part.get_mem h
  rcases eq_singleton_or_eq_empty hget with e | e <;> rw [e] at hget
  · exact Or.inl hget
  · exact Or.inr hget

theorem admits_presup_singleton : (presup φ).eval.admits {w} ↔ TrueAt w φ := Iff.rfl

theorem not_trueAt_of_falseAt (h : FalseAt w φ) : ¬TrueAt w φ := fun h' =>
  Set.singleton_ne_empty w (Part.mem_unique h' h)

/-- Trivalent and update truth and falsity coincide world by world (Lemma 10.1). -/
theorem trueAt_falseAt_iff (hφ : NonModal φ) (w : W) :
    (TrueAt w φ ↔ tval φ w = .true) ∧ (FalseAt w φ ↔ tval φ w = .false) := by
  induction hφ with
  | atom p => rw [trueAt_atom, falseAt_atom, tval]; split_ifs with h <;> simp [h]
  | not _ ih =>
    rw [trueAt_not, falseAt_not, tval, ih.2, ih.1]
    cases tval _ w <;> decide
  | and _ _ ihφ ihψ =>
    rw [trueAt_and, falseAt_and, tval, ihφ.1, ihφ.2, ihψ.1, ihψ.2]
    cases tval _ w <;> cases tval _ w <;> decide
  | presup _ ih =>
    rw [trueAt_presup, tval, ih.1]
    refine ⟨by split_ifs with h <;> simp [h], ⟨fun h => (not_falseAt_presup h).elim, ?_⟩⟩
    split_ifs <;> simp

theorem trueAt_iff (hφ : NonModal φ) : TrueAt w φ ↔ tval φ w = .true :=
  (trueAt_falseAt_iff hφ w).1

theorem falseAt_iff (hφ : NonModal φ) : FalseAt w φ ↔ tval φ w = .false :=
  (trueAt_falseAt_iff hφ w).2

/-- Admittance of a conjunction at a world. -/
theorem admits_and_singleton :
    (and φ ψ).eval.admits {w} ↔ φ.eval.admits {w} ∧ (TrueAt w φ → ψ.eval.admits {w}) := by
  constructor
  · rintro ⟨hφ, hψ⟩
    refine ⟨hφ, fun ht => ?_⟩
    have hψ' : (ψ.eval ((φ.eval {w}).get hφ)).Dom := hψ
    rwa [Part.get_eq_of_mem ht] at hψ'
  · rintro ⟨hφ, hψ⟩
    refine ⟨hφ, ?_⟩
    show (ψ.eval ((φ.eval {w}).get hφ)).Dom
    have hget := Part.get_mem hφ
    rcases eq_singleton_or_eq_empty hget with h | h <;> rw [h] at hget ⊢
    · exact hψ hget
    · exact admits_of_mem (empty_mem_eval_empty ψ)

/-- Non-modal updates are distributive (Fact A.2): an update is defined iff it is defined at
every world of the state, and keeps exactly the worlds at which the sentence is true. -/
theorem mem_eval_iff (hφ : NonModal φ) (σ τ : Set W) :
    τ ∈ φ.eval σ ↔ (∀ w ∈ σ, φ.eval.admits {w}) ∧ τ = {w ∈ σ | TrueAt w φ} := by
  induction hφ generalizing σ τ with
  | atom p => simp [trueAt_atom, CCP.Partial.admits, eval]
  | @not φ' hφ ih =>
    rw [mem_eval_not]
    constructor
    · rintro ⟨υ, hυ, rfl⟩
      obtain ⟨hadm, rfl⟩ := (ih _ _).1 hυ
      refine ⟨hadm, Set.ext fun w => ?_⟩
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_and, trueAt_not]
      exact ⟨fun ⟨hw, h⟩ => ⟨hw, (trueAt_or_falseAt (hadm w hw)).resolve_left (h hw)⟩,
        fun ⟨hw, h⟩ => ⟨hw, fun _ => not_trueAt_of_falseAt h⟩⟩
    · rintro ⟨hadm, rfl⟩
      refine ⟨_, (ih _ _).2 ⟨hadm, rfl⟩, Set.ext fun w => ?_⟩
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_and, trueAt_not]
      exact ⟨fun ⟨hw, h⟩ =>
          ⟨hw, (trueAt_or_falseAt (show φ'.eval.admits {w} from hadm w hw)).resolve_left (h hw)⟩,
        fun ⟨hw, h⟩ => ⟨hw, fun _ => not_trueAt_of_falseAt h⟩⟩
  | @and φ' ψ' hφ hψ ihφ ihψ =>
    rw [mem_eval_and]
    constructor
    · rintro ⟨υ, hυ, hτ⟩
      obtain ⟨hadmφ, rfl⟩ := (ihφ _ _).1 hυ
      obtain ⟨hadmψ, rfl⟩ := (ihψ _ _).1 hτ
      refine ⟨fun w hw => admits_and_singleton.2 ⟨hadmφ w hw, fun ht => hadmψ w ⟨hw, ht⟩⟩,
        Set.ext fun w => ?_⟩
      simp [trueAt_and, and_assoc]
    · rintro ⟨hadm, rfl⟩
      refine ⟨_, (ihφ _ _).2 ⟨fun w hw => (admits_and_singleton.1 (hadm w hw)).1, rfl⟩,
        (ihψ _ _).2 ⟨fun w hw => (admits_and_singleton.1 (hadm w hw.1)).2 hw.2,
          Set.ext fun w => ?_⟩⟩
      simp [trueAt_and, and_assoc]
  | @presup φ' hφ ih =>
    rw [mem_eval_presup]
    constructor
    · rintro ⟨hs, rfl⟩
      obtain ⟨hadm, hσ⟩ := (ih _ _).1 hs
      have ht : ∀ w ∈ τ, TrueAt w φ' := fun w hw => ((Set.ext_iff.1 hσ w).1 hw).2
      exact ⟨fun w hw => admits_presup_singleton.2 (ht w hw),
        (Set.sep_eq_self_iff_mem_true.2 fun w hw => trueAt_presup.2 (ht w hw)).symm⟩
    · rintro ⟨hadm, rfl⟩
      have ht : ∀ w ∈ σ, TrueAt w φ' := fun w hw => admits_presup_singleton.1 (hadm w hw)
      have hσ : {w ∈ σ | TrueAt w (presup φ')} = σ :=
        Set.sep_eq_self_iff_mem_true.2 fun w hw => trueAt_presup.2 (ht w hw)
      rw [hσ]
      exact ⟨(ih _ _).2 ⟨fun w hw => admits_of_mem (ht w hw),
        (Set.sep_eq_self_iff_mem_true.2 ht).symm⟩, rfl⟩

/-- A non-modal sentence is satisfied iff it is true at every world of the state. -/
theorem satisfies_iff (hφ : NonModal φ) : Satisfies σ φ ↔ ∀ w ∈ σ, TrueAt w φ := by
  rw [Satisfies, mem_eval_iff hφ]
  constructor
  · rintro ⟨_, hσ⟩ w hw
    exact ((Set.ext_iff.1 hσ w).1 hw).2
  · exact fun h => ⟨fun w hw => admits_of_mem (h w hw), (Set.sep_eq_self_iff_mem_true.2 h).symm⟩

/-- A non-modal sentence is admitted iff it is admitted at every world of the state. -/
theorem admits_iff (hφ : NonModal φ) : φ.eval.admits σ ↔ ∀ w ∈ σ, φ.eval.admits {w} :=
  ⟨fun h => ((mem_eval_iff hφ _ _).1 (Part.get_mem h)).1,
   fun h => Part.dom_iff_mem.2 ⟨_, (mem_eval_iff hφ _ _).2 ⟨h, rfl⟩⟩⟩

/-- For non-modal sentences, entailment is entailment at every world (Lemma 10.2). -/
theorem entails_iff (hφ : NonModal φ) (hψ : NonModal ψ) :
    Entails φ ψ ↔ ∀ w, TrueAt w φ → TrueAt w ψ :=
  ⟨fun h w hw => h {w} {w} hw, fun h σ τ hτ => (satisfies_iff hψ).2 fun w hw =>
    h w ((Set.ext_iff.1 ((mem_eval_iff hφ σ τ).1 hτ).2 w).1 hw).2⟩

/-- For non-modal sentences, entailment is preservation of fixed points (D73). -/
theorem entails_iff_satisfies (hφ : NonModal φ) (hψ : NonModal ψ) :
    Entails φ ψ ↔ ∀ σ, Satisfies σ φ → Satisfies σ ψ :=
  ⟨fun h σ hs => h σ σ hs, fun h => (entails_iff hφ hψ).2 fun w hw => h {w} hw⟩

/-- The update and trivalent entailment notions coincide on PL+∂ (Fact 10.3). -/
theorem entails_iff_tval (hφ : NonModal φ) (hψ : NonModal ψ) :
    Entails φ ψ ↔ ∀ w, tval φ w = .true → tval ψ w = .true := by
  rw [entails_iff hφ hψ]
  exact forall_congr' fun w => imp_congr (trueAt_iff hφ) (trueAt_iff hψ)

/-- A non-modal sentence presupposes exactly what both it and its negation entail, Peters'
characterisation of trivalent presupposition. -/
theorem presupposes_iff (hφ : NonModal φ) (hψ : NonModal ψ) :
    Presupposes φ ψ ↔ Entails φ ψ ∧ Entails (not φ) ψ := by
  constructor
  · refine fun h => ⟨fun σ τ hτ => ?_, fun σ τ hτ => ?_⟩
    · have hs := (satisfies_iff hψ).1 (h σ (admits_of_mem hτ))
      exact (satisfies_iff hψ).2 fun w hw => hs w (eval_eliminative φ hτ hw)
    · have ha : (not φ).eval.admits σ := admits_of_mem hτ
      have hs := (satisfies_iff hψ).1 (h σ ha)
      exact (satisfies_iff hψ).2 fun w hw => hs w (eval_eliminative (not φ) hτ hw)
  · rintro ⟨h₁, h₂⟩ σ hσ
    refine (satisfies_iff hψ).2 fun w hw => ?_
    rcases trueAt_or_falseAt ((admits_iff hφ).1 hσ w hw) with ht | hf
    · exact h₁ {w} {w} ht
    · exact h₂ {w} {w} (trueAt_not.2 hf)

end Formula

end Beaver2001
