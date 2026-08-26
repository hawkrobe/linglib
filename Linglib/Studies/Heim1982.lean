import Mathlib.Data.Fin.VecNotation
import Linglib.Semantics.Dynamic.FileChange
import Linglib.Data.Examples.Heim1982

/-!
# Heim (1982): The Semantics of Definite and Indefinite Noun Phrases

[heim-1982] analyses indefinites and definites alike as variables and
locates their difference in a felicity condition on files: an indefinite's
card must be new to the file, a definite's already present and, if it has
descriptive content, entailed by it (the Extended Novelty-Familiarity-
Condition, Ch. III §2.3 and §5.1). The dissertation's final theory (Ch. III
§4.4) interprets logical forms directly by their *file change potentials* —
rules (I)–(IV): atoms filter the file and add their cards, cumulative
formulas update in sequence, the universal quantifier tests the file against
its two auxiliary updates, negation tests it against one — and defines the
truth of an utterance by the truth of the resulting file (criterion (C),
§3.2). Quantifier Indexing and Existential Closure are then dispensable:
operators bind whatever cards are novel, and existential force comes from
the truth of a file being the existence of a satisfying sequence.

This file states the logical forms and the four rules over the substrate's
file change potentials (`FCP`, with a file a `State` of world–assignment
points and felicity its `Part`-definedness), and proves the claims the book
draws from them on its own examples.

## Main definitions

* `LF`, `LF.fcp` — the logical forms of the revised theory and rules
  (I)–(IV); `LF.pro`, `LF.pred₁`, `LF.pred₂` for pronouns and predications.
* `everyDog`, `noDog`, `aDog`, `womanDog`, `pretzelText`, `kingLocal`,
  `kingGlobal` — the book's texts Ch. I (9), (16), (17), Ch. III (5) of §2.5,
  (2) of §4.1 and (10) of §5.2.

## Main statements

* `admits_indef`, `admits_defNP`, `admits_pro` — the Extended
  Novelty-Familiarity-Condition is definedness.
* `admits_womanDog`, `admits_pretzel` — felicity conditions project through
  the elementary steps of file change (§2.5, §4.1): a text needs its
  indefinites' cards novel in the initial file, and its pronouns' cards are
  supplied by intermediate files, inside the nuclear scope of `every` too.
* `admits_aDog`, `not_admits_everyDog`, `not_admits_noDog` — Ch. I (9) vs
  (16)/(17): an indefinite's card outlives its sentence, a card introduced
  inside `every` or `not` does not.
* `trueIn_indef`, `trueIn_pro_pred` — criterion (C) gives a free indefinite
  existential force and a definite the force of its card (§3.2).
* `le_of_mem_fcp`, `fcp_empty` — Principle (A): updates only add information,
  and a false file stays false.
* `every_eq_cond` — rule (III) is the negated conjunction `¬(φ₁ ∧ ¬φ₂)`.
* `novel_of_mem_kingLocal`, `familiar_of_mem_kingGlobal` — accommodation
  inside the auxiliary file of a negation yields the narrow-scope reading;
  accommodating the initial file implies the existence of the king (§5.2).
-/

namespace Heim1982

open DynamicSemantics

variable {W M : Type*} {n : ℕ}

/-- A file (Ch. III): a referential information state with numbered cards. -/
abbrev File (W M : Type*) := State W ℕ M

/-- Logical forms of the revised theory (Ch. III §4.4, §5.1): atomic formulas
over indexed variables, indefinite and definite noun phrases with their
descriptive content, cumulative (sequenced), universally quantified and
negated formulas. Predicates are interpreted directly. -/
inductive LF (M : Type*)
  | atom {n : ℕ} (ζ : (Fin n → M) → Prop) (args : Fin n → ℕ)
  | indef (i : ℕ) (N : M → Prop)
  | defNP (i : ℕ) (N : M → Prop)
  | seq (φ ψ : LF M)
  | every (φ₁ φ₂ : LF M)
  | neg (ψ : LF M)

namespace LF

/-- A pronoun or trace: a definite without descriptive content. -/
def pro (i : ℕ) : LF M := defNP i fun _ => True

/-- A one-place predication at card `i`. -/
def pred₁ (N : M → Prop) (i : ℕ) : LF M := atom (fun m => N (m 0)) fun _ : Fin 1 => i

/-- A two-place predication at cards `i`, `j`. -/
def pred₂ (R : M → M → Prop) (i j : ℕ) : LF M := atom (fun m => R (m 0) (m 1)) ![i, j]

/-- The proposition state of an atomic formula: the points with exactly the
atom's cards, whose values stand in `ζ`. -/
def atomState (ζ : (Fin n → M) → Prop) (args : Fin n → ℕ) : File W M :=
  {q | q.domain = Set.range args ∧ ∃ m : Fin n → M, (∀ k, m k ∈ q.assignment (args k)) ∧ ζ m}

/-- The file change of a one-place atom. -/
def unary (N : M → Prop) (i : ℕ) : FCP W ℕ M :=
  FCP.ofState (atomState (fun m => N (m 0)) fun _ : Fin 1 => i)

/-- Rules (I)–(IV) of Ch. III §4.4 with the Extended Novelty-Familiarity-
Condition of §5.1: an atom merges the file with its proposition state
(filtering at familiar cards, adding novel ones); an indefinite is defined
only if its card is novel and then introduces it; a definite is defined only
if its card is familiar and the file entails its content, and then changes
nothing; sequencing composes; `every` keeps the points of `F` all of whose
extensions in `F + φ₁` extend to `(F + φ₁) + φ₂`; `not` keeps the points of
`F` with no extension in `F + ψ`. -/
def fcp : LF M → FCP W ℕ M
  | atom ζ args => FCP.ofState (atomState ζ args)
  | indef i N => FCP.indef i (unary N i)
  | defNP i N => fun F =>
      Part.assert (State.Familiar F i ∧ FCP.supports F (unary N i)) fun _ => Part.some F
  | seq φ ψ => φ.fcp.seq ψ.fcp
  | every φ₁ φ₂ => fun F => (φ₁.fcp F).bind fun F₁ => (φ₂.fcp F₁).map fun F₂ =>
      {p ∈ F | ∀ q ∈ F₁, p ≤ q → ∃ r ∈ F₂, q ≤ r}
  | neg ψ => FCP.neg ψ.fcp

theorem unary_eq_atomVar (N : M → Prop) (i : ℕ) : (unary N i : FCP W ℕ M) = FCP.atomVar N i := by
  refine congrArg FCP.ofState (Set.ext fun q => ?_)
  constructor
  · rintro ⟨hd, m, hm, hN⟩
    exact ⟨hd.trans Set.range_const, m 0, hm 0, hN⟩
  · rintro ⟨hd, m, hm, hN⟩
    exact ⟨hd.trans Set.range_const.symm, fun _ => m, fun _ => hm, hN⟩

/-! ### The Extended Novelty-Familiarity-Condition -/

/-- An indefinite is defined exactly when its card is novel. -/
theorem admits_indef (i : ℕ) (N : M → Prop) (F : File W M) :
    (indef i N).fcp.admits F ↔ State.Novel F i := by
  simp [fcp, FCP.indef, CCP.Partial.admits, unary, FCP.ofState, State.Novel, Part.assert]

/-- A definite is defined exactly when its card is familiar and the file
entails its descriptive content. -/
theorem admits_defNP (i : ℕ) (N : M → Prop) (F : File W M) :
    (defNP i N).fcp.admits F ↔ State.Familiar F i ∧ FCP.supports F (unary N i) := by
  simp [fcp, CCP.Partial.admits, Part.assert]

theorem supports_unary_true (F : File W M) {i : ℕ} (h : State.Familiar F i) :
    FCP.supports F (unary (fun _ => True) i) := by
  rw [FCP.supports, unary_eq_atomVar, FCP.atomVar_eq_of_familiar _ _ h]
  exact congrArg Part.some (Set.sep_eq_self_iff_mem_true.mpr fun p hp =>
    let ⟨m, hm⟩ := Part.dom_iff_mem.mp (h p hp); ⟨m, hm, trivial⟩)

/-- A pronoun at a familiar card changes nothing. -/
theorem fcp_pro (F : File W M) {i : ℕ} (h : State.Familiar F i) : (pro i).fcp F = Part.some F :=
  Part.assert_pos ⟨h, supports_unary_true F h⟩

/-- A pronoun is defined exactly when its card is familiar. -/
theorem admits_pro (F : File W M) (i : ℕ) : (pro i).fcp.admits F ↔ State.Familiar F i :=
  ⟨fun ⟨h, _⟩ => h.1, fun h => by rw [CCP.Partial.admits, fcp_pro F h]; trivial⟩

/-- The file change of an indefinite at a novel card: random assignment then
filtering. -/
theorem fcp_indef {F : File W M} {i : ℕ} (N : M → Prop) (h : State.Novel F i) :
    (indef i N).fcp F = Part.some {p ∈ F.randomAssign i | ∃ m ∈ p.assignment i, N m} := by
  simp only [fcp, FCP.indef]
  rw [Part.assert_pos (show ∀ p ∈ F, ¬(p.assignment i).Dom from h), unary_eq_atomVar,
    FCP.atomVar_eq_of_familiar _ _ (State.familiar_randomAssign F i)]

theorem mem_fcp_indef {F F' : File W M} {i : ℕ} {N : M → Prop} :
    F' ∈ (indef i N).fcp F ↔
      State.Novel F i ∧ F' = {p ∈ F.randomAssign i | ∃ m ∈ p.assignment i, N m} :=
  ⟨fun h => have hn : State.Novel F i := (Part.mem_assert_iff.mp h).1
    ⟨hn, Part.mem_some_iff.mp (fcp_indef N hn ▸ h)⟩,
   fun ⟨hn, hF⟩ => hF ▸ fcp_indef N hn ▸ Part.mem_some _⟩

/-! ### Membership and projection through the rules -/

theorem mem_fcp_seq {φ ψ : LF M} {F F' : File W M} :
    F' ∈ (φ.seq ψ).fcp F ↔ ∃ F₁ ∈ φ.fcp F, F' ∈ ψ.fcp F₁ :=
  Part.mem_bind_iff

theorem mem_fcp_every {φ₁ φ₂ : LF M} {F F' : File W M} :
    F' ∈ (every φ₁ φ₂).fcp F ↔ ∃ F₁ ∈ φ₁.fcp F, ∃ F₂ ∈ φ₂.fcp F₁,
      F' = {p ∈ F | ∀ q ∈ F₁, p ≤ q → ∃ r ∈ F₂, q ≤ r} := by
  simp only [fcp, Part.mem_bind_iff, Part.mem_map_iff]
  exact exists_congr fun _ => and_congr_right fun _ => exists_congr fun _ =>
    and_congr_right fun _ => eq_comm

/-- The universal quantifier tests the file: its output is a subset. -/
theorem subset_of_mem_fcp_every {φ₁ φ₂ : LF M} {F F' : File W M}
    (h : F' ∈ (every φ₁ φ₂).fcp F) : F' ⊆ F := by
  obtain ⟨_, -, _, -, rfl⟩ := mem_fcp_every.mp h
  exact fun _ hp => hp.1

theorem admits_seq_of_mem {φ ψ : LF M} {F F' : File W M} (h : F' ∈ φ.fcp F)
    (h' : ψ.fcp.admits F') : (φ.seq ψ).fcp.admits F :=
  Part.dom_iff_mem.mpr ⟨_, mem_fcp_seq.mpr ⟨F', h, Part.get_mem h'⟩⟩

theorem admits_pro_seq {ψ : LF M} {F : File W M} {i : ℕ} (h : State.Familiar F i)
    (h' : ψ.fcp.admits F) : ((pro i).seq ψ).fcp.admits F :=
  admits_seq_of_mem (by rw [fcp_pro F h]; exact Part.mem_some F) h'

theorem admits_every_of_mem {φ₁ φ₂ : LF M} {F F₁ : File W M} (h : F₁ ∈ φ₁.fcp F)
    (h' : φ₂.fcp.admits F₁) : (every φ₁ φ₂).fcp.admits F :=
  Part.dom_iff_mem.mpr ⟨_, mem_fcp_every.mpr ⟨F₁, h, _, Part.get_mem h', rfl⟩⟩

/-- Rule (III) is the negated conjunction `¬(φ₁ ∧ ¬φ₂)`. -/
theorem every_eq_cond (φ₁ φ₂ : LF M) :
    (every φ₁ φ₂).fcp = FCP.cond (W := W) φ₁.fcp φ₂.fcp := by
  funext F
  simp only [fcp, FCP.cond, FCP.neg, CCP.Partial.seq, PFun.comp_apply, Part.map_bind,
    Part.map_map]
  refine congrArg (Part.bind _) (funext fun F₁ =>
    congrArg (fun g => Part.map g (φ₂.fcp F₁)) (funext fun F₂ => Set.ext fun p => ?_))
  simp only [Function.comp, Set.mem_ofPred_eq, mem_lowerClosure, not_exists, not_and]
  exact and_congr_right fun _ => forall_congr' fun q =>
    ⟨fun h ⟨hq, hno⟩ hpq => let ⟨r, hr, hqr⟩ := h hq hpq; hno r hr hqr,
     fun h hq hpq => Classical.byContradiction fun hne =>
      h ⟨hq, fun r hr hqr => hne ⟨r, hr, hqr⟩⟩ hpq⟩

/-- Felicity conditions of a quantified formula project as those of a
conditional: the restrictive term must be felicitous in the file, the nuclear
scope in the file updated with it. -/
theorem admits_every (φ₁ φ₂ : LF M) (F : File W M) :
    (every φ₁ φ₂).fcp.admits F ↔ ∃ h : φ₁.fcp.admits F, φ₂.fcp.admits ((φ₁.fcp F).get h) := by
  rw [every_eq_cond]; exact CCP.Partial.admits_cond _ _ _

/-! ### Cards through the rules -/

/-- A card not among an atom's is novel at its proposition state. -/
theorem novel_atomState {ζ : (Fin n → M) → Prop} {args : Fin n → ℕ} {j : ℕ}
    (hj : j ∉ Set.range args) : State.Novel (atomState (W := W) ζ args) j :=
  fun _ ⟨hq, _⟩ hd => hj (hq ▸ Possibility.mem_domain.mpr hd)

theorem familiar_of_mem_indef {F F' : File W M} {i : ℕ} {N : M → Prop}
    (h : F' ∈ (indef i N).fcp F) : State.Familiar F' i := by
  obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h
  exact (State.familiar_randomAssign F i).mono fun _ hp => hp.1

theorem familiar_of_mem_indef_of_familiar {F F' : File W M} {i j : ℕ} {N : M → Prop}
    (hj : State.Familiar F j) (h : F' ∈ (indef i N).fcp F) : State.Familiar F' j := by
  obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h
  exact (hj.randomAssign i).mono fun _ hp => hp.1

theorem novel_of_mem_indef {F F' : File W M} {i j : ℕ} {N : M → Prop} (hij : j ≠ i)
    (hj : State.Novel F j) (h : F' ∈ (indef i N).fcp F) : State.Novel F' j := by
  obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h
  exact (hj.randomAssign hij).mono fun _ hp => hp.1

theorem familiar_of_mem_atom {ζ : (Fin n → M) → Prop} {args : Fin n → ℕ} {F F' : File W M}
    {j : ℕ} (hj : State.Familiar F j) (h : F' ∈ (atom ζ args).fcp F) : State.Familiar F' j :=
  FCP.familiar_ofState hj h

theorem novel_of_mem_atom {ζ : (Fin n → M) → Prop} {args : Fin n → ℕ} {F F' : File W M}
    {j : ℕ} (hj : j ∉ Set.range args) (hF : State.Novel F j) (h : F' ∈ (atom ζ args).fcp F) :
    State.Novel F' j :=
  FCP.novel_ofState (novel_atomState hj) hF h

/-! ### Principle (A) and false files -/

/-- Principle (A): every update ascends in informativeness. -/
theorem le_of_mem_fcp (φ : LF M) : ∀ {F F' : File W M}, F' ∈ φ.fcp F → F ≤ F' := by
  induction φ with
  | atom ζ args => exact fun h => FCP.le_ofState _ h
  | indef i N =>
    intro F F' h
    obtain ⟨hn, h⟩ := Part.mem_assert_iff.mp h
    exact (State.le_randomAssign hn).trans (FCP.le_ofState _ h)
  | defNP i N =>
    intro F F' h
    obtain ⟨-, h⟩ := Part.mem_assert_iff.mp h
    exact Part.mem_some_iff.mp h ▸ le_rfl
  | seq φ ψ ihφ ihψ =>
    intro F F' h
    obtain ⟨F₁, h₁, h₂⟩ := mem_fcp_seq.mp h
    exact (ihφ h₁).trans (ihψ h₂)
  | every φ₁ φ₂ _ _ =>
    exact fun h => State.le_def.mpr fun q hq => ⟨q, subset_of_mem_fcp_every h hq, le_rfl⟩
  | neg ψ _ =>
    exact fun h => State.le_def.mpr fun q hq => ⟨q, FCP.neg_eliminative _ h hq, le_rfl⟩

/-- Once false, always false (§3.2): every update of the absurd file is absurd. -/
theorem fcp_empty (φ : LF M) : ∀ {F' : File W M}, F' ∈ φ.fcp ∅ → F' = ∅ := by
  induction φ with
  | atom ζ args => exact fun h => Part.mem_some_iff.mp (FCP.ofState_empty _ ▸ h)
  | indef i N =>
    intro F' h
    obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h
    exact Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨⟨_, hq, _⟩, _⟩ => hq
  | defNP i N =>
    intro F' h
    obtain ⟨-, h⟩ := Part.mem_assert_iff.mp h
    exact Part.mem_some_iff.mp h
  | seq φ ψ ihφ ihψ =>
    intro F' h
    obtain ⟨F₁, h₁, h₂⟩ := mem_fcp_seq.mp h
    exact ihψ (ihφ h₁ ▸ h₂)
  | every φ₁ φ₂ _ _ =>
    exact fun h => Set.eq_empty_iff_forall_notMem.mpr fun _ hp => subset_of_mem_fcp_every h hp
  | neg ψ _ =>
    exact fun h => Set.eq_empty_iff_forall_notMem.mpr fun _ hp => FCP.neg_eliminative _ h hp

/-! ### Truth (§3.2)

Criterion (C): an utterance is true with respect to a file iff the resulting
file is true, i.e. has a satisfying point (`FCP.trueIn`). No existential
closure is needed: a novel card ranges over the whole domain, a familiar one
over the values its card admits. -/

/-- A free indefinite has existential force: "A woman₁ …" is true w.r.t. a
true file iff some individual is a woman. -/
theorem trueIn_indef {F : File W M} {i : ℕ} (N : M → Prop) (h : State.Novel F i) :
    FCP.trueIn F (indef i N).fcp ↔ F.Nonempty ∧ ∃ m, N m := by
  simp only [FCP.trueIn, fcp_indef N h, Part.mem_some_iff, exists_eq_left]
  constructor
  · rintro ⟨p, hp, m', hm', hN⟩
    obtain ⟨q, hq, m, rfl⟩ := hp
    obtain rfl : m' = m := by simpa [Possibility.update] using hm'
    exact ⟨⟨q, hq⟩, _, hN⟩
  · rintro ⟨⟨q, hq⟩, m, hN⟩
    exact ⟨q.update i (Part.some m), ⟨q, hq, m, rfl⟩, m, by simp [Possibility.update], hN⟩

/-- A definite has the force of its card: "She₁ is a woman" is true w.r.t. a
file iff some point's value at card 1 is a woman. -/
theorem trueIn_pro_pred {F : File W M} {i : ℕ} (N : M → Prop) (h : State.Familiar F i) :
    FCP.trueIn F ((pro i).seq (pred₁ N i)).fcp ↔ ∃ p ∈ F, ∃ m ∈ p.assignment i, N m := by
  have : ((pro i).seq (pred₁ N i)).fcp F = FCP.atomVar N i F := by
    show ((pro i).fcp F).bind _ = _
    rw [fcp_pro F h, Part.bind_some]
    simp only [pred₁, fcp]
    exact congrFun (unary_eq_atomVar N i) F
  simp only [FCP.trueIn, this, FCP.atomVar_eq_of_familiar _ _ h, Part.mem_some_iff,
    exists_eq_left, Set.Nonempty, Set.mem_ofPred_eq]

end LF

/-! ### The book's texts -/

section Texts

open LF

variable (dog cameIn layDown woman person pretzel king : M → Prop)
  (bit hit bought ate lunch : M → M → Prop)

/-- Ch. I (9): "A dog₁ came in. It₁ lay down under the table." -/
def aDog : LF M := (indef 1 dog).seq ((pred₁ cameIn 1).seq ((pro 1).seq (pred₁ layDown 1)))

/-- Ch. I (16): "Every dog₁ came in. It₁ lay down under the table." -/
def everyDog : LF M :=
  (every (indef 1 dog) (pred₁ cameIn 1)).seq ((pro 1).seq (pred₁ layDown 1))

/-- Ch. I (17): "No dog₁ came in. It₁ lay down under the table." -/
def noDog : LF M := (neg ((indef 1 dog).seq (pred₁ cameIn 1))).seq ((pro 1).seq (pred₁ layDown 1))

/-- Ch. III (5) of §2.5: "A woman₁ was bitten by a dog₂. She₁ hit him₂." -/
def womanDog : LF M :=
  (indef 1 woman).seq ((indef 2 dog).seq ((pred₂ bit 2 1).seq ((pro 1).seq
    ((pro 2).seq (pred₂ hit 1 2)))))

/-- Ch. III (2) of §4.1: "Everyone₁ bought a pretzel₂ and ate it₂." -/
def pretzelText : LF M :=
  every (indef 1 person) ((indef 2 pretzel).seq ((pred₂ bought 1 2).seq ((pro 2).seq
    (pred₂ ate 1 2))))

/-- Ch. III (10) of §5.2 under local accommodation: the king's card is added
in the auxiliary file of the negation. -/
def kingLocal (m i : ℕ) : LF M := neg ((indef i king).seq (pred₂ lunch m i))

/-- Ch. III (10) of §5.2 under global accommodation: the king's card is added
to the initial file. -/
def kingGlobal (m i : ℕ) : LF M := (indef i king).seq (neg (pred₂ lunch m i))

variable {dog cameIn layDown woman person pretzel king bit hit bought ate lunch}

/-- (9) is felicitous whenever card 1 is novel: the indefinite's card is
familiar for the pronoun of the next sentence. -/
theorem admits_aDog {F : File W M} (h : State.Novel F 1) :
    (aDog dog cameIn layDown).fcp.admits F := by
  unfold aDog
  have m1 := mem_fcp_indef (F := F) (N := dog).mpr ⟨h, rfl⟩
  exact admits_seq_of_mem m1 (admits_seq_of_mem (Part.mem_some _)
    (admits_pro_seq (familiar_of_mem_atom (familiar_of_mem_indef m1) (Part.mem_some _)) trivial))

/-- (16) is infelicitous whenever card 1 is novel and the universal sentence
is true: `every` returns a subset of the file, at which card 1 is still novel,
so the pronoun is undefined. -/
theorem not_admits_everyDog {F : File W M} (h : State.Novel F 1)
    (ht : FCP.trueIn F (every (indef 1 dog) (pred₁ cameIn 1)).fcp) :
    ¬ (everyDog dog cameIn layDown).fcp.admits F := by
  rintro ⟨hd, hrest⟩
  obtain ⟨F', hF', p, hp⟩ := ht
  obtain rfl := Part.get_eq_of_mem hF' hd
  obtain ⟨hpro, -⟩ := hrest
  have hf : State.Familiar _ 1 := hpro.1.1
  exact h p (subset_of_mem_fcp_every hF' hp) (hf p hp)

/-- (17) is infelicitous whenever card 1 is novel and the negated sentence is
true, for the same reason. -/
theorem not_admits_noDog {F : File W M} (h : State.Novel F 1)
    (ht : FCP.trueIn F (neg ((indef 1 dog).seq (pred₁ cameIn 1))).fcp) :
    ¬ (noDog dog cameIn layDown).fcp.admits F := by
  rintro ⟨hd, hrest⟩
  obtain ⟨F', hF', p, hp⟩ := ht
  obtain rfl := Part.get_eq_of_mem hF' hd
  obtain ⟨hpro, -⟩ := hrest
  have hf : State.Familiar _ 1 := hpro.1.1
  exact h p (FCP.neg_eliminative _ hF' hp) (hf p hp)

/-- (5) of §2.5 is felicitous whenever cards 1 and 2 are novel in the initial
file: the definites of its second sentence find their cards in the file the
first sentence has produced. -/
theorem admits_womanDog {F : File W M} (h1 : State.Novel F 1) (h2 : State.Novel F 2) :
    (womanDog dog woman bit hit).fcp.admits F := by
  unfold womanDog
  have m1 := mem_fcp_indef (F := F) (N := woman).mpr ⟨h1, rfl⟩
  have m2 := mem_fcp_indef (N := dog).mpr ⟨novel_of_mem_indef (by decide) h2 m1, rfl⟩
  have f1 := familiar_of_mem_atom (args := ![2, 1]) (ζ := fun m => bit (m 0) (m 1))
    (familiar_of_mem_indef_of_familiar (familiar_of_mem_indef m1) m2) (Part.mem_some _)
  have f2 := familiar_of_mem_atom (args := ![2, 1]) (ζ := fun m => bit (m 0) (m 1))
    (familiar_of_mem_indef m2) (Part.mem_some _)
  exact admits_seq_of_mem m1 (admits_seq_of_mem m2 (admits_seq_of_mem (Part.mem_some _)
    (admits_pro_seq f1 (admits_pro_seq f2 trivial))))

/-- (2) of §4.1 is felicitous against a file at which cards 1 and 2 are novel:
"it₂" finds its card in the intermediate file produced by "a pretzel₂" inside
the nuclear scope. -/
theorem admits_pretzel {F : File W M} (h1 : State.Novel F 1) (h2 : State.Novel F 2) :
    (pretzelText person pretzel bought ate).fcp.admits F := by
  unfold pretzelText
  have m1 := mem_fcp_indef (F := F) (N := person).mpr ⟨h1, rfl⟩
  have m2 := mem_fcp_indef (N := pretzel).mpr ⟨novel_of_mem_indef (by decide) h2 m1, rfl⟩
  have f2 := familiar_of_mem_atom (args := ![1, 2]) (ζ := fun m => bought (m 0) (m 1))
    (familiar_of_mem_indef m2) (Part.mem_some _)
  exact admits_every_of_mem m1 (admits_seq_of_mem m2 (admits_seq_of_mem (Part.mem_some _)
    (admits_pro_seq f2 trivial)))

/-- Local accommodation (§5.2, option (a)) leaves the initial file's cards as
they were: the king's card does not survive the negation — the narrow-scope
reading. -/
theorem novel_of_mem_kingLocal {F F' : File W M} {m i : ℕ} (h : State.Novel F i)
    (hF' : F' ∈ (kingLocal king lunch m i).fcp F) : State.Novel F' i :=
  h.mono (FCP.neg_eliminative _ hF')

/-- Global accommodation (§5.2, option (b)) makes the king's card part of the
resulting file, which thereby entails that there is a king. -/
theorem familiar_of_mem_kingGlobal {F F' : File W M} {m i : ℕ}
    (hF' : F' ∈ (kingGlobal king lunch m i).fcp F) :
    State.Familiar F' i ∧ ∀ p ∈ F', ∃ x ∈ p.assignment i, king x := by
  obtain ⟨F₁, h₁, h₂⟩ := mem_fcp_seq.mp hF'
  have hsub := FCP.neg_eliminative _ h₂
  refine ⟨(familiar_of_mem_indef h₁).mono hsub, fun p hp => ?_⟩
  obtain ⟨-, rfl⟩ := mem_fcp_indef.mp h₁
  exact (hsub hp).2

end Texts

end Heim1982
