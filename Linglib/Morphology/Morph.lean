/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.SplitBy
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Morphs

A **morph** is a minimal segmental form together with its attachment kind:
root, prefix, suffix, infix, proclitic, enclitic, or free form. It is the form
side of Haspelmath's form–content pairing, never zero and never discontinuous.

## Main declarations

* `Morph.Kind`: a bound morph has a position relative to its host
  (`Morph.Position`) and an attachment, affix or clitic (`Morph.Attachment`);
  roots and free forms have neither.
* `Morph`: an attachment kind with the bare segmental material; `Morph.pref`,
  `Morph.suff`, `Morph.infixed`, `Morph.procl`, `Morph.encl`, `Morph.root` and
  `Morph.free` build the morphs of each kind.
* `Morph.Kind.position?`, `Morph.Kind.side?`, `Morph.Kind.attachment?`: the
  projections of a bound kind; an infix is bound inside its host, on no side.
* `Morph.Side.attach`: attachment of an element on a side of a sequence, the
  linear shadow of attachment on a word tree.
* `Morph.wordsAt`, `Morph.surface`: the words of a sequence of morphs at an
  attachment, read off the positions of adjacent morphs, and its surface form in
  boundary notation.

## Main results

* `Morph.flatMap_wordsAt`: the words at `.affix` nest in the words at `.clitic`.
* `Morph.wordsAt_append_cons`: a host with morphs bound before and after it is
  one word.
* `Morph.countP_le_one_of_mem_wordsAt`: every word has at most one morph that is
  not bound.

## Implementation notes

`Morph.Side` is the two-sided part of `Morph.Position` that attachment to a
sequence or a word tree uses. `ToString` writes Leipzig boundary notation (`un-`,
`-able`, `<um>`, `l=`, `=s`), which brackets infixes and has no separate mark for
endoclitics. An affix attaches more tightly than a clitic: the words at `.affix`
keep a clitic apart, as Haspelmath's definition of the word does, and the words at
`.clitic` are the units separated by spaces. In a sequence an infix follows its
host, as in `Word.Tree.toList`, and two adjacent roots are two words, a compound
being a `Word.Tree.compound`. A discontinuous exponent, such as a circumfix, is a
list of such sequences, which its owner joins with `…`.

## References

* [haspelmath-2020]
* [haspelmath-2023]
-/

@[expose] public section

namespace Morphology

/-- The side of its host on which a morph attaches in a sequence. -/
inductive Morph.Side where
  /-- Prefixes and proclitics attach before the host. -/
  | before
  /-- Suffixes and enclitics attach after the host. -/
  | after
  deriving DecidableEq, Repr, Fintype

/-- Where a bound morph sits relative to its host. -/
inductive Morph.Position where
  /-- Prefixes and proclitics sit before the host. -/
  | before
  /-- Infixes and endoclitics sit inside the host. -/
  | inside
  /-- Suffixes and enclitics sit after the host. -/
  | after
  deriving DecidableEq, Repr, Fintype

/-- A bound morph attaches as an affix or as a clitic, by its descriptive label. -/
inductive Morph.Attachment where
  /-- An affix is written with `-`. -/
  | affix
  /-- A clitic is written with `=`. -/
  | clitic
  deriving DecidableEq, Repr, Fintype

/-- The kind of a morph says how it attaches. -/
inductive Morph.Kind where
  /-- A bound morph sits at a position relative to its host, as an affix or a clitic. -/
  | bound (position : Morph.Position) (attachment : Morph.Attachment)
  /-- The morph is a root. -/
  | root
  /-- The morph is free and not a root, as a particle or an auxiliary is. -/
  | free
  deriving DecidableEq, Repr, Fintype

/-- A **morph** is a minimal segmental form with its attachment kind. -/
structure Morph where
  /-- The kind says how the morph attaches. -/
  kind : Morph.Kind
  /-- The form is the bare segmental material, with no boundary notation. -/
  form : String
  deriving DecidableEq, Repr

namespace Morph

/-! ### Sides and positions -/

namespace Side

variable {α : Type*}

/-- `s.toPosition` is the position of the side `s`. -/
def toPosition : Side → Position
  | .before => .before
  | .after => .after

@[simp] theorem toPosition_before : before.toPosition = .before := rfl

@[simp] theorem toPosition_after : after.toPosition = .after := rfl

/-- `s.attach a l` attaches `a` on the side `s` of the sequence `l`. -/
def attach : Side → α → List α → List α
  | .before, a, l => a :: l
  | .after, a, l => l ++ [a]

@[simp] theorem attach_before (a : α) (l : List α) : before.attach a l = a :: l := rfl

@[simp] theorem attach_after (a : α) (l : List α) : after.attach a l = l ++ [a] := rfl

end Side

namespace Position

/-- `p.side?` is the side of the position `p`, and `none` inside the host. -/
def side? : Position → Option Side
  | .before => some .before
  | .inside => none
  | .after => some .after

@[simp] theorem side?_before : before.side? = some .before := rfl

@[simp] theorem side?_inside : inside.side? = none := rfl

@[simp] theorem side?_after : after.side? = some .after := rfl

@[simp] theorem side?_toPosition (s : Side) : s.toPosition.side? = some s := by cases s <;> rfl

variable {p : Position}

theorem side?_eq_some_iff {s : Side} : p.side? = some s ↔ p = s.toPosition := by
  cases p <;> cases s <;> simp

theorem side?_eq_none_iff : p.side? = none ↔ p = inside := by cases p <;> simp

end Position

/-! ### Kinds -/

namespace Kind

/-- `k.position?` is the position of a bound kind, and `none` for roots and free forms. -/
def position? : Kind → Option Position
  | .bound p _ => some p
  | .root | .free => none

/-- `k.attachment?` is the attachment of a bound kind, and `none` for roots and free forms. -/
def attachment? : Kind → Option Attachment
  | .bound _ a => some a
  | .root | .free => none

/-- `k.side?` is the side of a kind bound on a side, and `none` for infixes, endoclitics, roots
and free forms. -/
def side? (k : Kind) : Option Side := k.position?.bind Position.side?

@[simp] theorem position?_bound (p : Position) (a : Attachment) :
    (bound p a).position? = some p := rfl

@[simp] theorem position?_root : root.position? = none := rfl

@[simp] theorem position?_free : free.position? = none := rfl

@[simp] theorem attachment?_bound (p : Position) (a : Attachment) :
    (bound p a).attachment? = some a := rfl

@[simp] theorem attachment?_root : root.attachment? = none := rfl

@[simp] theorem attachment?_free : free.attachment? = none := rfl

@[simp] theorem side?_bound (p : Position) (a : Attachment) : (bound p a).side? = p.side? := rfl

@[simp] theorem side?_root : root.side? = none := rfl

@[simp] theorem side?_free : free.side? = none := rfl

variable {k : Kind}

theorem position?_eq_some_iff {p : Position} : k.position? = some p ↔ ∃ a, k = bound p a := by
  cases k <;> simp [eq_comm]

theorem attachment?_eq_some_iff {a : Attachment} :
    k.attachment? = some a ↔ ∃ p, k = bound p a := by
  cases k <;> simp [eq_comm]

theorem side?_eq_some_iff {s : Side} : k.side? = some s ↔ ∃ a, k = bound s.toPosition a := by
  cases k <;> simp [Position.side?_eq_some_iff]

theorem isSome_position?_iff : k.position?.isSome ↔ ∃ p a, k = bound p a := by
  cases k <;> simp

theorem isSome_attachment?_iff : k.attachment?.isSome ↔ ∃ p a, k = bound p a := by
  cases k <;> simp

end Kind

/-! ### Morphs of each kind -/

/-- `bound p a s` is the morph of form `s` bound at `p` with attachment `a`. -/
@[simps] def bound (position : Position) (attachment : Attachment) (s : String) : Morph :=
  ⟨.bound position attachment, s⟩

/-- `pref s` is the prefix of form `s`. -/
@[simps] def pref (s : String) : Morph := ⟨.bound .before .affix, s⟩

/-- `suff s` is the suffix of form `s`. -/
@[simps] def suff (s : String) : Morph := ⟨.bound .after .affix, s⟩

/-- `infixed s` is the infix of form `s`. -/
@[simps] def infixed (s : String) : Morph := ⟨.bound .inside .affix, s⟩

/-- `procl s` is the proclitic of form `s`. -/
@[simps] def procl (s : String) : Morph := ⟨.bound .before .clitic, s⟩

/-- `encl s` is the enclitic of form `s`. -/
@[simps] def encl (s : String) : Morph := ⟨.bound .after .clitic, s⟩

/-- `root s` is the root of form `s`. -/
@[simps] def root (s : String) : Morph := ⟨.root, s⟩

/-- `free s` is the free non-root morph of form `s`. -/
@[simps] def free (s : String) : Morph := ⟨.free, s⟩

/-! ### Words -/

namespace Attachment

/-- An affix attaches more tightly than a clitic. -/
instance : LinearOrder Attachment :=
  LinearOrder.lift' (fun | .affix => (0 : Fin 2) | .clitic => 1) fun a b ↦ by
    cases a <;> cases b <;> simp

@[simp] theorem affix_le (a : Attachment) : affix ≤ a := by cases a <;> decide

@[simp] theorem le_clitic (a : Attachment) : a ≤ clitic := by cases a <;> decide

end Attachment

variable {l l' : Attachment}

/-- Adjacent morphs `m₁ m₂` are in one word at the attachment `l` when `m₁` is bound before its
host or `m₂` after or inside it, no more loosely than `l`. -/
def JoinsAt (l : Attachment) (m₁ m₂ : Morph) : Prop :=
  (∃ a ≤ l, m₁.kind = .bound .before a) ∨ ∃ p ≠ .before, ∃ a ≤ l, m₂.kind = .bound p a

instance (l : Attachment) : DecidableRel (JoinsAt l) := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∨ _))

theorem JoinsAt.mono (h : l ≤ l') {m₁ m₂ : Morph} : JoinsAt l m₁ m₂ → JoinsAt l' m₁ m₂ :=
  Or.imp (fun ⟨a, ha, e⟩ ↦ ⟨a, ha.trans h, e⟩) fun ⟨p, hp, a, ha, e⟩ ↦ ⟨p, hp, a, ha.trans h, e⟩

/-- The words of a sequence of morphs at the attachment `l` are its maximal runs of morphs
joined at `l`. -/
def wordsAt (l : Attachment) (ms : List Morph) : List (List Morph) :=
  ms.splitBy fun m₁ m₂ ↦ decide (JoinsAt l m₁ m₂)

@[simp] theorem flatten_wordsAt (l : Attachment) (ms : List Morph) :
    (wordsAt l ms).flatten = ms :=
  List.flatten_splitBy ..

/-- Words at a tighter attachment nest in the words at a looser one. -/
theorem flatMap_wordsAt (h : l ≤ l') (ms : List Morph) :
    (wordsAt l' ms).flatMap (wordsAt l) = wordsAt l ms :=
  List.flatMap_splitBy_splitBy (fun _ _ hj ↦ decide_eq_true ((of_decide_eq_true hj).mono h)) ms

/-- A host with morphs bound before it on one side and after or inside it on the other, none
more loosely than `l`, is one word at `l`. -/
theorem wordsAt_append_cons {P S : List Morph} (h : Morph)
    (hP : ∀ p ∈ P, ∃ a ≤ l, p.kind = .bound .before a)
    (hS : ∀ s ∈ S, ∃ q ≠ .before, ∃ a ≤ l, s.kind = .bound q a) :
    wordsAt l (P ++ h :: S) = [P ++ h :: S] := by
  refine List.splitBy_of_isChain (by simp) ?_
  induction P with
  | nil =>
    induction S generalizing h with
    | nil => simp
    | cons s S ih =>
      rw [List.nil_append, List.isChain_cons_cons]
      exact ⟨decide_eq_true (.inr (hS s (by simp))), ih s fun t ht ↦ hS t (by simp [ht])⟩
  | cons p P ih =>
    rw [List.cons_append, List.isChain_cons]
    exact ⟨fun _ _ ↦ decide_eq_true (.inl (hP p (by simp))), ih fun q hq ↦ hP q (by simp [hq])⟩

/-- After a morph not bound before its host, a joined run continues with morphs bound after or
inside their hosts. -/
private theorem bound_back_of_isChain_joinsAt {a : Morph} {t : List Morph}
    (h : (a :: t).IsChain fun m₁ m₂ ↦ decide (JoinsAt l m₁ m₂))
    (ha : a.kind.position? ≠ some .before) :
    ∀ b ∈ t, ∃ p, b.kind.position? = some p ∧ p ≠ .before := by
  induction t generalizing a with
  | nil => simp
  | cons b t ih =>
    rw [List.isChain_cons_cons, decide_eq_true_iff] at h
    obtain ⟨p, hpb, a', -, hp⟩ := h.1.resolve_left fun ⟨a', _, e⟩ ↦ ha (by simp [e])
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨p, by simp [hp], hpb⟩
    · exact ih h.2 (by simpa [hp] using hpb) c hc

/-- A joined run has at most one morph that is not bound. -/
theorem countP_le_one_of_isChain_joinsAt {w : List Morph}
    (h : w.IsChain fun m₁ m₂ ↦ decide (JoinsAt l m₁ m₂)) :
    w.countP (fun m ↦ m.kind.position? = none) ≤ 1 := by
  induction w with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a.kind.position? = none
    · rw [List.countP_cons_of_pos (by simpa using ha), List.countP_eq_zero.mpr fun b hb ↦ ?_]
      obtain ⟨p, hp, -⟩ := bound_back_of_isChain_joinsAt h (by simp [ha]) b hb
      simp [hp]
    · rw [List.countP_cons_of_neg (by simpa using ha)]
      exact ih h.tail

/-- Every word has at most one morph that is not bound, a root or a free form hosting the
rest. -/
theorem countP_le_one_of_mem_wordsAt {ms w : List Morph} (hw : w ∈ wordsAt l ms) :
    w.countP (fun m ↦ m.kind.position? = none) ≤ 1 :=
  countP_le_one_of_isChain_joinsAt (List.isChain_of_mem_splitBy hw)

/-! ### Boundary notation -/

instance : ToString Morph :=
  ⟨fun m => match m.kind with
    | .bound .before .affix => m.form ++ "-"
    | .bound .after .affix => "-" ++ m.form
    | .bound .before .clitic => m.form ++ "="
    | .bound .after .clitic => "=" ++ m.form
    | .bound .inside _ => "<" ++ m.form ++ ">"
    | .root | .free => m.form⟩

/-- The surface form of a sequence of morphs writes each word in boundary notation and separates
the words by spaces. -/
def surface (ms : List Morph) : String :=
  " ".intercalate ((wordsAt .clitic ms).map fun w ↦ String.join (w.map toString))

end Morph

end Morphology
