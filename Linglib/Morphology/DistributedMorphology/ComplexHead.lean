import Linglib.Morphology.DistributedMorphology.Locality
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

/-!
# Complex heads and Vocabulary Insertion from the inside out

A morpheme at PF is a bundle of features together with a variable Q that
Vocabulary Insertion substitutes with a phonological exponent, the features
persisting; a root carries its form from the start. The complex head that
successive adjunction builds — the M-Word, its terminals the morphemes — is
the root with the morphemes above it, innermost first, each linearized on
one side, so that linearization respects No Tangling: prefixes outermost
first, the root, then suffixes innermost first. Vocabulary Insertion targets
morphemes only, once each, and proceeds from the inside out; at each
morpheme the context an item sees is the complex head as it then stands,
the inner morphemes realized — their features and the morphophonological
features of their exponents — and the outer ones still bare. Which
morphemes count as context is a locality regime: the concatenated
neighbors after null exponents are pruned, or every morpheme by
hierarchical distance. What insertion does to a morpheme's features is a
second parameter: they persist, or the item's features are rewritten away.

## Main definitions

* `Morpheme`, `ComplexHead`: the morpheme with its Q variable, and the
  complex head.
* `ComplexHead.order`, `ComplexHead.exponents`: linearization and the
  surface exponents.
* `Locality`, `Discharge`: the two regimes and the two fates of features.
* `ComplexHead.contextAt`, `ComplexHead.insertAt`, `ComplexHead.insertAll`:
  the context a morpheme presents, insertion at one morpheme, and insertion
  from the inside out.

## Main results

* `insertAt_of_isRealized`, `exp_insertAll_of_eq_some`: Uniqueness — a
  realized morpheme is never realized again.
* `feats_insertAll_nondeletion`: under non-deletion, features survive
  insertion.
* `exp_insertUpTo_of_le`, `visible_of_exp_none`: inside-out insertion leaves
  the outer morphemes bare, so outward-looking conditioning sees features
  only.
* `length_heads_insertAll`: insertion adds no morpheme.

## References

* [D. Embick, *The morpheme: A theoretical introduction*][embick-2015]
* [D. Embick and R. Noyer, *Distributed Morphology and the
  syntax/morphology interface*][embick-noyer-2007]
* [J. D. Bobaljik, *The ins and outs of contextual allomorphy*][bobaljik-2000]
* [M. Halle, *Distributed Morphology: Impoverishment and Fission*][halle-1997]
-/

namespace DistributedMorphology

open Morphology (Morph)

/-- A morpheme at PF: its features, the value of its Q variable — `none`
before Vocabulary Insertion, the exponent after — and the side on which it
is linearized. -/
structure Morpheme (F E : Type*) where
  /-- The synsem and diacritic features. -/
  feats : List F
  /-- The Q variable: `none` until an exponent is substituted for it. -/
  exp : Option E := none
  /-- The side of its host the morpheme is linearized on. -/
  side : Morph.Side := .after
  deriving DecidableEq, Repr

/-- The complex head: the root, whose form is present from the start, and
the morphemes adjoined above it, innermost first. -/
structure ComplexHead (F E : Type*) where
  /-- The root, with its underlying form. -/
  root : Morpheme F E
  /-- The morphemes above the root, innermost first. -/
  heads : List (Morpheme F E)
  deriving DecidableEq, Repr

namespace Morpheme

variable {F E : Type*}

/-- The morpheme has been realized. -/
def IsRealized (s : Morpheme F E) : Prop := s.exp.isSome

instance (s : Morpheme F E) : Decidable s.IsRealized := inferInstanceAs (Decidable (_ = true))

/-- Substitute the exponent for Q. -/
def realize (s : Morpheme F E) (e : E) : Morpheme F E := { s with exp := some e }

end Morpheme

namespace ComplexHead

variable {F E : Type*} (w : ComplexHead F E)

/-! ### Linearization -/

/-- The positions of the complex head in linear order, respecting No Tangling:
prefixal morphemes outermost first, the root (`none`), suffixal morphemes
innermost first. -/
def order : List (Option ℕ) :=
  ((List.range w.heads.length).filter fun i =>
      (w.heads[i]?.map (·.side)) = some .before).reverse.map some ++
    none :: ((List.range w.heads.length).filter fun i =>
      (w.heads[i]?.map (·.side)) = some .after).map some

/-- The morpheme at a position. -/
def at? : Option ℕ → Option (Morpheme F E)
  | none => some w.root
  | some i => w.heads[i]?

/-- The surface exponents, in linear order. -/
def exponents : List E := w.order.filterMap fun p => (w.at? p).bind (·.exp)

/-! ### Context -/

/-- Which morphemes stand as context to a morpheme undergoing insertion: its
concatenated neighbors, null exponents pruned; or every morpheme of the
complex head by hierarchical distance, inner and outer. -/
inductive Locality where
  /-- The concatenated neighbors, with null exponents pruned. -/
  | concatenation
  /-- Every morpheme, by hierarchical distance. -/
  | hierarchical
  deriving DecidableEq, Repr

/-- What insertion does to a morpheme's features: they persist, or the
inserted item's features are rewritten away. -/
inductive Discharge where
  /-- Features survive insertion. -/
  | nondeletion
  /-- The item's features are deleted on insertion. -/
  | rewriting
  deriving DecidableEq, Repr

/-- The features a morpheme presents as context: its own, and — once
realized — the morphophonological features of its exponent. -/
def visible (expFeatures : E → List F) (s : Morpheme F E) : List F :=
  s.feats ++ (s.exp.map expFeatures).getD []

/-- A bare morpheme presents its features only: nothing of an exponent is
visible before insertion. -/
@[simp] theorem visible_of_exp_none {expFeatures : E → List F} {s : Morpheme F E}
    (h : s.exp = none) : visible expFeatures s = s.feats := by
  simp [visible, h]

/-- A realized morpheme whose exponent is null is pruned from
concatenation. -/
def Pruned (isNull : E → Prop) (s : Morpheme F E) : Prop := ∃ e, s.exp = some e ∧ isNull e

instance (isNull : E → Prop) [DecidablePred isNull] (s : Morpheme F E) :
    Decidable (Pruned isNull s) :=
  match h : s.exp with
  | none => .isFalse (by simp [Pruned, h])
  | some e => decidable_of_iff (isNull e) (by simp [Pruned, h])

variable (isNull : E → Prop) [DecidablePred isNull]

/-- The linear order with pruned morphemes removed. -/
def concat : List (Option ℕ) :=
  w.order.filter fun p => ¬ ∃ s ∈ w.at? p, Pruned isNull s

/-- The concatenated neighbors of head `i`: the inner side and the outer side
of the position, each the nearest unpruned morpheme, if any. -/
def neighbors (i : ℕ) : Option (Morpheme F E) × Option (Morpheme F E) :=
  let c := w.concat isNull
  match c.idxOf? (some i) with
  | none => (none, none)
  | some k =>
    let before := if k = 0 then none else (c[k - 1]?).bind w.at?
    let after := (c[k + 1]?).bind w.at?
    if (w.heads[i]?.map (·.side)) = some .before then (after, before) else (before, after)

/-- The context head `i` presents to Vocabulary Insertion: its features in
focus; inner context on the left, outer on the right, nearest first — under
concatenation the unpruned neighbors, under hierarchy every morpheme of the
complex head by distance. -/
def contextAt (loc : Locality) (expFeatures : E → List F) (i : ℕ) : Neighborhood (List F) :=
  match loc with
  | .concatenation =>
    let (inner, outer) := w.neighbors isNull i
    ⟨(w.heads[i]?.map (·.feats)).getD [], (inner.map fun s => [visible expFeatures s]).getD [],
      (outer.map fun s => [visible expFeatures s]).getD []⟩
  | .hierarchical =>
    ⟨(w.heads[i]?.map (·.feats)).getD [],
      ((w.heads.take i).reverse ++ [w.root]).map (visible expFeatures),
      (w.heads.drop (i + 1)).map (visible expFeatures)⟩

/-! ### Insertion -/

variable [DecidableEq F] (vocab : List (VocabularyItem F E)) (loc : Locality)
  (expFeatures : E → List F) (dis : Discharge)

/-- Vocabulary Insertion at head `i`: the Subset Principle's winner is
substituted for Q, once only; under rewriting its features are deleted. -/
def insertAt (i : ℕ) : ComplexHead F E :=
  match w.heads[i]? with
  | none => w
  | some s =>
    if s.IsRealized then w
    else
      match winner? vocab (w.contextAt isNull loc expFeatures i) with
      | none => w
      | some item =>
        let feats := match dis with
          | .nondeletion => s.feats
          | .rewriting => s.feats.diff item.site.focus
        let s' : Morpheme F E := { s with exp := some item.exponent, feats := feats }
        { w with heads := w.heads.set i s' }

/-- Insertion at the first `n` heads, from the inside out. -/
def insertUpTo (n : ℕ) : ComplexHead F E :=
  (List.range n).foldl (fun w i => w.insertAt isNull vocab loc expFeatures dis i) w

/-- Vocabulary Insertion from the inside out: every head in turn. -/
def insertAll : ComplexHead F E := w.insertUpTo isNull vocab loc expFeatures dis w.heads.length

/-! ### Uniqueness and terminal insertion -/

variable {w vocab loc expFeatures dis}

@[simp] theorem insertUpTo_zero : w.insertUpTo isNull vocab loc expFeatures dis 0 = w := rfl

theorem insertUpTo_succ (n : ℕ) :
    w.insertUpTo isNull vocab loc expFeatures dis (n + 1) =
      (w.insertUpTo isNull vocab loc expFeatures dis n).insertAt isNull vocab loc expFeatures dis
        n := by
  simp [insertUpTo, List.range_succ]

@[simp] theorem root_insertAt (i : ℕ) :
    (w.insertAt isNull vocab loc expFeatures dis i).root = w.root := by
  unfold insertAt; split <;> (try split) <;> (try split) <;> rfl

@[simp] theorem length_heads_insertAt (i : ℕ) :
    (w.insertAt isNull vocab loc expFeatures dis i).heads.length = w.heads.length := by
  unfold insertAt; split <;> (try split) <;> (try split) <;> simp

/-- A realized morpheme is left alone: insertion applies once. -/
theorem insertAt_of_isRealized {i : ℕ} {s : Morpheme F E} (hs : w.heads[i]? = some s)
    (h : s.IsRealized) : w.insertAt isNull vocab loc expFeatures dis i = w := by
  unfold insertAt; rw [hs]; simp [h]

/-- Insertion at one head touches no other. -/
theorem getElem?_heads_insertAt_of_ne {i j : ℕ} (h : i ≠ j) :
    (w.insertAt isNull vocab loc expFeatures dis i).heads[j]? = w.heads[j]? := by
  unfold insertAt; split <;> (try split) <;> (try split) <;> simp [List.getElem?_set_ne h]

/-- A realized exponent survives insertion elsewhere and at its own head. -/
theorem exp_insertAt_of_eq_some {i j : ℕ} {s : Morpheme F E} {e : E} (hs : w.heads[j]? = some s)
    (he : s.exp = some e) :
    ∃ s', (w.insertAt isNull vocab loc expFeatures dis i).heads[j]? = some s' ∧
      s'.exp = some e := by
  by_cases hij : i = j
  · subst hij
    rw [insertAt_of_isRealized isNull hs (by simp [Morpheme.IsRealized, he])]
    exact ⟨s, hs, he⟩
  · rw [getElem?_heads_insertAt_of_ne isNull hij]; exact ⟨s, hs, he⟩

theorem exp_insertUpTo_of_eq_some (n : ℕ) {j : ℕ} {s : Morpheme F E} {e : E}
    (hs : w.heads[j]? = some s) (he : s.exp = some e) :
    ∃ s', (w.insertUpTo isNull vocab loc expFeatures dis n).heads[j]? = some s' ∧
      s'.exp = some e := by
  induction n generalizing w with
  | zero => exact ⟨s, hs, he⟩
  | succ n ih =>
    rw [insertUpTo_succ]
    obtain ⟨s', hs', he'⟩ := ih hs
    exact exp_insertAt_of_eq_some isNull hs' he'

/-- **Uniqueness**: an exponent, once substituted for Q, is never replaced. -/
theorem exp_insertAll_of_eq_some {j : ℕ} {s : Morpheme F E} {e : E} (hs : w.heads[j]? = some s)
    (he : s.exp = some e) :
    ∃ s', (w.insertAll isNull vocab loc expFeatures dis).heads[j]? = some s' ∧
      s'.exp = some e :=
  exp_insertUpTo_of_eq_some isNull _ hs he

/-! ### Inside-out insertion -/

/-- Insertion at an inner head leaves an outer head bare. -/
theorem exp_insertAt_of_lt {i j : ℕ} (hij : i < j) {s : Morpheme F E} (hs : w.heads[j]? = some s)
    (he : s.exp = none) :
    ∃ s', (w.insertAt isNull vocab loc expFeatures dis i).heads[j]? = some s' ∧
      s'.exp = none := by
  rw [getElem?_heads_insertAt_of_ne isNull hij.ne]; exact ⟨s, hs, he⟩

/-- Inside-out insertion up to `n` leaves every head from `n` on bare: when
a head is reached, its outer context carries features only. -/
theorem exp_insertUpTo_of_le (n : ℕ) {j : ℕ} (hnj : n ≤ j) {s : Morpheme F E}
    (hs : w.heads[j]? = some s) (he : s.exp = none) :
    ∃ s', (w.insertUpTo isNull vocab loc expFeatures dis n).heads[j]? = some s' ∧
      s'.exp = none := by
  induction n generalizing w with
  | zero => exact ⟨s, hs, he⟩
  | succ n ih =>
    rw [insertUpTo_succ]
    obtain ⟨s', hs', he'⟩ := ih (Nat.le_of_succ_le hnj) hs
    exact exp_insertAt_of_lt isNull (Nat.lt_of_succ_le hnj) hs' he'

/-! ### Non-deletion -/

theorem feats_insertAt_nondeletion (i : ℕ) :
    (w.insertAt isNull vocab loc expFeatures .nondeletion i).heads.map (·.feats) =
      w.heads.map (·.feats) := by
  unfold insertAt
  cases hs : w.heads[i]? with
  | none => rfl
  | some s =>
    simp only
    split_ifs with hr
    · rfl
    cases winner? vocab (w.contextAt isNull loc expFeatures i) with
    | none => rfl
    | some item =>
      simp only [List.map_set]
      apply List.ext_getElem?
      intro k
      by_cases hk : i = k
      · subst hk
        rw [List.getElem?_set_self (by simpa using (List.getElem?_eq_some_iff.1 hs).1)]
        simp [hs]
      · rw [List.getElem?_set_ne hk]

/-- Under non-deletion, features survive inside-out insertion. -/
theorem feats_insertUpTo_nondeletion (n : ℕ) :
    (w.insertUpTo isNull vocab loc expFeatures .nondeletion n).heads.map (·.feats) =
      w.heads.map (·.feats) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [insertUpTo_succ, feats_insertAt_nondeletion, ih]

theorem feats_insertAll_nondeletion :
    (w.insertAll isNull vocab loc expFeatures .nondeletion).heads.map (·.feats) =
      w.heads.map (·.feats) :=
  feats_insertUpTo_nondeletion isNull _

theorem length_heads_insertUpTo (n : ℕ) :
    (w.insertUpTo isNull vocab loc expFeatures dis n).heads.length = w.heads.length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [insertUpTo_succ, length_heads_insertAt, ih]

@[simp] theorem length_heads_insertAll :
    (w.insertAll isNull vocab loc expFeatures dis).heads.length = w.heads.length :=
  length_heads_insertUpTo isNull _

end ComplexHead

end DistributedMorphology
