import Linglib.Phonology.Prosody.Syllable

/-!
# Metrical feet
[hayes-1995] [selkirk-1980] [kager-1999]

The canonical metrical foot ([selkirk-1980]; [nespor-vogel-1986]; [hayes-1995];
[kager-1999]): a flat, **headed** constituent over syllable positions — a non-empty,
ordered sequence of syllables with one distinguished `head` (the stressed daughter /
head terminal). Headedness (trochaic/iambic), binarity, and the
trochee/iamb/moraic **inventory are all derived** from the structure, not stored — the
moraic/syllabic split is a counting parameter on `moraCount`, not a different kind of
foot. Re-representations into the prosodic tree (`Prosody.Tree`) and the metrical grid
are *functions* that recover the same head.

## Main definitions

* `isFootTree` / `IsFoot` — structural foot well-formedness on the prosodic-tree carrier
  (an `f`-node over a non-empty list of σ-leaves; the Layeredness core).
* `Foot` — a headed constituent over syllable positions (`head : Fin _`, so non-empty).
* `Foot.IsTrochaic` / `IsIambic` / `IsBinary` / `IsDegenerate` — derived shape predicates.
* `Foot.moraCount` — mora count under a weight reading (the quantity axis).
* `Foot.IsSyllabicTrochee` / `IsMoraicTrochee` / `IsCanonicalIamb` — the *derived* inventory.
* `Foot.toProsTree` / `Foot.toGrid` — re-representations that preserve the head.
* `footMorae` — mora count of a `Tree`-extracted weight-list foot (the flat metrical
  parse is now `Prosody.Footing`).

## Main results

* `Foot.itl_gap` — the Iambic/Trochaic Law ([hayes-1985]): a binary iamb need not be
  weight-blind-characterizable, unlike a binary (syllabic) trochee.
* `Foot.headFlags_toProsTree` — the prosodic-tree re-representation carries the same
  head profile as `toGrid` (head-preservation, the functorial spine).
* `Foot.isFoot_toProsTree` — every `Foot`'s prosodic tree is a well-formed foot tree
  (`IsFoot`): the functoriality/well-formedness bridge onto the carrier.
-/

namespace Prosody

/-! ### Carrier well-formedness -/

/-- The structural `Bool` foot checker on the prosodic-tree carrier ([selkirk-1980];
    matches `Foot.toProsTree`): an `f`-node dominating a non-empty list of σ-leaves. -/
def isFootTree : Tree → Bool
  | .node a cs => a.isFt && !cs.isEmpty &&
      cs.all (fun | .node b ds => b.isSyl && ds.isEmpty)

/-- A well-formed foot: an `f`-node dominating a non-empty list of σ-leaves — the
    inviolable Layeredness + σ-Headedness core ([selkirk-1980]; [hayes-1995]). Foot
    binarity (FtBin) and recursive internally-layered feet (contested — Golston 2021 vs
    [martinez-paricio-kager-2015]) are violable and deferred; this is flat feet, the
    sibling of `IsWord`'s Layeredness. -/
def IsFoot (t : Tree) : Prop := isFootTree t

instance (t : Tree) : Decidable (IsFoot t) :=
  inferInstanceAs (Decidable (isFootTree t = true))

-- A σ-leaf is a non-`f` node, so not a foot; a flat `f`-node over a σ-leaf is one.
example : ¬ IsFoot (.node (.syl 2) []) := by decide
example : IsFoot (.node .ft [.node (.syl 2) []]) := by decide

/-! ### The canonical foot -/

/-- The canonical metrical foot ([selkirk-1980]; [hayes-1995]; [kager-1999]): a
    non-empty, ordered sequence of syllable positions with one distinguished `head`
    (the stressed daughter, the head). The `Fin` index forces non-emptiness by construction.
    The inventory and headedness are derived below, not stored. -/
structure Foot (S : Type*) where
  syllables : List S
  head      : Fin syllables.length
  deriving DecidableEq, Repr

namespace Foot
variable {S : Type*}

/-- The head (stressed) syllable — the head terminal. -/
def headSyllable (f : Foot S) : S := f.syllables.get f.head

/-- The number of dominated syllables. -/
def length (f : Foot S) : ℕ := f.syllables.length

/-- A monosyllabic foot `(σ́)`. -/
def monosyllable (a : S) : Foot S := ⟨[a], 0⟩
/-- A head-initial disyllable `(σ́σ)` — trochaic. -/
def trochee (a b : S) : Foot S := ⟨[a, b], 0⟩
/-- A head-final disyllable `(σσ́)` — iambic. -/
def iamb (a b : S) : Foot S := ⟨[a, b], 1⟩

/-! ### Derived shape predicates -/

/-- Head-initial (trochaic). -/
def IsTrochaic (f : Foot S) : Prop := f.head.val = 0
/-- Head-final (iambic). -/
def IsIambic (f : Foot S) : Prop := f.head.val + 1 = f.syllables.length
/-- A binary (disyllabic) foot. -/
def IsBinary (f : Foot S) : Prop := f.syllables.length = 2
/-- A degenerate (monosyllabic) foot. -/
def IsDegenerate (f : Foot S) : Prop := f.syllables.length = 1

instance (f : Foot S) : Decidable f.IsTrochaic := by unfold IsTrochaic; infer_instance
instance (f : Foot S) : Decidable f.IsIambic := by unfold IsIambic; infer_instance
instance (f : Foot S) : Decidable f.IsBinary := by unfold IsBinary; infer_instance
instance (f : Foot S) : Decidable f.IsDegenerate := by unfold IsDegenerate; infer_instance

/-- Above the monosyllable, headedness is exclusive: a foot is not both trochaic and
    iambic (at length 1 the sole σ is both head-initial and head-final). -/
theorem not_trochaic_and_iambic (f : Foot S) (h : 1 < f.syllables.length) :
    ¬ (f.IsTrochaic ∧ f.IsIambic) := by
  rintro ⟨ht, hi⟩
  unfold IsTrochaic at ht; unfold IsIambic at hi; omega

/-! ### Quantity and the derived inventory -/

/-- Mora count under a weight reading `w` — the quantity axis the moraic/syllabic
    split parameterizes (`FtBin`-by-μ). -/
def moraCount (w : S → ℕ) (f : Foot S) : ℕ := (f.syllables.map w).sum

/-- Syllabic trochee `(σ́σ)`: head-initial and binary, weight-blind ([hayes-1995]). -/
def IsSyllabicTrochee (f : Foot S) : Prop := f.IsTrochaic ∧ f.IsBinary
/-- Moraic trochee `(H)`/`(LL)`: head-initial and bimoraic ([hayes-1995]). -/
def IsMoraicTrochee (w : S → ℕ) (f : Foot S) : Prop := f.IsTrochaic ∧ moraCount w f = 2
/-- Canonical iamb over Hayes' right-prominent inventory `{(H),(LL),(LH)}`
    ([hayes-1995]): head-final, and either a bimoraic monosyllable or an even/right-heavy
    bi-or-trimoraic disyllable. Unlike the trochee, the iamb references weight — the
    quantity-sensitivity the Iambic/Trochaic Law predicts. -/
def IsCanonicalIamb (w : S → ℕ) (f : Foot S) : Prop :=
  f.IsIambic ∧
    ((f.length = 1 ∧ moraCount w f = 2) ∨
     (f.length = 2 ∧ 2 ≤ moraCount w f ∧ moraCount w f ≤ 3 ∧
       (f.syllables.map w).headD 0 ≤ (f.syllables.map w).getLast?.getD 0))

instance (f : Foot S) : Decidable f.IsSyllabicTrochee := by
  unfold IsSyllabicTrochee; infer_instance
instance (w : S → ℕ) (f : Foot S) : Decidable (IsMoraicTrochee w f) := by
  unfold IsMoraicTrochee; infer_instance
instance (w : S → ℕ) (f : Foot S) : Decidable (IsCanonicalIamb w f) := by
  unfold IsCanonicalIamb; infer_instance

/-- **The Iambic/Trochaic Law** ([hayes-1985], after Bolton 1894): a binary iamb is
    *not* characterizable weight-blind — the head-final binary cell admits the
    left-heavy `(H L̗)` that Hayes' canonical inventory excludes — whereas a binary
    trochee is exactly `IsSyllabicTrochee` (weight-blind). Witness: `(H L̗)`. -/
theorem itl_gap : ∃ f : Foot ℕ, (f.IsIambic ∧ f.IsBinary) ∧ ¬ IsCanonicalIamb id f :=
  ⟨Foot.iamb 2 1, by decide⟩

/-! ### Re-representations (preserving the head) -/

/-- Re-represent as a prosodic tree ([selkirk-1980]; [ito-mester-2003]): a depth-1 `.f`
    node over `.σ` leaves, the head σ marked via `Constituent.isHead`. The `.f` node
    itself is marked `isHead` when the foot heads its ω (the `isHead` argument, set by the
    caller building the word tree). -/
def toProsTree (w : S → Syllable.Weight) (f : Foot S) (isHead : Bool := false) : Tree :=
  .node (.ft isHead) ((List.finRange f.syllables.length).map (fun i =>
    .node (.syl (w (f.syllables.get i)) (decide (i = f.head))) []))

/-- Re-represent as a metrical-grid row ([hayes-1995]): a head mark per position. -/
def toGrid (f : Foot S) : List Bool :=
  (List.finRange f.syllables.length).map (fun i => decide (i = f.head))

/-- The σ-leaves' head flags. -/
private def childHeadFlags : Tree → List Bool
  | .node _ cs => cs.map (fun | .node a _ => a.isHead)

@[simp] theorem toGrid_length (f : Foot S) :
    (toGrid f).length = f.syllables.length := by simp [toGrid]

/-- The two re-representations carry the **same head profile**: the prosodic tree's
    σ-leaf head flags are exactly `toGrid f`. So both recover the foot's head. -/
theorem headFlags_toProsTree (w : S → Syllable.Weight) (f : Foot S) :
    childHeadFlags (toProsTree w f) = toGrid f := by
  simp [childHeadFlags, toProsTree, toGrid, List.map_map, Function.comp, Constituent.isHead]

/-- **Functoriality / well-formedness bridge**: a `Foot` record's prosodic-tree
    re-representation is always a well-formed foot tree — `toProsTree` lands in the
    depth-1 f/σ band that `isFootTree` carves out. With `headFlags_toProsTree`
    (head-preservation) this is the load-bearing half of the `Foot S ≃ {t // IsFoot t}`
    embedding that bridges footing-on-`Foot` to OT-on-`Tree`. -/
theorem isFoot_toProsTree (w : S → Syllable.Weight) (f : Foot S) :
    IsFoot (f.toProsTree w) := by
  have hpos : 0 < f.syllables.length := f.head.pos
  unfold IsFoot isFootTree toProsTree
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide, ?_⟩, ?_⟩
  · simpa [List.isEmpty_map, List.finRange_eq_nil_iff] using hpos.ne'
  · rw [List.all_map, List.all_eq_true]
    intro i _
    rfl

end Foot

/-! ### Foot mora count -/

/-- Mora count of a foot given as a weight-list (each weight *is* a mora count). The
    moraic measure for `Tree`-extracted feet (`Prosody.feet`, in `Word.lean`); for a
    headed `Foot S`, use `Foot.moraCount`. -/
def footMorae (ws : List Syllable.Weight) : Nat :=
  ws.foldl (· + ·) 0

/-! ### Footings
[lamont-2022c] [kager-2007]

A **footing**: a flat parse into feet and stray (unfooted) syllables, no designated head
([lamont-2022c]); the σ-type `S` carries quantity (`Unit` insensitive, `Syllable.Weight` not).
A prosodic word ω (`Prosody.Word`) is the headed refinement of a footing. -/

/-- A footing: a flat sequence of feet and stray (unfooted) syllables, no designated head
    ([lamont-2022c]). -/
abbrev Footing (S : Type*) := List (Foot S ⊕ S)

namespace Footing
variable {S : Type*} (fc : Footing S)

/-- The feet, left to right. -/
def feet : List (Foot S) := fc.filterMap Sum.getLeft?

/-- The stray (unfooted) syllables, left to right. -/
def strays : List S := fc.filterMap Sum.getRight?

/-- The total number of syllables, footed and stray. -/
def size : Nat := (fc.map (Sum.elim Foot.length (fun _ => 1))).sum

/-- The `Parse(σ)` violation profile ([lamont-2022c]): `1` at each stray σ, `0` at each footed. -/
def strayMarks : List Nat := fc.flatMap (Sum.elim (List.replicate ·.length 0) (fun _ => [1]))

end Footing

/-! ### Worked examples -/

-- Inventory falls out of the derived predicates (no `FootType` enum).
example : (Foot.trochee 1 1).IsSyllabicTrochee := by decide
example : (Foot.trochee 2 0 : Foot ℕ).IsMoraicTrochee id := by decide
example : (Foot.iamb 1 2 : Foot ℕ).IsCanonicalIamb id := by decide
example : ¬ (Foot.iamb 2 1 : Foot ℕ).IsCanonicalIamb id := by decide
example : (Foot.monosyllable 0).IsDegenerate := by decide

-- The re-representations recover the head: a trochee marks position 0, an iamb 1.
example : Foot.toGrid (Foot.trochee 1 1) = [true, false] := by decide
example : Foot.toGrid (Foot.iamb 1 1) = [false, true] := by decide

end Prosody
