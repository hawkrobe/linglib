import Linglib.Syntax.Minimalist.Basic

/-!
# A canonical total order on `SyntacticObject` representatives

To make the selection-induced externalization section
([marcolli-chomsky-berwick-2025] §1.12.1 / Lemma 1.13.5) **fully computable**,
exocentric nodes — off `Dom(h)`, where c-selection does not pick a head and the
section is noncanonical — are linearised by a canonical *structural* comparison
`cmpFM` rather than the classical (noncomputable) `Quot.out` representative.

`cmpFM` is a strict-total comparison on `FreeMagma (LIToken ⊕ Nat)`:

- `cmpFM_swap`: `cmpFM a b = (cmpFM b a).swap` (antisymmetry of the comparison)
- `cmpFM_eq`:  `cmpFM a b = .eq → a = b` (distinct reps compare unequal)

These two facts make `smallerFirst` (place the `cmpFM`-smaller subtree first)
**commutative**, which is exactly what `FreeCommMagma.lift` needs to lift the
embedding to the quotient. No `Quot.out`, hence computable.

The leaf comparators reuse mathlib's `compare` (and its `Std.OrientedOrd.eq_swap`
/ `Std.compare_eq_iff_eq` laws) on `ℕ`/`String`; `Cat` is compared via its
constructor index.
-/

namespace Minimalist

private theorem then_eq_eq {o₁ o₂ : Ordering} :
    o₁.then o₂ = .eq ↔ o₁ = .eq ∧ o₂ = .eq := by cases o₁ <;> simp [Ordering.then]

/-! ### Category comparison -/

/-- Comparison on syntactic categories via the constructor index. -/
def cmpCat (c₁ c₂ : Cat) : Ordering := compare c₁.ctorIdx c₂.ctorIdx

theorem cmpCat_swap (c₁ c₂ : Cat) : cmpCat c₁ c₂ = (cmpCat c₂ c₁).swap :=
  Std.OrientedOrd.eq_swap

theorem cmpCat_eq {c₁ c₂ : Cat} (h : cmpCat c₁ c₂ = .eq) : c₁ = c₂ := by
  have : c₁.ctorIdx = c₂.ctorIdx := Std.compare_eq_iff_eq.mp h
  cases c₁ <;> cases c₂ <;> simp_all [Cat.ctorIdx]

/-! ### Lexicographic list comparison -/

/-- Lexicographic comparison on lists, given an element comparison. -/
def cmpList {β : Type*} (cmp : β → β → Ordering) : List β → List β → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => (cmp x y).then (cmpList cmp xs ys)

theorem cmpList_swap {β : Type*} {cmp : β → β → Ordering}
    (hsw : ∀ a b, cmp a b = (cmp b a).swap) :
    ∀ xs ys, cmpList cmp xs ys = (cmpList cmp ys xs).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      simp only [cmpList, hsw x y, cmpList_swap hsw xs ys, Ordering.swap_then]

theorem cmpList_eq {β : Type*} {cmp : β → β → Ordering}
    (heq : ∀ a b, cmp a b = .eq → a = b) :
    ∀ xs ys, cmpList cmp xs ys = .eq → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpList] at h
  | _ :: _, [], h => by simp [cmpList] at h
  | x :: xs, y :: ys, h => by
      obtain ⟨h1, h2⟩ := then_eq_eq.mp h
      rw [heq x y h1, cmpList_eq heq xs ys h2]

/-! ### Lexical item / token comparison -/

/-- Comparison on simple lexical items: category, then selectional stack,
    then phonological form. -/
def cmpSimpleLI (s₁ s₂ : SimpleLI) : Ordering :=
  (cmpCat s₁.cat s₂.cat).then
    ((cmpList cmpCat s₁.sel s₂.sel).then (compare s₁.phonForm s₂.phonForm))

theorem cmpSimpleLI_swap (s₁ s₂ : SimpleLI) :
    cmpSimpleLI s₁ s₂ = (cmpSimpleLI s₂ s₁).swap := by
  simp only [cmpSimpleLI, cmpCat_swap s₁.cat s₂.cat,
    cmpList_swap cmpCat_swap s₁.sel s₂.sel,
    Std.OrientedOrd.eq_swap (a := s₁.phonForm) (b := s₂.phonForm), Ordering.swap_then]

theorem cmpSimpleLI_eq {s₁ s₂ : SimpleLI} (h : cmpSimpleLI s₁ s₂ = .eq) : s₁ = s₂ := by
  obtain ⟨hc, hr⟩ := then_eq_eq.mp h
  obtain ⟨hs, hp⟩ := then_eq_eq.mp hr
  have e1 := cmpCat_eq hc
  have e2 := cmpList_eq (fun _ _ => cmpCat_eq) _ _ hs
  have e3 := Std.compare_eq_iff_eq.mp hp
  cases s₁; cases s₂; simp_all

/-- Comparison on lexical items: lexicographic on their feature lists
    (the `nonempty` proof is irrelevant). -/
def cmpLexItem (l₁ l₂ : LexicalItem) : Ordering :=
  cmpList cmpSimpleLI l₁.features l₂.features

theorem cmpLexItem_swap (l₁ l₂ : LexicalItem) :
    cmpLexItem l₁ l₂ = (cmpLexItem l₂ l₁).swap :=
  cmpList_swap cmpSimpleLI_swap l₁.features l₂.features

theorem cmpLexItem_eq {l₁ l₂ : LexicalItem} (h : cmpLexItem l₁ l₂ = .eq) : l₁ = l₂ := by
  have : l₁.features = l₂.features := cmpList_eq (fun _ _ => cmpSimpleLI_eq) _ _ h
  cases l₁; cases l₂; simp_all

/-- Comparison on tokens: by `id`, then by lexical item. -/
def cmpTok (t₁ t₂ : LIToken) : Ordering :=
  (compare t₁.id t₂.id).then (cmpLexItem t₁.item t₂.item)

theorem cmpTok_swap (t₁ t₂ : LIToken) : cmpTok t₁ t₂ = (cmpTok t₂ t₁).swap := by
  simp only [cmpTok, Std.OrientedOrd.eq_swap (a := t₁.id) (b := t₂.id),
    cmpLexItem_swap t₁.item t₂.item, Ordering.swap_then]

theorem cmpTok_eq {t₁ t₂ : LIToken} (h : cmpTok t₁ t₂ = .eq) : t₁ = t₂ := by
  obtain ⟨hi, hl⟩ := then_eq_eq.mp h
  have ei := Std.compare_eq_iff_eq.mp hi
  have el := cmpLexItem_eq hl
  cases t₁; cases t₂; simp_all

/-! ### Leaf and tree comparison -/

/-- Comparison on a planar leaf label `LIToken ⊕ Nat` (lexical token vs trace). -/
def cmpLeaf : LIToken ⊕ Nat → LIToken ⊕ Nat → Ordering
  | .inl t₁, .inl t₂ => cmpTok t₁ t₂
  | .inl _, .inr _ => .lt
  | .inr _, .inl _ => .gt
  | .inr m, .inr n => compare m n

theorem cmpLeaf_swap (x y : LIToken ⊕ Nat) : cmpLeaf x y = (cmpLeaf y x).swap := by
  cases x with
  | inl t₁ => cases y with
    | inl t₂ => exact cmpTok_swap t₁ t₂
    | inr n => rfl
  | inr m => cases y with
    | inl t₂ => rfl
    | inr n => exact Std.OrientedOrd.eq_swap

theorem cmpLeaf_eq {x y : LIToken ⊕ Nat} (h : cmpLeaf x y = .eq) : x = y := by
  cases x with
  | inl t₁ => cases y with
    | inl t₂ => exact congrArg Sum.inl (cmpTok_eq h)
    | inr n => simp [cmpLeaf] at h
  | inr m => cases y with
    | inl t₂ => simp [cmpLeaf] at h
    | inr n => exact congrArg Sum.inr (Std.compare_eq_iff_eq.mp h)

/-- Structural comparison on planar representatives: leaves before nodes,
    then lexicographic on `(left, right)`. -/
def cmpFM : FreeMagma (LIToken ⊕ Nat) → FreeMagma (LIToken ⊕ Nat) → Ordering
  | .of x, .of y => cmpLeaf x y
  | .of _, .mul _ _ => .lt
  | .mul _ _, .of _ => .gt
  | .mul a b, .mul c d => (cmpFM a c).then (cmpFM b d)

theorem cmpFM_swap : ∀ a b : FreeMagma (LIToken ⊕ Nat),
    cmpFM a b = (cmpFM b a).swap
  | .of x, .of y => cmpLeaf_swap x y
  | .of _, .mul _ _ => rfl
  | .mul _ _, .of _ => rfl
  | .mul a b, .mul c d => by
      simp only [cmpFM, cmpFM_swap a c, cmpFM_swap b d, Ordering.swap_then]

theorem cmpFM_eq : ∀ {a b : FreeMagma (LIToken ⊕ Nat)},
    cmpFM a b = .eq → a = b
  | .of _, .of _, h => congrArg _ (cmpLeaf_eq h)
  | .of _, .mul _ _, h => by simp [cmpFM] at h
  | .mul _ _, .of _, h => by simp [cmpFM] at h
  | .mul a b, .mul c d, h => by
      obtain ⟨h1, h2⟩ := then_eq_eq.mp h
      rw [cmpFM_eq h1, cmpFM_eq h2]

/-! ### Commutative tie-breaker -/

/-- Place the `cmpFM`-smaller subtree first. Commutative (`smallerFirst_comm`)
    because `cmpFM` is an antisymmetric strict-total comparison, so this is a
    well-defined choice independent of argument order — the computable,
    `Quot.out`-free tie-break for exocentric nodes. -/
def smallerFirst (x y : FreeMagma (LIToken ⊕ Nat)) : FreeMagma (LIToken ⊕ Nat) :=
  if cmpFM x y = .gt then y * x else x * y

theorem smallerFirst_comm (x y : FreeMagma (LIToken ⊕ Nat)) :
    smallerFirst x y = smallerFirst y x := by
  unfold smallerFirst
  rw [cmpFM_swap y x]
  cases hxy : cmpFM x y
  · simp [Ordering.swap]
  · rw [cmpFM_eq hxy]; simp [Ordering.swap]
  · simp [Ordering.swap]

/-- Forgetting order, `smallerFirst` is the product of its arguments. -/
theorem mk_smallerFirst (x y : FreeMagma (LIToken ⊕ Nat)) :
    (FreeCommMagma.mk (smallerFirst x y) : SyntacticObject)
      = FreeCommMagma.mk x * FreeCommMagma.mk y := by
  unfold smallerFirst
  split
  · exact FreeCommMagma.swap y x
  · rfl

end Minimalist
