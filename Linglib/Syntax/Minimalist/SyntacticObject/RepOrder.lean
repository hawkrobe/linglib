import Linglib.Syntax.Minimalist.Defs

/-!
# Canonical comparison on the SO₀ alphabet

A carrier-free family of strict-total comparisons on the lexical alphabet
(`Cat`, `SimpleLI`, `LexicalItem`, `LIToken`) and on lists thereof. Each `cmp*`
satisfies two laws:

- `cmp*_swap`: `cmp a b = (cmp b a).swap` (antisymmetry)
- `cmp*_eq`:  `cmp a b = .eq → a = b` (distinct values compare unequal)

These make the comparison usable as a commutative tie-break: the `SO`-carrier
externalization ([marcolli-chomsky-berwick-2025] §1.12.1 / Lemma 1.13.5) orders
exocentric nodes — off `Dom(h)`, where c-selection does not pick a head — by
`cmpList cmpTok` (`SyntacticObject/Externalization.lean`'s `exoYield`), keeping
the section computable with no `Quot.out`.

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

end Minimalist
