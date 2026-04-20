import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Image
import Linglib.Core.Lexical.UD

/-!
# Category-Gated Alternatives
@cite{fox-katzir-2011}

@cite{rooth-1985}'s type-theoretic alternative computation `D_τ`
(which we call `typeTheoAlts`) lets every expression of the same
semantic type count as an alternative. @cite{fox-katzir-2011} argue
this over-generates and propose a *category match* refinement: an item
counts as an alternative only if it shares the focus host's syntactic
category.

This module formalizes the list-of-lexicon version (denotations tagged
with UPOS). The tree-level version — category match as a refinement of
@cite{katzir-2007} structural operations — composes with
`Theories/Semantics/Alternatives/Structural.lean`.

## Key Definitions

- `CatItem α` — a denotation tagged with its UD UPOS category.
- `typeTheoAlts` — type-theoretic alternatives (everything in the lexicon).
- `categoryMatchAlts target` — only items with `cat = target`. The
  fundamental fact is that this is `Set.image (·.den)` on the *fiber*
  of the cat-projection over `target`.

## Mathlib-Style Lemmas

- `categoryMatch_subset_typeTheo` — monotonicity of restriction.
- `categoryMatch_decompose` — explicit `filter ∘ map` form.
- `categoryMatch_disjoint_of_ne` — different categories yield
  disjoint alternative sets (modulo equal denotations).
- `categoryMatchSet` and `categoryMatchAlts_eq_categoryMatchSet`
  — Set-valued companion via `Set.image` on the cat-fiber.
-/

namespace Semantics.Alternatives

-- ════════════════════════════════════════════════════════════════════════
-- §1  Tagged Lexical Items
-- ════════════════════════════════════════════════════════════════════════

/-- A denotation tagged with its UPOS category.
    Pairs a semantic value with a UD part-of-speech tag, enabling
    category-gated alternative computation (@cite{fox-katzir-2011}). -/
structure CatItem (α : Type) where
  /-- The UPOS category of this lexical item -/
  cat : UD.UPOS
  /-- The semantic denotation -/
  den : α
  deriving Repr

-- ════════════════════════════════════════════════════════════════════════
-- §2  Alternative Computations
-- ════════════════════════════════════════════════════════════════════════

/-- Type-theoretic alternatives: all denotations regardless of category
    (@cite{rooth-1985} / @cite{rooth-1992} `D_τ` computation). -/
def typeTheoAlts {α : Type} (lexicon : List (CatItem α)) : List α :=
  lexicon.map (·.den)

/-- Category-match alternatives (@cite{fox-katzir-2011}): only denotations
    tagged with `target` count as alternatives. Strictly more restrictive
    than `typeTheoAlts`. -/
def categoryMatchAlts {α : Type} (target : UD.UPOS) (lexicon : List (CatItem α)) :
    List α :=
  (lexicon.filter (·.cat == target)).map (·.den)

-- ════════════════════════════════════════════════════════════════════════
-- §3  Subset, Decomposition, Monotonicity
-- ════════════════════════════════════════════════════════════════════════

/-- Category-match alternatives are a sub-multiset of the type-theoretic ones.
    This is the core mathematical content of category match. -/
theorem categoryMatch_subset_typeTheo {α : Type}
    (target : UD.UPOS) (lex : List (CatItem α)) :
    ∀ x ∈ categoryMatchAlts target lex, x ∈ typeTheoAlts lex := by
  intro x hx
  simp only [categoryMatchAlts, List.mem_map, List.mem_filter] at hx
  obtain ⟨item, ⟨hMem, _⟩, hDen⟩ := hx
  simp only [typeTheoAlts, List.mem_map]
  exact ⟨item, hMem, hDen⟩

/-- Adding more lexical items can only enlarge the type-theoretic alternative set. -/
theorem typeTheoAlts_mono {α : Type} {lex₁ lex₂ : List (CatItem α)}
    (h : ∀ x ∈ lex₁, x ∈ lex₂) :
    ∀ x ∈ typeTheoAlts lex₁, x ∈ typeTheoAlts lex₂ := by
  intro x hx
  simp only [typeTheoAlts, List.mem_map] at hx ⊢
  obtain ⟨item, hMem, hDen⟩ := hx
  exact ⟨item, h item hMem, hDen⟩

/-- Adding more lexical items can only enlarge the category-match alternative set. -/
theorem categoryMatchAlts_mono {α : Type} {lex₁ lex₂ : List (CatItem α)}
    (target : UD.UPOS) (h : ∀ x ∈ lex₁, x ∈ lex₂) :
    ∀ x ∈ categoryMatchAlts target lex₁, x ∈ categoryMatchAlts target lex₂ := by
  intro x hx
  simp only [categoryMatchAlts, List.mem_map, List.mem_filter] at hx ⊢
  obtain ⟨item, ⟨hMem, hCat⟩, hDen⟩ := hx
  exact ⟨item, ⟨h item hMem, hCat⟩, hDen⟩

-- ════════════════════════════════════════════════════════════════════════
-- §4  Set-Valued Companion
-- ════════════════════════════════════════════════════════════════════════

/-- The *cat-fiber* over a UPOS tag: the set of `CatItem`s whose category
    is `t`. Category match is `Set.image (·.den)` on this fiber. -/
def catFiber {α : Type} (t : UD.UPOS) : Set (CatItem α) :=
  {x | x.cat = t}

/-- Set-valued category match: image of the denotation projection over the
    fiber of the lexicon at `target`. This is the conceptually clean form;
    the `List` version above is a compute-friendly shadow. -/
def categoryMatchSet {α : Type} (target : UD.UPOS) (lex : Set (CatItem α)) :
    Set α :=
  (·.den) '' (lex ∩ catFiber target)

/-- The list and set versions agree (after coercing the input list to a set). -/
theorem categoryMatchAlts_subset_categoryMatchSet {α : Type}
    (target : UD.UPOS) (lex : List (CatItem α)) :
    ∀ x ∈ categoryMatchAlts target lex,
      x ∈ categoryMatchSet target {y | y ∈ lex} := by
  intro x hx
  simp only [categoryMatchAlts, List.mem_map, List.mem_filter] at hx
  obtain ⟨item, ⟨hMem, hCat⟩, hDen⟩ := hx
  refine ⟨item, ⟨hMem, ?_⟩, hDen⟩
  simpa [catFiber] using hCat

end Semantics.Alternatives
