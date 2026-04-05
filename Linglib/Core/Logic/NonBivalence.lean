import Linglib.Core.Logic.Duality

/-!
# Non-Bivalence: Local vs Global Trivalence
@cite{ramotowska-marty-romoli-santorio-2025} @cite{kriz-spector-2021}

The deepest architectural insight from the counterfactual embedding
literature: whether gaps arise LOCALLY (during composition, before the
quantifier) or GLOBALLY (after the quantifier has already seen Boolean
values) determines whether quantifier strength matters.

## The Dichotomy

- **Local scope**: gaps are the quantifier's input. Both ⊔-fold and
  ⊓-fold fix `.indet` — strength is irrelevant. This is the homogeneity
  theory's architecture for counterfactuals.

- **Global scope**: the quantifier sees only Boolean values. Aggregation
  over Bools is always determinate, and mixed inputs yield the
  strength-dependent pattern (strong → false, weak → true). This is the
  selectional theory's architecture.

## Mathematical Foundation

The gap sublattice theorem: `.indet` is a fixed point of both `⊔` and
`⊓` in the Truth3 lattice (it is a sublattice). Folding either operation
over all-gap input returns gap. This is why LOCAL gaps erase the
quantifier's projection type — the quantifier cannot "see past" gaps
regardless of whether it is conjunctive or disjunctive.

The Bool exclusion theorem: `ofBool` maps into {⊥, ⊤}, which contains no
gaps. Folding over `map ofBool` always yields a definite value, and mixed
Bool inputs distinguish ⊔-fold from ⊓-fold — which IS the strength
effect.

## Main Definitions

- `TrivalenceScope`: whether gaps arise locally or globally
- `gap_sup_gap`, `gap_inf_gap`: gap sublattice (fixed point of both ops)
- `foldl_sup_gap`, `foldl_inf_gap`: gap absorption under aggregation
- `local_strength_irrelevant`: both duality types agree on all-gap input
- `global_always_determinate`: aggregation over `map ofBool` is never gap
- `global_mixed_pattern`: mixed Bools → ∃ gives true, ∀ gives false
- `dichotomy_local`, `dichotomy_global`: the unifying theorems
-/

namespace Core.NonBivalence

open Core.Duality

-- ════════════════════════════════════════════════════════════════
-- The Scope Distinction
-- ════════════════════════════════════════════════════════════════

/-- Whether truth-value gaps arise before or after quantifier evaluation.

- **local**: gaps arise during composition (e.g., each individual's
  counterfactual is `.indet`). The quantifier sees `List Truth3` with
  gaps in it. This is the homogeneity theory's architecture.
- **global**: the quantifier sees only Boolean values (gaps arise, if at
  all, only after quantification). This is the selectional theory's
  architecture, where each selection function picks a world with
  determinate individual outcomes. -/
inductive TrivalenceScope where
  | «local»   -- gaps visible to the quantifier
  | global    -- quantifier sees only Bools
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════════════════
-- Gap Sublattice: indet is a fixed point of both ⊔ and ⊓
-- ════════════════════════════════════════════════════════════════

/-- Gap is a fixed point of sup: `gap ⊔ gap = gap`. -/
@[simp] theorem gap_sup_gap : (Truth3.indet : Truth3) ⊔ .indet = .indet := rfl

/-- Gap is a fixed point of inf: `gap ⊓ gap = gap`. -/
@[simp] theorem gap_inf_gap : (Truth3.indet : Truth3) ⊓ .indet = .indet := rfl

/-- Sup-fold with indet accumulator over all-indet list. -/
private theorem foldl_sup_indet_acc (l : List Truth3) (hl : l.all (· == .indet)) :
    l.foldl (· ⊔ ·) Truth3.indet = .indet := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.all_cons, Bool.and_eq_true] at *
    have hhd : hd = .indet := by cases hd <;> simp_all
    subst hhd; exact ih hl.2

/-- Inf-fold with indet accumulator over all-indet list. -/
private theorem foldl_inf_indet_acc (l : List Truth3) (hl : l.all (· == .indet)) :
    l.foldl (· ⊓ ·) Truth3.indet = .indet := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.all_cons, Bool.and_eq_true] at *
    have hhd : hd = .indet := by cases hd <;> simp_all
    subst hhd; exact ih hl.2

/-- Folding sup over all-gap input yields gap. -/
theorem foldl_sup_gap (n : Nat) (hn : n > 0) :
    (List.replicate n Truth3.indet).foldl (· ⊔ ·) ⊥ = .indet := by
  cases n with
  | zero => omega
  | succ k =>
    simp only [List.replicate_succ, List.foldl_cons]
    change (List.replicate k Truth3.indet).foldl (· ⊔ ·) Truth3.indet = Truth3.indet
    exact foldl_sup_indet_acc _ (by simp)

/-- Folding inf over all-gap input yields gap. -/
theorem foldl_inf_gap (n : Nat) (hn : n > 0) :
    (List.replicate n Truth3.indet).foldl (· ⊓ ·) ⊤ = .indet := by
  cases n with
  | zero => omega
  | succ k =>
    simp only [List.replicate_succ, List.foldl_cons]
    change (List.replicate k Truth3.indet).foldl (· ⊓ ·) Truth3.indet = Truth3.indet
    exact foldl_inf_indet_acc _ (by simp)

-- ════════════════════════════════════════════════════════════════
-- Local Architecture: Strength Is Irrelevant
-- ════════════════════════════════════════════════════════════════

/-- Existential aggregation over all-gap input yields gap. -/
theorem existsAny_gap (n : Nat) (hn : n > 0) :
    existsAny (List.replicate n Truth3.indet) = .indet :=
  foldl_sup_gap n hn

/-- Universal aggregation over all-gap input yields gap. -/
theorem forallAll_gap (n : Nat) (hn : n > 0) :
    forallAll (List.replicate n Truth3.indet) = .indet :=
  foldl_inf_gap n hn

/-- **Local strength irrelevance**: when all inputs are gaps, both
    existential and universal aggregation return gap. The quantifier's
    projection type is invisible.

    This is why the homogeneity theory (local gaps) predicts that
    strength has no effect — all quantified counterfactuals are
    equally undefined. -/
theorem local_strength_irrelevant (d : DualityType) (n : Nat) (hn : n > 0) :
    aggregate d (List.replicate n Truth3.indet) = .indet := by
  cases d
  · exact existsAny_gap n hn
  · exact forallAll_gap n hn

-- ════════════════════════════════════════════════════════════════
-- Global Architecture: Strength Determines the Pattern
-- ════════════════════════════════════════════════════════════════

/-- Sup-fold with `ofBool` accumulator. -/
private theorem foldl_sup_ofBool_acc (bs : List Bool) (acc : Bool) :
    (bs.map Truth3.ofBool).foldl (· ⊔ ·) (Truth3.ofBool acc) =
    Truth3.ofBool (bs.foldl (· || ·) acc) := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [show Truth3.ofBool acc ⊔ Truth3.ofBool b = Truth3.ofBool (acc || b) from
      by cases acc <;> cases b <;> rfl]
    exact ih (acc || b)

/-- Inf-fold with `ofBool` accumulator. -/
private theorem foldl_inf_ofBool_acc (bs : List Bool) (acc : Bool) :
    (bs.map Truth3.ofBool).foldl (· ⊓ ·) (Truth3.ofBool acc) =
    Truth3.ofBool (bs.foldl (· && ·) acc) := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [show Truth3.ofBool acc ⊓ Truth3.ofBool b = Truth3.ofBool (acc && b) from
      by cases acc <;> cases b <;> rfl]
    exact ih (acc && b)

/-- `foldl (· || ·) false = any id`. -/
private theorem foldl_or_false_eq_any (bs : List Bool) :
    bs.foldl (· || ·) false = bs.any id := by
  suffices ∀ acc, bs.foldl (· || ·) acc = (acc || bs.any id) from by
    simp only [this false, Bool.false_or]
  intro acc
  induction bs generalizing acc with
  | nil => simp only [List.foldl_nil, List.any_nil, Bool.or_false]
  | cons b bs ih =>
    simp only [List.foldl_cons, List.any_cons, id, ih (acc || b), Bool.or_assoc]

/-- `foldl (· && ·) true = all id`. -/
private theorem foldl_and_true_eq_all (bs : List Bool) :
    bs.foldl (· && ·) true = bs.all id := by
  suffices ∀ acc, bs.foldl (· && ·) acc = (acc && bs.all id) from by
    simp only [this true, Bool.true_and]
  intro acc
  induction bs generalizing acc with
  | nil => simp only [List.foldl_nil, List.all_nil, Bool.and_true]
  | cons b bs ih =>
    simp only [List.foldl_cons, List.all_cons, id, ih (acc && b), Bool.and_assoc]

/-- Existential aggregation over `map ofBool` = `ofBool (any id)`. -/
theorem existsAny_ofBool (bs : List Bool) :
    existsAny (bs.map Truth3.ofBool) = Truth3.ofBool (bs.any id) := by
  show (bs.map Truth3.ofBool).foldl (· ⊔ ·) ⊥ = Truth3.ofBool (bs.any id)
  have h : (⊥ : Truth3) = Truth3.ofBool false := rfl
  rw [h, foldl_sup_ofBool_acc, foldl_or_false_eq_any]

/-- Universal aggregation over `map ofBool` = `ofBool (all id)`. -/
theorem forallAll_ofBool (bs : List Bool) :
    forallAll (bs.map Truth3.ofBool) = Truth3.ofBool (bs.all id) := by
  show (bs.map Truth3.ofBool).foldl (· ⊓ ·) ⊤ = Truth3.ofBool (bs.all id)
  have h : (⊤ : Truth3) = Truth3.ofBool true := rfl
  rw [h, foldl_inf_ofBool_acc, foldl_and_true_eq_all]

/-- **Global determinacy**: aggregation over `map ofBool` is never gap,
    regardless of duality type. The quantifier always gets a definite
    answer when its inputs are Boolean.

    This is why the selectional theory (global Bools) always produces
    determinate embedded counterfactuals. -/
theorem global_always_determinate (d : DualityType) (bs : List Bool) :
    aggregate d (bs.map Truth3.ofBool) ≠ .indet := by
  cases d with
  | existential =>
    show existsAny (bs.map Truth3.ofBool) ≠ .indet
    rw [existsAny_ofBool]
    cases bs.any id <;> exact Truth3.noConfusion
  | universal =>
    show forallAll (bs.map Truth3.ofBool) ≠ .indet
    rw [forallAll_ofBool]
    cases bs.all id <;> exact Truth3.noConfusion

/-- **Global mixed pattern**: when Bool inputs are mixed (some true, some
    false), existential aggregation yields `.true` and universal yields
    `.false`. This IS the strength effect.

    Strong quantifiers (universal-like, ⊓-fold) reject mixed scenarios.
    Weak quantifiers (existential-like, ⊔-fold) accept mixed scenarios. -/
theorem global_mixed_pattern (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    aggregate .existential (bs.map Truth3.ofBool) = .true ∧
    aggregate .universal (bs.map Truth3.ofBool) = .false := by
  refine ⟨?_, ?_⟩
  · -- Existential: any true → result true
    show existsAny (bs.map Truth3.ofBool) = .true
    rw [existsAny_ofBool, show bs.any id = true from h_some_true]; rfl
  · -- Universal: some false → not all true → all id = false
    show forallAll (bs.map Truth3.ofBool) = .false
    rw [forallAll_ofBool]
    have h_not_all : bs.all id = false := by
      rw [Bool.eq_false_iff]
      intro h_all
      obtain ⟨x, hx_mem, hx_eq⟩ := List.any_eq_true.mp h_some_false
      have := List.all_eq_true.mp h_all x hx_mem
      cases x <;> simp_all [id]
    rw [h_not_all]; rfl

-- ════════════════════════════════════════════════════════════════
-- The Dichotomy Theorem
-- ════════════════════════════════════════════════════════════════

/-- **The Local Dichotomy**: when gaps arise locally (before the
    quantifier), both existential and universal aggregation return
    `.indet`. Strength is invisible. -/
theorem dichotomy_local (n : Nat) (hn : n > 0) :
    ∀ d : DualityType, aggregate d (List.replicate n Truth3.indet) = .indet :=
  λ d => local_strength_irrelevant d n hn

/-- **The Global Dichotomy**: when the quantifier sees only Bools,
    mixed inputs produce the strength effect: existential → `.true`,
    universal → `.false`. -/
theorem dichotomy_global (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    aggregate .existential (bs.map Truth3.ofBool) = .true ∧
    aggregate .universal (bs.map Truth3.ofBool) = .false :=
  global_mixed_pattern bs h_some_true h_some_false

end Core.NonBivalence
