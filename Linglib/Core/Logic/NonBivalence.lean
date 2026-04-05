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

## Algebraic Foundation

The local/global dichotomy reduces to two general facts about bounded
lattices:

1. **Idempotency** (`sup_idem`, `inf_idem`): every element `a` of a
   lattice satisfies `a ⊔ a = a` and `a ⊓ a = a`. Folding either
   operation over a constant list with that constant as accumulator
   yields the constant back. Applied to `.indet`, this gives gap
   absorption: gap in, gap out.

2. **Identity elements** (`bot_sup_eq`, `top_inf_eq`): `⊥ ⊔ a = a`
   and `⊤ ⊓ a = a`. When the initial accumulator is the identity,
   the first fold step transitions to the first element, and then
   idempotency takes over.

3. **Bounded sublattice** `{⊥, ⊤}`: `ofBool` embeds `Bool` into the
   two-element sublattice `{⊥, ⊤}` of any bounded lattice. Since
   `ofBool` is a lattice homomorphism (`ofBool a ⊔ ofBool b = ofBool
   (a || b)`), folding `⊔`/`⊓` over `map ofBool` reduces to folding
   `||`/`&&` over `Bool` — which is always definite.

## Verification Against the Literature

### @cite{ramotowska-marty-romoli-santorio-2025} (S&P 18, §2.2.2)

The `TrivalenceScope` type formalizes their local/global distinction:
- `TrivalenceScope.local` = homogeneity theory's architecture (gaps
  arise per-individual before quantification, §2.2.2 "local scope")
- `TrivalenceScope.global` = selectional theory's architecture (each
  selection function yields determinate outcomes, §2.2.2 "global scope")

`local_strength_irrelevant` captures their Table 2 prediction for the
homogeneity theory: both strong and weak quantifiers yield gap.
`global_mixed_pattern` captures the selectional theory's Table 2
prediction: strong → false, weak → true.

### @cite{agha-jeretic-2022} (SALT 32, §2–3)

The same local/global structure appears in the modal domain:
- `shouldD` (their eq. 27–28) uses supervaluation over deontic
  alternatives (= `dist`), producing gaps for mixed modal bases.
  This is `TrivalenceScope.local`.
- `mustD` (their eq. 25) is universal quantification over the modal
  base, always Boolean. This is `TrivalenceScope.global`.

The should/must contrast parallels the/all: both exhibit the homogeneity
pattern where supervaluation gaps erase quantifier strength.

## Main Definitions

- `TrivalenceScope`: whether gaps arise locally or globally
- `gap_sup_gap`, `gap_inf_gap`: instances of `sup_idem`, `inf_idem`
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
  gaps in it. This is the homogeneity theory's architecture
  (@cite{ramotowska-marty-romoli-santorio-2025} §2.2.2) and the
  `shouldD := ⊕D` architecture (@cite{agha-jeretic-2022} eq. 27–28).
- **global**: the quantifier sees only Boolean values (gaps arise, if at
  all, only after quantification). This is the selectional theory's
  architecture, where each selection function picks a world with
  determinate individual outcomes. -/
inductive TrivalenceScope where
  | «local»   -- gaps visible to the quantifier
  | global    -- quantifier sees only Bools
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════════════════
-- Gap Sublattice: Idempotency in Bounded Lattices
-- ════════════════════════════════════════════════════════════════

/-! The gap sublattice theorem — `.indet` is a fixed point of both
`⊔` and `⊓` — is an instance of the general lattice-theoretic fact
that every element is idempotent under both operations (`sup_idem`,
`inf_idem` from mathlib). There is nothing special about `.indet` here;
what makes the dichotomy work is that `.indet` is the ONLY element
outside `{⊥, ⊤}`. -/

/-- Gap is a fixed point of sup: `gap ⊔ gap = gap`.
    Instance of `sup_idem` (mathlib `Order.Lattice`). -/
@[simp] theorem gap_sup_gap : (Truth3.indet : Truth3) ⊔ .indet = .indet := sup_idem _

/-- Gap is a fixed point of inf: `gap ⊓ gap = gap`.
    Instance of `inf_idem` (mathlib `Order.Lattice`). -/
@[simp] theorem gap_inf_gap : (Truth3.indet : Truth3) ⊓ .indet = .indet := inf_idem _

/-- Folding an idempotent binary operation over a constant list with
    the constant as accumulator returns the constant. General lemma
    used to derive gap absorption from `sup_idem` / `inf_idem`. -/
private theorem foldl_idem_const {α : Type*} (f : α → α → α) (a : α)
    (h : f a a = a) (n : Nat) :
    (List.replicate n a).foldl f a = a := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.foldl_cons, h, ih]

/-- Folding sup over all-gap input yields gap.

    Two mathlib facts at work:
    1. **Identity**: `⊥ ⊔ a = a` — the first fold step transitions
       the accumulator from `⊥` to `.indet`.
    2. **Idempotency** (`sup_idem`): `a ⊔ a = a` — every subsequent
       fold step preserves `.indet`. -/
theorem foldl_sup_gap (n : Nat) (hn : n > 0) :
    (List.replicate n Truth3.indet).foldl (· ⊔ ·) ⊥ = .indet := by
  cases n with
  | zero => omega
  | succ k =>
    simp only [List.replicate_succ, List.foldl_cons]
    -- ⊥ ⊔ .indet = .indet (identity element: ⊥ is identity for ⊔)
    change (List.replicate k Truth3.indet).foldl (· ⊔ ·) Truth3.indet = Truth3.indet
    exact foldl_idem_const (· ⊔ ·) Truth3.indet (sup_idem _) k

/-- Folding inf over all-gap input yields gap.

    Dual of `foldl_sup_gap`:
    1. **Identity**: `⊤ ⊓ a = a` — first step transitions to `.indet`.
    2. **Idempotency** (`inf_idem`): `a ⊓ a = a` — subsequent steps preserve. -/
theorem foldl_inf_gap (n : Nat) (hn : n > 0) :
    (List.replicate n Truth3.indet).foldl (· ⊓ ·) ⊤ = .indet := by
  cases n with
  | zero => omega
  | succ k =>
    simp only [List.replicate_succ, List.foldl_cons]
    -- ⊤ ⊓ .indet = .indet (identity element: ⊤ is identity for ⊓)
    change (List.replicate k Truth3.indet).foldl (· ⊓ ·) Truth3.indet = Truth3.indet
    exact foldl_idem_const (· ⊓ ·) Truth3.indet (inf_idem _) k

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

    This captures the homogeneity theory's prediction
    (@cite{ramotowska-marty-romoli-santorio-2025} Table 2): all
    quantified counterfactuals are equally undefined, regardless
    of quantifier strength.

    Also captures the `shouldD := ⊕D` prediction
    (@cite{agha-jeretic-2022} §2): supervaluation over a mixed
    deontic base yields gap regardless of quantifier type.

    Algebraically: `⊥ ⊔ a = a` (identity) then `a ⊔ a = a`
    (`sup_idem`); dually `⊤ ⊓ a = a` then `a ⊓ a = a`. -/
theorem local_strength_irrelevant (d : DualityType) (n : Nat) (hn : n > 0) :
    aggregate d (List.replicate n Truth3.indet) = .indet := by
  cases d
  · exact existsAny_gap n hn
  · exact forallAll_gap n hn

-- ════════════════════════════════════════════════════════════════
-- Global Architecture: Strength Determines the Pattern
-- ════════════════════════════════════════════════════════════════

/-! ### The `ofBool` lattice homomorphism

`ofBool` embeds `Bool` into the two-element sublattice `{⊥, ⊤}` of
`Truth3`. It is both a sup-homomorphism and an inf-homomorphism:

    ofBool (a || b) = ofBool a ⊔ ofBool b
    ofBool (a && b) = ofBool a ⊓ ofBool b

This homomorphism property is the algebraic reason that folding
lattice operations over `map ofBool` reduces to folding Boolean
operations — and therefore always produces a definite result. -/

/-- `ofBool` preserves `⊔`/`||` (sup-homomorphism). -/
private theorem ofBool_sup (a b : Bool) :
    Truth3.ofBool a ⊔ Truth3.ofBool b = Truth3.ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- `ofBool` preserves `⊓`/`&&` (inf-homomorphism). -/
private theorem ofBool_inf (a b : Bool) :
    Truth3.ofBool a ⊓ Truth3.ofBool b = Truth3.ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- Sup-fold with `ofBool` accumulator — homomorphism propagation. -/
private theorem foldl_sup_ofBool_acc (bs : List Bool) (acc : Bool) :
    (bs.map Truth3.ofBool).foldl (· ⊔ ·) (Truth3.ofBool acc) =
    Truth3.ofBool (bs.foldl (· || ·) acc) := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons, ofBool_sup]
    exact ih (acc || b)

/-- Inf-fold with `ofBool` accumulator — homomorphism propagation. -/
private theorem foldl_inf_ofBool_acc (bs : List Bool) (acc : Bool) :
    (bs.map Truth3.ofBool).foldl (· ⊓ ·) (Truth3.ofBool acc) =
    Truth3.ofBool (bs.foldl (· && ·) acc) := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons, ofBool_inf]
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

/-- Existential aggregation over `map ofBool` = `ofBool (any id)`.

    Since `ofBool` is a sup-homomorphism and `⊥ = ofBool false`,
    folding `⊔` over `map ofBool` reduces to folding `||` over
    the original Bool list. -/
theorem existsAny_ofBool (bs : List Bool) :
    existsAny (bs.map Truth3.ofBool) = Truth3.ofBool (bs.any id) := by
  show (bs.map Truth3.ofBool).foldl (· ⊔ ·) ⊥ = Truth3.ofBool (bs.any id)
  have h : (⊥ : Truth3) = Truth3.ofBool false := rfl
  rw [h, foldl_sup_ofBool_acc, foldl_or_false_eq_any]

/-- Universal aggregation over `map ofBool` = `ofBool (all id)`.

    Since `ofBool` is an inf-homomorphism and `⊤ = ofBool true`,
    folding `⊓` over `map ofBool` reduces to folding `&&` over
    the original Bool list. -/
theorem forallAll_ofBool (bs : List Bool) :
    forallAll (bs.map Truth3.ofBool) = Truth3.ofBool (bs.all id) := by
  show (bs.map Truth3.ofBool).foldl (· ⊓ ·) ⊤ = Truth3.ofBool (bs.all id)
  have h : (⊤ : Truth3) = Truth3.ofBool true := rfl
  rw [h, foldl_inf_ofBool_acc, foldl_and_true_eq_all]

/-- **Global determinacy**: aggregation over `map ofBool` is never gap,
    regardless of duality type. The quantifier always gets a definite
    answer when its inputs are Boolean.

    This captures the selectional theory's architecture
    (@cite{ramotowska-marty-romoli-santorio-2025} §2.2.2): selection
    functions always pick worlds with determinate individual outcomes,
    so the quantifier sees only `{⊥, ⊤}` — the gap-free sublattice.

    Also captures the `mustD := ∀` architecture
    (@cite{agha-jeretic-2022} eq. 25): universal quantification over
    a Boolean-valued modal base always yields a definite result. -/
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

    This captures the selectional theory's Table 2 prediction
    (@cite{ramotowska-marty-romoli-santorio-2025}):
    strong quantifiers (universal, ⊓-fold) reject mixed scenarios,
    weak quantifiers (existential, ⊔-fold) accept mixed scenarios. -/
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
    `.indet`. Strength is invisible.

    @cite{ramotowska-marty-romoli-santorio-2025} §2.2.2: homogeneity theory.
    @cite{agha-jeretic-2022} §2: `shouldD := ⊕D` architecture. -/
theorem dichotomy_local (n : Nat) (hn : n > 0) :
    ∀ d : DualityType, aggregate d (List.replicate n Truth3.indet) = .indet :=
  λ d => local_strength_irrelevant d n hn

/-- **The Global Dichotomy**: when the quantifier sees only Bools,
    mixed inputs produce the strength effect: existential → `.true`,
    universal → `.false`.

    @cite{ramotowska-marty-romoli-santorio-2025} §2.2.2: selectional theory.
    @cite{agha-jeretic-2022} §2: `mustD := ∀` architecture. -/
theorem dichotomy_global (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    aggregate .existential (bs.map Truth3.ofBool) = .true ∧
    aggregate .universal (bs.map Truth3.ofBool) = .false :=
  global_mixed_pattern bs h_some_true h_some_false

end Core.NonBivalence
