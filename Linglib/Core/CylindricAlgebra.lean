import Linglib.Core.Assignment
import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Cylindric Algebras: Algebraic Foundation for Variable-Binding Semantics
@cite{henkin-monk-tarski-1971}

Cylindric algebras, introduced by Tarski and systematically developed
in @cite{henkin-monk-tarski-1971}, provide the algebraic foundation for
first-order predicate logic with equality. A cylindric algebra of
dimension α is a Boolean algebra enriched with *cylindrification*
operators `cκ` (existential quantification over coordinate κ) and
*diagonal elements* `dκl` (equality between coordinates κ and l),
satisfying axioms (C₀)–(C₇).

Every framework in this library that binds variables — whether over
entities, times, situations, or discourse referents — operates on
assignments `ℕ → D` and therefore lives inside the same cylindric set
algebra of dimension ω. The two primitive operations, cylindrification
(`∃d. φ(g[n↦d])`) and diagonal (`g(n) = g(m)`), recur across the
entire codebase under different names. This module provides the single
algebraic source.

## Connections across the library

### Proved bridges (`Core/CylindricAlgebra/`)

The bridge modules in `Core/CylindricAlgebra/` prove algebraic identities
(not analogies) between framework-specific operations and cylindric ops.

| Framework | Operation | = Cylindric | Bridge |
|---|---|---|---|
| VarAssignment | `∃ d, p (updateVar g n d)` | `cylindrify n p g` | `VarAssignment.lean` |
| VarAssignment | `lookupVar n g = lookupVar m g` | `diagonal n m g` | `VarAssignment.lean` |
| CDRT (@cite{muskens-1996}) | `closure (new n ;; φ)` | `cylindrify n (closure φ)` | `DynamicSemantics.lean` |
| CDRT | `eq' (dref n) (dref m)` | `diagonal n m` | `DynamicSemantics.lean` |
| Charlow (@cite{charlow-2019}) | `staticExists x body` | `cylindrify x body` | `DynamicSemantics.lean` |
| Charlow | `dynamicExists x body` | `cylindrify x body` | `DynamicSemantics.lean` |
| DRS/Accessibility | `closure (introReg n ;; D)` | `cylindrify n (closure D)` | `Accessibility.lean` |
| DPL (@cite{groenendijk-stokhof-1991}) | `closure (DPLRel.exists_ x φ)` | `cylindrify x (closure φ)` | `DPL/Bridge.lean` |
| DPL | `closure (atom (g(x) = g(y)))` | `diagonal x y` | `DPL/Bridge.lean` |

### Unproved connections (same algebra, bridges not yet formalized)

These frameworks use `Assignment.update` or `VarAssignment.updateVar`
internally, so their quantificational operations are instances of
cylindrification by the same argument — the bridge theorems just haven't
been written yet.

| Framework | Its existential | Cylindric reading |
|---|---|---|
| ~~DPL (@cite{groenendijk-stokhof-1991})~~ | moved to Proved bridges | see `DPL/Bridge.lean` |
| PLA (@cite{dekker-2012}) | `exists_ i φ` | `cylindrify i (⟦φ⟧)` |
| DynamicGQ (@cite{chierchia-1995}) | `{p \| ∃ x, P x ∧ p.2 = q.2.update v x}` | `cylindrify v P` |
| Bilateral Update (@cite{aloni-2022}) | `exists_ x domain φ` | `cylindrify x (domain ∩ φ)` |
| PIP (@cite{keshet-abney-2024}) | `exists_ v domain body` | `cylindrify v (domain ∩ body)` |
| File Change (@cite{heim-1982}) | indefinite extends Dom, widens Sat | `cylindrify n (⟦φ⟧)` |
| Kamp & Reyle DRS (@cite{kamp-reyle-1993}) | `box [n] [conds]` | `cylindrify n (interp conds)` |
| IntensionalCDRT (@cite{hofmann-2025}) | intensional `new n ;; φ` | `cylindrify n (closure φ)` |

### Same algebra, different base type

These frameworks instantiate `VarAssignment D` at a non-entity domain.
The cylindric axioms (C1–C7) hold for any `D`; only the base type differs.

| Framework | Domain `D` | Its binder | Cylindric reading |
|---|---|---|---|
| @cite{partee-1973} tense | `Time` | `λt. φ(g[n↦t])` | `cylindrify n φ` over temporal assignments |
| @cite{percus-2000} situations | `Situation` | `λs. φ(g[n↦s])` | `cylindrify n φ` over situation assignments |
| @cite{heim-kratzer-1998} | `Entity` | `λx. φ(g[n↦x])` | `cylindrify n φ` over entity assignments |
| @cite{abusch-1997} tense | `Time` | temporal `updateVar` | `cylindrify n φ` over temporal assignments |

### Structural parallels (not assignment-based)

These are not instances of assignment cylindrification but share the same
algebraic shape. Formalizing these would require showing they satisfy C0–C7
over a different carrier.

| Framework | Analogue of cylindrify | Notes |
|---|---|---|
| Team Semantics | `{s[x↦d] \| s ∈ T, d ∈ D}` | Powerset lifting of cylindrify |
| Update Semantics (@cite{veltman-1996}) | state elimination | Weaker — no diagonal |
| Continuation semantics | `shift`/`reset` scope | Different algebraic structure |

## Structure

- §1: Abstract cylindric algebra class (HMT Def 1.1.1)
- §2: Support and cylindrification on assignments
- §3: Cylindric algebra axioms C1–C4 for the assignment algebra
- §4: Diagonal elements on assignments
- §5: Axioms C5–C7 for the assignment algebra
- §6: Substitution via cylindrification + diagonal (HMT §1.5)
- §7: Derived theorems (HMT §1.2)
-/

namespace Core.CylindricAlgebra

open Core (Assignment)

-- ════════════════════════════════════════════════════════════════
-- § 1. Abstract Cylindric Algebra (HMT Def 1.1.1)
-- ════════════════════════════════════════════════════════════════

/-- A cylindric algebra of dimension α (@cite{henkin-monk-tarski-1971},
Def 1.1.1).

An algebraic structure `𝔄 = ⟨A, +, ·, -, 0, 1, cκ, dκl⟩` where
`⟨A, +, ·, -, 0, 1⟩` is a Boolean algebra (axiom C₀) and the
cylindrifications `cκ` and diagonal elements `dκl` satisfy axioms
(C₁)–(C₇). -/
class CylAlg (α : Type*) (A : Type*) [BooleanAlgebra A] where
  /-- Cylindrification at coordinate κ. -/
  cyl : α → A → A
  /-- Diagonal element for coordinates κ, l. -/
  diag : α → α → A
  cyl_bot : ∀ κ : α, cyl κ ⊥ = ⊥
  le_cyl : ∀ (κ : α) (x : A), x ≤ cyl κ x
  cyl_inf_cyl : ∀ (κ : α) (x y : A), cyl κ (x ⊓ cyl κ y) = cyl κ x ⊓ cyl κ y
  cyl_comm : ∀ (κ l : α) (x : A), cyl κ (cyl l x) = cyl l (cyl κ x)
  diag_refl : ∀ κ : α, diag κ κ = ⊤
  diag_cyl : ∀ (κ l m : α), κ ≠ l → κ ≠ m →
    diag l m = cyl κ (diag l κ ⊓ diag κ m)
  cyl_diag_compl : ∀ (κ l : α) (x : A), κ ≠ l →
    cyl κ (diag κ l ⊓ x) ⊓ cyl κ (diag κ l ⊓ xᶜ) = ⊥

-- ════════════════════════════════════════════════════════════════
-- § 2. Support and Cylindrification on Assignments
-- ════════════════════════════════════════════════════════════════

section AssignmentAlgebra

variable {E : Type*}

/-- A predicate on assignments is *invariant on* `B` if it only
depends on the values of registers in `B`: assignments that agree
on `B` satisfy `p` identically. -/
def invariantOn (p : Assignment E → Prop) (B : List Nat) : Prop :=
  ∀ g₁ g₂, (∀ n ∈ B, g₁ n = g₂ n) → (p g₁ ↔ p g₂)

/-- Cylindrification at register `n`: existentially quantify over
the value at slot `n`, leaving all other slots fixed.

In cylindric algebra notation, `cₙ(p)(g) = ∃e. p(g[n↦e])`. -/
def cylindrify (n : Nat) (p : Assignment E → Prop) : Assignment E → Prop :=
  fun g => ∃ e, p (g.update n e)

/-- A predicate is *cylindrification-closed* at register `n` if
abstracting over `n` doesn't change the predicate: `cₙ(p) = p`.
This means `p` doesn't depend on register `n`. -/
def cylClosed (n : Nat) (p : Assignment E → Prop) : Prop :=
  cylindrify n p = p

private theorem update_self (g : Assignment E) (n : Nat) : g.update n (g n) = g := by
  funext m; by_cases h : m = n <;> simp [Assignment.update, h]

/-- If `p` is invariant on `B` and `n ∉ B`, then `p` is
cylindrification-closed at `n`. Invariance on `B` implies
`p` doesn't depend on any register outside `B`. -/
theorem cylClosed_of_invariantOn {p : Assignment E → Prop} {B : List Nat} {n : Nat}
    (hinv : invariantOn p B) (hn : n ∉ B) : cylClosed n p := by
  ext g; simp only [cylindrify]; constructor
  · rintro ⟨e, he⟩
    exact (hinv (g.update n e) g (fun m hm => by
      simp [Assignment.update, show m ≠ n from fun h => hn (h ▸ hm)])).mp he
  · intro hg
    exact ⟨g n, (hinv g (g.update n (g n)) (fun m hm => by
      simp [Assignment.update, show m ≠ n from fun h => hn (h ▸ hm)])).mp hg⟩

/-- `invariantOn p []` is equivalent to `WeakestPrecondition.isProper`:
the predicate takes the same value everywhere. -/
theorem invariantOn_nil_iff {p : Assignment E → Prop} :
    invariantOn p [] ↔ ∀ g₁ g₂, p g₁ ↔ p g₂ :=
  ⟨fun h g₁ g₂ => h g₁ g₂ (fun _ h => nomatch h),
   fun h g₁ g₂ _ => h g₁ g₂⟩

-- ════════════════════════════════════════════════════════════════
-- § 3. Cylindric Algebra Axioms C1–C4
-- ════════════════════════════════════════════════════════════════

/-! We verify that `cylindrify` on `Assignment E → Prop` satisfies the
cylindric set algebra axioms (@cite{henkin-monk-tarski-1971}, §1.1).
Together with the Boolean algebra structure on `Assignment E → Prop`,
this establishes that predicates on assignments form an
`ω`-dimensional cylindric set algebra with base `E`. -/

/-- **C1**: Cylindrification preserves the empty set. `cₙ(⊥) = ⊥`. -/
theorem cylindrify_bot (n : Nat) :
    cylindrify n (fun _ : Assignment E => False) = fun _ => False := by
  ext g; simp [cylindrify]

/-- **C2**: Every element is below its cylindrification. `p ≤ cₙ(p)`.

Proof: witness the current value at register `n`. -/
theorem le_cylindrify (n : Nat) (p : Assignment E → Prop) (g : Assignment E) :
    p g → cylindrify n p g :=
  fun h => ⟨g n, by rw [update_self]; exact h⟩

/-- **C3**: Cylindrification distributes over conjunction with
a cylindrified factor. `cₙ(p ∧ cₙ(q)) = cₙ(p) ∧ cₙ(q)`. -/
theorem cylindrify_inter_cylindrify (n : Nat) (p q : Assignment E → Prop) :
    cylindrify n (fun g => p g ∧ cylindrify n q g) =
    fun g => cylindrify n p g ∧ cylindrify n q g := by
  ext g; simp only [cylindrify]; constructor
  · rintro ⟨e, hp, e', hq⟩
    exact ⟨⟨e, hp⟩, ⟨e', by rw [Assignment.update_overwrite] at hq; exact hq⟩⟩
  · rintro ⟨⟨e₁, hp⟩, ⟨e₂, hq⟩⟩
    exact ⟨e₁, hp, e₂, by rw [Assignment.update_overwrite]; exact hq⟩

/-- **C4**: Cylindrifications commute. `cₙ(cₘ(p)) = cₘ(cₙ(p))`. -/
theorem cylindrify_comm (n m : Nat) (p : Assignment E → Prop) :
    cylindrify n (cylindrify m p) = cylindrify m (cylindrify n p) := by
  ext g; simp only [cylindrify]; constructor
  · rintro ⟨e₁, e₂, hp⟩
    by_cases h : n = m
    · subst h; exact ⟨e₁, e₂, by rw [Assignment.update_overwrite] at hp ⊢; exact hp⟩
    · exact ⟨e₂, e₁, by rw [← Assignment.update_comm g e₁ e₂ h]; exact hp⟩
  · rintro ⟨e₂, e₁, hp⟩
    by_cases h : n = m
    · subst h; exact ⟨e₂, e₁, by rw [Assignment.update_overwrite] at hp ⊢; exact hp⟩
    · exact ⟨e₁, e₂, by rw [Assignment.update_comm g e₁ e₂ h]; exact hp⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. Diagonal Elements on Assignments
-- ════════════════════════════════════════════════════════════════

/-- Diagonal element: the set of assignments where registers κ and l
agree. `Dκl = {g ∈ ωU : g(κ) = g(l)}`.

In DRT, this is the denotation of the identity condition `uκ is ul`.
In predicate logic, it corresponds to the equation `vκ = vl`. -/
def diagonal (κ l : Nat) : Assignment E → Prop :=
  fun g => g κ = g l

-- ════════════════════════════════════════════════════════════════
-- § 5. Axioms C5–C7
-- ════════════════════════════════════════════════════════════════

/-- **C₅**: Every assignment agrees with itself at any register.
`Dκκ = ωU`. -/
theorem diagonal_refl (κ : Nat) :
    @diagonal E κ κ = (fun _ => True) := by
  ext; simp [diagonal]

/-- **C₆**: Diagonal composition via cylindrification.

If κ ≠ l and κ ≠ m, then `Dlm = Cκ(Dlκ ∩ Dκm)`: two registers agree
iff there exists a witness value at a third register matching both.
This is the algebraic expression of transitivity of equality. -/
theorem diagonal_cyl (κ l m : Nat) (hκl : κ ≠ l) (hκm : κ ≠ m) :
    @diagonal E l m = cylindrify κ
      (fun (g : Assignment E) => diagonal l κ g ∧ diagonal κ m g) := by
  ext g; constructor
  · intro (h : g l = g m)
    show ∃ e, (g.update κ e) l = (g.update κ e) κ ∧
              (g.update κ e) κ = (g.update κ e) m
    refine ⟨g l, ?_, ?_⟩
    · rw [Assignment.update_ne g (g l) (Ne.symm hκl), Assignment.update_at]
    · rw [Assignment.update_at, Assignment.update_ne g (g l) (Ne.symm hκm)]; exact h
  · rintro ⟨e, h₁, h₂⟩
    have hl : (g.update κ e) l = g l := Assignment.update_ne g e (Ne.symm hκl)
    have hm : (g.update κ e) m = g m := Assignment.update_ne g e (Ne.symm hκm)
    calc g l = (g.update κ e) l := hl.symm
      _ = (g.update κ e) κ := h₁
      _ = (g.update κ e) m := h₂
      _ = g m := hm

/-- **C₇**: Substitution is functional.

If κ ≠ l, then `Cκ(Dκl ∩ X) ∩ Cκ(Dκl ∩ Xᶜ) = ∅`. Both witnesses
must equal `g l`, so both conjuncts operate on the same updated
assignment, contradicting `p` and `¬p`. -/
theorem cyl_diag_compl (κ l : Nat) (p : Assignment E → Prop) (hκl : κ ≠ l) :
    (fun g => cylindrify κ (fun g' => @diagonal E κ l g' ∧ p g') g ∧
             cylindrify κ (fun g' => @diagonal E κ l g' ∧ ¬p g') g) =
    (fun _ : Assignment E => False) := by
  ext g; constructor
  · rintro ⟨⟨e₁, hd₁, hp₁⟩, ⟨e₂, hd₂, hp₂⟩⟩
    simp only [diagonal] at hd₁ hd₂
    have he₁ : e₁ = g l := by
      have h1 : (g.update κ e₁) κ = e₁ := Assignment.update_at g κ e₁
      have h2 : (g.update κ e₁) l = g l := Assignment.update_ne g e₁ (Ne.symm hκl)
      rw [h1, h2] at hd₁; exact hd₁
    have he₂ : e₂ = g l := by
      have h1 : (g.update κ e₂) κ = e₂ := Assignment.update_at g κ e₂
      have h2 : (g.update κ e₂) l = g l := Assignment.update_ne g e₂ (Ne.symm hκl)
      rw [h1, h2] at hd₂; exact hd₂
    subst he₁; subst he₂
    exact hp₂ hp₁
  · exact False.elim

-- ════════════════════════════════════════════════════════════════
-- § 6. Substitution (HMT §1.5)
-- ════════════════════════════════════════════════════════════════

/-- Algebraic substitution: replace coordinate κ with the value at l.

`σ^κ_l(x) = cκ(dκl · x)` (@cite{henkin-monk-tarski-1971}, §1.5).
The substitution first constrains register κ to equal register l
(via the diagonal `dκl`), then existentially abstracts over the old
value at κ (via cylindrification `cκ`).

In DRT, this is anaphora resolution: "uκ refers to whatever ul
refers to." -/
def substitute (κ l : Nat) (p : Assignment E → Prop) : Assignment E → Prop :=
  cylindrify κ (fun g => @diagonal E κ l g ∧ p g)

/-- Direct (semantic) substitution: evaluate `p` with register κ
reading from register l. -/
def directSubst (κ l : Nat) (p : Assignment E → Prop) : Assignment E → Prop :=
  fun g => p (g.update κ (g l))

/-- Algebraic substitution equals direct substitution (HMT §1.5).

The cylindric algebra expression `cκ(dκl · x)` computes the same
predicate as directly evaluating `x` with register κ replaced by
the value at register l.

For DRT: resolving an anaphoric link `uκ = ul` (diagonal) followed
by dref closure (cylindrification) gives the same result as directly
reading register l in place of register κ. -/
theorem substitute_eq_directSubst (κ l : Nat) (p : Assignment E → Prop)
    (h : κ ≠ l) : substitute κ l p = directSubst κ l p := by
  ext g; simp only [substitute, directSubst, cylindrify, diagonal]; constructor
  · rintro ⟨e, hd, hp⟩
    have heq : e = g l := by
      have h1 := Assignment.update_at g κ e
      have h2 := Assignment.update_ne g e (Ne.symm h : l ≠ κ)
      rw [h1, h2] at hd; exact hd
    subst heq; exact hp
  · intro hp
    exact ⟨g l, by simp [Assignment.update_ne g (g l) (Ne.symm h : l ≠ κ)], hp⟩

/-- Self-substitution is cylindrification. `σ^κ_κ(x) = cκ(x)`. -/
theorem substitute_self (κ : Nat) (p : Assignment E → Prop) :
    substitute κ κ p = cylindrify κ p := by
  ext g; simp only [substitute, cylindrify]; constructor
  · rintro ⟨e, _, hp⟩; exact ⟨e, hp⟩
  · rintro ⟨e, hp⟩; exact ⟨e, by simp [diagonal], hp⟩

/-- Substitution preserves invariance: if `p` doesn't depend on
register κ, then substituting at κ doesn't change the predicate. -/
theorem substitute_invariant (κ l : Nat) (p : Assignment E → Prop)
    (h : κ ≠ l) (hinv : cylClosed κ p) :
    substitute κ l p = p := by
  rw [substitute_eq_directSubst κ l p h]
  have hcyl : cylindrify κ p = p := hinv
  ext g; simp only [directSubst]; constructor
  · intro hp
    have : cylindrify κ p g := ⟨g l, hp⟩
    rwa [hcyl] at this
  · intro hp
    -- From p g, derive cylindrify κ p g
    have hcg : cylindrify κ p g := le_cylindrify κ p g hp
    -- cylindrify κ p (g.update κ (g l)) ↔ p (g.update κ (g l)) by cylClosed
    -- cylindrify κ p (g.update κ (g l)) = ∃ e, p ((g.update κ (g l)).update κ e)
    -- = ∃ e, p (g.update κ e)  (by update_overwrite)
    -- = cylindrify κ p g
    suffices cylindrify κ p (g.update κ (g l)) from (congr_fun hcyl _).mp this
    simp only [cylindrify]
    obtain ⟨e, he⟩ := hcg
    exact ⟨e, by rwa [Assignment.update_overwrite]⟩

-- ════════════════════════════════════════════════════════════════
-- § 7. Derived Cylindric Algebra Theorems (HMT §1.2)
-- ════════════════════════════════════════════════════════════════

/-- HMT Theorem 1.2.1: `cκ(x) = 0 iff x = 0`. -/
theorem cylindrify_eq_bot_iff (κ : Nat) (p : Assignment E → Prop) :
    cylindrify κ p = (fun _ => False) ↔ p = (fun _ => False) := by
  constructor
  · intro h
    ext g; constructor
    · intro hp
      have : cylindrify κ p g := le_cylindrify κ p g hp
      rw [h] at this; exact this
    · exact False.elim
  · intro h; rw [h]; exact cylindrify_bot κ

/-- HMT Theorem 1.2.2: `cκ(1) = 1`. -/
theorem cylindrify_top [Nonempty E] (κ : Nat) :
    cylindrify κ (fun _ : Assignment E => True) = (fun _ => True) := by
  ext g; simp only [cylindrify]; constructor
  · intro _; trivial
  · intro _; exact ⟨Classical.arbitrary E, trivial⟩

/-- HMT Theorem 1.2.3: `cκ(cκ(x)) = cκ(x)`. Cylindrification is
idempotent. -/
theorem cylindrify_idem (κ : Nat) (p : Assignment E → Prop) :
    cylindrify κ (cylindrify κ p) = cylindrify κ p := by
  ext g; simp only [cylindrify]; constructor
  · rintro ⟨_, e₂, hp⟩
    exact ⟨e₂, by rwa [Assignment.update_overwrite] at hp⟩
  · rintro ⟨e, hp⟩
    exact ⟨g κ, e, by rwa [Assignment.update_overwrite]⟩

/-- HMT Corollary 1.2.4: `cylClosed κ p ↔ p = cκ(q)` for some q. -/
theorem cylClosed_iff_range (κ : Nat) (p : Assignment E → Prop) :
    cylClosed κ p ↔ ∃ q, p = cylindrify κ q := by
  constructor
  · intro h; exact ⟨p, h.symm⟩
  · rintro ⟨q, rfl⟩
    show cylindrify κ (cylindrify κ q) = cylindrify κ q
    exact cylindrify_idem κ q

/-- HMT Theorem 1.2.6(ii): Cylindrification distributes over join.
`cκ(x + y) = cκ(x) + cκ(y)`. -/
theorem cylindrify_or (κ : Nat) (p q : Assignment E → Prop) :
    cylindrify κ (fun g => p g ∨ q g) =
    (fun g => cylindrify κ p g ∨ cylindrify κ q g) := by
  ext g; simp only [cylindrify]; constructor
  · rintro ⟨e, h⟩
    cases h with
    | inl hp => exact Or.inl ⟨e, hp⟩
    | inr hq => exact Or.inr ⟨e, hq⟩
  · rintro (⟨e, hp⟩ | ⟨e, hq⟩)
    · exact ⟨e, Or.inl hp⟩
    · exact ⟨e, Or.inr hq⟩

end AssignmentAlgebra

end Core.CylindricAlgebra
