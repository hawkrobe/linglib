import Mathlib.Init

/-!
# Variable Assignments
@cite{heim-kratzer-1998} @cite{henkin-monk-tarski-1971} @cite{spector-2025}
@cite{beaver-krahmer-2001} @cite{van-der-berg-1996} @cite{nouwen-2003}
@cite{brasoveanu-2008}

The polymorphic assignment substrate shared by every variable-binding framework
in the library: Tarski-style total assignments, partial assignments (trivalent
semantics), plural assignments (plural dynamic semantics), and a generic
`VarAssignment` alias.

`Assignment E := ℕ → E` is **pre-intensional** — pure Tarski variable mapping —
so it lives at the top of `Core` rather than inside `Core.IntensionalLogic`.
The intensional substrate (`Frame`, `SitAssignment F := Assignment F.Index`,
`DenotGS`) builds on this in `Core/IntensionalLogic/`.
-/

namespace Core

-- ════════════════════════════════════════════════════════════════
-- Total Assignments (Tarski-style; the extensional substrate)
-- @cite{heim-kratzer-1998} @cite{henkin-monk-tarski-1971}
-- ════════════════════════════════════════════════════════════════

/-- Variable assignment: a function from natural-number indices to values in
    `E`. Instantiated at `F.Entity` for entity pronouns (Heim & Kratzer
    1998), at `F.Index` for situation pronouns (Hanink 2021 / Bondarenko 2023),
    at `Time` for temporal variables, and at any other carrier whenever a
    framework needs Tarski-style variable interpretation. -/
abbrev Assignment (E : Type*) := Nat → E

namespace Assignment

/-- Pointwise update `g[n↦d]`: set register `n` to `d`, leaving all other
    registers fixed. -/
def update {E : Type*} (g : Assignment E) (n : Nat) (d : E) : Assignment E :=
  fun m => if m = n then d else g m

@[simp] theorem update_at {E : Type*} (g : Assignment E) (n : Nat) (d : E) :
    (g.update n d) n = d := by simp [update]

@[simp] theorem update_ne {E : Type*} (g : Assignment E) {n m : Nat} (d : E)
    (h : m ≠ n) : (g.update n d) m = g m := by simp [update, h]

theorem update_overwrite {E : Type*} (g : Assignment E) (n : Nat) (x y : E) :
    (g.update n x).update n y = g.update n y := by
  funext m; simp [update]; split <;> rfl

theorem update_comm {E : Type*} (g : Assignment E) {n m : Nat} (x y : E)
    (h : n ≠ m) : (g.update n x).update m y = (g.update m y).update n x := by
  funext k; simp [update]; by_cases hn : k = n <;> by_cases hm : k = m <;> simp_all

theorem update_self {E : Type*} (g : Assignment E) (n : Nat) :
    g.update n (g n) = g := by
  funext i; simp [update]; intro h; exact congrArg g h.symm

end Assignment

-- ════════════════════════════════════════════════════════════════
-- Partial Assignments
-- @cite{spector-2025} @cite{beaver-krahmer-2001}
-- ════════════════════════════════════════════════════════════════

/-- Partial assignment: variables may be undefined (`none`).

    Used in trivalent semantics (@cite{spector-2025}, @cite{beaver-krahmer-2001})
    where `g(x) = none` means variable `x` is not valued, yielding
    undefinedness (`#`) in predicate application. -/
abbrev PartialAssign (D : Type*) := Nat → Option D

namespace PartialAssign

variable {D : Type*}

/-- A partial assignment that values no variables. -/
def empty : PartialAssign D := λ _ => none

/-- Update a partial assignment at index `n`. -/
def update (g : PartialAssign D) (n : Nat) (d : D) : PartialAssign D :=
  λ m => if m = n then some d else g m

/-- Whether variable `n` is valued by `g`. -/
def valued (g : PartialAssign D) (n : Nat) : Bool :=
  (g n).isSome

/-- The `U(x)` / `isValued` predicate: `x` is valued.
    @cite{spector-2025} §2.2.2: always bivalent (never undefined). -/
def isValued (g : PartialAssign D) (n : Nat) : Bool :=
  g.valued n

@[simp] theorem valued_update_at (g : PartialAssign D) (n : Nat) (d : D) :
    (g.update n d).valued n = true := by simp [update, valued]

@[simp] theorem valued_update_ne (g : PartialAssign D) {n m : Nat} (d : D)
    (h : m ≠ n) : (g.update n d).valued m = g.valued m := by
  simp [update, valued, h]

theorem valued_empty (n : Nat) : (empty (D := D)).valued n = false := rfl

/-- Coerce a total assignment to a partial assignment (always valued). -/
def ofTotal (g : Assignment D) : PartialAssign D :=
  λ n => some (g n)

theorem valued_ofTotal (g : Assignment D) (n : Nat) :
    (ofTotal g).valued n = true := rfl

end PartialAssign

-- ════════════════════════════════════════════════════════════════
-- Plural Assignments
-- @cite{van-der-berg-1996} @cite{nouwen-2003} @cite{brasoveanu-2008}
-- @cite{spector-2025} §6
-- ════════════════════════════════════════════════════════════════

/-- Plural assignment: a set of atomic (partial) assignments.

    @cite{spector-2025} §6.2: "contexts are viewed as pairs `(w, G)`,
    where `G` is a set of assignments, a plural assignment." Plural
    assignments track inter-variable dependencies (e.g., which book
    each student read) that individual assignments cannot express.

    Originates in plural dynamic semantics (@cite{van-der-berg-1996},
    @cite{nouwen-2003}, @cite{brasoveanu-2008}). Spector's innovation
    is using them in a static (non-dynamic) setting.

    Uses a structure wrapper to prevent Lean from currying
    `(Nat → Option D) → Prop` into `Nat → Option D → Prop`. -/
@[ext] structure PluralAssign (D : Type*) where
  /-- The membership predicate on atomic assignments. -/
  pred : PartialAssign D → Prop

namespace PluralAssign

variable {D : Type*}

instance : Membership (PartialAssign D) (PluralAssign D) where
  mem G g := G.pred g

/-- Whether `G` contains at least one atomic assignment. -/
def Nonempty (G : PluralAssign D) : Prop := ∃ g, g ∈ G

/-- Restrict a plural assignment to atomic assignments mapping `x` to `a`.
    @cite{spector-2025} §6.2: `G_{x=a}` is the subset of `G` where
    `g(x) = a`. -/
def restrict (G : PluralAssign D) (x : Nat) (a : D) : PluralAssign D :=
  ⟨λ g => g ∈ G ∧ g x = some a⟩

/-- Whether any atomic assignment in `G` is defined for `x`. -/
def defined (G : PluralAssign D) (x : Nat) : Prop :=
  ∃ g, g ∈ G ∧ (g x).isSome

/-- Whether `x` is singular in `G`: there is exactly one value
    assigned to `x` across all atomic assignments in `G`.
    @cite{spector-2025} §6.2: `|G(x)| = 1` — the variable denotes
    an atomic individual. Requires both:
    - **existence**: at least one `g ∈ G` defines `x`
    - **agreement**: all `g ∈ G` that define `x` agree on the value -/
def singular (G : PluralAssign D) (x : Nat) : Prop :=
  ∃ d : D, (∃ g, g ∈ G ∧ g x = some d) ∧
           (∀ g, g ∈ G → (g x).isSome → g x = some d)

/-- The `atomic(x)` predicate for plural assignments (propositional).
    @cite{spector-2025} §6.3: ⟦atomic(x)⟧^{w,G} = 1 if |G(x)| = 1,
    0 if |G(x)| ≠ 1. Replaces `U(x)` from the simplified system.
    Equivalent to `singular`: all assignments in G that define x
    map it to the same value. -/
def isAtomic (G : PluralAssign D) (x : Nat) : Prop :=
  singular G x

/-- The null plural assignment: all possible partial assignments.
    @cite{spector-2025} §6: the starting context contains all pairs. -/
def null : PluralAssign D := ⟨λ _ => True⟩

/-- Build a plural assignment from a predicate. -/
def ofPred (p : PartialAssign D → Prop) : PluralAssign D := ⟨p⟩

/-- Witness-level singularity: `G` assigns `x` uniquely to `d`.
    @cite{spector-2025} §6.2: at least one atomic assignment maps `x` to `d`,
    and all assignments in `G` that define `x` agree on `d`. -/
def singularAt (G : PluralAssign D) (x : Nat) (d : D) : Prop :=
  (∃ g, g ∈ G ∧ g x = some d) ∧ (∀ g, g ∈ G → (g x).isSome → g x = some d)

/-- `singular` is the existential closure of `singularAt`. -/
theorem singular_iff_exists_singularAt (G : PluralAssign D) (x : Nat) :
    G.singular x ↔ ∃ d, G.singularAt x d := Iff.rfl

end PluralAssign

end Core

-- ════════════════════════════════════════════════════════════════
-- Generic Variable Assignment (@cite{partee-1973}, @cite{heim-kratzer-1998})
-- ════════════════════════════════════════════════════════════════

namespace Core.VarAssignment

/-- Generic variable assignment: maps indices to values in domain `D`.
    Instantiate with `D = Entity` for pronoun interpretation (@cite{heim-kratzer-1998})
    or `D = Time` for temporal variable interpretation.

    This is the same type as `Core.Assignment D` (both are `ℕ → D`). The
    alias exists for historical reasons; prefer `Core.Assignment` in new
    code. -/
abbrev VarAssignment (D : Type*) := Nat → D

/-- Modified assignment g[n ↦ d]: update index `n` to value `d`. -/
def updateVar {D : Type*} (g : VarAssignment D) (n : Nat) (d : D) : VarAssignment D :=
  λ i => if i = n then d else g i

/-- Variable denotation: ⟦xₙ⟧^g = g(n). -/
def lookupVar {D : Type*} (n : Nat) (g : VarAssignment D) : D := g n

/-- Lambda abstraction over variable `n`: bind a variable in `body`. -/
def varLambdaAbs {D α : Type*} (n : Nat) (body : VarAssignment D → α) :
    VarAssignment D → D → α :=
  λ g d => body (updateVar g n d)

@[simp]
theorem update_lookup_same {D : Type*} (g : VarAssignment D) (n : Nat) (d : D) :
    lookupVar n (updateVar g n d) = d := by
  simp [lookupVar, updateVar]

@[simp]
theorem update_lookup_other {D : Type*} (g : VarAssignment D)
    (n i : Nat) (d : D) (h : i ≠ n) :
    lookupVar i (updateVar g n d) = lookupVar i g := by
  simp [lookupVar, updateVar, h]

theorem update_update_same {D : Type*} (g : VarAssignment D) (n : Nat) (d₁ d₂ : D) :
    updateVar (updateVar g n d₁) n d₂ = updateVar g n d₂ := by
  funext i; simp [updateVar]; by_cases h : i = n <;> simp [h]

theorem update_self {D : Type*} (g : VarAssignment D) (n : Nat) :
    updateVar g n (g n) = g := by
  funext i; simp only [updateVar]; by_cases h : i = n <;> simp [h]

end Core.VarAssignment
