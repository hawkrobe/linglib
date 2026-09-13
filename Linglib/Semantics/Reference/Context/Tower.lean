import Linglib.Semantics.Reference.Context.Basic
import Linglib.Semantics.Reference.Rigidity

/-!
# Context Tower
[abusch-1997] [anand-nevins-2004] [cumming-2026] [schlenker-2003]

A depth-indexed stack of context shifts unifying the codebase's context-manipulation
mechanisms: Kaplanian indexicals (origin access), shifted indexicals (local access),
De Bruijn temporal indexing (depth-relative access), situation introduction (mood),
and domain expansion (branching time).

The tower is parametric over any context type `C`. `Context` serves as the canonical
instantiation — it represents what a single context layer looks like. The tower wraps
it with a stack of shifts.

## Main definitions

- `ContextTower.origin`, `ContextTower.innermost`, `ContextTower.contextAt`,
  `ContextTower.push`, `ContextTower.root`.
- `AccessPattern`: a depth specification plus a projection, resolved against a tower;
  `AccessPattern.origin` and `AccessPattern.innermost` read a coordinate of the speech-act
  context and of the innermost context respectively.
- `AccessPattern.Stable`: invariance of an access pattern under a shift.

-/

namespace Reference

-- ════════════════════════════════════════════════════════════════
-- § Shift Labels
-- ════════════════════════════════════════════════════════════════

/-- Classification of context shifts by their linguistic source. -/
inductive ShiftLabel where
  | attitude    -- attitude verb embedding (believe, say, want)
  | temporal    -- temporal shift (sequence of tense, historical present)
  | evidential  -- evidential perspective shift ([cumming-2026])
  | mood        -- mood operator (SUBJ situation introduction)
  | perspective -- full perspective shift (agent + time + world)
  | quotation   -- direct quotation
  | clauseChain -- clause chain scope (final verb TAM scopes over medial clauses)
  | roleShift   -- sign language Role Shift (viewpoint + perspective shift)
  | generic     -- unclassified shift
  deriving DecidableEq, Repr, Inhabited

-- ════════════════════════════════════════════════════════════════
-- § Context Shift
-- ════════════════════════════════════════════════════════════════

/-- A single context shift: a function transforming a context, tagged with
    its linguistic source. -/
structure ContextShift (C : Type*) where
  /-- The context transformation -/
  apply : C → C
  /-- What kind of linguistic operation introduced this shift -/
  label : ShiftLabel

-- ════════════════════════════════════════════════════════════════
-- § Context Tower
-- ════════════════════════════════════════════════════════════════

/-- A context tower: an origin context with a stack of shifts.

    The origin is the speech-act context (Kaplan's c*). Each shift corresponds
    to an embedding operator (attitude verb, temporal shift, mood operator).
    Contexts at each depth are computed by folding shifts over the origin —
    the path condition holds by construction. -/
structure ContextTower (C : Type*) where
  /-- The root context (speech-act context) -/
  origin : C
  /-- Shifts from outermost to innermost. `shifts[0]` is the first embedding
      (e.g., the matrix attitude verb); the last element is the deepest. -/
  shifts : List (ContextShift C)

namespace ContextTower

variable {C : Type*}

/-- Embedding depth (number of shifts). -/
def depth (t : ContextTower C) : ℕ := t.shifts.length

/-- The context at depth k, computed by folding the first k shifts over
    the origin. Saturates at tower depth: `contextAt k` for `k ≥ depth`
    returns the innermost context.

    - `contextAt 0` = origin
    - `contextAt depth` = innermost -/
def contextAt (t : ContextTower C) (k : ℕ) : C :=
  (t.shifts.take k).foldl (λ c σ => σ.apply c) t.origin

/-- The innermost (most deeply embedded) context: fold all shifts over origin. -/
def innermost (t : ContextTower C) : C :=
  t.shifts.foldl (λ c σ => σ.apply c) t.origin

/-- Trivial tower with no shifts. -/
def root (c : C) : ContextTower C := ⟨c, []⟩

/-- Push a new shift onto the tower (embed one level deeper). -/
def push (t : ContextTower C) (σ : ContextShift C) : ContextTower C :=
  ⟨t.origin, t.shifts ++ [σ]⟩

-- ════════════════════════════════════════════════════════════════
-- § Algebraic Properties
-- ════════════════════════════════════════════════════════════════

@[simp] theorem root_origin (c : C) : (root c).origin = c := rfl

@[simp] theorem root_innermost (c : C) : (root c).innermost = c := rfl

@[simp] theorem contextAt_zero (t : ContextTower C) : t.contextAt 0 = t.origin := rfl

@[simp] theorem contextAt_depth (t : ContextTower C) :
    t.contextAt t.depth = t.innermost := by
  simp only [contextAt, innermost, depth, List.take_length]

/-- Past the tower depth, `contextAt` saturates at the innermost context.
    This is because `List.take k` on a list shorter than `k` returns the
    whole list. -/
theorem contextAt_saturates (t : ContextTower C) (k : ℕ) (hk : t.depth ≤ k) :
    t.contextAt k = t.innermost := by
  simp only [contextAt, innermost, depth] at *
  rw [List.take_of_length_le hk]

@[simp] theorem push_origin (t : ContextTower C) (σ : ContextShift C) :
    (t.push σ).origin = t.origin := rfl

@[simp] theorem root_depth (c : C) : (root c).depth = 0 := rfl

@[simp] theorem push_depth (t : ContextTower C) (σ : ContextShift C) :
    (t.push σ).depth = t.depth + 1 := by
  simp [push, depth]

@[simp] theorem root_contextAt (c : C) (k : ℕ) : (root c).contextAt k = c := by
  simp [root, contextAt]

/-- Pushing a shift updates the innermost context. -/
@[simp] theorem push_innermost (t : ContextTower C) (σ : ContextShift C) :
    (t.push σ).innermost = σ.apply t.innermost := by
  simp only [push, innermost, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Below the tower depth, a push leaves the context at each depth unchanged. -/
theorem push_contextAt_of_le (t : ContextTower C) (σ : ContextShift C) {k : ℕ}
    (hk : k ≤ t.depth) : (t.push σ).contextAt k = t.contextAt k := by
  simp only [contextAt, push]
  rw [List.take_append_of_le_length hk]

/-- Beyond the tower depth, a push saturates at the shifted innermost context. -/
theorem push_contextAt_of_lt (t : ContextTower C) (σ : ContextShift C) {k : ℕ}
    (hk : t.depth < k) : (t.push σ).contextAt k = σ.apply t.innermost := by
  rw [← push_innermost, contextAt_saturates _ _ (by rw [push_depth]; exact hk)]

@[simp] theorem push_contextAt_succ_depth (t : ContextTower C) (σ : ContextShift C) :
    (t.push σ).contextAt (t.depth + 1) = σ.apply t.innermost :=
  push_contextAt_of_lt _ _ (Nat.lt_succ_self _)

end ContextTower

-- ════════════════════════════════════════════════════════════════
-- § Depth Specification
-- ════════════════════════════════════════════════════════════════

/-- Which depth to read from in a tower.

    - `.origin`: always read from depth 0 (speech-act context)
    - `.local`: always read from the innermost context
    - `.relative k`: read from depth k -/
inductive DepthSpec where
  | origin
  | local
  | relative (k : ℕ)
  deriving DecidableEq, Repr, Inhabited

namespace DepthSpec

/-- Resolve to a concrete depth index given the tower depth. -/
def resolve (d : DepthSpec) (towerDepth : ℕ) : ℕ :=
  match d with
  | .origin => 0
  | .local => towerDepth
  | .relative k => k

@[simp] theorem origin_resolve (n : ℕ) : DepthSpec.origin.resolve n = 0 := rfl
@[simp] theorem local_resolve (n : ℕ) : DepthSpec.local.resolve n = n := rfl
@[simp] theorem relative_resolve (k n : ℕ) : (DepthSpec.relative k).resolve n = k := rfl

end DepthSpec

-- ════════════════════════════════════════════════════════════════
-- § Access Patterns
-- ════════════════════════════════════════════════════════════════

/-- An access pattern: a depth specification plus a projection from context
    to value.

    This is how context-dependent expressions specify what they read:
    - `depth` says which tower layer to read from
    - `project` says which coordinate to extract

    English "I" = `⟨.origin, Context.agent⟩`
    Amharic "I" = `⟨.local, Context.agent⟩`
    English "now" = `⟨.origin, Context.time⟩` -/
structure AccessPattern (C : Type*) (R : Type*) where
  /-- Which depth to read from -/
  depth : DepthSpec
  /-- Which coordinate to extract -/
  project : C → R

namespace AccessPattern

variable {C R S : Type*}

/-- Resolve an access pattern against a tower. -/
def resolve (ap : AccessPattern C R) (t : ContextTower C) : R :=
  ap.project (t.contextAt (ap.depth.resolve t.depth))

/-- Map a function over the projected result. -/
def map (ap : AccessPattern C R) (f : R → S) : AccessPattern C S :=
  ⟨ap.depth, f ∘ ap.project⟩

/-- Origin access is invariant under push. This is the formal content of
    Kaplan's thesis: expressions reading from the speech-act context are
    unaffected by embedding operators. -/
theorem origin_stable (ap : AccessPattern C R) (hd : ap.depth = .origin)
    (t : ContextTower C) (σ : ContextShift C) :
    ap.resolve (t.push σ) = ap.resolve t := by
  simp only [resolve, hd, DepthSpec.origin_resolve,
             ContextTower.contextAt_zero, ContextTower.push_origin]

/-- Local access updates with push: the innermost projection tracks the
    new shift. -/
theorem local_updates (ap : AccessPattern C R) (hd : ap.depth = .local)
    (t : ContextTower C) (σ : ContextShift C) :
    ap.resolve (t.push σ) = ap.project (σ.apply t.innermost) := by
  simp only [resolve, hd, DepthSpec.local_resolve, ContextTower.push_depth]
  rw [← ContextTower.push_depth, ContextTower.contextAt_depth,
      ContextTower.push_innermost]

/-- An access pattern is *stable* under a shift when pushing that shift onto any
    tower leaves its resolution unchanged. This relation underlies both
    Kaplan-compliance (`Reference/Kaplan.lean`: an expression stable under
    *every* shift) and monsterhood (a shift that destabilizes *some* expression),
    the two being its ∀-over-shifts and ∃-over-expressions projections. -/
def Stable (ap : AccessPattern C R) (σ : ContextShift C) : Prop :=
  ∀ t, ap.resolve (t.push σ) = ap.resolve t

/-- Origin-depth access is stable under every shift — the access-pattern form
    of `origin_stable`, and the sufficient condition for Kaplan-compliance. -/
theorem stable_of_depth_origin (ap : AccessPattern C R) (hd : ap.depth = .origin)
    (σ : ContextShift C) : ap.Stable σ :=
  fun t => origin_stable ap hd t σ

/-- Read the coordinate `f` of the speech-act context: the access pattern of a Kaplanian
pure indexical. -/
def origin (f : C → R) : AccessPattern C R := ⟨.origin, f⟩

/-- Read the coordinate `f` of the innermost context: the access pattern of a shifted
indexical. -/
def innermost (f : C → R) : AccessPattern C R := ⟨.local, f⟩

@[simp] theorem origin_resolve (f : C → R) (t : ContextTower C) :
    (origin f).resolve t = f t.origin := rfl

@[simp] theorem innermost_resolve (f : C → R) (t : ContextTower C) :
    (innermost f).resolve t = f t.innermost := by
  simp [innermost, resolve]

theorem stable_origin (f : C → R) (σ : ContextShift C) : (origin f).Stable σ :=
  stable_of_depth_origin _ rfl σ

end AccessPattern

end Reference
