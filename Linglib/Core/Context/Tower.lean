import Linglib.Core.Context

/-!
# Context Tower

A depth-indexed stack of context shifts unifying the codebase's context-manipulation
mechanisms: Kaplanian indexicals (origin access), shifted indexicals (local access),
De Bruijn temporal indexing (depth-relative access), situation introduction (mood),
and domain expansion (branching time).

The tower is parametric over any context type `C`. `KContext` serves as the canonical
instantiation — it represents what a single context layer looks like. The tower wraps
it with a stack of shifts.

## Key Operations

- `.origin` — the root context (speech-act context, Kaplan's c*)
- `.innermost` — the most deeply embedded context (fold all shifts over origin)
- `.contextAt k` — the context at depth k (fold first k shifts)
- `.push σ` — embed deeper by adding a new shift
- `.root c` — trivial tower (no shifts, depth 0)

## How FA Composes with Towers

FA takes two meanings (function and argument). Both are parameterized by the same
tower. FA applies the function to the argument at that tower. The tower is threaded
as a reader parameter — `ContextTower C → ...` is the enriched meaning type.

## References

- Schlenker, P. (2003). A Plea for Monsters. *Linguistics & Philosophy*.
- Anand, P. & Nevins, A. (2004). Shifty Operators in Changing Contexts. SALT XIV.
- Abusch, D. (1997). Sequence of tense and temporal de re. *L&P* 20.
- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
-/

namespace Core.Context

-- ════════════════════════════════════════════════════════════════
-- § Shift Labels
-- ════════════════════════════════════════════════════════════════

/-- Classification of context shifts by their linguistic source. -/
inductive ShiftLabel where
  | attitude    -- attitude verb embedding (believe, say, want)
  | temporal    -- temporal shift (sequence of tense, historical present)
  | evidential  -- evidential perspective shift (Cumming 2026)
  | mood        -- mood operator (SUBJ situation introduction)
  | quotation   -- direct quotation
  | generic     -- unclassified shift
  deriving DecidableEq, Repr, BEq, Inhabited

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

@[simp] theorem root_innermost (c : C) : (root c).innermost = c := rfl

@[simp] theorem contextAt_zero (t : ContextTower C) : t.contextAt 0 = t.origin := rfl

theorem contextAt_depth (t : ContextTower C) :
    t.contextAt t.depth = t.innermost := by
  simp only [contextAt, innermost, depth, List.take_length]

@[simp] theorem push_origin (t : ContextTower C) (σ : ContextShift C) :
    (t.push σ).origin = t.origin := rfl

@[simp] theorem root_depth (c : C) : (root c).depth = 0 := rfl

theorem push_depth (t : ContextTower C) (σ : ContextShift C) :
    (t.push σ).depth = t.depth + 1 := by
  simp [push, depth]

@[simp] theorem root_contextAt (c : C) (k : ℕ) : (root c).contextAt k = c := by
  simp [root, contextAt]

/-- Pushing a shift updates the innermost context. -/
theorem push_innermost (t : ContextTower C) (σ : ContextShift C) :
    (t.push σ).innermost = σ.apply t.innermost := by
  simp only [push, innermost, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- In a root tower, all depths return the origin. -/
theorem root_contextAt_eq (c : C) (k : ℕ) : (root c).contextAt k = c := by
  simp [root, contextAt]

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
  deriving DecidableEq, Repr, BEq, Inhabited

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

    English "I" = `⟨.origin, KContext.agent⟩`
    Amharic "I" = `⟨.local, KContext.agent⟩`
    English "now" = `⟨.origin, KContext.time⟩` -/
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

/-- In a root tower, origin and local access agree. -/
theorem root_origin_eq_local (ap₁ ap₂ : AccessPattern C R)
    (h₁ : ap₁.depth = .origin) (h₂ : ap₂.depth = .local)
    (hProj : ap₁.project = ap₂.project) (c : C) :
    ap₁.resolve (ContextTower.root c) = ap₂.resolve (ContextTower.root c) := by
  simp [resolve, h₁, h₂, hProj]

end AccessPattern

end Core.Context
