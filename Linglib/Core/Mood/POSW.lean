import Mathlib.Order.Basic

/-!
# Partially Ordered Set of Worlds (POSW)
@cite{portner-2018} @cite{kratzer-1981} @cite{stalnaker-1978} @cite{farkas-2003} @cite{condoravdi-lauer-2012}

@cite{portner-2018} (Ch. 4) argues that the apparently disparate "mood"
phenomena — verbal mood (indicative/subjunctive selection by attitudes),
sentence mood (declarative/imperative/interrogative force), and modal
flavor (epistemic/deontic/bouletic) — all share a single mathematical
substrate: a **partially ordered set of worlds** that the relevant
linguistic objects update or quantify over. The pair-of-information-and-
ordering structure with `+`/`⋆` updates predates @cite{portner-2018};
@cite{farkas-2003} introduces it for assertion-vs-direction, and the
Stalnakerian context-set/Kratzerian ordering-source decomposition behind
it goes back to @cite{stalnaker-1978} and @cite{kratzer-1981}.
@cite{condoravdi-lauer-2012} works out the preferential-modal side
(desire predicates over orderings) in detail.

A POSW is a pair `c = ⟨cs_c, <_c⟩` where:
- `cs_c ⊆ W` is a non-empty set of worlds (the "context set" — the
  informational component, à la @cite{stalnaker-1978});
- `<_c` is a (reflexive transitive) preorder on `cs_c` (the "ordering
  source" component, à la @cite{kratzer-1981}).

There are two canonical updates:
- **`+`-update** refines `cs` by intersection: `c + p` keeps only
  `cs`-worlds where `p` holds. Targets the *informational* component.
- **`⋆`-update** refines `<` by promoting `p`-worlds: in `c ⋆ p`,
  the ordering on `cs` is the original ordering plus the constraint
  that any world satisfying `p` is at least as good as one that
  doesn't. Targets the *preferential* component.

There are two canonical necessity modals:
- `□_cs p` — informational necessity: `p` holds at every world in `cs`.
- `□_< p` — preferential necessity: `p` holds at every `<`-best world
  in `cs`.

Portner's central architectural insight is that *what differs across
mood-and-modality phenomena is which POSW component is targeted*, not
the substrate itself. Belief vs. desire is `□_cs` vs. `□_<` over the
same agent's POSW; assertion vs. directive is `+` vs. `⋆` over the
discourse POSW; epistemic vs. deontic modal flavor is the same split
again.

The `+` and `⋆` updates target *disjoint* POSW components — that is the
content of `updates_target_disjoint_components` below, which is the
mathematical core of Portner's unification thesis.

## Notes
- We work with `W → Prop` (classical propositions) rather than `W → Bool`
  (decidable propositions) because POSW is the foundational substrate;
  decidability concerns belong downstream.
- We use a *reflexive* partial preorder `lt` (so `lt w w` for `w ∈ cs`),
  matching @cite{portner-2018}'s "at-least-as-good" reading of `<`.
  (The name `lt` is kept for parallelism with @cite{portner-2018}'s `<`
  notation; mathematically it is a reflexive `≤`.)
-/

namespace Core.Mood

universe u

/-- A **partially ordered set of worlds** (POSW): a non-empty subset
    `cs` of worlds equipped with a reflexive transitive ordering `lt`
    on `cs`. @cite{portner-2018} (Ch. 4); the underlying pair structure
    appears already in @cite{farkas-2003}.

    Non-emptiness is not enforced at the type level — empty POSWs are
    pathological but algebraically permitted (e.g., the result of
    `+`-updating with an inconsistent proposition). Operations make
    sense regardless. -/
structure POSW (W : Type u) where
  /-- The context set: worlds compatible with the POSW's information. -/
  cs : W → Prop
  /-- The ordering: `lt w v` means w is at least as good as v.
      Reflexive on `cs`, transitive on `cs`. -/
  lt : W → W → Prop
  /-- Reflexivity on the context set. -/
  lt_refl : ∀ w, cs w → lt w w
  /-- Transitivity on the context set. -/
  lt_trans : ∀ w u v, cs w → cs u → cs v → lt w u → lt u v → lt w v

namespace POSW

variable {W : Type u}

/-! ## §1. Updates: `+` and `⋆` -/

/-- **`+`-update** (@cite{portner-2018}, Ch. 4 §4.1; @cite{farkas-2003}):
    refine `cs` by intersection with `p`. Leaves `<` untouched.

    Used by assertion (Stalnakerian context-set update) and by `□_cs`
    modals' restriction. -/
def plus (c : POSW W) (p : W → Prop) : POSW W where
  cs := fun w => c.cs w ∧ p w
  lt := c.lt
  lt_refl  := fun w hw => c.lt_refl w hw.1
  lt_trans := fun w u v hw hu hv => c.lt_trans w u v hw.1 hu.1 hv.1

/-- **`⋆`-update** (@cite{portner-2018}, Ch. 4 §4.1; @cite{farkas-2003}):
    refine `<` by promoting `p`-worlds. The new ordering keeps the old
    ordering and additionally requires that whenever the upper world
    satisfies `p`, the lower world does too.

    Used by directives (To-Do List update à la @cite{portner-2004})
    and by `□_<` modals' refinement (@cite{condoravdi-lauer-2012}). -/
def star (c : POSW W) (p : W → Prop) : POSW W where
  cs := c.cs
  lt := fun w v => c.lt w v ∧ (p v → p w)
  lt_refl  := fun w hw => ⟨c.lt_refl w hw, fun hp => hp⟩
  lt_trans := fun w u v hw hu hv => fun ⟨hwu, hwu'⟩ ⟨huv, huv'⟩ =>
    ⟨c.lt_trans w u v hw hu hv hwu huv, fun hp => hwu' (huv' hp)⟩

/-! ## §2. Modals: `□_cs` and `□_<` -/

/-- A world is **best** in `c` if it is in `cs` and at least as good
    as every other `cs`-world. The quantification domain of
    @cite{portner-2018}'s preferential necessity modal `□_<`. -/
def best (c : POSW W) (w : W) : Prop :=
  c.cs w ∧ ∀ v, c.cs v → c.lt v w

/-- **Informational necessity** `□_cs` (@cite{portner-2018}, Ch. 4 §4.1):
    `p` holds at every world in the context set. The semantics of
    `believe` and the Stalnakerian context-set entailment. -/
def boxCs (c : POSW W) (p : W → Prop) : Prop :=
  ∀ w, c.cs w → p w

/-- **Preferential necessity** `□_<` (@cite{portner-2018}, Ch. 4 §4.1):
    `p` holds at every `<`-best world in the context set. The
    semantics of `want` and Kratzerian deontic/bouletic modals
    (@cite{kratzer-1981}, @cite{condoravdi-lauer-2012}). -/
def boxLt (c : POSW W) (p : W → Prop) : Prop :=
  ∀ w, c.best w → p w

/-! ## §3. Algebraic facts -/

@[simp] theorem plus_cs (c : POSW W) (p : W → Prop) (w : W) :
    (c.plus p).cs w ↔ c.cs w ∧ p w := Iff.rfl

@[simp] theorem plus_lt (c : POSW W) (p : W → Prop) :
    (c.plus p).lt = c.lt := rfl

@[simp] theorem star_cs (c : POSW W) (p : W → Prop) :
    (c.star p).cs = c.cs := rfl

@[simp] theorem star_lt (c : POSW W) (p : W → Prop) (w v : W) :
    (c.star p).lt w v ↔ c.lt w v ∧ (p v → p w) := Iff.rfl

/-- **Portner's central insight**: the two updates target *disjoint*
    POSW components. `+` revises `cs` and leaves `lt` alone; `⋆`
    revises `lt` and leaves `cs` alone.

    This is the mathematical content of @cite{portner-2018}'s
    unification thesis (Ch. 4): the surface diversity of mood phenomena
    reduces to *which component of the same substrate gets touched*. -/
theorem updates_target_disjoint_components (c : POSW W) (p : W → Prop) :
    (c.plus p).lt = c.lt ∧ (c.star p).cs = c.cs :=
  ⟨rfl, rfl⟩

/-- `+`-update is monotone in the proposition (intersection lemma). -/
theorem plus_cs_mono (c : POSW W) (p q : W → Prop)
    (h : ∀ w, p w → q w) (w : W) :
    (c.plus p).cs w → (c.plus q).cs w :=
  fun ⟨hcs, hp⟩ => ⟨hcs, h w hp⟩

/-- `+`-update with a tautology is the identity on `cs`. -/
theorem plus_top_cs (c : POSW W) (w : W) :
    (c.plus (fun _ => True)).cs w ↔ c.cs w := by
  simp [plus]

/-- `□_cs` is upward monotone. -/
theorem boxCs_mono (c : POSW W) (p q : W → Prop)
    (h : ∀ w, p w → q w) :
    c.boxCs p → c.boxCs q :=
  fun hp w hw => h w (hp w hw)

/-- `□_<` is upward monotone. -/
theorem boxLt_mono (c : POSW W) (p q : W → Prop)
    (h : ∀ w, p w → q w) :
    c.boxLt p → c.boxLt q :=
  fun hp w hw => h w (hp w hw)

/-- After `+`-updating with `p`, `p` becomes informationally necessary.
    The Stalnakerian assertion principle: asserting `p` makes `p`
    common ground. @cite{stalnaker-1978}, @cite{portner-2018} (Ch. 4). -/
theorem boxCs_plus_self (c : POSW W) (p : W → Prop) :
    (c.plus p).boxCs p :=
  fun _ hw => hw.2

/-! ## §4. Refinement preorder

A POSW is more *refined* than another when it carries strictly more
information: a smaller context set, and a smaller (i.e., more
discriminating) ordering relation. In the @cite{portner-2018} update
algebra, both `+`-update and `⋆`-update produce a refinement of the
input POSW — refinement is what *update* means.

The order convention follows the partition / `Setoid` lattice in
mathlib: **finer ≤ coarser**, **more constrained ≤ less constrained**.
The trivial POSW (`cs = ⊤`, `lt = ⊤`) sits at the top; a fully
informative POSW (smaller `cs`, smaller `lt`) sits below.

The `boxCs_anti` lemma gives the modal counterpart: refining the POSW
*strengthens* informational necessity. `boxLt` admits no parallel
result in general — refinement can change which worlds are best.

(The componentwise refinement preorder is not stated in
@cite{portner-2018}; it is our linglib addition, packaging the
"update means refine" intuition into a `Preorder` instance so the
update lemmas factor through `≤` and downstream `Setoid`-style
machinery composes.) -/

/-- Refinement order on POSWs: `c₁ ≤ c₂` iff `c₁` is at least as
    constrained as `c₂` — its context set is a subset of `c₂`'s,
    and its ordering relation is a subset of `c₂`'s (fewer pairs are
    "at-least-as-good as" each other under `c₁` than under `c₂`).
    Both POSW updates land in the input's lower set. -/
instance instPreorder : Preorder (POSW W) where
  le c₁ c₂ :=
    (∀ w, c₁.cs w → c₂.cs w) ∧ (∀ w v, c₁.lt w v → c₂.lt w v)
  le_refl _ := ⟨fun _ h => h, fun _ _ h => h⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨fun w h => h₂₃.1 w (h₁₂.1 w h),
     fun w v h => h₂₃.2 w v (h₁₂.2 w v h)⟩

theorem le_iff (c₁ c₂ : POSW W) :
    c₁ ≤ c₂ ↔
      (∀ w, c₁.cs w → c₂.cs w) ∧ (∀ w v, c₁.lt w v → c₂.lt w v) :=
  Iff.rfl

/-- `+`-update lands below the input: refining `cs` by intersection
    with `p` can only constrain the POSW further. -/
theorem plus_le_self (c : POSW W) (p : W → Prop) : c.plus p ≤ c :=
  ⟨fun _ h => h.1, fun _ _ h => h⟩

/-- `⋆`-update lands below the input: refining `lt` with the
    `p`-promotion constraint can only constrain the POSW further. -/
theorem star_le_self (c : POSW W) (p : W → Prop) : c.star p ≤ c :=
  ⟨fun _ h => h, fun _ _ h => h.1⟩

/-- `+`-update is monotone in the underlying POSW: refining `c₁`
    against `c₂` is preserved by adding the same `+`-update on top. -/
theorem plus_mono {c₁ c₂ : POSW W} (h : c₁ ≤ c₂) (p : W → Prop) :
    c₁.plus p ≤ c₂.plus p :=
  ⟨fun w hp => ⟨h.1 w hp.1, hp.2⟩,
   fun w v hlt => h.2 w v hlt⟩

/-- `⋆`-update is monotone in the underlying POSW. -/
theorem star_mono {c₁ c₂ : POSW W} (h : c₁ ≤ c₂) (p : W → Prop) :
    c₁.star p ≤ c₂.star p :=
  ⟨fun w hcs => h.1 w hcs,
   fun w v hlt => ⟨h.2 w v hlt.1, hlt.2⟩⟩

/-- Refining the POSW *strengthens* informational necessity: if `c₁`
    is more refined than `c₂` and `p` is informationally necessary at
    `c₂`, then `p` is informationally necessary at `c₁` too.

    `boxLt` does *not* admit a parallel anti-monotonicity result:
    refining the POSW changes which worlds are best, and the change
    can move `p`-satisfying worlds either into or out of the best
    set. -/
theorem boxCs_anti (c₁ c₂ : POSW W) (h : c₁ ≤ c₂) (p : W → Prop) :
    c₂.boxCs p → c₁.boxCs p :=
  fun hbox w hcs => hbox w (h.1 w hcs)

end POSW
end Core.Mood
