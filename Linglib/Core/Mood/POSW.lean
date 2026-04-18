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

A POSW is a pair `c = ⟨cs_c, ≤_c⟩` where:
- `cs_c ⊆ W` is a non-empty set of worlds (the "context set" — the
  informational component, à la @cite{stalnaker-1978});
- `≤_c` is a reflexive transitive preorder on `cs_c` (the "ordering
  source" component, à la @cite{kratzer-1981}). @cite{portner-2018}
  writes this `<` and reads it "at-least-as-good as", which is the
  reflexive `≤` reading; we use `le` for mathlib alignment.

There are two canonical updates:
- **`+`-update** refines `cs` by intersection: `c + p` keeps only
  `cs`-worlds where `p` holds. Targets the *informational* component.
- **`⋆`-update** refines `≤` by promoting `p`-worlds: in `c ⋆ p`,
  the ordering on `cs` is the original ordering plus the constraint
  that any world satisfying `p` is at least as good as one that
  doesn't. Targets the *preferential* component.

There are two canonical necessity modals:
- `□_cs p` — informational necessity: `p` holds at every world in `cs`.
- `□_≤ p` — preferential necessity: `p` holds at every `≤`-best world
  in `cs`.

Portner's central architectural insight is that *what differs across
mood-and-modality phenomena is which POSW component is targeted*, not
the substrate itself. Belief vs. desire is `□_cs` vs. `□_≤` over the
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
- @cite{portner-2018} (Ch. 4, footnote 3) flags a strict-typing wart:
  on his definition `c + p` is technically not a POSW because the
  ordering is not restricted to the new (smaller) `cs`. We inherit the
  same wart (our `plus` keeps `c.le` unchanged), and the same
  workaround: read the `le_refl` / `le_trans` axioms as conditioned on
  `cs`-membership, so behaviour outside `cs` is irrelevant.
- We use a reflexive partial preorder `le` matching the partition /
  `Setoid` lattice convention (finer ≤ coarser).
-/

namespace Core.Mood

universe u

/-- A **partially ordered set of worlds** (POSW): a non-empty subset
    `cs` of worlds equipped with a reflexive transitive ordering `le`
    on `cs`. @cite{portner-2018} (Ch. 4) writes the ordering `<`
    (at-least-as-good); we use `le` for mathlib alignment. The
    underlying pair structure appears already in @cite{farkas-2003}.

    Non-emptiness is not enforced at the type level — empty POSWs are
    pathological but algebraically permitted (e.g., the result of
    `+`-updating with an inconsistent proposition). Operations make
    sense regardless. -/
structure POSW (W : Type u) where
  /-- The context set: worlds compatible with the POSW's information. -/
  cs : W → Prop
  /-- The ordering: `le w v` means w is at least as good as v.
      Reflexive on `cs`, transitive on `cs`. -/
  le : W → W → Prop
  /-- Reflexivity on the context set. -/
  le_refl : ∀ w, cs w → le w w
  /-- Transitivity on the context set. -/
  le_trans : ∀ w u v, cs w → cs u → cs v → le w u → le u v → le w v

namespace POSW

variable {W : Type u}

/-! ## §1. Updates: `+` and `⋆` -/

/-- **`+`-update** (@cite{portner-2018}, Ch. 4 §4.1; @cite{farkas-2003}):
    refine `cs` by intersection with `p`. Leaves `≤` untouched.

    Used by assertion (Stalnakerian context-set update) and by `□_cs`
    modals' restriction.

    *Footnote 3 wart*: the resulting `le` is not strictly restricted to
    the new `cs`, but the structure satisfies the (cs-conditioned)
    POSW axioms. -/
def plus (c : POSW W) (p : W → Prop) : POSW W where
  cs := fun w => c.cs w ∧ p w
  le := c.le
  le_refl  := fun w hw => c.le_refl w hw.1
  le_trans := fun w u v hw hu hv => c.le_trans w u v hw.1 hu.1 hv.1

/-- **`⋆`-update** (@cite{portner-2018}, Ch. 4 §4.1; @cite{farkas-2003}):
    refine `≤` by promoting `p`-worlds. The new ordering keeps the old
    ordering and additionally requires that whenever the upper world
    satisfies `p`, the lower world does too.

    Used by directives (To-Do List update à la @cite{portner-2004})
    and by `□_≤` modals' refinement (@cite{condoravdi-lauer-2012}). -/
def star (c : POSW W) (p : W → Prop) : POSW W where
  cs := c.cs
  le := fun w v => c.le w v ∧ (p v → p w)
  le_refl  := fun w hw => ⟨c.le_refl w hw, fun hp => hp⟩
  le_trans := fun w u v hw hu hv => fun ⟨hwu, hwu'⟩ ⟨huv, huv'⟩ =>
    ⟨c.le_trans w u v hw hu hv hwu huv, fun hp => hwu' (huv' hp)⟩

/-! ## §2. Modals: `□_cs` and `□_≤` -/

/-- A world is **best** in `c` if it is in `cs` and at least as good
    as every other `cs`-world. The quantification domain of
    @cite{portner-2018}'s preferential necessity modal `□_≤`. -/
def best (c : POSW W) (w : W) : Prop :=
  c.cs w ∧ ∀ v, c.cs v → c.le v w

/-- **Informational necessity** `□_cs` (@cite{portner-2018}, Ch. 4 §4.1):
    `p` holds at every world in the context set. The semantics of
    `believe` and the Stalnakerian context-set entailment. -/
def boxCs (c : POSW W) (p : W → Prop) : Prop :=
  ∀ w, c.cs w → p w

/-- **Preferential necessity** `□_≤` (@cite{portner-2018}, Ch. 4 §4.1):
    `p` holds at every `≤`-best world in the context set. The
    semantics of `want` and Kratzerian deontic/bouletic modals
    (@cite{kratzer-1981}, @cite{condoravdi-lauer-2012}). -/
def boxLe (c : POSW W) (p : W → Prop) : Prop :=
  ∀ w, c.best w → p w

@[deprecated boxLe (since := "2026-04-18")]
abbrev boxLt (c : POSW W) (p : W → Prop) : Prop := c.boxLe p

/-! ## §3. Algebraic facts -/

@[simp] theorem plus_cs (c : POSW W) (p : W → Prop) (w : W) :
    (c.plus p).cs w ↔ c.cs w ∧ p w := Iff.rfl

@[simp] theorem plus_le (c : POSW W) (p : W → Prop) :
    (c.plus p).le = c.le := rfl

@[simp] theorem star_cs (c : POSW W) (p : W → Prop) :
    (c.star p).cs = c.cs := rfl

@[simp] theorem star_le (c : POSW W) (p : W → Prop) (w v : W) :
    (c.star p).le w v ↔ c.le w v ∧ (p v → p w) := Iff.rfl

/-- **Portner's central insight**: the two updates target *disjoint*
    POSW components. `+` revises `cs` and leaves `le` alone; `⋆`
    revises `le` and leaves `cs` alone.

    This is the mathematical content of @cite{portner-2018}'s
    unification thesis (Ch. 4): the surface diversity of mood phenomena
    reduces to *which component of the same substrate gets touched*. -/
theorem updates_target_disjoint_components (c : POSW W) (p : W → Prop) :
    (c.plus p).le = c.le ∧ (c.star p).cs = c.cs :=
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

/-- `□_≤` is upward monotone. -/
theorem boxLe_mono (c : POSW W) (p q : W → Prop)
    (h : ∀ w, p w → q w) :
    c.boxLe p → c.boxLe q :=
  fun hp w hw => h w (hp w hw)

@[deprecated boxLe_mono (since := "2026-04-18")]
theorem boxLt_mono (c : POSW W) (p q : W → Prop)
    (h : ∀ w, p w → q w) :
    c.boxLe p → c.boxLe q :=
  boxLe_mono c p q h

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
The trivial POSW (`cs = ⊤`, `le = ⊤`) sits at the top; a fully
informative POSW (smaller `cs`, smaller `le`) sits below.

The `boxCs_anti` lemma gives the modal counterpart: refining the POSW
*strengthens* informational necessity. `boxLe` admits no parallel
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
instance : Preorder (POSW W) where
  le c₁ c₂ :=
    (∀ w, c₁.cs w → c₂.cs w) ∧ (∀ w v, c₁.le w v → c₂.le w v)
  le_refl _ := ⟨fun _ h => h, fun _ _ h => h⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨fun w h => h₂₃.1 w (h₁₂.1 w h),
     fun w v h => h₂₃.2 w v (h₁₂.2 w v h)⟩

theorem le_iff (c₁ c₂ : POSW W) :
    c₁ ≤ c₂ ↔
      (∀ w, c₁.cs w → c₂.cs w) ∧ (∀ w v, c₁.le w v → c₂.le w v) :=
  Iff.rfl

/-- `+`-update lands below the input: refining `cs` by intersection
    with `p` can only constrain the POSW further. -/
theorem plus_le_self (c : POSW W) (p : W → Prop) : c.plus p ≤ c :=
  ⟨fun _ h => h.1, fun _ _ h => h⟩

/-- `⋆`-update lands below the input: refining `le` with the
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

    `boxLe` does *not* admit a parallel anti-monotonicity result:
    refining the POSW changes which worlds are best, and the change
    can move `p`-satisfying worlds either into or out of the best
    set. -/
theorem boxCs_anti (c₁ c₂ : POSW W) (h : c₁ ≤ c₂) (p : W → Prop) :
    c₂.boxCs p → c₁.boxCs p :=
  fun hbox w hcs => hbox w (h.1 w hcs)

/-! ## §5. Subtype Preorder

`POSW W` is *not* a `Preorder W` (the `le` axioms are conditioned on
`cs`-membership). But it *is* a `Preorder (Subtype c.cs)` — the
`cs`-restricted subtype carries an unconditional reflexive transitive
preorder, courtesy of `le_refl` and `le_trans`. This makes mathlib's
`Preorder` API (transitivity tactics, `le_trans`, `le_refl`, …)
available on the in-context portion. -/

/-- The `cs`-restricted subtype carries a reflexive transitive
    preorder: the conditioning on `cs`-membership becomes
    unconditional once we work in the subtype. Gives access to
    mathlib's `Preorder` API on the in-context worlds. -/
instance instPreorderSubtype (c : POSW W) : Preorder {w // c.cs w} where
  le w v := c.le w.1 v.1
  le_refl w := c.le_refl w.1 w.2
  le_trans w u v := c.le_trans w.1 u.1 v.1 w.2 u.2 v.2

/-! ## §6. The `promote` preorder and `⋆`-update algebra

`⋆`-update has a clean lattice-theoretic identity: it is the
intersection of the existing preorder with the **promotion preorder**
of `p`, where `promote p w v` says "if `p` holds at the lower world it
holds at the higher one too". This factors out the algebraic content of
`star` and makes its commutativity and idempotency one-line corollaries
of `∧`-commutativity and `∧`-idempotency.

This identity also explains why `⋆`-update is *not* a literal monoid
action of `(W → Prop, ∧, ⊤)` on `POSW W`: `promote (p ∧ q)` is in
general strictly finer than `promote p ⊓ promote q` (a world where
`p` holds and `q` doesn't witnesses the gap). What we get is weaker
than a monoid action, but strong enough for the commutativity /
idempotency theorems below. -/

/-- The **promotion preorder** of a proposition: `w` is at least as
    `p`-good as `v` iff `p`-truth at `v` carries to `p`-truth at `w`.
    The structural content of `⋆`-update on the ordering: one
    `⋆`-application intersects `c.le` with `promote p`. -/
def promote (p : W → Prop) (w v : W) : Prop := p v → p w

theorem promote_refl (p : W → Prop) (w : W) : promote p w w :=
  fun hp => hp

theorem promote_trans (p : W → Prop) (w u v : W) :
    promote p w u → promote p u v → promote p w v :=
  fun h₁ h₂ hp => h₁ (h₂ hp)

/-- `⋆`-update is intersection of `c.le` with `promote p`. The
    structural identity that makes the algebra of `⋆` transparent:
    `(c ⋆ p).le = c.le ⊓ promote p`. -/
@[simp] theorem star_le_eq (c : POSW W) (p : W → Prop) (w v : W) :
    (c.star p).le w v ↔ c.le w v ∧ promote p w v := Iff.rfl

/-- **`⋆`-update commutes with itself**: applying two `⋆`-updates in
    either order produces the same ordering. Falls out of `∧`-commutativity
    on `(c.le w v) ∧ promote p w v ∧ promote q w v`. -/
theorem star_star_comm_le (c : POSW W) (p q : W → Prop) (w v : W) :
    ((c.star p).star q).le w v ↔ ((c.star q).star p).le w v := by
  simp only [star_le_eq]
  exact ⟨fun ⟨⟨h, hp⟩, hq⟩ => ⟨⟨h, hq⟩, hp⟩,
         fun ⟨⟨h, hq⟩, hp⟩ => ⟨⟨h, hp⟩, hq⟩⟩

/-- **`⋆`-update is idempotent**: applying the same `⋆`-update twice
    produces the same ordering as applying it once. Falls out of
    `∧`-idempotency on `promote p`. -/
theorem star_star_self_le (c : POSW W) (p : W → Prop) (w v : W) :
    ((c.star p).star p).le w v ↔ (c.star p).le w v := by
  simp only [star_le_eq]
  exact ⟨fun ⟨⟨h, hp⟩, _⟩ => ⟨h, hp⟩,
         fun ⟨h, hp⟩ => ⟨⟨h, hp⟩, hp⟩⟩

/-! ## §7. Farkas-style update fixed-point

@cite{farkas-2003}'s eq. 11 alternative to the @cite{portner-2018}
Indicative/Subjunctive Principles characterizes mood selection by
*update type*: declarative `+`-update vs. directive `⋆`-update, rather
than by the matrix operator. The mathematical core is the
**update-fixedpoint** characterization: an update *adds nothing*
exactly when its content is already consequential at the input.

For `+`-update on `cs`: `c` already implies `p` (i.e. `c.boxCs p`)
iff `c ≤ c.plus p` (i.e. `c.plus p` doesn't shrink `cs`). -/

/-- **Farkas update-fixedpoint** for `+`: the input refines the
    `+`-update iff the proposition is already informationally necessary.
    Formal content of @cite{farkas-2003}'s eq. 11 distinction between
    consequential and merely-redundant assertions. -/
theorem le_plus_iff_boxCs (c : POSW W) (p : W → Prop) :
    c ≤ c.plus p ↔ c.boxCs p := by
  constructor
  · intro h w hw
    exact (h.1 w hw).2
  · intro hp
    refine ⟨fun w hw => ⟨hw, hp w hw⟩, fun _ _ h => h⟩

/-! ## §8. Normal modality structure

`boxCs` and `boxLe` are both **normal modalities** in the sense of
modal logic: each satisfies necessitation (`□⊤`) and the K-axiom
(`□(p→q) → □p → □q`). This is because each is a universal
quantification over a `W`-subset (`c.cs` and `c.best` respectively),
and the universal-on-subset modality satisfies N + K trivially.

The third modal `boxAns` is *not* normal — it does not satisfy K.
A counterexample: with `cs = {a, b, c}`, inquiry partition
`{{a, b}, {c}}`, take `p` false on `{a, b}` and `q` true at `a`,
false at `b`. Then `boxAns p` (vacuously, since `p` is false on the
cell), `boxAns (p → q)` (vacuously, since `p → q` is true on the
cell when `p` is false), but not `boxAns q`. `boxAns` instead has its
own closure structure: it is closed under boolean operations on the
*proposition* (`POSWQ.boxAns_not / and / or / imp`), which makes it
a different kind of constancy modality.

The `NormalModality` typeclass packages N + K and exposes them by
TC inference, so any future code that abstracts over a normal box
can dispatch to `boxCs` and `boxLe` uniformly. -/

/-- A **normal modality** in the sense of basic modal logic:
    quantifies a unary box over `W → Prop` predicates, satisfying
    necessitation (`box ⊤`) and the K-axiom (`box (p → q) → box p
    → box q`). The two POSW universal modalities `boxCs` and `boxLe`
    are normal; `POSWQ.boxAns` is not (see the section docstring). -/
class NormalModality (W : Type u) (box : (W → Prop) → Prop) : Prop where
  /-- Necessitation: the box always holds for `⊤`. -/
  necessitation : box (fun _ => True)
  /-- The K-axiom: distribution of the box over implication. -/
  K : ∀ p q : W → Prop, box (fun w => p w → q w) → box p → box q

instance (c : POSW W) : NormalModality W c.boxCs where
  necessitation := fun _ _ => trivial
  K _ _ hpq hp w hcs := hpq w hcs (hp w hcs)

instance (c : POSW W) : NormalModality W c.boxLe where
  necessitation := fun _ _ => trivial
  K _ _ hpq hp w hbest := hpq w hbest (hp w hbest)

end POSW
end Core.Mood
