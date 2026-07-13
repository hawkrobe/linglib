/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.NormalForm

/-!
# Local autosegmental configurations

The named building blocks of autosegmental representations. `AR.junction as bs` links
every melody node of `as` to every timing slot of `bs`; its planar specializations —
`single`, `bare`, `float`, `contour`, `spread` — are the local configurations of
autosegmental tonology, and `concat`-products of them build every representation in the
current tone studies (`Studies/Jardine2016Tone`, `Studies/Jardine2017`,
`Studies/Jardine2019`). Building through them (rather than raw structure literals)
carries the in-bounds proof at arbitrary alphabets, where the studies' `by decide`
cannot go, and gives every configuration a simp kit.

The keystone is `isPlanar_junction_iff`: a junction is planar iff one side has at most
one node, so among complete many-to-many associations the No-Crossing Constraint
([goldsmith-1976]) admits exactly the one-to-many (`spread`), many-to-one (`contour`)
and degenerate configurations. (Formaliser's synthesis: the literature treats the NCC
as a filter on representations, not as a characterisation of local generators.)

`concat` is the coproduct, so builder products reach exactly the block-diagonal link
relations; connected shared-node configurations (e.g. a spread-fed contour, H→μ₁ with
L→μ₁μ₂) are planar but not products. TODO: a gluing operation dual to `concat`
(identify a shared boundary slot) reaching them, with the completeness target *every
planar AR is a concat/glue expression over the builders*; at that point `junction`
becomes primary and the five kits derive from its (the
`SimpleGraph.completeBipartiteGraph` move).

## Main definitions

* `AR.junction` — complete many-to-many association of a melody onto a slot sequence.
* `AR.single`, `AR.bare`, `AR.float`, `AR.contour`, `AR.spread` — the planar local
  configurations: one-to-one, toneless slot, floating autosegment ([leben-1973]; the
  tier-with-floats object is `Floating.lean`), several nodes on one slot, one node over
  several slots.

## Main results

* `AR.isPlanar_junction_iff` — NCC-planarity of a junction: one side is at most a
  singleton.
* `AR.linearize_junction` — every slot of a junction carries the whole melody.
* Per-builder simp kits: tier projections (at the `LabeledTuple` level, so `.len`,
  `.toList`, `.get?` follow from the `ofList` kit), reduced link sets, linearization,
  planarity, and OCP-cleanliness.
-/

namespace Autosegmental

variable {α β : Type*} {a : α} {b : β} {as : List α} {bs : List β}



/-! ### The junction in coordinates

The complete association as a two-tier `Representation` (`Bool`-indexed:
`true` the melody tier, `false` the timing tier), built by `ofData`; the
No-Crossing keystone in the foundational path form. -/

section CoordinateJunction

universe u
variable {α β : Type u}

/-- The two-tier alphabet: melody labels over `true`, timing labels over
    `false`. -/
abbrev TwoTier (α β : Type u) : Bool → Type u := fun b => bif b then α else β

/-- Complete many-to-many association of a melody onto a slot sequence, in
    coordinates. -/
def Representation.junction (as : List α) (bs : List β) :
    Representation (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool) :=
  Representation.ofData
    (fun b => match b with
      | true => (as : List (TwoTier α β true))
      | false => (bs : List (TwoTier α β false)))
    (fun i j p q => i = true ∧ j = false ∧ p < as.length ∧ q < bs.length)

instance (as : List α) (bs : List β) :
    Finite (Representation.junction as bs).obj.V :=
  inferInstanceAs (Finite ((_ : Bool) × Fin _))

@[simp] theorem Representation.tierWord_junction_true (as : List α) (bs : List β) :
    (Representation.junction as bs).tierWord true = as :=
  Representation.tierWord_ofData true

@[simp] theorem Representation.tierWord_junction_false (as : List α) (bs : List β) :
    (Representation.junction as bs).tierWord false = bs :=
  Representation.tierWord_ofData false

/-- Junction links are complete: every in-bounds melody–timing pair. -/
theorem Representation.link_junction (as : List α) (bs : List β) {b b' : Bool}
    {p q : ℕ} : (Representation.junction as bs).link b b' p q ↔
      b = true ∧ b' = false ∧ p < as.length ∧ q < bs.length ∨
        b = false ∧ b' = true ∧ p < bs.length ∧ q < as.length := by
  unfold Representation.junction
  rw [Representation.link_ofData]
  constructor
  · rintro ⟨hne, hp, hq, (⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩)⟩
    · exact Or.inl ⟨rfl, rfl, h1, h2⟩
    · exact Or.inr ⟨rfl, rfl, by simpa using hp, by simpa using hq⟩
  · rintro (⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩)
    · exact ⟨by decide, by simpa using h1, by simpa using h2,
        Or.inl ⟨rfl, rfl, h1, h2⟩⟩
    · exact ⟨by decide, by simpa using h1, by simpa using h2,
        Or.inr ⟨rfl, rfl, h2, h1⟩⟩

/-- **The No-Crossing Constraint selects the one-sided junctions**: a complete
    association is planar iff one side has at most one node — the one-to-many
    `spread`, many-to-one `contour`, and degenerate cases. -/
theorem Representation.isPlanar_junction_iff (as : List α) (bs : List β) :
    IsPlanar (Representation.junction as bs).obj.graph ↔
      as.length ≤ 1 ∨ bs.length ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    obtain ⟨ha, hb⟩ := hc
    rw [Nat.not_le] at ha hb
    exact h (v := ⟨true, ⟨0, show 0 < as.length by omega⟩⟩)
      (v' := ⟨false, ⟨1, show 1 < bs.length by omega⟩⟩)
      (w := ⟨true, ⟨1, show 1 < as.length by omega⟩⟩)
      (w' := ⟨false, ⟨0, show 0 < bs.length by omega⟩⟩)
      ⟨by simp, Or.inl ⟨rfl, rfl, show (0 : ℕ) < as.length by omega,
        show (1 : ℕ) < bs.length by omega⟩⟩
      ⟨by simp, Or.inl ⟨rfl, rfl, show (1 : ℕ) < as.length by omega,
        show (0 : ℕ) < bs.length by omega⟩⟩
      ⟨rfl, show (0 : ℕ) < 1 by omega⟩ ⟨rfl, show (0 : ℕ) < 1 by omega⟩
  · rintro h ⟨bv, pv⟩ ⟨bv', pv'⟩ ⟨bw, pw⟩ ⟨bw', pw'⟩ hvv' hww' hvw hw'v'
    obtain ⟨hbvw, hpvw⟩ := hvw
    obtain ⟨hbw'v', hpw'v'⟩ := hw'v'
    cases hbvw
    cases hbw'v'
    have hv' : bv' = !bv := by
      rcases hvv' with ⟨hne, -⟩
      cases bv <;> cases bv' <;> simp_all
    subst hv'
    rcases h with h | h <;> cases bv
    · have h1 : (pv' : ℕ) < as.length := pv'.isLt
      have h2 : (pw' : ℕ) < as.length := pw'.isLt
      have h3 : (pw' : ℕ) < (pv' : ℕ) := hpw'v'
      omega
    · have h1 : (pv : ℕ) < as.length := pv.isLt
      have h2 : (pw : ℕ) < as.length := pw.isLt
      have h3 : (pv : ℕ) < (pw : ℕ) := hpvw
      omega
    · have h1 : (pv : ℕ) < bs.length := pv.isLt
      have h2 : (pw : ℕ) < bs.length := pw.isLt
      have h3 : (pv : ℕ) < (pw : ℕ) := hpvw
      omega
    · have h1 : (pv' : ℕ) < bs.length := pv'.isLt
      have h2 : (pw' : ℕ) < bs.length := pw'.isLt
      have h3 : (pw' : ℕ) < (pv' : ℕ) := hpw'v'
      omega

/-! #### The planar local configurations -/

/-- One-to-one association. -/
def Representation.single (a : α) (b : β) := Representation.junction [a] [b]

/-- A bare (unassociated) timing slot. -/
def Representation.bare (b : β) := Representation.junction ([] : List α) [b]

/-- A floating autosegment ([leben-1973]). -/
def Representation.float (a : α) := Representation.junction [a] ([] : List β)

/-- Several melody nodes on one slot. -/
def Representation.contour (as : List α) (b : β) := Representation.junction as [b]

/-- One melody node over several slots. -/
def Representation.spread (a : α) (bs : List β) := Representation.junction [a] bs

theorem Representation.isPlanar_single (a : α) (b : β) :
    IsPlanar (Representation.single a b).obj.graph :=
  (Representation.isPlanar_junction_iff _ _).mpr (Or.inl (by simp))

theorem Representation.isPlanar_bare (b : β) :
    IsPlanar (Representation.bare (α := α) b).obj.graph :=
  (Representation.isPlanar_junction_iff _ _).mpr (Or.inl (by simp))

theorem Representation.isPlanar_float (a : α) :
    IsPlanar (Representation.float (β := β) a).obj.graph :=
  (Representation.isPlanar_junction_iff _ _).mpr (Or.inl (by simp))

theorem Representation.isPlanar_contour (as : List α) (b : β) :
    IsPlanar (Representation.contour as b).obj.graph :=
  (Representation.isPlanar_junction_iff _ _).mpr (Or.inr (by simp))

theorem Representation.isPlanar_spread (a : α) (bs : List β) :
    IsPlanar (Representation.spread a bs).obj.graph :=
  (Representation.isPlanar_junction_iff _ _).mpr (Or.inl (by simp))

/-- Two-tier factor embedding is a search over two bounded offsets. -/
theorem Representation.factorEmbeds_iff_two_tier
    {F X : Representation (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool)}
    [Finite F.obj.V] [Finite X.obj.V] :
    F.FactorEmbeds X ↔
      ∃ ot ≤ X.tierLength true, ∃ of ≤ X.tierLength false,
        F.IsFactorAt X (fun b => bif b then ot else of) := by
  rw [Representation.factorEmbeds_iff_bounded]
  constructor
  · rintro ⟨o, hb, hfa⟩
    refine ⟨o true, hb true, o false, hb false, ?_⟩
    have he : (fun b => bif b then o true else o false) = o :=
      funext fun b => by cases b <;> rfl
    rwa [he]
  · rintro ⟨ot, hot, of, hof, hfa⟩
    exact ⟨_, fun b => by cases b <;> simpa, hfa⟩

/-- The data-level factor check: `wsF`/`LF` occurs in `wsX`/`LX` at some pair
    of bounded offsets — list windows match and links transport shifted. The
    decidable face of `FactorEmbeds` for `ofData`-presented forms. -/
def dataEmbeds (wsF wsX : ∀ b : Bool, List (TwoTier α β b))
    (LF LX : Bool → Bool → ℕ → ℕ → Prop) : Prop :=
  ∃ ot ≤ (wsX true).length, ∃ of ≤ (wsX false).length,
    (∀ p < (wsF true).length, (wsX true)[p + ot]? = (wsF true)[p]?) ∧
    (∀ p < (wsF false).length, (wsX false)[p + of]? = (wsF false)[p]?) ∧
    ∀ p < (wsF true).length, ∀ q < (wsF false).length,
      (LF true false p q ∨ LF false true q p) →
        (LX true false (p + ot) (q + of) ∨ LX false true (q + of) (p + ot))

instance {wsF wsX : ∀ b : Bool, List (TwoTier α β b)}
    {LF LX : Bool → Bool → ℕ → ℕ → Prop}
    [DecidableEq α] [DecidableEq β]
    [∀ i j p q, Decidable (LF i j p q)] [∀ i j p q, Decidable (LX i j p q)] :
    Decidable (dataEmbeds wsF wsX LF LX) := by
  unfold dataEmbeds
  haveI : DecidableEq (TwoTier α β true) := inferInstanceAs (DecidableEq α)
  haveI : DecidableEq (TwoTier α β false) := inferInstanceAs (DecidableEq β)
  infer_instance

/-- **The spec**: on `ofData`-presented two-tier forms, factor embedding is the
    data-level check — the bridge that turns banned-subgraph verdicts into
    kernel computations. -/
theorem Representation.factorEmbeds_ofData_iff
    {wsF wsX : ∀ b : Bool, List (TwoTier α β b)}
    {LF LX : Bool → Bool → ℕ → ℕ → Prop} :
    (Representation.ofData wsF LF).FactorEmbeds (Representation.ofData wsX LX) ↔
      dataEmbeds wsF wsX LF LX := by
  rw [Representation.factorEmbeds_iff_two_tier]
  simp only [Representation.tierLength_ofData]
  constructor
  · rintro ⟨ot, hot, of, hof, hw, hl⟩
    refine ⟨ot, hot, of, hof, ?_, ?_, ?_⟩
    · intro p hp
      have := hw true p (by rw [Representation.tierLength_ofData]; exact hp)
      rwa [Representation.tierWord_ofData, Representation.tierWord_ofData] at this
    · intro p hp
      have := hw false p (by rw [Representation.tierLength_ofData]; exact hp)
      rwa [Representation.tierWord_ofData, Representation.tierWord_ofData] at this
    · intro p hp q hq hpq
      have hlk := hl true false p q ((Representation.link_ofData true false p q).mpr
        ⟨by decide, hp, hq, hpq⟩)
      rcases (Representation.link_ofData true false (p + ot) (q + of)).mp hlk with
        ⟨-, -, -, hres⟩
      exact hres
  · rintro ⟨ot, hot, of, hof, hwt, hwf, hlk⟩
    have hbt : ∀ p, p < (wsF true).length → p + ot < (wsX true).length := by
      intro p hp
      have h1 : (wsX true)[p + ot]? = some ((wsF true)[p]'hp) :=
        (hwt p hp).trans (List.getElem?_eq_getElem hp)
      exact (List.getElem?_eq_some_iff.mp h1).1
    have hbf : ∀ q, q < (wsF false).length → q + of < (wsX false).length := by
      intro q hq
      have h1 : (wsX false)[q + of]? = some ((wsF false)[q]'hq) :=
        (hwf q hq).trans (List.getElem?_eq_getElem hq)
      exact (List.getElem?_eq_some_iff.mp h1).1
    refine ⟨ot, hot, of, hof, ?_, ?_⟩
    · intro i p hp
      rw [Representation.tierLength_ofData] at hp
      cases i
      · rw [show ((Representation.ofData wsX LX).tierWord false)
            = wsX false from Representation.tierWord_ofData false,
          show ((Representation.ofData wsF LF).tierWord false)
            = wsF false from Representation.tierWord_ofData false]
        exact hwf p hp
      · rw [show ((Representation.ofData wsX LX).tierWord true)
            = wsX true from Representation.tierWord_ofData true,
          show ((Representation.ofData wsF LF).tierWord true)
            = wsF true from Representation.tierWord_ofData true]
        exact hwt p hp
    · intro i j p q hl
      rcases (Representation.link_ofData i j p q).mp hl with ⟨hne, hp, hq, hor⟩
      have hcases : i = true ∧ j = false ∨ i = false ∧ j = true := by
        cases i <;> cases j <;> simp_all
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hlk p hp q hq hor with hres | hres
        · exact (Representation.link_ofData true false _ _).mpr
            ⟨by decide, hbt p hp, hbf q hq, Or.inl hres⟩
        · exact (Representation.link_ofData true false _ _).mpr
            ⟨by decide, hbt p hp, hbf q hq, Or.inr hres⟩
      · rcases hlk q hq p hp hor.symm with hres | hres
        · exact (Representation.link_ofData false true _ _).mpr
            ⟨by decide, hbf p hp, hbt q hq, Or.inr hres⟩
        · exact (Representation.link_ofData false true _ _).mpr
            ⟨by decide, hbf p hp, hbt q hq, Or.inl hres⟩

/-- A timing slot **surfaces with** melody label `a`: some `a`-labelled melody
    node links to it. -/
def Representation.surfacesWith
    (X : Representation (Sigma.fst : ((b : Bool) × TwoTier α β b) → Bool))
    [Finite X.obj.V] (a : α) (j : ℕ) : Prop :=
  ∃ k, X.link true false k j ∧ (X.tierWord true)[k]? = some a

end CoordinateJunction

end Autosegmental
