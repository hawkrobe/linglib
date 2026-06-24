import Linglib.Data.UD.Basic
import Linglib.Features.Basic
import Linglib.Core.Order.PartialUnify
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.BoundedOrder.Basic

/-!
# Unification: subsumption and joins for feature bundles
[shieber-1986]

The information ordering of unification-based grammar ([shieber-1986] §3.2), on
`UD.MorphFeatures` — the depth-1, reentrancy-free fragment of Shieber's feature
structures. Every feature here is atomic-valued, so paths are single features, the
reentrancy clause of subsumption is vacuous, and the definition (§3.2.2: `D ⊑ D′` iff
`D(l) ⊑ D′(l)` for all `l ∈ dom(D)`; "an atomic feature structure neither subsumes nor
is subsumed by a different atomic feature structure"; "variables subsume all other
feature structures") reduces to the product of flat orders. Subsumption is registered
as `≤` (Shieber's `⊑`); the all-`none` bundle — Shieber's variable `[ ]` — is `⊥`.

Unification (§3.2.3) is "the most general feature structure `D` such that `D′ ⊑ D` and
`D′′ ⊑ D`", failing on conflict: `MorphFeatures.unify` returns `some` exactly on
`Compatible` (= bounded above) inputs, and its result is the least upper bound
(`unify_isLUB`). The example laws of §3.2.3 are theorems: unification is idempotent
(`unify_self`), commutative (`unify_comm`), and variables are identity elements
(`bot_unify`).

## Main declarations

* `Option.FlatLE` — the flat information order on one atomic feature slot.
* `instance : PartialOrder UD.MorphFeatures` — subsumption ("only a partial order",
  §3.2.3), with decidable `≤`.
* `instance : OrderBot UD.MorphFeatures` — the empty bundle is bottom.
* `instance : SemilatticeInf UD.MorphFeatures` — the meet is Shieber's
  *generalization* (anti-unification): total, unlike the join.
* `UD.MorphFeatures.Compatible` — boundedness above (`BddAbove {f, g}`), decidable
  via the `Bool` check (`compatible_iff_bddAbove`).
* `unify_isLUB`, `unify_eq_some_iff_isLUB`, `unify_comm`, `unify_assoc`,
  `unify_self`, `bot_unify`/`unify_bot`, `unify_mono` — the §3.2.3 laws plus
  associativity and guarded monotonicity.

## Theory-neutrality boundary

Three strata with different statuses: the *record* is annotation consensus
(`Data/UD/Basic.lean`); the *order* `≤` is shared substrate every framework consumes
its own way (DM's matching clause, underspecification, syncretism down-sets); the
*operations* `⊔`/`⊓` are commitments of the unification tradition — [shieber-1986]
§3.1 states unification-as-sole-combinator as a design constraint, and rival
frameworks combine differently (DM matches and competes; Minimalist Agree values
asymmetrically). This file is *not* that tradition's headquarters: unification-based
grammar (PATR, HPSG, LFG — reentrant feature structures, phrasal combination) is a
syntax family whose substrate belongs in `Syntax/` when consuming studies demand it.
What lives here is only the tradition's morphological-bundle fragment — the algebra
of one token's Feats column — which it shares with rivals: at the level of claims
about morphological feature combination this file is a sibling of `DM/` and
`Nanosyntax/`, not a foundation beneath them.

## Implementation notes

Morphology owns the bundle algebra: `MorphFeatures` is the token's morphology (UD's
Feats column), and unification at the ms-word level is the morphology/syntax interface
operation. The *matching clause* of DM's Subset Principle (an exponent is insertable
iff `exponent.features ≤ morpheme.features`) *could* consume `≤` directly, but the
existing `Morphology/DM/VocabularyInsertion.lean` matches by `List`-subset on `[BEq F]`
rather than `MorphFeatures.≤`; bridging is left for a future PR. The competition
clause — most-specified-wins — is separate `argmax` machinery already implemented in
that same file. (Nanosyntax's Superset Principle is *not* a consumer: it matches by
containment of syntactic trees, see `Nanosyntax/TreeSpellout.lean`'s `NanoTree.contains`,
not by an order on flat bundles.) Lives apart from `Data/UD/Basic.lean` so the
(heavily imported) standard mirror stays mathlib-free — this file is the one that
pays for `Mathlib.Order` — and it is the canonical home for order instances on
`UD.MorphFeatures`.

The non-distributivity of the subsumption lattice is a documented
obstruction (`MorphFeatures.not_distrib_witness`): any ≥3-value slot
(here, `Case`) makes the per-slot lattice the diamond Mₙ, modular but
*not* distributive ([carpenter-1992] p. 15, eq. (4), notes this
explicitly: "our partial orders are *not* required to be distributive
(and in fact, are not even required to be modular)"). This matters for
generalization-then-unification reorderings in paradigm-induction
learners.
-/

set_option autoImplicit false

/-! ### The flat order on one feature slot

`Option.FlatLE` is the slot-level subsumption relation ([shieber-1986]
§3.2.2: `none` below everything, distinct atoms incomparable). The
definition and its `refl`/`trans`/`antisymm`/`none_le` API live in
`Linglib/Core/Order/Flat.lean`, where they also carry the bundled
`PartialOrder`/`OrderBot`/`SemilatticeInf`/`PartialUnify` instances on
the order-carrying alias `Flat α`. Re-exported here under their
original names for backward compatibility with this file's own proofs
and consumers.
-/

namespace UD

/-- The 14-case feature-type index for `MorphFeatures` — the signature
of UD's Feats column treated as a fixed finite type family. -/
inductive MorphFeatureType where
  | number | gender | case_ | definite | degree | pronType
  | reflex
  | person | verbForm | tense | aspect | mood | voice | polarity
  deriving DecidableEq, Repr, Fintype

namespace MorphFeatureType

/-- Per-slot value space. The reflex slot is privative (`Unit`); all
other slots take their concrete UD enum. -/
def Val : MorphFeatureType → Type
  | .number   => Number
  | .gender   => Gender
  | .case_    => Case
  | .definite => Definite
  | .degree   => Degree
  | .pronType => PronType
  | .reflex   => Unit
  | .person   => Person
  | .verbForm => VerbForm
  | .tense    => Tense
  | .aspect   => Aspect
  | .mood     => Mood
  | .voice    => Voice
  | .polarity => Polarity

instance : ∀ t, DecidableEq (Val t)
  | .number   => inferInstanceAs (DecidableEq Number)
  | .gender   => inferInstanceAs (DecidableEq Gender)
  | .case_    => inferInstanceAs (DecidableEq Case)
  | .definite => inferInstanceAs (DecidableEq Definite)
  | .degree   => inferInstanceAs (DecidableEq Degree)
  | .pronType => inferInstanceAs (DecidableEq PronType)
  | .reflex   => inferInstanceAs (DecidableEq Unit)
  | .person   => inferInstanceAs (DecidableEq Person)
  | .verbForm => inferInstanceAs (DecidableEq VerbForm)
  | .tense    => inferInstanceAs (DecidableEq Tense)
  | .aspect   => inferInstanceAs (DecidableEq Aspect)
  | .mood     => inferInstanceAs (DecidableEq Mood)
  | .voice    => inferInstanceAs (DecidableEq Voice)
  | .polarity => inferInstanceAs (DecidableEq Polarity)

end MorphFeatureType

end UD

namespace UD.MorphFeatures

/-! ### Subsumption is a partial order with bottom -/

/-- Subsumption ([shieber-1986] §3.2.2): `f` carries a subset of `g`'s information —
field-wise flat order on the option slots, implication on the `reflex` flag. -/
def Subsumes (f g : MorphFeatures) : Prop :=
  f.number.FlatLE g.number ∧ f.gender.FlatLE g.gender ∧ f.case_.FlatLE g.case_ ∧
  f.definite.FlatLE g.definite ∧ f.degree.FlatLE g.degree ∧
  f.pronType.FlatLE g.pronType ∧ (f.reflex = true → g.reflex = true) ∧
  f.person.FlatLE g.person ∧ f.verbForm.FlatLE g.verbForm ∧ f.tense.FlatLE g.tense ∧
  f.aspect.FlatLE g.aspect ∧ f.mood.FlatLE g.mood ∧ f.voice.FlatLE g.voice ∧
  f.polarity.FlatLE g.polarity

/-! ### `MorphFeatures` as a feature bundle, and the derived order

`MorphFeatures` realizes `BundleLike` over the 14-case signature
`MorphFeatureType` ([carpenter-1992]'s abstract feature structure): each
slot projects to a `Flat` value, with the `reflex` flag normalized
`false ↦ none`, `true ↦ some ()` (the privative `Unit` case). The
valuation is injective, so `MorphFeatures` is `LawfulBundleLike`, and the
subsumption order *is* the per-slot `Flat` order pulled back along `val`
(`subsumes_iff_val_le`) — the `PartialOrder`/`OrderBot` laws derive from
the bundle embedding rather than being proved field by field. -/

/-- The valuation: project each slot as a `Flat` value, normalizing
`reflex : Bool` to a privative `Flat Unit`. -/
def val (f : MorphFeatures) :
    (t : MorphFeatureType) → Flat (MorphFeatureType.Val t)
  | .number   => f.number
  | .gender   => f.gender
  | .case_    => f.case_
  | .definite => f.definite
  | .degree   => f.degree
  | .pronType => f.pronType
  | .reflex   => if f.reflex then some () else none
  | .person   => f.person
  | .verbForm => f.verbForm
  | .tense    => f.tense
  | .aspect   => f.aspect
  | .mood     => f.mood
  | .voice    => f.voice
  | .polarity => f.polarity

instance : BundleLike MorphFeatures MorphFeatureType
    (fun t => Flat (MorphFeatureType.Val t)) where
  val := MorphFeatures.val

private theorem reflex_eq_of_val_reflex_eq {b1 b2 : Bool}
    (h : (if b1 then some () else none) = (if b2 then some () else none)) :
    b1 = b2 := by
  cases b1 <;> cases b2 <;> simp_all

/-- The valuation is injective: a `MorphFeatures` bundle is determined by
its per-slot assignments (with `reflex` reconstructed from `Option Unit`). -/
theorem val_injective : Function.Injective MorphFeatures.val := by
  intro f g h
  cases f; cases g
  simp only [mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrFun h .number
  · exact congrFun h .gender
  · exact congrFun h .case_
  · exact congrFun h .definite
  · exact congrFun h .degree
  · exact congrFun h .pronType
  · exact reflex_eq_of_val_reflex_eq (congrFun h .reflex)
  · exact congrFun h .person
  · exact congrFun h .verbForm
  · exact congrFun h .tense
  · exact congrFun h .aspect
  · exact congrFun h .mood
  · exact congrFun h .voice
  · exact congrFun h .polarity

instance : LawfulBundleLike MorphFeatures :=
  ⟨val_injective⟩

private theorem reflex_val_le_iff {b1 b2 : Bool} :
    Option.FlatLE (if b1 then some () else none) (if b2 then some () else none)
      ↔ (b1 = true → b2 = true) := by
  cases b1 <;> cases b2 <;> simp [Option.FlatLE]

/-- Subsumption is exactly the bundle order: the field-wise 14-conjunct form
coincides with the per-slot `Flat` order on the valuation `val`. -/
theorem subsumes_iff_val_le (f g : MorphFeatures) : Subsumes f g ↔ val f ≤ val g := by
  rw [Pi.le_def]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ t
    cases t
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact reflex_val_le_iff.mpr h7
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14
  · intro h
    exact ⟨h .number, h .gender, h .case_, h .definite, h .degree, h .pronType,
           reflex_val_le_iff.mp (h .reflex), h .person, h .verbForm, h .tense,
           h .aspect, h .mood, h .voice, h .polarity⟩

instance : PartialOrder MorphFeatures where
  le := Subsumes
  le_refl f := (subsumes_iff_val_le f f).mpr le_rfl
  le_trans f g h hfg hgh :=
    (subsumes_iff_val_le f h).mpr
      (((subsumes_iff_val_le f g).mp hfg).trans ((subsumes_iff_val_le g h).mp hgh))
  le_antisymm f g hfg hgf :=
    val_injective (le_antisymm ((subsumes_iff_val_le f g).mp hfg)
      ((subsumes_iff_val_le g f).mp hgf))

instance (f g : MorphFeatures) : Decidable (Subsumes f g) := by
  unfold Subsumes; infer_instance

/-- Subsumption is decidable (each slot is). -/
instance (f g : MorphFeatures) : Decidable (f ≤ g) :=
  inferInstanceAs (Decidable (Subsumes f g))

/-- The empty bundle — Shieber's variable `[ ]` — is bottom: "variables subsume all
other feature structures … they contain no information at all" (§3.2.2). -/
instance : OrderBot MorphFeatures where
  bot := {}
  bot_le f := (subsumes_iff_val_le {} f).mpr (by
    intro t; cases t <;> exact Option.FlatLE.none_le _)

/-! ### Compatibility is boundedness above; unification is the least upper bound -/

/-- `Prop`-native compatibility: the pair is bounded above in the subsumption
order — mathlib's `BddAbove`, so the bounds API applies directly. Characterized by
the executable `compatible` check via `compatible_iff_bddAbove`, which also makes
it decidable. -/
def Compatible (f g : MorphFeatures) : Prop := BddAbove ({f, g} : Set MorphFeatures)

private theorem clause_of_some_some {α : Type _} [BEq α] [LawfulBEq α] {x y : α}
    (h : ((some x : Option α).isNone || (some y : Option α).isNone
          || (some x : Option α) == some y) = true) : x = y := by
  simpa [Option.isNone] using h

private theorem some_flatLE_orElse {α : Type _} (a b : Option α) {x : α}
    (hx : a = some x) : (a <|> b) = some x := by
  subst hx; rfl

/-- The left input subsumes the merge. -/
theorem le_merge_left (f g : MorphFeatures) : f ≤ f.merge g := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | exact fun x hx => some_flatLE_orElse _ _ hx
      | exact fun hr => by simp [merge, hr]

private theorem flatLE_merge_right {α : Type _} [BEq α] [LawfulBEq α] (a b : Option α)
    (hcl : (a.isNone || b.isNone || a == b) = true) : b.FlatLE (a <|> b) := by
  intro x hx
  cases a with
  | none => simpa using hx
  | some v =>
    subst hx
    have : v = x := clause_of_some_some hcl
    simp [this]

/-- The right input subsumes the merge — *given compatibility* (the doubly committed
slots agree, so the left bias is harmless). -/
theorem le_merge_right {f g : MorphFeatures} (h : f.compatible g = true) :
    g ≤ f.merge g := by
  simp only [compatible, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨flatLE_merge_right _ _ h1, flatLE_merge_right _ _ h2,
         flatLE_merge_right _ _ h3, flatLE_merge_right _ _ h4,
         flatLE_merge_right _ _ h5, flatLE_merge_right _ _ h6,
         fun hr => by simp [merge, hr],
         flatLE_merge_right _ _ h7, flatLE_merge_right _ _ h8,
         flatLE_merge_right _ _ h9, flatLE_merge_right _ _ h10,
         flatLE_merge_right _ _ h11, flatLE_merge_right _ _ h12,
         flatLE_merge_right _ _ h13⟩

private theorem orElse_flatLE {α : Type _} {a b u : Option α}
    (ha : a.FlatLE u) (hb : b.FlatLE u) : (a <|> b).FlatLE u := by
  intro x hx
  cases a with
  | none => exact hb x (by simpa using hx)
  | some v => exact ha x (by simpa using hx)

/-- The merge is below every common upper bound — minimality ("the *most general*
feature structure", §3.2.3). -/
theorem merge_le {f g u : MorphFeatures} (hf : f ≤ u) (hg : g ≤ u) :
    f.merge g ≤ u := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hf
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := hg
  refine ⟨orElse_flatLE a1 b1, orElse_flatLE a2 b2, orElse_flatLE a3 b3,
          orElse_flatLE a4 b4, orElse_flatLE a5 b5, orElse_flatLE a6 b6, ?_,
          orElse_flatLE a8 b8, orElse_flatLE a9 b9, orElse_flatLE a10 b10,
          orElse_flatLE a11 b11, orElse_flatLE a12 b12, orElse_flatLE a13 b13,
          orElse_flatLE a14 b14⟩
  intro hr
  rcases Bool.or_eq_true_iff.mp (by simpa [merge] using hr) with h | h
  · exact a7 h
  · exact b7 h

private theorem clause_of_flatLE {α : Type _} [BEq α] [LawfulBEq α] {a b u : Option α}
    (ha : a.FlatLE u) (hb : b.FlatLE u) :
    (a.isNone || b.isNone || a == b) = true := by
  cases a with
  | none => simp
  | some x =>
    cases b with
    | none => simp
    | some y =>
      have hx := ha x rfl
      have hy := hb y rfl
      simp [beq_iff_eq, Option.some.inj (hx.symm.trans hy)]

/-- Bounded above implies the executable check passes. -/
theorem compatible_of_le {f g u : MorphFeatures} (hf : f ≤ u) (hg : g ≤ u) :
    f.compatible g = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, _, a8, a9, a10, a11, a12, a13, a14⟩ := hf
  obtain ⟨b1, b2, b3, b4, b5, b6, _, b8, b9, b10, b11, b12, b13, b14⟩ := hg
  simp only [compatible, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨clause_of_flatLE a1 b1, clause_of_flatLE a2 b2⟩,
    clause_of_flatLE a3 b3⟩, clause_of_flatLE a4 b4⟩, clause_of_flatLE a5 b5⟩,
    clause_of_flatLE a6 b6⟩, clause_of_flatLE a8 b8⟩, clause_of_flatLE a9 b9⟩,
    clause_of_flatLE a10 b10⟩, clause_of_flatLE a11 b11⟩, clause_of_flatLE a12 b12⟩,
    clause_of_flatLE a13 b13⟩, clause_of_flatLE a14 b14⟩

/-- The `Bool` check is exactly boundedness above in the subsumption order: the
order-theoretic identity of "compatible". -/
theorem compatible_iff_bddAbove (f g : MorphFeatures) :
    f.compatible g = true ↔ Compatible f g := by
  constructor
  · intro h
    refine ⟨f.merge g, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact le_merge_left _ g
    · rw [Set.mem_singleton_iff.mp hx]
      exact le_merge_right h
  · rintro ⟨u, hu⟩
    exact compatible_of_le (hu (Set.mem_insert _ _)) (hu (Set.mem_insert_of_mem _ rfl))

instance (f g : MorphFeatures) : Decidable (Compatible f g) :=
  decidable_of_iff _ (compatible_iff_bddAbove f g)

/-- Unification succeeds exactly on compatible inputs (§3.2.3: otherwise it "fails"). -/
theorem unify_eq_some_iff (f g : MorphFeatures) :
    (f.unify g).isSome = true ↔ Compatible f g := by
  rw [← compatible_iff_bddAbove]
  unfold unify
  by_cases hc : f.compatible g = true <;> simp [hc]

/-- **Unification is the least upper bound** ([shieber-1986] §3.2.3: "the most general
feature structure `D` such that `D′ ⊑ D` and `D′′ ⊑ D`"). -/
theorem unify_isLUB {f g u : MorphFeatures} (h : f.unify g = some u) :
    IsLUB {f, g} u := by
  unfold unify at h
  by_cases hc : f.compatible g = true
  · simp only [hc, if_true, Option.some.injEq] at h
    subst h
    constructor
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact le_merge_left _ g
      · rw [Set.mem_singleton_iff.mp hx]
        exact le_merge_right hc
    · intro v hv
      exact merge_le (hv (Set.mem_insert _ _)) (hv (Set.mem_insert_of_mem _ rfl))
  · simp [hc] at h

/-! ### Generalization: the meet

Shieber's *generalization* (anti-unification): the most specific bundle subsumed by
both inputs. Unlike unification it is total — the meet always exists — so
`MorphFeatures` is a genuine `SemilatticeInf` with `⊥`. -/

private def slotInf {α : Type _} [DecidableEq α] (a b : Option α) : Option α :=
  if a = b then a else none

private theorem slotInf_flatLE_left {α : Type _} [DecidableEq α] (a b : Option α) :
    (slotInf a b).FlatLE a := by
  unfold slotInf; split
  · exact .refl _
  · exact .none_le _

private theorem slotInf_flatLE_right {α : Type _} [DecidableEq α] (a b : Option α) :
    (slotInf a b).FlatLE b := by
  unfold slotInf; split
  · next h => subst h; exact .refl _
  · exact .none_le _

private theorem flatLE_slotInf {α : Type _} [DecidableEq α] {a b c : Option α}
    (h1 : c.FlatLE a) (h2 : c.FlatLE b) : c.FlatLE (slotInf a b) := by
  intro x hx
  have ha := h1 x hx
  have hb := h2 x hx
  unfold slotInf
  rw [ha, hb]
  simp

instance : Min MorphFeatures where
  min f g :=
    { number   := slotInf f.number g.number
      gender   := slotInf f.gender g.gender
      case_    := slotInf f.case_ g.case_
      definite := slotInf f.definite g.definite
      degree   := slotInf f.degree g.degree
      pronType := slotInf f.pronType g.pronType
      reflex   := f.reflex && g.reflex
      person   := slotInf f.person g.person
      verbForm := slotInf f.verbForm g.verbForm
      tense    := slotInf f.tense g.tense
      aspect   := slotInf f.aspect g.aspect
      mood     := slotInf f.mood g.mood
      voice    := slotInf f.voice g.voice
      polarity := slotInf f.polarity g.polarity }

private theorem band_true_left {x y : Bool} (h : (x && y) = true) : x = true := by
  cases x <;> simp_all

private theorem band_true_right {x y : Bool} (h : (x && y) = true) : y = true := by
  cases y <;> simp_all

private theorem band_true_intro {x y : Bool} (hx : x = true) (hy : y = true) :
    (x && y) = true := by simp [hx, hy]

instance : SemilatticeInf MorphFeatures :=
  { (inferInstance : PartialOrder MorphFeatures),
    (inferInstance : Min MorphFeatures) with
    inf := min
    inf_le_left := fun f g => show Subsumes (min f g) f from
      ⟨slotInf_flatLE_left _ _, slotInf_flatLE_left _ _, slotInf_flatLE_left _ _,
       slotInf_flatLE_left _ _, slotInf_flatLE_left _ _, slotInf_flatLE_left _ _,
       fun hr => band_true_left hr,
       slotInf_flatLE_left _ _, slotInf_flatLE_left _ _, slotInf_flatLE_left _ _,
       slotInf_flatLE_left _ _, slotInf_flatLE_left _ _, slotInf_flatLE_left _ _,
       slotInf_flatLE_left _ _⟩
    inf_le_right := fun f g => show Subsumes (min f g) g from
      ⟨slotInf_flatLE_right _ _, slotInf_flatLE_right _ _, slotInf_flatLE_right _ _,
       slotInf_flatLE_right _ _, slotInf_flatLE_right _ _, slotInf_flatLE_right _ _,
       fun hr => band_true_right hr,
       slotInf_flatLE_right _ _, slotInf_flatLE_right _ _, slotInf_flatLE_right _ _,
       slotInf_flatLE_right _ _, slotInf_flatLE_right _ _, slotInf_flatLE_right _ _,
       slotInf_flatLE_right _ _⟩
    le_inf := fun c f g hcf hcg => by
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hcf
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := hcg
      exact ⟨flatLE_slotInf a1 b1, flatLE_slotInf a2 b2, flatLE_slotInf a3 b3,
             flatLE_slotInf a4 b4, flatLE_slotInf a5 b5, flatLE_slotInf a6 b6,
             fun hr => band_true_intro (a7 hr) (b7 hr),
             flatLE_slotInf a8 b8, flatLE_slotInf a9 b9, flatLE_slotInf a10 b10,
             flatLE_slotInf a11 b11, flatLE_slotInf a12 b12, flatLE_slotInf a13 b13,
             flatLE_slotInf a14 b14⟩ }

/-! ### Unification computes least upper bounds — further laws -/

/-- `MorphFeatures` carries the pairwise-LUB structure of [carpenter-1992]'s
bounded complete partial order: `unify` is the partial join, with
`unify_isLUB` and `compatible_iff_bddAbove` supplying the two class
axioms. The unification laws — commutativity, associativity (with
failure propagating), `⊥`-identity, idempotence, monotonicity — are
inherited as one-line corollaries of the generic theorems in
`Core/Order/PartialUnify.lean`. -/
instance : PartialUnify MorphFeatures where
  unify := MorphFeatures.unify
  isLUB_of_unify_eq_some := unify_isLUB
  isSome_unify_of_bddAbove {a b} h :=
    (unify_eq_some_iff a b).mpr h

/-- The instance-projected `unify` is the same function as
`MorphFeatures.unify`. -/
@[simp] theorem unify_eq_partialUnify (f g : MorphFeatures) :
    PartialUnify.unify f g = f.unify g := rfl

/-- Unification succeeds with value `u` exactly when `u` is the least upper bound. -/
theorem unify_eq_some_iff_isLUB {f g u : MorphFeatures} :
    f.unify g = some u ↔ IsLUB {f, g} u := by
  rw [← unify_eq_partialUnify]
  exact PartialUnify.unify_eq_some_iff_isLUB

/-- Unification is commutative — a consequence of *total* compatibility: doubly
committed slots agree, so the per-field left bias washes out. -/
theorem unify_comm (f g : MorphFeatures) : f.unify g = g.unify f := by
  rw [← unify_eq_partialUnify, ← unify_eq_partialUnify]
  exact PartialUnify.unify_comm f g

/-- Unification is idempotent (§3.2.3's example law). -/
@[simp] theorem unify_self (f : MorphFeatures) : f.unify f = some f := by
  rw [← unify_eq_partialUnify]; exact PartialUnify.unify_self f

/-- Variables are unification identity elements (§3.2.3's example law):
unifying with the empty bundle returns the other input. -/
@[simp] theorem bot_unify (f : MorphFeatures) :
    (⊥ : MorphFeatures).unify f = some f := by
  rw [← unify_eq_partialUnify]; exact PartialUnify.bot_unify f

/-- Unification is associative, with failure propagating ([shieber-1986] §3.2.3's
order-independence): both associations compute the lub of all three bundles. -/
theorem unify_assoc (f g h : MorphFeatures) :
    (f.unify g).bind (·.unify h) = (g.unify h).bind (f.unify ·) := by
  have := PartialUnify.unify_assoc f g h
  simp only [unify_eq_partialUnify] at this
  exact this

/-- The empty bundle is a right identity for unification. -/
@[simp] theorem unify_bot (f : MorphFeatures) :
    f.unify (⊥ : MorphFeatures) = some f := by
  rw [← unify_eq_partialUnify]; exact PartialUnify.unify_bot f

/-- Unification fails exactly on incompatible inputs. -/
theorem unify_eq_none_iff (f g : MorphFeatures) :
    f.unify g = none ↔ ¬ Compatible f g := by
  rw [← unify_eq_partialUnify]
  exact PartialUnify.unify_eq_none_iff (a := f) (b := g)

/-- Unification is monotone where defined: shrinking both inputs preserves success and
shrinks the output. (Unguarded `merge`-monotonicity is false — the guard is needed.) -/
theorem unify_mono {f₁ f₂ g₁ g₂ u₂ : MorphFeatures} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂)
    (h2 : f₂.unify g₂ = some u₂) : ∃ u₁, f₁.unify g₁ = some u₁ ∧ u₁ ≤ u₂ := by
  rw [← unify_eq_partialUnify] at h2
  obtain ⟨u₁, hu₁, hle⟩ := PartialUnify.unify_mono hf hg h2
  exact ⟨u₁, unify_eq_partialUnify _ _ ▸ hu₁, hle⟩

end UD.MorphFeatures
