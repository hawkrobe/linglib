import Linglib.Data.UD.Basic
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
operation. A natural in-house consumer is the *matching clause* of DM's Subset
Principle (an exponent is insertable iff `exponent.features ≤ morpheme.features`);
the competition clause — most-specified-wins — is separate `argmax` machinery, already
implemented in `Morphology/DM/VocabularyInsertion.lean`. (Nanosyntax's Superset
Principle is *not* a consumer: it matches by containment of syntactic trees, see
`Nanosyntax/TreeSpellout.lean`'s `NanoTree.contains`, not by an order on flat
bundles.) Lives apart from `Data/UD/Basic.lean` so the (heavily imported) standard
mirror stays mathlib-free — this file is the one that pays for `Mathlib.Order` — and
it is the canonical home for order instances on `UD.MorphFeatures`.
-/

set_option autoImplicit false

/-! ### The flat order on one feature slot -/

/-- The flat information order on an atomic feature slot ([shieber-1986] §3.2.2):
`none` (no information) is below everything; distinct atoms are incomparable. Stated
as preservation of commitment: every committed value persists upward. -/
def Option.FlatLE {α : Type _} (a b : Option α) : Prop :=
  ∀ x : α, a = some x → b = some x

namespace Option.FlatLE

variable {α : Type _} {a b c : Option α}

protected theorem refl (a : Option α) : a.FlatLE a := fun _ h => h

protected theorem trans (h1 : a.FlatLE b) (h2 : b.FlatLE c) : a.FlatLE c :=
  fun x hx => h2 x (h1 x hx)

protected theorem antisymm (h1 : a.FlatLE b) (h2 : b.FlatLE a) : a = b := by
  cases a with
  | some x => exact (h1 x rfl).symm
  | none =>
    cases b with
    | none => rfl
    | some y => exact absurd (h2 y rfl) (by simp)

theorem none_le (b : Option α) : Option.FlatLE none b := fun _ h => nomatch h

instance [DecidableEq α] : Decidable (a.FlatLE b) :=
  match a, b with
  | none, _ => .isTrue (fun _ h => nomatch h)
  | some x, some y =>
    if h : x = y then .isTrue (fun _ hx => by simpa [h] using hx)
    else .isFalse (fun hle => h (Option.some.inj (hle x rfl)).symm)
  | some x, none => .isFalse (fun hle => nomatch hle x rfl)

end Option.FlatLE

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

private theorem bool_le_antisymm {x y : Bool}
    (h1 : x = true → y = true) (h2 : y = true → x = true) : x = y := by
  cases x <;> cases y <;> simp_all

instance : PartialOrder MorphFeatures where
  le := Subsumes
  le_refl f :=
    ⟨.refl _, .refl _, .refl _, .refl _, .refl _, .refl _, id,
     .refl _, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _⟩
  le_trans f g h hfg hgh := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hfg
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := hgh
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5,
           a6.trans b6, fun hr => b7 (a7 hr), a8.trans b8, a9.trans b9,
           a10.trans b10, a11.trans b11, a12.trans b12, a13.trans b13, a14.trans b14⟩
  le_antisymm f g hfg hgf := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hfg
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := hgf
    cases f; cases g
    simp only [mk.injEq]
    exact ⟨a1.antisymm b1, a2.antisymm b2, a3.antisymm b3, a4.antisymm b4,
           a5.antisymm b5, a6.antisymm b6, bool_le_antisymm a7 b7,
           a8.antisymm b8, a9.antisymm b9, a10.antisymm b10, a11.antisymm b11,
           a12.antisymm b12, a13.antisymm b13, a14.antisymm b14⟩

instance (f g : MorphFeatures) : Decidable (Subsumes f g) := by
  unfold Subsumes; infer_instance

/-- Subsumption is decidable (each slot is). -/
instance (f g : MorphFeatures) : Decidable (f ≤ g) :=
  inferInstanceAs (Decidable (Subsumes f g))

/-- The empty bundle — Shieber's variable `[ ]` — is bottom: "variables subsume all
other feature structures … they contain no information at all" (§3.2.2). -/
instance : OrderBot MorphFeatures where
  bot := {}
  bot_le f := show Subsumes {} f from
    ⟨Option.FlatLE.none_le _, Option.FlatLE.none_le _, Option.FlatLE.none_le _,
     Option.FlatLE.none_le _, Option.FlatLE.none_le _, Option.FlatLE.none_le _,
     (fun h => nomatch h : ({} : MorphFeatures).reflex = true → f.reflex = true),
     Option.FlatLE.none_le _, Option.FlatLE.none_le _, Option.FlatLE.none_le _,
     Option.FlatLE.none_le _, Option.FlatLE.none_le _, Option.FlatLE.none_le _,
     Option.FlatLE.none_le _⟩

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

private theorem orElse_comm_of_clause {α : Type _} [BEq α] [LawfulBEq α]
    {a b : Option α} (hcl : (a.isNone || b.isNone || a == b) = true) :
    (a <|> b) = (b <|> a) := by
  cases a with
  | none => cases b <;> rfl
  | some x =>
    cases b with
    | none => rfl
    | some y => simp [clause_of_some_some hcl]

/-- Unification is commutative — a consequence of *total* compatibility: doubly
committed slots agree, so the per-field left bias washes out. -/
theorem unify_comm (f g : MorphFeatures) : f.unify g = g.unify f := by
  unfold unify
  by_cases hc : f.compatible g = true
  · have hc2 : g.compatible f = true := compatible_comm f g ▸ hc
    simp only [hc, hc2, if_true, Option.some.injEq]
    simp only [compatible, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := hc
    unfold merge
    simp only [mk.injEq]
    exact ⟨orElse_comm_of_clause h1, orElse_comm_of_clause h2, orElse_comm_of_clause h3,
           orElse_comm_of_clause h4, orElse_comm_of_clause h5, orElse_comm_of_clause h6,
           Bool.or_comm _ _, orElse_comm_of_clause h7, orElse_comm_of_clause h8,
           orElse_comm_of_clause h9, orElse_comm_of_clause h10, orElse_comm_of_clause h11,
           orElse_comm_of_clause h12, orElse_comm_of_clause h13⟩
  · have hc' : ¬ g.compatible f = true := by rwa [compatible_comm g f]
    simp [hc, hc']

private theorem orElse_self {α : Type _} (a : Option α) : (a <|> a) = a := by
  cases a <;> rfl

/-- Unification is idempotent (§3.2.3's example law). -/
@[simp] theorem unify_self (f : MorphFeatures) : f.unify f = some f := by
  unfold unify
  simp only [compatible_self, if_true, Option.some.injEq]
  unfold merge
  cases f
  simp only [mk.injEq]
  exact ⟨orElse_self _, orElse_self _, orElse_self _, orElse_self _, orElse_self _,
         orElse_self _, Bool.or_self _, orElse_self _, orElse_self _, orElse_self _,
         orElse_self _, orElse_self _, orElse_self _, orElse_self _⟩

/-- Variables are unification identity elements (§3.2.3's example law): unifying with
the empty bundle returns the other input. -/
@[simp] theorem bot_unify (f : MorphFeatures) : (⊥ : MorphFeatures).unify f = some f := by
  have hb : (⊥ : MorphFeatures).compatible f = true :=
    compatible_of_le (u := f) bot_le le_rfl
  unfold unify
  simp only [hb, if_true, Option.some.injEq]
  show merge ⊥ f = f
  unfold merge
  cases f
  rfl

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

/-- Unification succeeds with value `u` exactly when `u` is the least upper bound. -/
theorem unify_eq_some_iff_isLUB {f g u : MorphFeatures} :
    f.unify g = some u ↔ IsLUB {f, g} u := by
  refine ⟨unify_isLUB, fun hu => ?_⟩
  have hc : f.compatible g = true :=
    compatible_of_le (hu.1 (Set.mem_insert _ _)) (hu.1 (Set.mem_insert_of_mem _ rfl))
  have hm : f.unify g = some (f.merge g) := by simp [unify, hc]
  rw [hm, Option.some_inj]
  exact (unify_isLUB hm).unique hu

private theorem isLUB_pair_step {f g h v u : MorphFeatures} (hv : IsLUB {f, g} v) :
    IsLUB {v, h} u ↔ IsLUB ({f, g, h} : Set MorphFeatures) u := by
  have hub : upperBounds ({v, h} : Set MorphFeatures) = upperBounds {f, g, h} := by
    ext w
    constructor
    · intro hw x hx
      rcases hx with rfl | rfl | rfl
      · exact (hv.1 (Set.mem_insert _ _)).trans (hw (Set.mem_insert _ _))
      · exact (hv.1 (Set.mem_insert_of_mem _ rfl)).trans (hw (Set.mem_insert _ _))
      · exact hw (Set.mem_insert_of_mem _ rfl)
    · intro hw x hx
      rcases hx with rfl | rfl
      · exact hv.2 fun y hy => by
          rcases hy with rfl | rfl
          · exact hw (Set.mem_insert _ _)
          · exact hw (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact hw (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  unfold IsLUB
  rw [hub]

/-- Unification is associative, with failure propagating ([shieber-1986] §3.2.3's
order-independence): both associations compute the lub of all three bundles. -/
theorem unify_assoc (f g h : MorphFeatures) :
    (f.unify g).bind (·.unify h) = (g.unify h).bind (f.unify ·) := by
  apply Option.ext
  intro u
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨v, hv, hu⟩
    have h3 : IsLUB ({f, g, h} : Set MorphFeatures) u :=
      (isLUB_pair_step (unify_isLUB hv)).mp (unify_isLUB hu)
    have hgh : g.compatible h = true := by
      refine compatible_of_le (u := u) ?_ ?_
      · exact h3.1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact h3.1 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    refine ⟨g.merge h, by simp [unify, hgh], ?_⟩
    have hw : IsLUB ({g, h} : Set MorphFeatures) (g.merge h) :=
      unify_isLUB (by simp [unify, hgh])
    rw [unify_eq_some_iff_isLUB]
    have : IsLUB ({g, h, f} : Set MorphFeatures) u := by
      have : ({g, h, f} : Set MorphFeatures) = {f, g, h} := by
        ext x; simp [Set.mem_insert_iff]; tauto
      rw [this]; exact h3
    have step := (isLUB_pair_step hw).mpr this
    have : ({g.merge h, f} : Set MorphFeatures) = {f, g.merge h} := Set.pair_comm _ _
    rwa [← this]
  · rintro ⟨w, hw, hu⟩
    have hu' : IsLUB ({g.merge h, f} : Set MorphFeatures) u := by
      rw [Set.pair_comm]
      rw [unify_eq_some_iff_isLUB] at hu
      have hwm : g.merge h = w := by
        have : g.unify h = some w := hw
        have hgh : g.compatible h = true :=
          compatible_of_le ((unify_isLUB hw).1 (Set.mem_insert _ _))
            ((unify_isLUB hw).1 (Set.mem_insert_of_mem _ rfl))
        simpa [unify, hgh] using this
      rwa [← hwm] at hu
    have h3 : IsLUB ({g, h, f} : Set MorphFeatures) u := by
      have hgh : g.compatible h = true :=
        compatible_of_le ((unify_isLUB hw).1 (Set.mem_insert _ _))
          ((unify_isLUB hw).1 (Set.mem_insert_of_mem _ rfl))
      exact (isLUB_pair_step (unify_isLUB (by simp [unify, hgh] :
        g.unify h = some (g.merge h)))).mp hu'
    have h3' : IsLUB ({f, g, h} : Set MorphFeatures) u := by
      have : ({g, h, f} : Set MorphFeatures) = {f, g, h} := by
        ext x; simp [Set.mem_insert_iff]; tauto
      rwa [this] at h3
    have hfg : f.compatible g = true := by
      refine compatible_of_le (u := u) ?_ ?_
      · exact h3'.1 (Set.mem_insert _ _)
      · exact h3'.1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    refine ⟨f.merge g, by simp [unify, hfg], ?_⟩
    rw [unify_eq_some_iff_isLUB]
    exact (isLUB_pair_step (unify_isLUB (by simp [unify, hfg] :
      f.unify g = some (f.merge g)))).mpr h3'

/-- The empty bundle is a right identity for unification. -/
@[simp] theorem unify_bot (f : MorphFeatures) : f.unify (⊥ : MorphFeatures) = some f := by
  rw [unify_comm]; exact bot_unify f

/-- Unification fails exactly on incompatible inputs. -/
theorem unify_eq_none_iff (f g : MorphFeatures) :
    f.unify g = none ↔ ¬ Compatible f g := by
  rw [← compatible_iff_bddAbove]
  unfold unify
  by_cases hc : f.compatible g = true <;> simp [hc]

/-- Unification is monotone where defined: shrinking both inputs preserves success and
shrinks the output. (Unguarded `merge`-monotonicity is false — the guard is needed.) -/
theorem unify_mono {f₁ f₂ g₁ g₂ u₂ : MorphFeatures} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂)
    (h2 : f₂.unify g₂ = some u₂) : ∃ u₁, f₁.unify g₁ = some u₁ ∧ u₁ ≤ u₂ := by
  have hlub := unify_isLUB h2
  have hf1 : f₁ ≤ u₂ := hf.trans (hlub.1 (Set.mem_insert _ _))
  have hg1 : g₁ ≤ u₂ := hg.trans (hlub.1 (Set.mem_insert_of_mem _ rfl))
  have hc : f₁.compatible g₁ = true := compatible_of_le hf1 hg1
  exact ⟨f₁.merge g₁, by simp [unify, hc], merge_le hf1 hg1⟩

end UD.MorphFeatures
