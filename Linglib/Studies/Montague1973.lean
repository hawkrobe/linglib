/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Logic.Assignment
import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Intensional.Rigidity
import Linglib.Semantics.Quantification.Polyadic
import Mathlib.Data.Fin.VecNotation

/-!
# Montague (1973): The Proper Treatment of Quantification in Ordinary English

The PTQ fragment as the paper builds it: syntactic categories and the category-to-type map
`f`, analysis trees for the rules its examples use (S1, S2, S4, S5, S14), and the
translation rules T1–T14 as one function `translate` into index- and assignment-relative
denotations at the types `f` assigns — with variables ranging over individual concepts, as
in the paper. The examples of §4 are theorems about `translate`.

* Under the meaning postulates for ordinary nouns and extensional verbs, the simple
  sentences translate to their first-order forms over the `*`-counterparts, and the two
  analysis trees of *a woman loves every man* translate to the two linear readings of
  `Quantification.Polyadic`, one entailing the other but not conversely: ambiguity
  "simply because quantifying terms may be introduced in more than one order".
* Partee's temperature puzzle: *the temperature is ninety* and *the temperature rises* are
  true while *ninety rises* is false, because *the temperature* denotes an individual
  concept and *is* asserts identity of extensions only; and *a price rises* is true of no
  individual, which is why its translation needs individual-concept variables.
* *John seeks a unicorn*: the de re analysis entails that there is a unicorn; the de dicto
  analysis is true in an interpretation with none.

Omitted: the string-level operations (gender, verb forms), tense (S17), and postulates
(5)–(9).

## References

* [R. Montague, *The Proper Treatment of Quantification in Ordinary English* (1973)][montague-1973]
* [D. Dowty, R. Wall, S. Peters, *Introduction to Montague Semantics*
  (1981)][dowty-wall-peters-1981]
-/

namespace Montague1973

open Intensional (Ty Denot)
open Intensional (IsRigid isRigid_const)
open Quantification (every_sem some_sem)
open Quantification.Polyadic (iterate surfaceScope inverseScope)

/-! ### Categories and the category-to-type map -/

/-- Syntactic categories: `e`, `t`, and the functor categories `A/B` and `A//B`, distinct as
categories but assigned the same type. -/
inductive Cat where
  | e | t
  | slash : Cat → Cat → Cat
  | dslash : Cat → Cat → Cat
  deriving DecidableEq, Repr

namespace Cat

/-- IV = t/e, intransitive verb phrases. -/
abbrev IV : Cat := .slash .t .e
/-- T = t/IV, terms. -/
abbrev T : Cat := .slash .t IV
/-- TV = IV/T, transitive verb phrases. -/
abbrev TV : Cat := .slash IV T
/-- CN = t//e, common noun phrases. -/
abbrev CN : Cat := .dslash .t .e

/-- The category-to-type map `f`: `f(e) = e`, `f(t) = t`,
`f(A/B) = f(A//B) = ⟨⟨s, f(B)⟩, f(A)⟩`. -/
abbrev ty : Cat → Ty
  | .e => .e
  | .t => .t
  | .slash a b | .dslash a b => .intens b.ty ⇒ a.ty

example : T.ty = (.intens (.intens .e ⇒ .t) ⇒ .t) := rfl
example : CN.ty = IV.ty := rfl

end Cat

/-! ### Basic expressions and analysis trees -/

/-- The basic expressions the examples use, by category. -/
inductive Basic : Cat → Type
  | john : Basic .T
  | mary : Basic .T
  | bill : Basic .T
  | ninety : Basic .T
  | man : Basic .CN
  | woman : Basic .CN
  | unicorn : Basic .CN
  | price : Basic .CN
  | temperature : Basic .CN
  | walk : Basic .IV
  | rise : Basic .IV
  | love : Basic .TV
  | find : Basic .TV
  | seek : Basic .TV
  | be : Basic .TV

/-- Analysis trees for the rules the examples use: basic expressions (S1), the determiners
*every*, *the*, *a* (S2), subject–predicate `F₄` (S4), verb–object `F₅` (S5), the pronoun
`heₙ`, and quantifying-in `F₁₀,ₙ` (S14). -/
inductive Analysis : Cat → Type
  | basic {A : Cat} : Basic A → Analysis A
  | he (n : ℕ) : Analysis .T
  | every : Analysis .CN → Analysis .T
  | the : Analysis .CN → Analysis .T
  | a : Analysis .CN → Analysis .T
  | f4 : Analysis .T → Analysis .IV → Analysis .t
  | f5 : Analysis .TV → Analysis .T → Analysis .IV
  | f10 (n : ℕ) : Analysis .T → Analysis .t → Analysis .t

/-! ### Interpretations and translation -/

variable (E W : Type)

/-- An interpretation of the fragment's constants: the names denote individuals (postulate
(1) makes their concepts rigid, so the individual is all that matters), and each other
constant denotes a sense of its type — an extension at every index. -/
structure Interp where
  john : E
  mary : E
  bill : E
  ninety : E
  man : W → Denot E W Cat.CN.ty
  woman : W → Denot E W Cat.CN.ty
  unicorn : W → Denot E W Cat.CN.ty
  price : W → Denot E W Cat.CN.ty
  temperature : W → Denot E W Cat.CN.ty
  walk : W → Denot E W Cat.IV.ty
  rise : W → Denot E W Cat.IV.ty
  love : W → Denot E W Cat.TV.ty
  find : W → Denot E W Cat.TV.ty
  seek : W → Denot E W Cat.TV.ty

variable {E W}

/-- The translation rules T1–T14: the extension at index `i`, under the assignment `g` of
individual-concept variables, of an analysis tree's translation, at the type `f` assigns
its category. Names translate to `P̂ P{^j}`, `heₙ` to `P̂ P{xₙ}`, *be* to
`Q̂ x̂ Q{ŷ [ˇx = ˇy]}`, the determiners by T2, the functional-application rules by
`α'(^β')`, and quantifying-in by `α'(x̂ₙ φ')`. -/
def translate (M : Interp E W) :
    {A : Cat} → Analysis A → Assignment (W → E) → W → Denot E W A.ty
  | _, .basic .john, _, i => fun P => P i fun _ => M.john
  | _, .basic .mary, _, i => fun P => P i fun _ => M.mary
  | _, .basic .bill, _, i => fun P => P i fun _ => M.bill
  | _, .basic .ninety, _, i => fun P => P i fun _ => M.ninety
  | _, .basic .man, _, i => M.man i
  | _, .basic .woman, _, i => M.woman i
  | _, .basic .unicorn, _, i => M.unicorn i
  | _, .basic .price, _, i => M.price i
  | _, .basic .temperature, _, i => M.temperature i
  | _, .basic .walk, _, i => M.walk i
  | _, .basic .rise, _, i => M.rise i
  | _, .basic .love, _, i => M.love i
  | _, .basic .find, _, i => M.find i
  | _, .basic .seek, _, i => M.seek i
  | _, .basic .be, _, i => fun Q x => Q i fun j y => x j = y j
  | _, .he n, g, i => fun P => P i (g n)
  | _, .every ζ, g, i => fun P => ∀ x, translate M ζ g i x → P i x
  | _, .the ζ, g, i => fun P => ∃ y, (∀ x, translate M ζ g i x ↔ x = y) ∧ P i y
  | _, .a ζ, g, i => fun P => ∃ x, translate M ζ g i x ∧ P i x
  | _, .f4 α δ, g, i => translate M α g i fun j => translate M δ g j
  | _, .f5 δ β, g, i => translate M δ g i fun j => translate M β g j
  | _, .f10 n α φ, g, i =>
    translate M α g i fun j x => translate M φ (Function.update g n x) j

/-! ### Extensional counterparts and meaning postulates -/

/-- `δ*` for a common noun or intransitive verb, `û δ(^u)`: the individuals whose rigid
concept is in `δ`'s extension. -/
def star₁ (δ : Denot E W Cat.CN.ty) : E → Prop := fun u => δ fun _ => u

/-- `δ*` for a transitive verb, `v̂ û δ(^u, ^v*)`, object-first: `star₂ δ v u` says `u`
bears `δ` to `v`. -/
def star₂ (δ : Denot E W Cat.TV.ty) : E → E → Prop :=
  fun v u => δ (fun j P => P j fun _ => v) fun _ => u

/-- The postulates the examples rest on ((1)–(4) of the paper): names are rigid (built into
`Interp`), the ordinary common nouns hold only of rigid concepts, *walk* is extensional,
and *love* and *find* reduce to relations between individuals. -/
structure Interp.LogicallyPossible (M : Interp E W) : Prop where
  man_rigid : ∀ i x, M.man i x → IsRigid x
  woman_rigid : ∀ i x, M.woman i x → IsRigid x
  unicorn_rigid : ∀ i x, M.unicorn i x → IsRigid x
  walk_ext : ∃ m : W → E → Prop, ∀ i x, M.walk i x ↔ m i (x i)
  love_ext : ∃ S : W → E → E → Prop, ∀ i Q x, M.love i Q x ↔ Q i fun j y => S j (x j) (y j)
  find_ext : ∃ S : W → E → E → Prop, ∀ i Q x, M.find i Q x ↔ Q i fun j y => S j (x j) (y j)

/-- A common noun holding only of rigid concepts is definable from its `*`-counterpart. -/
theorem star₁_iff {δ : Denot E W Cat.CN.ty} (hδ : ∀ x, δ x → IsRigid x) (x : W → E) (i : W) :
    δ x ↔ IsRigid x ∧ star₁ δ (x i) :=
  ⟨fun hx => ⟨hδ x hx, (congrArg δ ((hδ x hx).eq_const i)).mp hx⟩,
    fun ⟨hr, hx⟩ => (congrArg δ (hr.eq_const i)).mpr hx⟩

namespace Interp.LogicallyPossible

variable {M : Interp E W} (h : M.LogicallyPossible)
include h

theorem man_iff (i : W) (x : W → E) : M.man i x ↔ IsRigid x ∧ star₁ (M.man i) (x i) :=
  star₁_iff (h.man_rigid i) x i

theorem woman_iff (i : W) (x : W → E) : M.woman i x ↔ IsRigid x ∧ star₁ (M.woman i) (x i) :=
  star₁_iff (h.woman_rigid i) x i

theorem unicorn_iff (i : W) (x : W → E) :
    M.unicorn i x ↔ IsRigid x ∧ star₁ (M.unicorn i) (x i) :=
  star₁_iff (h.unicorn_rigid i) x i

/-- A transitive verb satisfying postulate (4) is definable from its `*`-counterpart:
`δ(x, Q) ↔ Q{ŷ δ*(ˇx, ˇy)}`. -/
theorem love_iff (i : W) (Q : W → Denot E W Cat.T.ty) (x : W → E) :
    M.love i Q x ↔ Q i fun j y => star₂ (M.love j) (y j) (x j) := by
  obtain ⟨S, hS⟩ := h.love_ext
  have : ∀ j v u, star₂ (M.love j) v u ↔ S j u v := fun j v u => hS j _ _
  simp only [hS]
  exact iff_of_eq (congrArg (Q i) (funext fun j => funext fun y => propext (this j _ _).symm))

theorem find_iff (i : W) (Q : W → Denot E W Cat.T.ty) (x : W → E) :
    M.find i Q x ↔ Q i fun j y => star₂ (M.find j) (y j) (x j) := by
  obtain ⟨S, hS⟩ := h.find_ext
  have : ∀ j v u, star₂ (M.find j) v u ↔ S j u v := fun j v u => hS j _ _
  simp only [hS]
  exact iff_of_eq (congrArg (Q i) (funext fun j => funext fun y => propext (this j _ _).symm))

end Interp.LogicallyPossible

/-- First-order data for the fragment: individuals, sets and relations (relations
object-first). -/
structure ExtData (E : Type) where
  john : E
  mary : E
  bill : E
  ninety : E
  man : E → Prop
  woman : E → Prop
  unicorn : E → Prop
  price : E → Prop
  temperature : E → Prop
  walk : E → Prop
  rise : E → Prop
  love : E → E → Prop
  find : E → E → Prop
  seek : E → E → Prop

variable (W) in
/-- The interpretation induced by first-order data, in which every constant is extensional:
a noun holds of the rigid concepts of its members, a verb of the concepts whose value at the
index is in its extension, and a transitive verb reduces to its relation. -/
def ExtData.interp (d : ExtData E) : Interp E W where
  john := d.john
  mary := d.mary
  bill := d.bill
  ninety := d.ninety
  man i x := IsRigid x ∧ d.man (x i)
  woman i x := IsRigid x ∧ d.woman (x i)
  unicorn i x := IsRigid x ∧ d.unicorn (x i)
  price i x := IsRigid x ∧ d.price (x i)
  temperature i x := IsRigid x ∧ d.temperature (x i)
  walk i x := d.walk (x i)
  rise i x := d.rise (x i)
  love i Q x := Q i fun j y => d.love (y j) (x j)
  find i Q x := Q i fun j y => d.find (y j) (x j)
  seek i Q x := Q i fun j y => d.seek (y j) (x j)

theorem ExtData.interp_logicallyPossible (d : ExtData E) : (d.interp W).LogicallyPossible where
  man_rigid _ _ hx := hx.1
  woman_rigid _ _ hx := hx.1
  unicorn_rigid _ _ hx := hx.1
  walk_ext := ⟨fun _ => d.walk, fun _ _ => Iff.rfl⟩
  love_ext := ⟨fun _ u v => d.love v u, fun _ _ _ => Iff.rfl⟩
  find_ext := ⟨fun _ u v => d.find v u, fun _ _ _ => Iff.rfl⟩

@[simp] theorem ExtData.star₁_man (d : ExtData E) (i : W) : star₁ ((d.interp W).man i) = d.man :=
  funext fun u => propext ⟨And.right, fun h => ⟨isRigid_const u, h⟩⟩

@[simp] theorem ExtData.star₁_woman (d : ExtData E) (i : W) :
    star₁ ((d.interp W).woman i) = d.woman :=
  funext fun u => propext ⟨And.right, fun h => ⟨isRigid_const u, h⟩⟩

@[simp] theorem ExtData.star₁_unicorn (d : ExtData E) (i : W) :
    star₁ ((d.interp W).unicorn i) = d.unicorn :=
  funext fun u => propext ⟨And.right, fun h => ⟨isRigid_const u, h⟩⟩

@[simp] theorem ExtData.star₁_walk (d : ExtData E) (i : W) : star₁ ((d.interp W).walk i) = d.walk :=
  rfl

@[simp] theorem ExtData.star₂_love (d : ExtData E) (i : W) : star₂ ((d.interp W).love i) = d.love :=
  rfl

@[simp] theorem ExtData.star₂_find (d : ExtData E) (i : W) : star₂ ((d.interp W).find i) = d.find :=
  rfl

/-! ### The examples of §4: extensional cases -/

open Analysis Basic

/-- *Bill is Mary* translates to `b = m`. -/
theorem translate_bill_is_mary (M : Interp E W) (g : Assignment (W → E)) (i : W) :
    translate M (f4 (basic bill) (f5 (basic be) (basic mary))) g i ↔ M.bill = M.mary :=
  Iff.rfl

section Extensional

variable {M : Interp E W} (h : M.LogicallyPossible) (g : Assignment (W → E)) (i : W)
include h

/-- *every man walks* translates to `∧u[man*(u) → walk*(u)]`. -/
theorem translate_every_man_walks :
    translate M (f4 (every (basic man)) (basic walk)) g i ↔
      every_sem (star₁ (M.man i)) (star₁ (M.walk i)) := by
  simp only [translate, every_sem]
  refine ⟨fun H u hu => H _ hu, fun H x hx => ?_⟩
  obtain ⟨hr, hx⟩ := (h.man_iff i x).1 hx
  exact (congrArg (M.walk i) (hr.eq_const i)).mpr (H _ hx)

/-- *a man walks* translates to `∨u[man*(u) ∧ walk*(u)]`. -/
theorem translate_a_man_walks :
    translate M (f4 (a (basic man)) (basic walk)) g i ↔
      some_sem (star₁ (M.man i)) (star₁ (M.walk i)) := by
  simp only [translate, some_sem]
  refine ⟨fun ⟨x, hx, hw⟩ => ?_, fun ⟨u, hu, hw⟩ => ⟨_, hu, hw⟩⟩
  obtain ⟨hr, hx⟩ := (h.man_iff i x).1 hx
  exact ⟨x i, hx, (congrArg (M.walk i) (hr.eq_const i)).mp hw⟩

/-- *the man walks* translates to `∨v[∧u[man*(u) ↔ u = v] ∧ walk*(v)]`. -/
theorem translate_the_man_walks :
    translate M (f4 (the (basic man)) (basic walk)) g i ↔
      ∃ v, (∀ u, star₁ (M.man i) u ↔ u = v) ∧ star₁ (M.walk i) v := by
  simp only [translate]
  constructor
  · rintro ⟨y, hy, hw⟩
    obtain ⟨hr, -⟩ := (h.man_iff i y).1 ((hy y).2 rfl)
    rw [hr.eq_const i] at hy hw
    refine ⟨y i, fun u => (hy _).trans ⟨fun e => congrFun e i, congrArg fun v _ => v⟩, hw⟩
  · rintro ⟨v, hv, hw⟩
    refine ⟨fun _ => v, fun x => ⟨fun hx => ?_, fun e => (congrArg (M.man i) e).mpr ?_⟩, hw⟩
    · obtain ⟨hr, hx⟩ := (h.man_iff i x).1 hx
      exact (hr.eq_const i).trans (congrArg (fun w _ => w) ((hv _).1 hx))
    · exact (hv v).2 rfl

/-- *John finds a unicorn* translates to `∨u[unicorn*(u) ∧ find*(j, u)]`. -/
theorem translate_john_finds_a_unicorn :
    translate M (f4 (basic john) (f5 (basic find) (a (basic unicorn)))) g i ↔
      some_sem (star₁ (M.unicorn i)) (star₂ (M.find i) · M.john) := by
  simp only [translate, some_sem, h.find_iff]
  refine ⟨fun ⟨x, hx, hf⟩ => ?_, fun ⟨u, hu, hf⟩ => ⟨_, hu, hf⟩⟩
  obtain ⟨-, hx⟩ := (h.unicorn_iff i x).1 hx
  exact ⟨x i, hx, hf⟩

/-- *Bill is a man* translates to `man*(b)`. -/
theorem translate_bill_is_a_man :
    translate M (f4 (basic bill) (f5 (basic be) (a (basic man)))) g i ↔
      star₁ (M.man i) M.bill := by
  simp only [translate]
  refine ⟨fun ⟨x, hx, e⟩ => ?_, fun hb => ⟨_, hb, rfl⟩⟩
  obtain ⟨-, hx⟩ := (h.man_iff i x).1 hx
  exact e ▸ hx

end Extensional

/-! ### *A woman loves every man*: two analysis trees -/

/-- The direct analysis, `F₄(a woman, F₅(love, every man))`. -/
def aWomanLovesEveryMan.direct : Analysis .t :=
  f4 (a (basic woman)) (f5 (basic love) (every (basic man)))

/-- The quantifying-in analysis, `F₁₀,₀(every man, F₄(a woman, F₅(love, he₀)))`. -/
def aWomanLovesEveryMan.quantifiedIn : Analysis .t :=
  f10 0 (every (basic man)) (f4 (a (basic woman)) (f5 (basic love) (he 0)))

section Scope

variable {M : Interp E W} (h : M.LogicallyPossible) (g : Assignment (W → E)) (i : W)
include h

/-- The direct analysis translates to `∨u[woman*(u) ∧ ∧v[man*(v) → love*(u, v)]]`: the
existential scopes over the universal. -/
theorem translate_direct :
    translate M aWomanLovesEveryMan.direct g i ↔
      surfaceScope some_sem every_sem (star₁ (M.woman i)) (star₁ (M.man i))
        (fun u v => star₂ (M.love i) v u) := by
  simp only [aWomanLovesEveryMan.direct, translate, surfaceScope, iterate, some_sem, every_sem,
    h.love_iff]
  constructor
  · rintro ⟨y, hy, H⟩
    exact ⟨y i, ((h.woman_iff i y).1 hy).2, fun v hv => H _ hv⟩
  · rintro ⟨u, hu, H⟩
    refine ⟨fun _ => u, hu, fun x hx => ?_⟩
    exact H _ ((h.man_iff i x).1 hx).2

/-- The quantifying-in analysis translates to `∧v[man*(v) → ∨u[woman*(u) ∧ love*(u, v)]]`:
the universal scopes over the existential. -/
theorem translate_quantifiedIn :
    translate M aWomanLovesEveryMan.quantifiedIn g i ↔
      inverseScope some_sem every_sem (star₁ (M.woman i)) (star₁ (M.man i))
        (fun u v => star₂ (M.love i) v u) := by
  simp only [aWomanLovesEveryMan.quantifiedIn, translate, inverseScope, iterate, some_sem,
    every_sem, h.love_iff, Function.update_self]
  constructor
  · intro H v hv
    obtain ⟨y, hy, hl⟩ := H _ hv
    exact ⟨y i, ((h.woman_iff i y).1 hy).2, hl⟩
  · intro H x hx
    obtain ⟨u, hu, hl⟩ := H _ ((h.man_iff i x).1 hx).2
    exact ⟨fun _ => u, hu, hl⟩

/-- The direct reading entails the quantified-in one. -/
theorem translate_quantifiedIn_of_direct (H : translate M aWomanLovesEveryMan.direct g i) :
    translate M aWomanLovesEveryMan.quantifiedIn g i :=
  (translate_quantifiedIn h g i).2 <|
    Quantification.Polyadic.iterate_every_some_of_some_every _ _ _ ((translate_direct h g i).1 H)

end Scope

/-- A four-individual interpretation — the men `0`, `1`, the women `2`, `3` — in which each
man is loved by a woman and no woman loves every man. -/
def loveData : ExtData ℕ where
  john := 0
  mary := 2
  bill := 1
  ninety := 90
  man u := u = 0 ∨ u = 1
  woman u := u = 2 ∨ u = 3
  unicorn _ := False
  price _ := False
  temperature _ := False
  walk _ := True
  rise _ := False
  love v u := (u = 2 ∧ v = 0) ∨ (u = 3 ∧ v = 1)
  find _ _ := False
  seek _ _ := False

/-- The two analysis trees are not logically equivalent: in `loveData` the quantifying-in
reading is true and the direct reading false. -/
theorem aWomanLovesEveryMan_ambiguous (g : Assignment (Unit → ℕ)) :
    translate (loveData.interp Unit) aWomanLovesEveryMan.quantifiedIn g () ∧
      ¬ translate (loveData.interp Unit) aWomanLovesEveryMan.direct g () := by
  have h := loveData.interp_logicallyPossible (W := Unit)
  rw [translate_quantifiedIn h g (), translate_direct h g ()]
  simp only [inverseScope, surfaceScope, iterate, every_sem, some_sem, ExtData.star₁_man,
    ExtData.star₁_woman, ExtData.star₂_love, loveData]
  refine ⟨fun v hv => ?_, fun ⟨u, hu, H⟩ => ?_⟩
  · rcases hv with rfl | rfl
    · exact ⟨2, by omega, by omega⟩
    · exact ⟨3, by omega, by omega⟩
  · have h0 := H 0 (by omega)
    have h1 := H 1 (by omega)
    omega

/-! ### The temperature puzzle -/

/-- Two moments, at which the temperature is `90` and then `95`. -/
def temperatureConcept : Fin 2 → ℕ := ![90, 95]

/-- An interpretation over numbers and two moments: *temperature* holds of the one concept
`temperatureConcept`, and a concept *rises* at a moment if its value is larger at a later
one. Postulate (2) does not apply to *temperature* and *price*, and (3) not to *rise*. -/
def temperatureInterp : Interp ℕ (Fin 2) where
  john := 0
  mary := 0
  bill := 0
  ninety := 90
  man _ _ := False
  woman _ _ := False
  unicorn _ _ := False
  price _ x := x = temperatureConcept
  temperature _ x := x = temperatureConcept
  walk _ _ := False
  rise i x := ∃ j, i < j ∧ x i < x j
  love _ _ _ := False
  find _ _ _ := False
  seek _ _ _ := False

/-- Partee's argument is invalid: at the first moment *the temperature is ninety* and *the
temperature rises* are true but *ninety rises* is false. -/
theorem temperature_argument_invalid (g : Assignment (Fin 2 → ℕ)) :
    translate temperatureInterp (f4 (the (basic temperature)) (f5 (basic be) (basic ninety))) g 0 ∧
      translate temperatureInterp (f4 (the (basic temperature)) (basic rise)) g 0 ∧
      ¬ translate temperatureInterp (f4 (basic ninety) (basic rise)) g 0 := by
  simp only [translate, temperatureInterp]
  exact ⟨⟨_, fun _ => Iff.rfl, rfl⟩, ⟨_, fun _ => Iff.rfl, 1, by decide, by decide⟩,
    fun ⟨_, _, hlt⟩ => lt_irrefl _ hlt⟩

/-- *A price rises* is true although no individual rises: the existential ranges over
individual concepts, which is why the translation needs individual-concept variables. -/
theorem a_price_rises (g : Assignment (Fin 2 → ℕ)) :
    translate temperatureInterp (f4 (a (basic price)) (basic rise)) g 0 ∧
      ∀ u : ℕ, ¬ temperatureInterp.rise 0 fun _ => u := by
  simp only [translate, temperatureInterp]
  exact ⟨⟨_, rfl, 1, by decide, by decide⟩, fun _ ⟨_, _, hlt⟩ => lt_irrefl _ hlt⟩

/-! ### *John seeks a unicorn*: de dicto and de re -/

/-- The de dicto analysis, `F₄(John, F₅(seek, a unicorn))`. -/
def johnSeeksAUnicorn.deDicto : Analysis .t := f4 (basic john) (f5 (basic seek) (a (basic unicorn)))

/-- The de re analysis, `F₁₀,₀(a unicorn, F₄(John, F₅(seek, he₀)))`. -/
def johnSeeksAUnicorn.deRe : Analysis .t :=
  f10 0 (a (basic unicorn)) (f4 (basic john) (f5 (basic seek) (he 0)))

/-- The de re reading entails that there is a unicorn, in every interpretation. -/
theorem exists_unicorn_of_deRe (M : Interp E W) (g : Assignment (W → E)) (i : W)
    (H : translate M johnSeeksAUnicorn.deRe g i) : ∃ x, M.unicorn i x := by
  simp only [johnSeeksAUnicorn.deRe, translate] at H
  obtain ⟨x, hx, -⟩ := H
  exact ⟨x, hx⟩

/-- An interpretation in which John seeks every property and there are no unicorns. -/
def seekingInterp : Interp ℕ Unit :=
  { loveData.interp Unit with seek := fun _ _ _ => True }

/-- The de dicto reading does not entail that there is a unicorn: it is true in
`seekingInterp`, where nothing is a unicorn. -/
theorem deDicto_without_unicorns (g : Assignment (Unit → ℕ)) :
    translate seekingInterp johnSeeksAUnicorn.deDicto g () ∧
      ∀ x, ¬ seekingInterp.unicorn () x :=
  ⟨trivial, fun _ h => h.2⟩

end Montague1973
