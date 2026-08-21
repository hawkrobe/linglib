import Linglib.Semantics.Presupposition.Basic
import Linglib.Logic.Modal.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Karttunen (1973): presuppositions of compound sentences

[karttunen-1973] asks how the presuppositions of a compound sentence are determined by
those of its parts. Complement-taking predicates are *plugs* (verbs of saying: nothing
projects), *holes* (factives, aspectuals, implicatives: everything projects), or
*filters*; the connectives are filters with asymmetric conditions — `if A then B` (13)
and `A and B` (17) presuppose what `A` presupposes and what `B` presupposes unless `A`
entails it, while `A or B` (24) filters what the negation of `A` entails. §9 relativizes
the entailment to a set `X` of background assumptions, (24b′), and `Entails X A C` is
that relation; `cond`, `conj`, `disj` are the relativized rules, with `X = Set.univ` the
absolute ones.

§8 derives the coincidence of (13) and (17) from three principles Harman supplied —
internal negation preserves presuppositions, logically equivalent sentences share them,
and the classical equivalences hold — which here is `neg_cond_neg_presup`, with
`cond_neg_presup` the corresponding fact for disjunction. On the Geraldine example
(25)–(28) the second disjunct's presupposition (27) is not filtered absolutely but is
filtered given (28) (`geraldine_presup_absolute`, `geraldine_presup_relative`). §10
rejects truth-functional three-valued conjunction on (35): it filters by the falsity of
the first conjunct where the entailment filter does not (`kleene_35`, `conj_presup_35`);
the substrate's pointwise `PartialProp.andFilter` agrees with (17) where the first
conjunct holds (`conj_presup_iff_andFilter`) and shares the truth-functional verdict where
it fails (`andFilter_35b`). §11 treats propositional attitudes: the [hintikka-1962]
equivalence (38) lets the hole treatment of *believe* survive (37) by re-collecting the
conjunction inside the attitude (`hole_conj_presup`, `hole_conj_assertion_iff`), but not
(42), where *believe* and *hope* cannot be re-collected — hence the tentative verdict that
the class are plugs (`conj_plug_plug_presup`).
-/

namespace Karttunen1973

open Semantics.Presupposition (PartialProp)
open ModalLogic (box box_and)

variable {W : Type*} (X : Set W) (p q : PartialProp W) (w : W)

/-! ### The filters -/

/-- `A` entails `C` given the background assumptions `X`: `X ∪ {A} ⊨ C`. -/
def Entails (A C : W → Prop) : Prop := ∀ w ∈ X, A w → C w

instance [Fintype W] [DecidablePred (· ∈ X)] (A C : W → Prop) [DecidablePred A]
    [DecidablePred C] : Decidable (Entails X A C) :=
  inferInstanceAs (Decidable (∀ w ∈ X, A w → C w))

/-- (13), relativized by (24b′): `if A then B` presupposes what `A` presupposes, and what
`B` presupposes unless `A` entails it given `X`. -/
def cond : PartialProp W :=
  ⟨fun w => p.presup w ∧ (¬ Entails X p.assertion q.presup → q.presup w),
   fun w => p.assertion w → q.assertion w⟩

/-- (17), relativized: `A and B` presupposes what `A` presupposes, and what `B` presupposes
unless `A` entails it given `X`. -/
def conj : PartialProp W :=
  ⟨fun w => p.presup w ∧ (¬ Entails X p.assertion q.presup → q.presup w),
   fun w => p.assertion w ∧ q.assertion w⟩

/-- (24), relativized: `A or B` presupposes what `A` presupposes, and what `B` presupposes
unless the negation of `A` entails it given `X`. -/
def disj : PartialProp W :=
  ⟨fun w => p.presup w ∧ (¬ Entails X (fun w => ¬ p.assertion w) q.presup → q.presup w),
   fun w => p.assertion w ∨ q.assertion w⟩

/-! ### Harman's derivation (§8) -/

/-- The conjunction filter is the conditional filter through `A ∧ B ≡ ¬(A → ¬B)`, with
negation a hole. -/
theorem neg_cond_neg_presup :
    (PartialProp.neg (cond X p (PartialProp.neg q))).presup = (conj X p q).presup := rfl

/-- The disjunction filter is the conditional filter through `A ∨ B ≡ ¬A → B`. -/
theorem cond_neg_presup : (cond X (PartialProp.neg p) q).presup = (disj X p q).presup := rfl

/-- Where the first conjunct holds, (17) agrees with the substrate's pointwise filter
`PartialProp.andFilter`. -/
theorem conj_presup_iff_andFilter (hX : w ∈ X) (h : p.assertion w) :
    (conj X p q).presup w ↔ (PartialProp.andFilter p q).presup w :=
  and_congr_right fun _ =>
    ⟨fun hc _ => by_contra fun hq => hq (hc fun he => hq (he w hX h)), fun hq _ => hq h⟩

/-! ### Background assumptions (§9) -/

/-- Whether Geraldine is a Mormon and whether she has worn holy underwear. -/
inductive Geraldine where
  | mormonWorn
  | mormonUnworn
  | gentileWorn
  | gentileUnworn
  deriving DecidableEq, Fintype

/-- (26) `Geraldine is a Mormon`. -/
abbrev mormon : Set Geraldine := {.mormonWorn, .mormonUnworn}

/-- (27) `Geraldine has worn holy underwear`. -/
abbrev worn : Set Geraldine := {.mormonWorn, .gentileWorn}

/-- (28) `All Mormons have worn holy underwear`, Fred's background assumption. -/
abbrev allMormonsWorn : Set Geraldine := {Geraldine.mormonUnworn}ᶜ

/-- `She has given up wearing her holy underwear`: presupposes (27); the assertion is
idealized. -/
def givenUp : PartialProp Geraldine := ⟨(· ∈ worn), fun _ => True⟩

/-- (25) `Either Geraldine is not a Mormon or she has given up wearing her holy underwear`,
relative to the background `X`. -/
def geraldine (X : Set Geraldine) : PartialProp Geraldine :=
  disj X (.ofProp (· ∉ mormon)) givenUp

/-- Absolutely, (25) presupposes (27): (26) alone does not entail it. -/
theorem geraldine_presup_absolute : ¬ (geraldine Set.univ).presup .mormonUnworn := by
  simp only [geraldine, disj, Entails, PartialProp.ofProp, givenUp]; decide

/-- Given (28), (25) presupposes nothing: (26) and (28) together entail (27). -/
theorem geraldine_presup_relative : ∀ w ∈ allMormonsWorn, (geraldine allMormonsWorn).presup w := by
  simp only [geraldine, disj, Entails, PartialProp.ofProp, givenUp]; decide

/-! ### Truth-functional conjunction (§10) -/

/-- Whether Paris is the capital of France and whether France has a king. -/
inductive France where
  | parisKing
  | parisNoKing
  | marseilleKing
  | marseilleNoKing
  deriving DecidableEq, Fintype

/-- `Paris is the capital of France`. -/
abbrev capitalParis : Set France := {.parisKing, .parisNoKing}

/-- `France has a king`. -/
abbrev hasKing : Set France := {.parisKing, .marseilleKing}

/-- `The king of France is bald`: presupposes a king; baldness is idealized. -/
def kingBald : PartialProp France := ⟨(· ∈ hasKing), fun _ => True⟩

/-- (35a) `Paris is the capital of France, and the king of France is bald` and (35b) with
`Marseilles` both presuppose a king under (17): neither capital claim entails one. -/
theorem conj_presup_35 :
    ¬ (conj Set.univ (.ofProp (· ∈ capitalParis)) kingBald).presup .parisNoKing ∧
      ¬ (conj Set.univ (.ofProp (· ∉ capitalParis)) kingBald).presup .parisNoKing := by
  simp only [conj, Entails, PartialProp.ofProp, kingBald]; decide

open Semantics.Presupposition.PartialProp in
/-- Strong-Kleene conjunction makes (35b) false at the actual world and so bivalent —
presupposition-free — while (35a) is undefined. -/
theorem kleene_35 :
    eval (ofProp (· ∈ capitalParis)) .parisNoKing ⊓ eval kingBald .parisNoKing = .indet ∧
      eval (ofProp (· ∉ capitalParis)) .parisNoKing ⊓ eval kingBald .parisNoKing = .false := by
  rw [(eval_eq_true_iff (ofProp (· ∈ capitalParis)) _).2
      ⟨trivial, (by decide : France.parisNoKing ∈ capitalParis)⟩,
    (eval_eq_false_iff (ofProp (· ∉ capitalParis)) _).2
      ⟨trivial, (by decide : ¬ France.parisNoKing ∉ capitalParis)⟩,
    (eval_eq_indet_iff kingBald _).2 (by decide : France.parisNoKing ∉ hasKing)]
  decide

/-- The substrate's pointwise filter shares the truth-functional verdict on (35b): the
second conjunct's presupposition is filtered where the first conjunct is false. -/
theorem andFilter_35b :
    (PartialProp.andFilter (.ofProp (· ∉ capitalParis)) kingBald).presup .parisNoKing := by
  simp only [PartialProp.andFilter, PartialProp.ofProp, kingBald]; decide

/-! ### Propositional attitudes (§11) -/

section Attitudes

variable (att att₁ att₂ : (W → Prop) → W → Prop) (R : W → W → Prop) (A C : W → Prop)


/-- A hole lets the complement's presuppositions through: `att` applies to its assertion. -/
def hole (att : (W → Prop) → W → Prop) (φ : PartialProp W) : PartialProp W :=
  ⟨φ.presup, att φ.assertion⟩

/-- A plug blocks them. -/
def plug (att : (W → Prop) → W → Prop) (φ : PartialProp W) : PartialProp W :=
  ⟨fun _ => True, att φ.assertion⟩

/-- (37) `Bill believes that Fred has been beating Zelda, and furthermore, Bill believes that
Fred has stopped beating Zelda` under the hole treatment presupposes `A` unless the first
conjunct — that Bill believes `A` — entails `A`. The same holds of (42), with *hope* as the
second attitude. -/
theorem conj_hole_hole_presup :
    (conj Set.univ (hole att₁ (.ofProp A)) (hole att₂ ⟨A, C⟩)).presup w ↔
      (¬ (∀ v, att₁ A v → A v) → A w) := by
  simp [conj, Entails, hole, PartialProp.ofProp]

/-- (39), the re-collected `Bill believes that Fred has been beating Zelda and that he has
stopped`: the filter applies inside the complement and nothing is presupposed, whatever the
verb's status. -/
theorem hole_conj_presup : (hole att (conj Set.univ (.ofProp A) ⟨A, C⟩)).presup w :=
  ⟨trivial, fun h => (h fun _ _ hv => hv).elim⟩

/-- (38): (37) and (39) assert the same thing ([hintikka-1962]), so the hole treatment
survives (37) only by letting the equivalence do the filtering. -/
theorem hole_conj_assertion_iff :
    (hole (box R) (conj Set.univ (.ofProp A) ⟨A, C⟩)).assertion w ↔
      (conj Set.univ (hole (box R) (.ofProp A)) (hole (box R) ⟨A, C⟩)).assertion w :=
  box_and R A C w

/-- Two distinct attitudes (43) admit no re-collection; as plugs, (42) presupposes nothing
outright — K's tentative verdict for the whole class. -/
theorem conj_plug_plug_presup :
    (conj Set.univ (plug att₁ (.ofProp A)) (plug att₂ ⟨A, C⟩)).presup w :=
  ⟨trivial, fun _ => trivial⟩

end Attitudes

end Karttunen1973
