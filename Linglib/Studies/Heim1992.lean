import Linglib.Semantics.Attitudes.Desire.Conditional
import Linglib.Semantics.Dynamic.Partial
import Linglib.Semantics.Presupposition.BeliefEmbedding

/-!
# Heim (1992): presupposition projection in attitude reports

[heim-1992] derives Karttunen's generalization — if the complement of an
attitude report presupposes `p`, the report presupposes that the attitude
holder believes `p` ([karttunen-1974-presupposition]) — from context change potentials for
the attitude predicates. The belief rule (18) makes `c + a believes φ`
defined iff `Dox_a(w) + φ` is defined for every `w ∈ c`, and then keeps the
worlds whose doxastic state `φ` maps to itself; `believes` is that rule as a
`CCP.Partial` combinator, with the doxastic accessibility assignment
`Dox : E → W → Set W` of (11)–(12). On atomic complements its definedness
condition is Karttunen's rule (3) taken on the union of the doxastic states
(`admits_believes_iff_iUnion`) and the local-context condition of
[schlenker-2009] (`admits_believes_iff_presupAttributedToHolder`). The
paper's derivations follow: the *too*-discourse (20) presupposes nothing
(`believes_too_admits`), while its *doubt* variant (25) is admitted only by
contexts its first conjunct reduces to the absurd context
(`doubt_too_admits_iff`). The factive rule for *know* from footnote 47
(`knows`) demands `c + φ = c` outright, so a *know* report projects its
complement's presupposition transparently
(`transparentProjection_of_admits_knows`); a belief report does so only when
`Dox` is veridical (`transparentProjection_of_admits_believes`), and
`believes_admits_not_knows` is the two-world witness on Patrick's cello (2).

The desire half (§4) replaces the Hintikka-style rule (27) with the
comparative-belief semantics (31): `a wants φ` holds iff each doxastic
alternative's closest `φ`-worlds are more desirable than its closest
`¬φ`-worlds, on [stalnaker-1968] / [lewis-1973] similarity. The substrate is
`Semantics/Attitudes/Desire/Conditional.lean` (`Frame`, `Want`, `Defined`). The four-world
model below shows the
naive rule failing on the shape of [asher-1987]'s Concorde case (32) and the
(40) amendment blocking simultaneous `want p ∧ want ¬p`. Stalnaker's get-well
/ have-been-sick contrast ([stalnaker-1984], Heim's three-world model on
p. 195) needs a non-trivial similarity ordering and is not formalized.
-/

namespace Heim1992

open DynamicSemantics CCP.Partial Semantics.Presupposition Desire.Conditional
open Semantics.Presupposition.BeliefEmbedding
  (presupAttributedToHolder transparentProjection opaque_implies_transparent_when_reflexive)

/-! ### Belief reports -/

section Belief

variable {W E : Type*} (Dox : E → W → Set W) (a : E) (φ : CCP.Partial W) (p : PartialProp W)
  (c : Set W)

/-- Rule (18): `c + a believes φ` is defined iff `Dox_a(w) + φ` is defined for every `w ∈ c`,
and then equals `{w ∈ c | Dox_a(w) + φ = Dox_a(w)}`. -/
def believes : CCP.Partial W :=
  λ c => ⟨∀ w ∈ c, φ.admits (Dox a w), λ _ => {w ∈ c | Dox a w ∈ φ (Dox a w)}⟩

theorem admits_believes : (believes Dox a φ).admits c ↔ ∀ w ∈ c, φ.admits (Dox a w) :=
  Iff.rfl

@[simp] theorem believes_get (h : (believes Dox a φ).admits c) :
    (believes Dox a φ c).get h = {w ∈ c | Dox a w ∈ φ (Dox a w)} := rfl

/-- Karttunen's generalization: if `φ` presupposes `p`, then `a believes φ` presupposes that
`a` believes `p`. -/
theorem admits_believes_ofPartialProp :
    (believes Dox a (ofPartialProp p)).admits c ↔
      ∀ w ∈ c, ModalLogic.Epistemic.believes Dox a p.presup w :=
  Iff.rfl

/-- Karttunen's rule (3) on atomic complements: definedness on each `Dox_a(w)` is definedness
on their union, the beliefs attributed to `a` in `c`. -/
theorem admits_believes_iff_iUnion :
    (believes Dox a (ofPartialProp p)).admits c ↔
      (ofPartialProp p).admits (⋃ w ∈ c, Dox a w) :=
  Set.iUnion₂_subset_iff.symm

/-- The definedness condition of (18) is the local-context condition of [schlenker-2009]. -/
theorem admits_believes_iff_presupAttributedToHolder :
    (believes Dox a (ofPartialProp p)).admits c ↔ presupAttributedToHolder ⟨c, Dox, a⟩ p :=
  ⟨λ h w hw _ hx => h w hw hx.2, λ h w hw _ hx => h w hw ⟨hw, hx⟩⟩

/-- (20) presupposes nothing: every context admits `John believes that Mary_i is here, and he
believes that Susan_F is here too_i`, where by (22) the *too*-clause presupposes that Mary is
here. -/
theorem believes_too_admits (m s : Set W) :
    (seq (believes Dox a (ofPartialProp (.ofProp m)))
      (believes Dox a (ofPartialProp ⟨m, s⟩))).admits c :=
  ⟨λ _ _ _ _ => trivial, λ _ hw => ((mem_ofPartialProp_self _ _).1 hw.2).2⟩

/-- (25) `John doubts that Mary_i is here and believes that Susan_F is here too_i` is admitted
only by contexts in which John already believes Mary is here — which its first conjunct then
reduces to the absurd context. -/
theorem doubt_too_admits_iff (m s : Set W) :
    (seq (neg (believes Dox a (ofPartialProp (.ofProp m))))
      (believes Dox a (ofPartialProp ⟨m, s⟩))).admits c ↔ ∀ w ∈ c, Dox a w ⊆ m := by
  refine ⟨λ ⟨_, h⟩ w hw => ?_,
    λ h => ⟨λ _ _ _ _ => trivial, λ w hw => (hw.2 ⟨hw.1, ?_⟩).elim⟩⟩
  · by_contra hm
    exact hm (h w ⟨hw, λ hS => hm ((mem_ofPartialProp_self _ _).1 hS.2).2⟩)
  · exact (mem_ofPartialProp_self _ _).2 ⟨λ _ _ => trivial, h w hw.1⟩

/-- The factive rule of footnote 47: `c + a knows φ` is undefined unless `c + φ = c`, and is
otherwise `c + a believes φ`. -/
def knows : CCP.Partial W := λ c => Part.assert (c ∈ φ c) λ _ => believes Dox a φ c

theorem admits_knows :
    (knows Dox a φ).admits c ↔ c ∈ φ c ∧ (believes Dox a φ).admits c :=
  exists_prop

/-- A *know* report projects its complement's presupposition transparently. -/
theorem transparentProjection_of_admits_knows (h : (knows Dox a (ofPartialProp p)).admits c) :
    transparentProjection c p :=
  ((mem_ofPartialProp_self _ _).1 h.fst).1

/-- With veridical `Dox` on `c`, rule (18) already projects the complement's presupposition
transparently — the factivity that `knows` imposes outright. -/
theorem transparentProjection_of_admits_believes (hrefl : ∀ w ∈ c, w ∈ Dox a w)
    (h : (believes Dox a (ofPartialProp p)).admits c) : transparentProjection c p :=
  opaque_implies_transparent_when_reflexive ⟨c, Dox, a⟩ p hrefl
    ((admits_believes_iff_presupAttributedToHolder Dox a p c).1 h)

end Belief

/-! ### The know/believe contrast on Patrick's cello -/

/-- Whether Patrick owns a cello. -/
inductive CelloWorld where
  | owns
  | lacks
  deriving DecidableEq

/-- Patrick's misconception (2): whatever the facts, he believes he owns a cello. -/
def celloDox (_ : Unit) (_ : CelloWorld) : Set CelloWorld := {.owns}

/-- `Patrick sells his cello` (1): presupposes that he owns one. -/
def sellsCello : PartialProp CelloWorld := ⟨(· = .owns), λ _ => True⟩

/-- Where Patrick lacks a cello but believes he owns one, `Patrick believes he is selling his
cello` is admitted and `Patrick knows he is selling his cello` is not: `celloDox` is not
veridical at `lacks`. -/
theorem believes_admits_not_knows :
    (believes celloDox () (ofPartialProp sellsCello)).admits {.lacks} ∧
      ¬ (knows celloDox () (ofPartialProp sellsCello)).admits {.lacks} :=
  ⟨λ _ _ _ h => h,
   λ h => nomatch transparentProjection_of_admits_knows _ _ _ _ h rfl⟩

/-! ### Desire reports: the four-world model -/

/-- Worlds classified by two binary dimensions, recovered (`r`) and sick (`s`):
`w0 = r ∧ s`, `w1 = r ∧ ¬s`, `w2 = ¬r ∧ s`, `w3 = ¬r ∧ ¬s`. -/
inductive HealthWorld where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Fintype

def recovered : Set HealthWorld | .w0 | .w1 => True | _ => False
def sick : Set HealthWorld | .w0 | .w2 => True | _ => False

instance : DecidablePred (· ∈ recovered) := λ w => by
  cases w <;> first | exact isTrue trivial | exact isFalse id

/-- The naive Hintikka rule (27) — `a wants φ` iff every doxastic alternative is a `φ`-world,
`bel ⊆ φ` — which Heim rejects on [asher-1987]'s Concorde case (32), predicts `wants recovered`
false under the belief state `sick`, since `w2` is believed and not recovered. -/
theorem not_sick_subset_recovered : ¬ sick ⊆ recovered := λ h => @h .w2 trivial

/-- Every world is equally similar to every other. -/
def trivialSim : Semantics.Conditionals.SimilarityOrdering HealthWorld := by
  refine Semantics.Conditionals.SimilarityOrdering.ofBool (λ _ _ _ => true) ?_ ?_
  · intros; rfl
  · intros; rfl

/-- Recovered worlds are preferred to non-recovered ones, at every evaluation world. -/
def prefRecovered : HealthWorld → HealthWorld → HealthWorld → Prop :=
  λ _ x y => x ∈ recovered ∧ y ∉ recovered

instance (w : HealthWorld) : DecidableRel (prefRecovered w) :=
  λ x y => inferInstanceAs (Decidable (x ∈ recovered ∧ y ∉ recovered))

instance (w : HealthWorld) : Std.Antisymm (prefRecovered w) :=
  ⟨λ _ _ ⟨_, hny⟩ ⟨hy, _⟩ => absurd hy hny⟩

abbrev heimFrame : Frame HealthWorld := ⟨trivialSim, prefRecovered⟩

/-- The (40) amendment: `want recovered` is defined when both recovered and non-recovered
worlds are believed possible. -/
theorem defined_recovered : Defined Set.univ recovered :=
  ⟨⟨.w0, trivial, trivial⟩, ⟨.w2, trivial, id⟩⟩

/-- Under (40) and an asymmetric preference, `want recovered` and `want ¬recovered` cannot both
hold. (Heim's own worry about (40)'s restrictiveness, at (41)–(42), concerns wanting what one is
convinced of; her remedy (43) replaces `Dox_a` by a superset `F_a`.) -/
theorem not_want_recovered_compl (h : Want heimFrame Set.univ .w0 recovered) :
    ¬ Want heimFrame Set.univ .w0 recoveredᶜ :=
  h.not_compl defined_recovered

end Heim1992
