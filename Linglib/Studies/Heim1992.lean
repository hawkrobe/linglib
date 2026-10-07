module

public import Linglib.Semantics.Attitudes.Preference.Conditional
public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Logic.Modal.Defs
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Heim (1992): Presupposition Projection and the Semantics of Attitude Verbs

Heim gives the attitude predicates context change potentials and derives their projection
behaviour. The belief rule (18) is `believes`, a `CCP.Partial` combinator over the doxastic
accessibility of (11)–(12): the report is defined iff the complement is defined on each doxastic
state, so a complement presupposing `p` yields a report presupposing that its holder believes `p`,
Karttunen's generalization. The factive rule of footnote 47 makes *know* admit only contexts that
admit its complement's presupposition, which a belief report need not. The desire half replaces
the Hintikka-style rule (27) with the comparative semantics (31) on similarity, the library's
`Desire.Conditional.Want`, with the amendment (40) blocking `want p ∧ want ¬p`.

## Main results

* `admits_believes_iff`, `believes_ofPartialProp`: on atomic complements the belief rule is
  Karttunen's admittance in the holder's beliefs, and the update with a partial proposition.
* `believes_too_admits`, `doubt_too_admits_iff`: the *too*-discourse presupposes nothing, and its
  *doubt* variant is admitted only by contexts its first conjunct reduces to the absurd one.
* `admits_of_admits_knows`, `believes_admits_not_knows`: *know* passes on its complement's
  presupposition and *believe* need not, as Patrick's cello shows.
* `defined_recovered`, `not_want_recovered_compl`: on a four-world model shaped like Asher's
  Concorde case, the amendment blocks wanting both `p` and `¬p`.

## Implementation notes

* The three-world model of Section 4.1 for Stalnaker's get-well and have-been-sick contrast
  ([stalnaker-1984]) needs a non-trivial similarity ordering and is not formalized; the
  four-world model here uses the trivial ordering.

## References

* [heim-1992]
* [karttunen-1974-presupposition]
* [asher-1987]
* [stalnaker-1984]
* [stalnaker-1968]
* [lewis-1973]
-/

@[expose] public section

namespace Heim1992

open DynamicSemantics PartialUpdate CCP.Partial Presupposition Desire.Conditional

/-! ### Belief reports -/

section Belief

variable {W E : Type*} (Dox : E → W → Set W) (a : E) (φ : CCP.Partial W) (p : PartialProp W)
  (c : Set W)

/-- By rule (18), `c + a believes φ` is defined iff `Dox_a(w) + φ` is defined for every `w ∈ c`,
and then equals `{w ∈ c | Dox_a(w) + φ = Dox_a(w)}`. -/
def believes : CCP.Partial W :=
  fun c ↦ ⟨∀ w ∈ c, φ.Admits (Dox a w), fun _ ↦ {w ∈ c | Dox a w ∈ φ (Dox a w)}⟩

/-- By Karttunen's generalization, if `φ` presupposes `p`, then `a believes φ` presupposes that
`a` believes `p`. -/
theorem admits_believes_ofPartialProp :
    (believes Dox a (ofPartialProp p)).Admits c ↔
      ∀ w ∈ c, ModalLogic.Box (.ofSuccessors (Dox a)) p.presup w :=
  Iff.rfl

/-- On atomic complements, Karttunen's rule (3) makes definedness on each `Dox_a(w)` admittance
in their union, the beliefs attributed to `a` in `c`. -/
theorem admits_believes_iff :
    (believes Dox a (ofPartialProp p)).Admits c ↔ p.Admits (beliefContext (Dox a) c) :=
  beliefContext_subset_iff.symm

/-- On atomic complements (18) is static, as in the calculation (24), since `a believes φ` is the
update with the partial proposition that presupposes that `a` believes `φ`'s presupposition and
asserts that `a` believes its assertion. -/
theorem believes_ofPartialProp :
    believes Dox a (ofPartialProp p) = ofPartialProp
      ⟨ModalLogic.Box (.ofSuccessors (Dox a)) p.presup,
        ModalLogic.Box (.ofSuccessors (Dox a)) p.assertion⟩ := by
  funext c
  refine Part.ext' Iff.rfl fun h _ ↦ Set.ext fun w ↦ ?_
  simp only [believes, mem_ofPartialProp_self, Set.mem_ofPred_eq, ofPartialProp_get]
  exact ⟨fun ⟨hw, _, ha⟩ ↦ ⟨hw, ha⟩, fun ⟨hw, ha⟩ ↦ ⟨hw, h w hw, ha⟩⟩

/-- (20) presupposes nothing, since every context admits `John believes that Mary_i is here, and
he believes that Susan_F is here too_i`, where by (22) the *too*-clause presupposes that Mary is
here. -/
theorem believes_too_admits (m s : Set W) :
    (seq (believes Dox a (ofPartialProp (.ofProp m)))
      (believes Dox a (ofPartialProp ⟨m, s⟩))).Admits c :=
  ⟨fun _ _ _ _ ↦ trivial, fun _ hw ↦ ((mem_ofPartialProp_self _ _).1 hw.2).2⟩

/-- (25) `John doubts that Mary_i is here and believes that Susan_F is here too_i` is admitted
only by contexts in which John already believes Mary is here — which its first conjunct then
reduces to the absurd context. -/
theorem doubt_too_admits_iff (m s : Set W) :
    (seq (neg (believes Dox a (ofPartialProp (.ofProp m))))
      (believes Dox a (ofPartialProp ⟨m, s⟩))).Admits c ↔ ∀ w ∈ c, Dox a w ⊆ m := by
  refine ⟨fun ⟨_, h⟩ w hw ↦ ?_,
    fun h ↦ ⟨fun _ _ _ _ ↦ trivial, fun w hw ↦ (hw.2 ⟨hw.1, ?_⟩).elim⟩⟩
  · by_contra hm
    exact hm (h w ⟨hw, fun hS ↦ hm ((mem_ofPartialProp_self _ _).1 hS.2).2⟩)
  · exact (mem_ofPartialProp_self _ _).2 ⟨fun _ _ ↦ trivial, h w hw.1⟩

/-- By the factive rule of footnote 47, `c + a knows φ` is undefined unless `c + φ = c`, and is
otherwise `c + a believes φ`. -/
def knows : CCP.Partial W := fun c ↦ Part.assert (c ∈ φ c) fun _ ↦ believes Dox a φ c

theorem admits_knows :
    (knows Dox a φ).Admits c ↔ c ∈ φ c ∧ (believes Dox a φ).Admits c :=
  exists_prop

/-- A context admitting a *know* report admits its complement's presupposition. -/
theorem admits_of_admits_knows (h : (knows Dox a (ofPartialProp p)).Admits c) : p.Admits c :=
  ((mem_ofPartialProp_self _ _).1 h.fst).1

end Belief

/-! ### The know/believe contrast on Patrick's cello -/

/-- Whether Patrick owns a cello. -/
inductive CelloWorld where
  | owns
  | lacks
  deriving DecidableEq

/-- In Patrick's misconception (2), whatever the facts, he believes he owns a cello. -/
def celloDox (_ : Unit) (_ : CelloWorld) : Set CelloWorld := {.owns}

/-- `Patrick sells his cello` (1) presupposes that he owns one. -/
def sellsCello : PartialProp CelloWorld := ⟨(· = .owns), fun _ ↦ True⟩

/-- Where Patrick lacks a cello but believes he owns one, `Patrick believes he is selling his
cello` is admitted and `Patrick knows he is selling his cello` is not, since `celloDox` is not
veridical at `lacks`. -/
theorem believes_admits_not_knows :
    (believes celloDox () (ofPartialProp sellsCello)).Admits {.lacks} ∧
      ¬ (knows celloDox () (ofPartialProp sellsCello)).Admits {.lacks} :=
  ⟨fun _ _ _ h ↦ h,
   fun h ↦ nomatch admits_of_admits_knows _ _ _ _ h rfl⟩

/-! ### Desire reports: the four-world model -/

/-- Worlds are classified by two binary dimensions, recovered (`r`) and sick (`s`), with
`w0 = r ∧ s`, `w1 = r ∧ ¬s`, `w2 = ¬r ∧ s` and `w3 = ¬r ∧ ¬s`. -/
inductive HealthWorld where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Fintype

def recovered : Set HealthWorld | .w0 | .w1 => True | _ => False
def sick : Set HealthWorld | .w0 | .w2 => True | _ => False

instance : DecidablePred (· ∈ recovered) := fun w ↦ by
  cases w <;> first | exact isTrue trivial | exact isFalse id

/-- The naive Hintikka rule (27) — `a wants φ` iff every doxastic alternative is a `φ`-world,
`bel ⊆ φ` — which Heim rejects on [asher-1987]'s Concorde case (32), predicts `wants recovered`
false under the belief state `sick`, since `w2` is believed and not recovered. -/
theorem not_sick_subset_recovered : ¬ sick ⊆ recovered := fun h ↦ @h .w2 trivial

/-- Every world is equally similar to every other. -/
abbrev trivialSim (_ : HealthWorld) : Preorder HealthWorld := ⊤

/-- Recovered worlds are preferred to non-recovered ones, at every evaluation world. -/
def prefRecovered : HealthWorld → HealthWorld → HealthWorld → Prop :=
  fun _ x y ↦ x ∈ recovered ∧ y ∉ recovered

instance (w : HealthWorld) : DecidableRel (prefRecovered w) :=
  fun x y ↦ inferInstanceAs (Decidable (x ∈ recovered ∧ y ∉ recovered))

instance (w : HealthWorld) : Std.Antisymm (prefRecovered w) :=
  ⟨fun _ _ ⟨_, hny⟩ ⟨hy, _⟩ ↦ absurd hy hny⟩

abbrev heimFrame : Frame HealthWorld := ⟨trivialSim, prefRecovered⟩

/-- Under the (40) amendment, `want recovered` is defined when both recovered and non-recovered
worlds are believed possible. -/
theorem defined_recovered : Desire.IsContingent Set.univ recovered :=
  ⟨⟨.w0, trivial, trivial⟩, ⟨.w2, trivial, id⟩⟩

/-- Under (40) and an asymmetric preference, `want recovered` and `want ¬recovered` cannot both
hold. (Heim's own worry about (40)'s restrictiveness, at (41)–(42), concerns wanting what one is
convinced of; her remedy (43) replaces `Dox_a` by a superset `F_a`.) -/
theorem not_want_recovered_compl (h : Want heimFrame Set.univ .w0 recovered) :
    ¬ Want heimFrame Set.univ .w0 recoveredᶜ :=
  h.not_compl defined_recovered

end Heim1992
