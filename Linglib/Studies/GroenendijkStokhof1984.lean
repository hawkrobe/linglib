import Linglib.Semantics.Questions.Partition.Lattice
import Linglib.Data.Examples.GroenendijkStokhof1984
import Mathlib.Data.Fintype.Basic

/-!
# Groenendijk and Stokhof (1984): Studies on the Semantics of Questions

This file formalizes the propositional analysis of wh-complements and interrogatives of
[groenendijk-stokhof-1984], "Studies on the semantics of questions and the pragmatics of
answers", chapters I and II: at an index, *who walks* denotes the proposition
true at exactly the indices where the extension of *walk* is what it is at that index, so a
question is an equivalence relation on indices, the library's `QUD`, and to know the answer is
to have one's doxastic alternatives inside the actual cell (`Knows`). The arguments the
dissertation takes as data follow: knowing who walks entails knowing of each walker that they
walk, argument (V) (`knows_who_entails_knows_that`); it excludes believing of a non-walker that
they walk, the strong exhaustiveness of (VIII) (`strong_exhaustiveness`); knowing whether *p*
or *q* fixes both, (IX); knowing who walks is knowing who does not, (X)
(`knows_who_iff_knows_who_not`); and a wh-question entails each of its polar questions, (5).
The de dicto and de re readings of *which girl walks* diverge as in (XI) and (XII): the de re
reading, restricted to the actual girls, follows from knowing who walks, the de dicto one does
not (`de_re_entailed`, `de_dicto_not_entailed`), and *which men walk* yields *which men do not
walk* only de re or with *who the men are* added, (7) to (10). Section 3.2 of chapter I is the
contrast between the rigid answer *Mary* and the description *the girl from next door*: the
description answers as the name does exactly for a questioner whose information fixes its
referent (`description_answers_iff_referent_fixed`).

## Implementation notes

Extensions are Boolean-valued over a finite domain so that the wh-question is `QUD.ofProject`
and knowledge in the concrete counter-models decides. The domain of discourse is fixed across
indices, the assumption under which the dissertation accepts (X). The chapter VI judgments on
mention-some, pragmatic answerhood, and the pair-list and choice readings are rows of
`Data.Examples.GroenendijkStokhof1984` and are not yet consumed by a theorem.

## References

* [groenendijk-stokhof-1984]
* [karttunen-1977]

## TODO

Chapter VI's pragmatic notion of answerhood relative to an information state, and the pair-list
and choice readings of chapter I's (11) to (18), are not formalized.
-/

namespace GroenendijkStokhof1984

open scoped QUD

variable {W E : Type*}

section Questions

variable [Fintype E]

/-! ### Questions and knowing their answers -/

/-- *Who P?*: indices are alike when the extension of `P` is the same, section 1.4 of
chapter II. -/
def whQ (P : E → W → Bool) : QUD W := QUD.ofProject λ w x => P x w

/-- *Whether p?*: indices are alike when `p` has the same value. -/
def whetherQ (p : W → Bool) : QUD W := QUD.ofProject p

/-- *Whether p or q?*: indices are alike when both values agree, (IX). -/
def whetherOrQ (p q : W → Bool) : QUD W := QUD.ofProject λ w => (p w, q w)

/-- An agent whose doxastic alternatives at `w` are `dox` knows the answer to `q` when every
alternative lies in the cell of `w`. -/
def Knows (dox : Set W) (q : QUD W) (w : W) : Prop := dox ⊆ q.cell w

theorem whQ_r {P : E → W → Bool} {w v : W} : (whQ P).r w v ↔ ∀ x, P x w = P x v := by
  simp [whQ, funext_iff]

/-- (V) and (2): knowing who walks entails, of each walker, knowing that they walk; with the
non-factive *tell* in place of *know* the same holds, the entailment resting on extensionality
alone. -/
theorem knows_who_entails_knows_that {dox : Set W} {P : E → W → Bool} {w : W}
    (h : Knows dox (whQ P) w) (x : E) : ∀ v ∈ dox, P x v = P x w :=
  λ _ hv => (whQ_r.mp (h hv) x).symm

/-- (1) and (4): knowing whether Mary walks entails knowing that she does or that she does not,
according to the index. -/
theorem knows_whether_entails {dox : Set W} {p : W → Bool} {w : W}
    (h : Knows dox (whetherQ p) w) : ∀ v ∈ dox, p v = p w :=
  λ v hv => ((QUD.ofProject_r p w v).mp (h hv)).symm

/-- (IX): knowing whether Mary walks or Bill sleeps fixes both. -/
theorem knows_whether_or_entails {dox : Set W} {p q : W → Bool} {w : W}
    (h : Knows dox (whetherOrQ p q) w) : ∀ v ∈ dox, p v = p w ∧ q v = q w := by
  intro v hv
  have := (QUD.ofProject_r (λ w => (p w, q w)) w v).mp (h hv)
  exact ⟨(Prod.mk.inj this).1.symm, (Prod.mk.inj this).2.symm⟩

/-- (VIII) and (6): if only Bill walks, John, who believes that Bill and Suzy walk, does not
know who walks; the proposition denoted by *who walks* is exhaustive. -/
theorem strong_exhaustiveness {dox : Set W} {P : E → W → Bool} {w v : W} {suzy : E}
    (hv : v ∈ dox) (hbelief : P suzy v = true) (hfact : P suzy w = false) :
    ¬ Knows dox (whQ P) w :=
  λ h => by simpa [hfact] using (knows_who_entails_knows_that h suzy v hv).symm.trans hbelief

/-- (X): knowing who walks is knowing who does not walk, the domain of discourse being fixed. -/
theorem knows_who_iff_knows_who_not {dox : Set W} {P : E → W → Bool} {w : W} :
    Knows dox (whQ P) w ↔ Knows dox (whQ λ x v => !P x v) w := by
  simp only [Knows, Set.subset_def, QUD.mem_cell_iff_r, whQ_r, Bool.not_inj_iff]

/-- (5): *Who walks?* entails *Does John walk?*. -/
theorem wh_refines_polar (P : E → W → Bool) (e : E) : whQ P ⊑ whetherQ (P e) :=
  λ _ _ h => decide_eq_true (whQ_r.mp (QUD.r_of_sameAnswer h) e)

/-! ### De dicto and de re readings, chapter II section 1.6

*Which girl walks* read de re asks, of the actual girls, which walk; read de dicto it asks
which individuals are girls that walk, so that knowing its answer takes knowing of each of
them that she is a girl. -/

/-- *Which G P?* de re at `w`: the extension of `P` on the actual `G`s. -/
def deRe (G P : E → W → Bool) (w : W) : QUD W := whQ λ x v => G x w && P x v

/-- *Which G P?* de dicto: the extension of `G` and `P` together. -/
def deDicto (G P : E → W → Bool) : QUD W := whQ λ x v => G x v && P x v

/-- (XI) read de re is valid: knowing who walks is knowing, of each actual girl, whether she
walks. -/
theorem de_re_entailed {dox : Set W} {G P : E → W → Bool} {w : W} (h : Knows dox (whQ P) w) :
    Knows dox (deRe G P w) w :=
  λ _ hv => (whQ_r (P := λ x v => G x w && P x v)).mpr λ x => by rw [whQ_r.mp (h hv) x]

/-- (XII) read de re on both sides is valid: knowing which men walk is knowing which men do
not, of the actual men. -/
theorem de_re_negation {dox : Set W} {G P : E → W → Bool} {w : W} :
    Knows dox (deRe G P w) w ↔ Knows dox (deRe G (λ x v => !P x v) w) w := by
  simp only [Knows, Set.subset_def, QUD.mem_cell_iff_r, deRe, whQ_r]
  refine forall_congr' λ v => forall_congr' λ _ => forall_congr' λ x => ?_
  cases G x w <;> simp

/-- (8) to (10): with *who the men are* added, *which men walk* yields *which men do not
walk* de dicto as well. -/
theorem de_dicto_negation_with_domain {dox : Set W} {G P : E → W → Bool} {w : W}
    (hG : Knows dox (whQ G) w) (h : Knows dox (deDicto G P) w) :
    Knows dox (deDicto G (λ x v => !P x v)) w := by
  intro v hv
  refine (whQ_r (P := λ x v => G x v && !P x v)).mpr λ x => ?_
  have hg := whQ_r.mp (hG hv) x
  have hp := (whQ_r (P := λ x v => G x v && P x v)).mp (h hv) x
  cases hgw : G x w <;> cases hgv : G x v <;> simp_all

/-! #### The counter-models

One individual and two indices, the actual one and the alternative John cannot exclude. -/

namespace Model

/-- The individual walks at both indices. -/
def walk : Unit → Bool → Bool := λ _ _ => true

/-- She is a girl at the actual index only: John does not believe her to be a girl. -/
def girl : Unit → Bool → Bool := λ _ w => w

/-- (XI) read de dicto is invalid: John knows who walks but not which girl walks. -/
theorem de_dicto_not_entailed :
    Knows Set.univ (whQ walk) true ∧ ¬ Knows Set.univ (deDicto girl walk) true :=
  ⟨λ v _ => by rw [QUD.mem_cell_iff_r]; cases v <;> decide,
    λ h => absurd (h (Set.mem_univ false)) (by rw [QUD.mem_cell_iff_r]; decide)⟩

/-- Nobody walks, and John errs about who is a man. -/
def noWalk : Unit → Bool → Bool := λ _ _ => false

/-- (XII) read de dicto on both sides is invalid: John knows which men walk, none, yet not
which men do not walk. -/
theorem de_dicto_negation_invalid :
    Knows Set.univ (deDicto girl noWalk) true ∧
      ¬ Knows Set.univ (deDicto girl λ x v => !noWalk x v) true :=
  ⟨λ v _ => by rw [QUD.mem_cell_iff_r]; cases v <;> decide,
    λ h => absurd (h (Set.mem_univ false)) (by rw [QUD.mem_cell_iff_r]; decide)⟩

end Model

end Questions

/-! ### Rigid and descriptive answers, chapter I section 3.2

*Mary* answers *Whom did John kiss?* for every questioner; *the girl from next door* answers
it for a questioner who knows who the girl from next door is. -/

/-- The proposition a description answer expresses, read de dicto: at each index the
description's referent there has the property. -/
def descriptionAnswer (d : W → E) (P : E → W → Bool) : Set W := {v | P (d v) v = true}

/-- The proposition the same answer expresses through the description's actual referent. -/
def referentAnswer (d : W → E) (P : E → W → Bool) (w : W) : Set W := {v | P (d w) v = true}

/-- A description answers as its referent's name does exactly on the information of a
questioner for whom the referent is fixed; a name, rigid, needs no information. -/
theorem description_answers_iff_referent_fixed {dox : Set W} {d : W → E} {P : E → W → Bool}
    {w : W} (hfix : ∀ v ∈ dox, d v = d w) :
    dox ∩ descriptionAnswer d P = dox ∩ referentAnswer d P w :=
  Set.ext λ v =>
    ⟨λ ⟨hv, hp⟩ => ⟨hv, by simpa [descriptionAnswer, referentAnswer, hfix v hv] using hp⟩,
      λ ⟨hv, hp⟩ => ⟨hv, by simpa [descriptionAnswer, referentAnswer, hfix v hv] using hp⟩⟩

/-- A rigid designation answers alike at every index. -/
theorem rigid_answer {d : W → E} {P : E → W → Bool} {w : W} (hrigid : ∀ v, d v = d w) :
    descriptionAnswer d P = referentAnswer d P w :=
  Set.ext λ v => by simp [descriptionAnswer, referentAnswer, hrigid v]

end GroenendijkStokhof1984
