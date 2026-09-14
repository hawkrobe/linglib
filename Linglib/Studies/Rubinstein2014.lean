import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Semantics.Homogeneity.Decided
import Linglib.Fragments.English.Auxiliaries
import Linglib.Data.Examples.Rubinstein2014
import Mathlib.Data.Fintype.Prod

/-!
# Rubinstein (2014): On Necessity and Comparison

This file formalizes the paper's account of weak necessity as comparison. The ordering source
of [kratzer-1981] is split by negotiability: the priorities every discourse participant
endorses are promoted to the modal base and, with the circumstances, delimit the favored
worlds, while the negotiable priorities an opinionated assessor promotes remain an ordering
source (`Backgrounds`). Strong necessity quantifies over all favored worlds and weak necessity
over the best of them under the negotiable ordering, so strong necessity entails weak
(`strong_entails_weak`) and not conversely, and with nothing promoted the two are Kratzer's
simple necessity and necessity. The paper's tax-report scenario is the shift from *should* to
*have to* when a negotiable ideal is endorsed (`tax_shift`). Weak necessity modals form a
natural class with the evaluative comparatives *good*, *better*, *preferable*, and
*worthwhile*, diagnosed by the felicity of denying strong necessity after them and by
neg-raising; the paper's English, Hebrew, and Spanish stimuli are rows, read by
`negRaising_iff_comparative` and `strength_tests`, with the membership of an English modal
verb in the class derived from the force the English fragment assigns it. Neg-raising is the
substrate's decidedness of a modal's domain, and `comparative_split` exhibits a background
whose favored worlds are undecided while its best worlds are decided, the configuration in
which the comparative modal neg-raises and the strong one cannot.

## Implementation notes

The favored worlds are the intersection of the circumstances and the promoted priorities, the
consistent case of the paper's compatibility-restricted union of [frank-1996]; the best
favored worlds are the substrate's `bestAmong`, minimality under the ordering source. The
concrete models have two-valued worlds, and their claims are decided after unfolding the
operators. Hebrew has no lexical or compositional weak necessity, so its route to weak
necessity is the evaluative comparative alone (`strategies`); the counts of the paper's
crosslinguistic survey are not formalized.

## References

* [rubinstein-2014]
* [kratzer-1981]
* [frank-1996]
* [sloman-1970]
* [horn-1978]
* [von-fintel-iatridou-2008]
-/

namespace Rubinstein2014

open Modality.Kratzer Data.Examples

variable {W : Type*}

/-! ### Favored worlds and the two necessities -/

/-- Modal backgrounds with the ordering source split by negotiability: the circumstances, the
non-negotiable priorities promoted to the modal base, and the negotiable priorities that
remain an ordering source. -/
structure Backgrounds (W : Type*) where
  circumstances : ModalBase W
  nonNegotiable : ModalBase W
  negotiable : OrderingSource W

/-- The favored worlds: those compatible with the circumstances and the non-negotiable
priorities. -/
def favoredWorlds (b : Backgrounds W) (w : W) : Set W :=
  propIntersection (b.circumstances w ++ b.nonNegotiable w)

/-- Strong necessity: truth throughout the favored worlds. -/
def strongNecessity (b : Backgrounds W) (p : W → Prop) (w : W) : Prop :=
  ∀ v ∈ favoredWorlds b w, p v

/-- Weak necessity: truth throughout the best favored worlds under the negotiable ordering. -/
def weakNecessity (b : Backgrounds W) (p : W → Prop) (w : W) : Prop :=
  ∀ v ∈ bestAmong (favoredWorlds b w) (b.negotiable w), p v

theorem strong_entails_weak {b : Backgrounds W} {p : W → Prop} {w : W}
    (h : strongNecessity b p w) : weakNecessity b p w :=
  λ v hv => h v (bestAmong_subset _ _ hv)

/-- With no promoted priorities the favored worlds are Kratzer's accessible worlds. -/
theorem favoredWorlds_of_none (f : ModalBase W) (g : OrderingSource W) (w : W) :
    favoredWorlds ⟨f, emptyBackground, g⟩ w = accessibleWorlds f w := by
  show propIntersection (f w ++ []) = _
  rw [List.append_nil]; rfl

/-- With nothing promoted and no negotiable priorities, strong necessity is Kratzer's simple
necessity. -/
theorem strongNecessity_iff_simpleNecessity (f : ModalBase W) (p : W → Prop) (w : W) :
    strongNecessity ⟨f, emptyBackground, emptyBackground⟩ p w ↔ simpleNecessity f p w := by
  rw [simpleNecessity_iff_all, strongNecessity, favoredWorlds_of_none]

/-- With nothing promoted, weak necessity is Kratzer's necessity under the negotiable
ordering source. -/
theorem weakNecessity_iff_necessity (f : ModalBase W) (g : OrderingSource W) (p : W → Prop)
    (w : W) : weakNecessity ⟨f, emptyBackground, g⟩ p w ↔ necessity f g p w := by
  rw [necessity_iff_all, weakNecessity, favoredWorlds_of_none]; rfl

/-- Without negotiable priorities the two necessities coincide. -/
theorem weakNecessity_iff_strongNecessity {b : Backgrounds W} {w : W} (hg : b.negotiable w = [])
    (p : W → Prop) : weakNecessity b p w ↔ strongNecessity b p w := by
  rw [weakNecessity, strongNecessity, hg, bestAmong_nil]

/-! ### Comparison against strength -/

/-- A background whose favored worlds are all the worlds and whose one negotiable ideal makes
a single world best. -/
def split : Backgrounds Bool :=
  ⟨emptyBackground, emptyBackground, Function.const Bool [(· = true)]⟩

/-- The scenario before the endorsement: worlds record whether domestic and international
revenue is reported, the law on domestic revenue is non-negotiable, and the accountant's ideal
of reporting international revenue is negotiable. -/
def taxBefore : Backgrounds (Bool × Bool) :=
  ⟨emptyBackground, Function.const _ [(·.1 = true)], Function.const _ [(·.2 = true)]⟩

/-- The scenario after the manager endorses the ideal: both priorities non-negotiable. -/
def taxAfter : Backgrounds (Bool × Bool) :=
  ⟨emptyBackground, Function.const _ [(·.1 = true), (·.2 = true)], emptyBackground⟩

/-- Reporting all revenue. -/
def reportAll (w : Bool × Bool) : Prop := w.1 = true ∧ w.2 = true

/-- Decide a claim about a two-valued model by unfolding the operators. -/
scoped macro "decide_model" : tactic =>
  `(tactic| (simp only [strongNecessity, weakNecessity, favoredWorlds, bestAmong,
      Core.Order.Normality.mem_optimal, kratzerPreorder, Core.Order.Normality.fromProps,
      Preorder.ofCriteria_le_iff, propIntersection, emptyBackground, Function.const_apply,
      List.append_nil, List.nil_append, Set.Subsingleton, Set.mem_ofPred_eq, List.forall_mem_cons,
      List.mem_nil_iff, false_implies, implies_true, and_true, split, taxBefore, taxAfter,
      reportAll]; decide))

/-- Weak necessity does not entail strong: the ideal holds at the best world and fails at a
favored one. -/
theorem weak_not_entails_strong :
    weakNecessity split (· = true) false ∧ ¬ strongNecessity split (· = true) false := by
  decide_model

/-- The comparative split: a background whose favored worlds are undecided while its best
worlds are decided. -/
theorem comparative_split :
    ¬ (favoredWorlds split false).Subsingleton ∧
      (bestAmong (favoredWorlds split false) (split.negotiable false)).Subsingleton := by
  decide_model

/-- In that background the comparative modal neg-raises, its domain the decided best worlds,
and the strong modal, ranging over the undecided favored worlds, does not. -/
theorem negRaising_split :
    (∀ p : Bool → Prop, ¬ weakNecessity split p false →
      ∀ v ∈ bestAmong (favoredWorlds split false) (split.negotiable false), ¬ p v) ∧
    ¬ (∀ p : Bool → Prop, ¬ strongNecessity split p false →
      ∀ v ∈ favoredWorlds split false, ¬ p v) :=
  ⟨(Homogeneity.negRaising_iff_subsingleton _).2 comparative_split.2,
    λ h => comparative_split.1 ((Homogeneity.negRaising_iff_subsingleton _).1 h)⟩

/-! ### The tax report -/

/-- Before the endorsement *we should report all our revenue* holds and *we have to* does
not; after it *we have to* holds. -/
theorem tax_shift :
    (weakNecessity taxBefore reportAll (false, false) ∧
      ¬ strongNecessity taxBefore reportAll (false, false)) ∧
      strongNecessity taxAfter reportAll (false, false) := by
  decide_model

/-! ### The comparative class in the data -/

/-- The English fragment assigns the modal verb weak necessity. -/
def WeakInFragment (modal : String) : Prop :=
  ∃ a ∈ [English.Auxiliaries.should, English.Auxiliaries.ought, English.Auxiliaries.must,
    English.Auxiliaries.haveTo, English.Auxiliaries.need],
    a.form = modal ∧ ∃ m ∈ a.modality, m.1 = .weakNecessity

instance : DecidablePred WeakInFragment := λ _ => by unfold WeakInFragment; infer_instance

/-- Membership in the comparative class: an evaluative comparative, or a modal verb the
fragment marks weak necessity. -/
def InComparativeClass (e : LinguisticExample) : Prop :=
  e.feature? "category" = some "evaluativeComparative" ∨
    WeakInFragment ((e.feature? "modal").getD "")

instance : DecidablePred InComparativeClass := λ _ => by unfold InComparativeClass; infer_instance

/-- The neg-raising stimuli. -/
def negRaisingRows : List LinguisticExample :=
  Examples.all.filter λ e => e.feature? "diagnostic" = some "negRaising"

/-- The lower-negation reading of a negated attitude is available exactly for the comparative
class: the weak necessity verbs and the evaluative comparatives, not the strong modals. -/
theorem negRaising_iff_comparative :
    ∀ e ∈ negRaisingRows,
      (e.readings.lookup "lowerNeg" = some .acceptable ↔ InComparativeClass e) := by
  decide +kernel

/-- The strength tests, denying strong necessity after the expression or opposing it to strong
necessity with an exclusive, are felicitous exactly for the comparative class. -/
theorem strength_tests :
    ∀ e ∈ Examples.all, e.feature? "diagnostic" ∈ [some "test1", some "test2"] →
      (e.judgment = .acceptable ↔ InComparativeClass e) := by
  decide +kernel

/-- The routes to weak necessity: a dedicated item, a strong modal with weakening morphology,
or evaluative comparative language. -/
inductive Strategy
  | lexical
  | compositional
  | evaluativeComparative
  deriving DecidableEq, Repr

/-- The strategy a row exemplifies. -/
def strategy? (e : LinguisticExample) : Option Strategy :=
  e.parse? "strategy" [("lexical", Strategy.lexical), ("compositional", .compositional),
    ("evaluativeComparative", .evaluativeComparative)]

/-- English has a lexical and Spanish a compositional weak necessity, and Hebrew has neither,
its route being the evaluative comparative. -/
theorem strategies :
    (∃ e ∈ Examples.all, e.language = "stan1293" ∧ strategy? e = some .lexical) ∧
      (∃ e ∈ Examples.all, e.language = "stan1288" ∧ strategy? e = some .compositional) ∧
      ∀ e ∈ Examples.all, e.language = "hebr1245" →
        strategy? e ≠ some .lexical ∧ strategy? e ≠ some .compositional := by
  decide +kernel

end Rubinstein2014
