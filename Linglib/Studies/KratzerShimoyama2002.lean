module

public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Set.Lattice.Bounded
public import Linglib.Logic.Modal.Defs
public import Linglib.Fragments.Japanese.Determiners
public import Linglib.Fragments.German.PolarityItems
public import Linglib.Studies.Haspelmath1997
public import Linglib.Data.Examples.KratzerShimoyama2002

/-!
# Kratzer and Shimoyama (2002): Indeterminate Pronouns: The View from Japanese

This file formalizes the paper's Hamblin semantics for indeterminate pronouns and its
application to German *irgendein*. Every expression denotes a set of alternatives; an
indeterminate pronoun denotes a set of individuals, composition is pointwise functional
application, and the alternatives expand until an operator, existential, universal, negative,
or interrogative, closes them. Since closure returns a single proposition, alternatives are
caught by the nearest operator, which is the paper's locality constraint on association.
Determiner quantification is the special case in which the alternatives are individuals.
*Irgendein* widens a domain-restricted indefinite to the whole extension of its noun, and
modals are sensitive to the propositional alternatives in their scope; their truth conditions
are weak, and the distribution requirement behind the free-choice effect, that every
alternative be realised at some accessible world, is not entailed by them but derived as a
conversational implicature from the reasons a speaker could have for widening, present
under *kann* and *muss* and cancelled under negated possibility. The paper closes with the
selectivity of Indo-European indeterminates, *irgendein* associating only with existential
closure, and the Beck effects, in which an intervening operator blocks the in situ wh-phrase.

The paper's sentences with *irgendein* are acceptable exactly in the environments the fragment
entry `German.PolarityItems.irgendein` lists (`rows_irgendein`). Under a negative operator
selectivity decides: *niemand* and *auf keinen Fall* close their scope with [∃] and admit the
item, while the inflectional negation *nicht* carries [Neg] and does not
(`rows_irgendein_selective`). Strength does not decide it, since the licensing table licenses the
item under the downward-entailing *nicht* (`negation_licenses_irgendein`). Haspelmath's map
agrees: the environments the entry lists realize functions of his *irgend-* series, and
inflectional negation realizes direct negation, which the series lacks (`irgendein_haspelmath`).

## Implementation notes

Hamblin functional application is mathlib's `Set.seq`, and singleton denotations are
`{f}`; the four sentential operators return singleton sets, as in the paper, so that closure
is idle on an already closed set. The modal semantics is stated for an accessibility relation
on any type of worlds, and the free-choice computations are the paper's three tables with
the derived implicature as a hypothesis. The Beck-effect paradigm and its scrambled
counterpart are example rows, keyed by the intervener's interpretable feature, and so is the
paradigm of *irgendein*, keyed by its licensing environment. Locators
follow the 2002 manuscript, whose numbering the published chapter keeps.

## References

* [kratzer-shimoyama-2002]
* [hamblin-1973b] — alternative semantics for questions
* [haspelmath-1997] — the Latvian and Japanese series
* [kadmon-landman-1993] — widening for a reason
* [beck-1996] — intervention effects
-/

@[expose] public section

namespace KratzerShimoyama2002

open ModalLogic

/-! ### Hamblin composition (§2, §3) -/

section Composition

variable {W E : Type*}

/-- A singleton set of functions applies pointwise as an image: the verb of *dare nemutta*
introduces one alternative, the indeterminate a set of individuals. -/
theorem seq_singleton (f : E → W → Prop) (A : Set E) : Set.seq {f} A = f '' A := by
  ext p; simp [Set.mem_seq_iff]

/-- `opExists A` is existential closure, the single proposition true where some alternative is. -/
def opExists (A : Set (W → Prop)) : Set (W → Prop) := {fun w ↦ ∃ p ∈ A, p w}

/-- `opForall A` is universal closure, the single proposition true where every alternative is. -/
def opForall (A : Set (W → Prop)) : Set (W → Prop) := {fun w ↦ ∀ p ∈ A, p w}

/-- `opNeg A` is negative closure, the single proposition true where no alternative is. -/
def opNeg (A : Set (W → Prop)) : Set (W → Prop) := {fun w ↦ ∀ p ∈ A, ¬ p w}

/-- The question operator returns the alternatives themselves. -/
def opQ (A : Set (W → Prop)) : Set (W → Prop) := A

/-- Negative closure is the negation of existential closure. -/
theorem opNeg_eq (A : Set (W → Prop)) : opNeg A = {fun w ↦ ¬ ∃ p ∈ A, p w} := by
  simp [opNeg, not_exists]

theorem opExists_singleton (p : W → Prop) : opExists {p} = {p} := by simp [opExists]

theorem opForall_singleton (p : W → Prop) : opForall {p} = {p} := by simp [opForall]

/-- Alternatives are caught by the nearest operator (4): once closed, a set has a single
member, so a higher operator finds nothing left to quantify over. -/
theorem opForall_opExists (A : Set (W → Prop)) : opForall (opExists A) = opExists A :=
  opForall_singleton _

theorem opExists_opForall (A : Set (W → Prop)) : opExists (opForall A) = opForall A :=
  opExists_singleton _

/-- Determiner quantification as the special case with individual alternatives (§2):
existential closure over the propositions a predicate yields from a set of individuals is
the ordinary existential quantifier. -/
theorem opExists_image (P : E → W → Prop) (A : Set E) :
    opExists (P '' A) = {fun w ↦ ∃ x ∈ A, P x w} := by
  simp [opExists]

theorem opForall_image (P : E → W → Prop) (A : Set E) :
    opForall (P '' A) = {fun w ↦ ∀ x ∈ A, P x w} := by
  simp [opForall]

end Composition

/-! ### *Dare(-ga) nemutta* (§2) -/

section Derivation

variable {W E : Type*} (human slept : E → W → Prop)

/-- `dare human w` is *dare* 'who', the humans at the evaluation world. -/
def dare (w : W) : Set E := {x | human x w}

/-- `nemutta slept` is *nemutta* 'slept', a single alternative. -/
def nemutta : Set (E → W → Prop) := {slept}

/-- *Dare nemutta* denotes a proposition for each human. -/
theorem dare_nemutta (w : W) :
    Set.seq (nemutta slept) (dare human w) = {p | ∃ x, human x w ∧ p = slept x} := by
  rw [nemutta, seq_singleton]
  ext p; simp [dare, eq_comm]

/-- *Dare-ka nemutta* says that someone slept. -/
theorem dare_ka (w : W) :
    opExists (Set.seq (nemutta slept) (dare human w)) = {fun w' ↦ ∃ x, human x w ∧ slept x w'} := by
  rw [nemutta, seq_singleton, opExists_image]; rfl

/-- *Dare-mo nemutta* says that everyone slept. -/
theorem dare_mo (w : W) :
    opForall (Set.seq (nemutta slept) (dare human w)) = {fun w' ↦ ∀ x, human x w → slept x w'} := by
  rw [nemutta, seq_singleton, opForall_image]; rfl

end Derivation

/-! ### Widening and modals (§7) -/

section Modals

variable {W E : Type*}

/-- `ein man D` is *ein Mann* with the contextual domain `D`, a subset of the men. -/
def ein (man : E → Prop) (D : Set E) : Set E := {x | man x ∧ x ∈ D}

/-- *irgend-* widens over every value of the domain variable. -/
def irgend (den : Set E → Set E) : Set E := ⋃ D, den D

/-- *irgendein Mann* denotes all the men. -/
theorem irgend_ein (man : E → Prop) : irgend (ein man) = {x | man x} := by
  ext x
  simp only [irgend, ein, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨Set.univ, h, Set.mem_univ x⟩⟩

/-- The restricted indefinite is included in its widening. -/
theorem subset_irgend (den : Set E → Set E) (D : Set E) : den D ⊆ irgend den :=
  Set.subset_iUnion den D

/-- `kann R A` is *kann* over the propositional alternatives `A`, the possibility that some
alternative holds. -/
def kann (R : W → W → Prop) (A : Set (W → Prop)) : Set (W → Prop) :=
  {◇[R] fun w ↦ ∃ p ∈ A, p w}

/-- `muss R A` is *muss* over the propositional alternatives `A`, the necessity that some
alternative holds. -/
def muss (R : W → W → Prop) (A : Set (W → Prop)) : Set (W → Prop) :=
  {□[R] fun w ↦ ∃ p ∈ A, p w}

/-- `distribution R A w` is the distribution requirement, that every alternative is possible. -/
def distribution (R : W → W → Prop) (A : Set (W → Prop)) (w : W) : Prop :=
  ∀ p ∈ A, ◇[R] p w

/-- On a single alternative the modals are the Kripke modals. -/
theorem kann_singleton (R : W → W → Prop) (p : W → Prop) : kann R {p} = {◇[R] p} := by
  simp [kann]

theorem muss_singleton (R : W → W → Prop) (p : W → Prop) : muss R {p} = {□[R] p} := by
  simp [muss]

/-- The distribution requirement is not entailed by *muss* (§6): with two alternatives
and a single accessible world verifying one of them, necessity holds and distribution
fails. -/
theorem not_distribution_of_muss :
    ∃ (R : Bool → Bool → Prop) (A : Set (Bool → Prop)) (w : Bool),
      (∀ q ∈ muss R A, q w) ∧ ¬ distribution R A w :=
  ⟨Eq, {fun w ↦ w = true, fun w ↦ w = false}, true,
    fun q hq ↦ by
      rw [muss, Set.mem_singleton_iff] at hq
      subst hq
      exact fun w' hw' ↦ ⟨_, Set.mem_insert _ _, hw'.symm⟩,
    fun h ↦ by
      obtain ⟨w', hw', hp⟩ := h _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      subst hw'
      exact Bool.noConfusion hp⟩

end Modals

/-! ### The free-choice implicature (§8)

Widening is for a reason: strengthening, avoiding a false claim, or avoiding a false
exhaustivity inference. For (16), had the speaker chosen the narrower set with one
alternative, the exhaustivity inference would have excluded the other; the only reason to
widen is that this inference is false, so each alternative's possibility implies the other's.
The same reasoning yields the implicature of (17); under the negated possibility of (18)
every such reason is already entailed by what was said, and the implicature is cancelled. -/

section FreeChoice

variable {W : Type*} (R : W → W → Prop) (A B : W → Prop) (w : W)

/-- *Kann* over the two alternatives is the possibility of their disjunction. -/
theorem kann_pair : (∀ q ∈ kann R {A, B}, q w) ↔ ◇[R] (fun w ↦ A w ∨ B w) w := by
  simp [kann, diamond, exists_or, and_or_left]

/-- *Muss* over the two alternatives is the necessity of their disjunction. -/
theorem muss_pair : (∀ q ∈ muss R {A, B}, q w) ↔ □[R] (fun w ↦ A w ∨ B w) w := by
  simp [muss, box]

/-- In (16) the truth-conditional content with the implicature yields free choice. -/
theorem total_kann (hT : ◇[R] (fun w ↦ A w ∨ B w) w) (hI : ◇[R] A w ↔ ◇[R] B w) :
    ◇[R] A w ∧ ◇[R] B w := by
  obtain ⟨w', hw', h⟩ := hT
  rcases h with h | h
  · exact ⟨⟨w', hw', h⟩, hI.mp ⟨w', hw', h⟩⟩
  · exact ⟨hI.mpr ⟨w', hw', h⟩, ⟨w', hw', h⟩⟩

/-- In (17) the total meaning implies both possibilities once some world is accessible. -/
theorem total_muss (hT : □[R] (fun w ↦ A w ∨ B w) w) (hI : □[R] A w ↔ □[R] B w)
    (hser : ∃ w', R w w') : ◇[R] A w ∧ ◇[R] B w := by
  obtain ⟨w₀, hw₀⟩ := hser
  by_cases hA : □[R] A w
  · exact ⟨⟨w₀, hw₀, hA w₀ hw₀⟩, ⟨w₀, hw₀, hI.mp hA w₀ hw₀⟩⟩
  · have hB : ¬ □[R] B w := fun h ↦ hA (hI.mpr h)
    simp only [box, not_forall] at hA hB
    obtain ⟨wa, hwa, ha⟩ := hA
    obtain ⟨wb, hwb, hb⟩ := hB
    exact ⟨⟨wb, hwb, (hT wb hwb).resolve_right hb⟩, ⟨wa, hwa, (hT wa hwa).resolve_left ha⟩⟩

/-- In (18), under negated possibility, every reason for widening is already entailed, so no
strengthening is available. -/
theorem total_neg_kann (hT : ¬ ◇[R] (fun w ↦ A w ∨ B w) w) : ¬ ◇[R] A w ∧ ¬ ◇[R] B w :=
  ⟨fun ⟨w', hw', h⟩ ↦ hT ⟨w', hw', Or.inl h⟩, fun ⟨w', hw', h⟩ ↦ hT ⟨w', hw', Or.inr h⟩⟩

end FreeChoice

/-! ### Selectivity and intervention (§9) -/

open Data.Examples

/-- Japanese indeterminates do not change shape: *dare-ka* and *dare-mo* share their base
and differ in force. -/
theorem japanese_same_base :
    Japanese.Determiners.dare_ka.indeterminate = Japanese.Determiners.dare_mo.indeterminate ∧
      Japanese.Determiners.dare_ka.force ≠ Japanese.Determiners.dare_mo.force :=
  ⟨rfl, by decide⟩

/-- The Latvian series are selective (§1, §9): in [haspelmath-1997]'s figure the *kaut*-series
is existential, the *ne*-series confined to the direct scope of negation and the *jeb*-series to
indirect negation, comparatives and free choice, so that no function of the map is served by two
series. -/
theorem latvian_selective :
    Haspelmath1997.latvian.Pairwise (Disjoint ·.functions ·.functions) := by
  decide

/-- The Japanese series of [haspelmath-1997] are as disjoint as the Latvian ones, so the contrast
the paper draws between the two systems is one of shape and not of distribution: the Latvian
marker sits on the pronoun, while the Japanese indeterminate keeps its shape under each particle
(`japanese_same_base`). -/
theorem japanese_series_disjoint :
    Haspelmath1997.japanese.Pairwise (Disjoint ·.functions ·.functions) := by
  decide

/-- In the Beck effects (23) and their scrambled counterparts (24), a multiple question with the
second wh-phrase in situ is ungrammatical iff an operator bearing an interpretable feature,
inflectional negation or the existential closure of a quantifier, intervenes between the
wh-phrase and the complementiser. -/
theorem rows_beck :
    ∀ r ∈ Examples.all, (r.feature? "order").isSome →
      (r.judgment = .ungrammatical ↔
        r.feature? "order" = some "intervener-first" ∧ r.feature? "feature" ≠ some "none") := by
  decide +kernel

/-! ### The distribution of *irgendein* (§6, §9) -/

open PolarityItem

/-- `contextOf? r` is the licensing environment a row of the *irgendein* paradigm names. -/
def contextOf? (r : LinguisticExample) : Option LicensingContext :=
  r.parse? "context"
    [("question", .question), ("doubtVerb", .doubtVerb), ("modalPossibility", .modalPossibility),
      ("modalNecessity", .modalNecessity), ("nobody", .nobody), ("negation", .negation)]

/-- A sentence with *irgendein* is acceptable exactly in the environments the fragment entry
lists, (12), (13), (16)–(18), (21) and (22). -/
theorem rows_irgendein :
    ∀ r ∈ Examples.all, ∀ c ∈ contextOf? r,
      (r.judgment = .acceptable ↔ c ∈ German.PolarityItems.irgendein.licensingContexts) := by
  decide

/-- Under a negative operator *irgendein* is acceptable exactly when the operator closes its scope
with [∃] and not with [Neg]: under *niemand* and *auf keinen Fall* and not under *nicht*, (12),
(18) and (21). -/
theorem rows_irgendein_selective :
    ∀ r ∈ Examples.all, (contextOf? r).isSome → ∀ f ∈ r.feature? "feature",
      (r.judgment = .acceptable ↔ f = "exists") := by
  decide

/-- The licensing table licenses *irgendein* under inflectional negation, which is downward
entailing, and (21) is ungrammatical: strength does not exclude the item there, and selectivity
does. -/
theorem negation_licenses_irgendein :
    LicensingContext.negation.licenses German.PolarityItems.irgendein ∧
      Examples.ex21.judgment = .ungrammatical := by
  decide

/-- Haspelmath's map agrees with the paper. Every environment the entry lists realizes a function
of the *irgend-* series, and inflectional negation realizes direct negation, which the series
lacks. -/
theorem irgendein_haspelmath :
    ∀ s ∈ Haspelmath1997.german, s.pronoun = German.Indefinites.irgendEntry →
      (∀ c ∈ German.PolarityItems.irgendein.licensingContexts, ∀ f ∈ c.haspelmathFunction,
        f ∈ s.functions) ∧
        ∀ f ∈ LicensingContext.negation.haspelmathFunction, f ∉ s.functions := by
  decide

end KratzerShimoyama2002
