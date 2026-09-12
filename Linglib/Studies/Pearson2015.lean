import Linglib.Semantics.Reference.Rigidity
import Linglib.Semantics.Reference.Acquaintance
import Linglib.Features.Logophoricity
import Linglib.Syntax.Category.Pronoun.Logophoric

/-!
# Pearson (2015): The Interpretation of the Logophoric Pronoun in Ewe

This file formalizes the semantics in [pearson-2015] of the Ewe logophoric pronoun *yè*. On
the view of Heim and von Stechow after [chierchia-1990], *yè* is bound by the individual
abstractor an attitude verb introduces, which fixes its distribution to attitude complements
with the attitude holder as antecedent and predicts an obligatory de se reading; the
fieldwork finding is that *yè* is de se or de re. The proposal keeps the binding and lets
*yè* also sit in a covert constituent housing a concept-generator variable
([percus-sauerland-2003], [charlow-sharvit-2014]): a generator maps a res to an individual
concept and is suitable when reliable, returning the res in the actual world or, for the
holder's epistemic alternatives, the holder, and acquaintance-based, its concepts lying in
the holder's conceptual cover ([aloni-2001]) (`Reliable`, `Suitable`, `sayDeSe`, `sayDeRe`).
The de se reading is the de re reading through the self concept, so whenever the holder is
acquainted with herself as herself the de se reading entails the de re one
(`sayDeRe_of_sayDeSe`), and a de re claim about a res needs a concept in the cover that
reliably returns it (`claimDeRe_reliable`). In the paper's first scenario, John praising a
paper he does not recognize as his own, the de se reading is false and the de re reading
true (`ye_de_se_de_re_ambiguous`); in the second, John believing himself Napoleon and calling
the patient he sees on television delusional, *John claims he is delusional* is true and
*John claims Napoleon is delusional* false, since no concept in John's cover returns the
actual Napoleon (`napoleon_contrast`). In both readings the antecedent is the attitude
holder, the carrier's requirement of a self antecedent in the sense of [sells-1987]
(`ye_antecedent_is_attitude_holder`).

## Implementation notes

Concepts are functions from centered worlds, the attitude alternatives of
[lewis-1979-attitudes], to individuals, and a cover of `Semantics/Reference/Acquaintance`
supplies acquaintance; reliability is checked over a finite res domain, and the scenarios
are finite models with one attitude alternative each. The contrast between *yè* and PRO, a
φ-less minimal pronoun ([kratzer-2009]) that takes no long-distance antecedent, is described
in prose.

## References

* [pearson-2015]
* [sells-1987]
* [chierchia-1990]
* [percus-sauerland-2003]
* [charlow-sharvit-2014]
* [aloni-2001]
* [lewis-1979-attitudes]
* [kratzer-2009]
-/

namespace Pearson2015

open Reference.Acquaintance
open Features.Logophoricity

/-! ### Concept generators -/

/-- A centered attitude alternative: a world with the individual the attitude holder
identifies as herself there. -/
abbrev Centered (W E : Type*) := W × E

/-- An individual concept: a function from centered worlds to individuals, an element of an
`Acquaintance.Cover`. -/
abbrev Concept (W E : Type*) := Centered W E → E

/-- A concept generator: from a res to an individual concept. -/
abbrev ConceptGenerator (W E : Type*) := E → Concept W E

/-- A centered property: holds of an individual at a world. -/
abbrev CProp (W E : Type*) := E → W → Prop

variable {W E : Type*}

/-- The epistemic alternatives of the attitude holder: the centers of her attitude
alternatives. -/
def epiAlt (alts : List (Centered W E)) : List E := alts.map Prod.snd

/-- The self concept: the center of each alternative. -/
def selfConcept : Concept W E := Prod.snd

/-- The de se denotation of *say* (76): the embedded property holds of the center at each
attitude alternative. -/
def sayDeSe (alts : List (Centered W E)) (P : CProp W E) : Prop := ∀ p ∈ alts, P p.2 p.1

/-- A generator is reliable for holder `x` in `w` over the res domain `dom` (82): for each res
`u` its concept returns `u` in the actual world, or `u` is an epistemic alternative of `x` and
the concept returns `x`. -/
def Reliable [DecidableEq E] (alts : List (Centered W E)) (G : ConceptGenerator W E) (x : E)
    (w : W) (dom : List E) : Prop :=
  ∀ u ∈ dom, G u (w, x) = u ∨ (u ∈ epiAlt alts ∧ G u (w, x) = x)

/-- A generator is suitable for `x` in `w` (82): reliable, and acquaintance-based in that each
concept it produces lies in the holder's cover. -/
def Suitable [DecidableEq E] (cover : Cover (Centered W E) E) (alts : List (Centered W E))
    (G : ConceptGenerator W E) (x : E) (w : W) (dom : List E) : Prop :=
  Reliable alts G x w dom ∧ ∀ u ∈ dom, G u ∈ cover

/-- The de re denotation of *say* for a pronoun res (77), (79): some suitable generator, fed
the center as res, picks an individual with the property at each alternative. -/
def sayDeRe [DecidableEq E] (cover : Cover (Centered W E) E) (alts : List (Centered W E))
    (P : CProp W E) (x : E) (w : W) (dom : List E) : Prop :=
  ∃ G : ConceptGenerator W E, Suitable cover alts G x w dom ∧ ∀ p ∈ alts, P (G p.2 p) p.1

/-- The de re denotation for a name res (79): the generator is fed the fixed individual
`res` rather than the center. -/
def claimDeRe [DecidableEq E] (cover : Cover (Centered W E) E) (alts : List (Centered W E))
    (P : CProp W E) (res x : E) (w : W) (dom : List E) : Prop :=
  ∃ G : ConceptGenerator W E, Suitable cover alts G x w dom ∧ ∀ p ∈ alts, P (G res p) p.1

/-! ### General consequences -/

/-- The de se reading is the de re reading through the self concept: when the self concept is
in the holder's cover and every res in the domain is the holder or one of her epistemic
alternatives, the de se reading entails the de re reading. -/
theorem sayDeRe_of_sayDeSe [DecidableEq E] {cover : Cover (Centered W E) E}
    {alts : List (Centered W E)} {P : CProp W E} {x : E} {w : W} {dom : List E}
    (hself : selfConcept ∈ cover) (hdom : ∀ u ∈ dom, u = x ∨ u ∈ epiAlt alts)
    (h : sayDeSe alts P) : sayDeRe cover alts P x w dom :=
  ⟨λ _ => selfConcept,
    ⟨λ u hu => (hdom u hu).elim (λ e => Or.inl e.symm) (λ e => Or.inr ⟨e, rfl⟩),
      λ _ _ => hself⟩,
    h⟩

/-- A de re claim about a res in the domain needs a concept in the cover that reliably returns
it: the res itself in the actual world, or the holder if the res is one of her epistemic
alternatives. -/
theorem claimDeRe_reliable [DecidableEq E] {cover : Cover (Centered W E) E}
    {alts : List (Centered W E)} {P : CProp W E} {res x : E} {w : W} {dom : List E}
    (h : claimDeRe cover alts P res x w dom) (hres : res ∈ dom) :
    ∃ f ∈ cover, f (w, x) = res ∨ (res ∈ epiAlt alts ∧ f (w, x) = x) :=
  let ⟨G, ⟨hrel, hcov⟩, _⟩ := h; ⟨G res, hcov res hres, hrel res hres⟩

/-! ### Scenario 1: the de se / de re ambiguity (75), §5.3

John has found an old paper he wrote but does not recognize as his own; impressed, he says
"Whoever wrote this is clever". *John be yè le cleva*, 'John said that *yè* was clever', is
judged true, yet John never self-ascribes cleverness. -/

/-- Worlds: the actual world and John's say-alternative. -/
abbrev Wld := Fin 2

/-- Individuals: John and the author John takes to be someone else. -/
abbrev Ind := Fin 2

def actual : Wld := 0
def bel : Wld := 1
def john : Ind := 0
def auth : Ind := 1

/-- John's single say-alternative: the belief world centered on John. -/
def sayAlts : List (Centered Wld Ind) := [(bel, john)]

/-- The res domain: the attitude holder. -/
def dom : List Ind := [john]

/-- *clever* in the belief world: the author is clever and John is not. -/
def cleverP : CProp Wld Ind := λ y w => w = bel ∧ y = auth

instance : DecidableRel cleverP := λ _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The concept "the author of the paper": John in the actual world, the believed author in
John's belief world. -/
def authorConcept : Concept Wld Ind := λ p => if p.1 = actual then john else auth

/-- The generator carrying the author concept for every res. -/
def authorGen : ConceptGenerator Wld Ind := λ _ => authorConcept

/-- John's cover: the author concept. -/
def s1Cover : Cover (Centered Wld Ind) Ind := {authorConcept}

/-- The de se reading is false: at John's alternative the center, John, is not clever. -/
theorem deSe_false : ¬ sayDeSe sayAlts cleverP := by unfold sayDeSe; decide

/-- The author generator is suitable for John: reliable, returning John in the actual world,
and in his cover. -/
theorem authorGen_suitable : Suitable s1Cover sayAlts authorGen john actual dom :=
  ⟨by unfold Reliable; decide, λ _ _ => Set.mem_singleton _⟩

/-- The de re reading is true: through the author concept the individual picked at John's
alternative is clever. -/
theorem deRe_true : sayDeRe s1Cover sayAlts cleverP john actual dom :=
  ⟨authorGen, authorGen_suitable, by decide⟩

/-- *yè* is de se or de re: the same sentence is false on the de se LF (78) and true on the de
re LF (79). -/
theorem ye_de_se_de_re_ambiguous :
    ¬ sayDeSe sayAlts cleverP ∧ sayDeRe s1Cover sayAlts cleverP john actual dom :=
  ⟨deSe_false, deRe_true⟩

/-! ### Scenario 2: the Napoleon contrast (80) to (85), §6

John believes he is Napoleon; watching a report he does not recognize himself and says the
patient he sees is delusional. *John claims he is delusional*, with *yè* read de re, is true;
*John claims Napoleon is delusional* is false, though John believes he is Napoleon: the bound
pronoun ranges over John's epistemic alternatives and is overwritten with John, whom he
identifies through the in-cover "patient on television" concept, while the name denotes the
actual Napoleon, to whom John bears no acquaintance. -/

namespace Napoleon

/-- Worlds: the actual world and John's claim-alternative. -/
abbrev Wld := Fin 2

/-- Individuals: John, the patient John sees on television, and Napoleon. -/
abbrev Ind := Fin 3

def actualN : Wld := 0
def belN : Wld := 1
def john : Ind := 0
def patient : Ind := 1
def napoleon : Ind := 2

/-- John's claim-alternative: the belief world centered on John. -/
def claimAlts : List (Centered Wld Ind) := [(belN, john)]

/-- *delusional* in the belief world: the patient. -/
def delusionalP : CProp Wld Ind := λ y w => w = belN ∧ y = patient

instance : DecidableRel delusionalP := λ _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The concept "the patient I saw on television": John in the actual world, the patient in
John's belief world. -/
def patientConcept : Concept Wld Ind := λ p => if p.1 = actualN then john else patient

/-- The generator carrying the patient concept for every res. -/
def patientGen : ConceptGenerator Wld Ind := λ _ => patientConcept

/-- John's cover: the patient concept alone; no concept returns the actual Napoleon. -/
def johnCover : Cover (Centered Wld Ind) Ind := {patientConcept}

/-- *John claims he is delusional* is true de re: the center, John, fed to the patient
generator, is the delusional patient at the alternative. -/
theorem claimsHe_true : sayDeRe johnCover claimAlts delusionalP john actualN [john] :=
  ⟨patientGen, ⟨by unfold Reliable; decide, λ _ _ => Set.mem_singleton _⟩, by decide⟩

/-- *John claims Napoleon is delusional* is false: the only concept in John's cover returns
John, not Napoleon, in the actual world, and Napoleon is not an epistemic alternative of
John. -/
theorem claimsNapoleon_false :
    ¬ claimDeRe johnCover claimAlts delusionalP napoleon john actualN [napoleon] := by
  intro h
  obtain ⟨f, hf, hr⟩ := claimDeRe_reliable h (List.mem_singleton_self _)
  rw [johnCover, Set.mem_singleton_iff] at hf
  subst hf
  exact absurd hr (by decide)

/-- The Napoleon contrast: the bound-pronoun reading is true and the name reading false. -/
theorem napoleon_contrast :
    sayDeRe johnCover claimAlts delusionalP john actualN [john] ∧
      ¬ claimDeRe johnCover claimAlts delusionalP napoleon john actualN [napoleon] :=
  ⟨claimsHe_true, claimsNapoleon_false⟩

end Napoleon

/-! ### The carrier -/

/-- *yè*'s antecedent is the attitude holder in both readings, bound by the attitude verb's
abstractor: the carrier's required role is self, an attitude holder in the sense of
[sells-1987]. -/
theorem ye_antecedent_is_attitude_holder : Logophoric.requiredRole ye = LogophoricRole.self :=
  rfl

end Pearson2015
