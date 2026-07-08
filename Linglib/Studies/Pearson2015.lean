import Linglib.Semantics.Intensional.Rigidity
import Linglib.Semantics.Reference.Acquaintance
import Linglib.Features.Logophoricity
import Linglib.Syntax.Category.Pronoun.Logophoric

/-!
# Pearson (2015): The interpretation of the logophoric pronoun in Ewe
[pearson-2015] [sells-1987] [percus-sauerland-2003] [charlow-sharvit-2014]
[chierchia-1990] [kratzer-2009] [lewis-1979-attitudes] [aloni-2001]

[pearson-2015] (*Nat Lang Semantics* 23(2)) gives the definitive modern semantics of the
Ewe logophoric pronoun *yè* — the carrier `ye : LogophoricPronoun`
(`Syntax/Category/Pronoun/Logophoric.lean`, `requiredRole = .self`). The traditional Heim & von
Stechow view (after [chierchia-1990]) is that *yè* bears an `[log]` feature that must be
bound by the **individual abstractor** an attitude verb introduces in the embedded left
periphery — so *yè* obligatorily occurs under an attitude predicate and takes the **attitude
holder** as antecedent (this *is* the `.self` requirement: Sells' antecedent-must-be-a-self).
That view predicts *yè* is obligatorily **de se**.

[pearson-2015]'s fieldwork finding is that this prediction is **wrong**: *yè* is de se / de re
**ambiguous**. Her account keeps *yè* bound by the attitude abstractor (preserving the
distribution) but lets it additionally sit inside a **`resP`** — a covert constituent housing a
**concept generator** variable ([percus-sauerland-2003], [charlow-sharvit-2014]) — yielding the
de re reading. A concept generator maps a *res* to an individual concept; it is **suitable**
when *reliable* (returns the res in the actual world, with a variable over the holder's
epistemic alternatives overwritten with the holder) and **acquaintance-based** (the concept is
one of the holder's available ways of identifying — a member of her conceptual cover,
[aloni-2001]).

## This file

* `Concept` / `ConceptGenerator` — over `Intensional.Intension`; a `Concept` *is* an element of an
  `Acquaintance.Cover`, so acquaintance is membership in the holder's cover.
* `sayDeSe` (eq. 76), `sayDeRe`/`claimDeRe` (eq. 77/79b) — the two denotations of *say*, with
  `Reliable` (eq. 82.i, reliability-with-epistemic-overwrite) and `Suitable` (eq. 82 = reliable
  ∧ acquaintance-based-via-cover).
* **Scenario 1** (eq. 75, §5.3): John says "whoever wrote this is clever", unaware he is the
  author. `ye_de_se_de_re_ambiguous` proves the de se LF is **false** while the de re LF is
  **true** — via an explicit witnessing "author" concept generator. [pearson-2015]'s central
  finding, made true by construction.
* **Scenario 2** (`Napoleon`, §6, eq. 80–85): John believes he is Napoleon and, not recognising
  himself on TV, says the patient is delusional. `napoleon_contrast` proves "John claims he is
  delusional" **true** but "John claims Napoleon is delusional" **false** — the bound pronoun
  (overwritten to John, whom John is acquainted with) succeeds where the name (the actual-world
  Napoleon, to whom John bears no acquaintance, so no cover concept reliably picks him) fails.
* `ye_antecedent_is_attitude_holder` grounds the carrier: *yè*'s antecedent is the attitude
  holder in both readings, i.e. the carrier's `requiredRole = .self`.

Deferred to prose: the *yè*-vs-PRO φ-feature asymmetry (§7.1: PRO is a φ-less [kratzer-2009]
minimal pronoun, so — unlike *yè* — it takes no long-distance antecedent).
-/

namespace Pearson2015

open Intensional (Intension)
open Semantics.Reference.Acquaintance (Cover)
open Features.Logophoricity (LogophoricRole Logophoric)

/-! ### Concept generators ([percus-sauerland-2003], [charlow-sharvit-2014]) -/

/-- A (Lewis) centered attitude alternative: a world paired with the individual the
    attitude holder identifies as herself there ([lewis-1979-attitudes]). -/
abbrev Centered (W E : Type*) := W × E

/-- An individual concept à la [percus-sauerland-2003]: a function from centered worlds
    to individuals (`Intensional.Intension` over `Centered`). This is exactly an element of an
    `Acquaintance.Cover (Centered W E) E`. -/
abbrev Concept (W E : Type*) := Intension (Centered W E) E

/-- A concept generator: from a *res* to an individual concept. -/
abbrev ConceptGenerator (W E : Type*) := E → Concept W E

/-- A centered property (type ⟨e,⟨s,t⟩⟩): holds of an individual at a world. -/
abbrev CProp (W E : Type*) := E → W → Prop

/-- The epistemic alternatives of the attitude holder = the de se centers of her
    attitude alternatives. -/
def epiAlt {W E : Type*} (alts : List (Centered W E)) : List E := alts.map Prod.snd

/-! ### `say` de se and de re ([pearson-2015] eq. 76, 77, 82) -/

/-- `⟦say^de se⟧` (eq. 76): the embedded property holds of the **de se center** at each
    attitude alternative. *yè* bound directly by the attitude abstractor. -/
def sayDeSe {W E : Type*} (alts : List (Centered W E)) (P : CProp W E) : Prop :=
  ∀ p ∈ alts, P p.2 p.1

/-- A concept generator is **reliable** for holder `x` in `w` ([pearson-2015] eq. 82.i, the
    "Reliability" clause; over a finite res domain `dom`): for each res `u` the concept returns
    `u` in the actual world, **or** `u` is an epistemic alternative of `x` and the concept
    returns `x` (the epistemic-alternative *overwrite*). -/
def Reliable {W E : Type*} [DecidableEq E] (alts : List (Centered W E))
    (G : ConceptGenerator W E) (x : E) (w : W) (dom : List E) : Prop :=
  ∀ u ∈ dom, G u (w, x) = u ∨ (u ∈ epiAlt alts ∧ G u (w, x) = x)

/-- A concept generator is **suitable** for `x` in `w` ([pearson-2015] eq. 82): it is `Reliable`
    **and acquaintance-based** — each concept it produces (for a res in `dom`) is one of the
    holder's available ways of identifying, i.e. a member of her conceptual cover ([aloni-2001];
    `Acquaintance.Cover`). The cover is what makes suitability non-trivial: a generator whose
    concepts lie outside the holder's cover is unsuitable, even if reliable. -/
def Suitable {W E : Type*} [DecidableEq E] (cover : Cover (Centered W E) E)
    (alts : List (Centered W E)) (G : ConceptGenerator W E) (x : E) (w : W) (dom : List E) : Prop :=
  Reliable alts G x w dom ∧ ∀ u ∈ dom, G u ∈ cover

/-- `⟦say^de re⟧` for a **pronoun** (*yè*) res (eq. 77/79b): there is a `Suitable` concept
    generator `G` such that at each attitude alternative `⟨w',y⟩`, the individual `G`'s concept
    (fed the **de se center** `y` as res) picks out at `⟨w',y⟩` has the embedded property at
    `w'`. *yè* sits in a `resP`, bound by the attitude abstractor. -/
def sayDeRe {W E : Type*} [DecidableEq E] (cover : Cover (Centered W E) E)
    (alts : List (Centered W E)) (P : CProp W E) (x : E) (w : W) (dom : List E) : Prop :=
  ∃ G : ConceptGenerator W E, Suitable cover alts G x w dom ∧ ∀ p ∈ alts, P (G p.2 p) p.1

/-- `⟦say^de re⟧` for a **name** res (eq. 79): like `sayDeRe`, but the res fed to `G` is the
    fixed individual `res` (a rigid, actual-world-bound name), not the de se center. The
    difference from `sayDeRe` is exactly the pronoun/name asymmetry that delivers §6. -/
def claimDeRe {W E : Type*} [DecidableEq E] (cover : Cover (Centered W E) E)
    (alts : List (Centered W E)) (P : CProp W E) (res x : E) (w : W) (dom : List E) : Prop :=
  ∃ G : ConceptGenerator W E, Suitable cover alts G x w dom ∧ ∀ p ∈ alts, P (G res p) p.1

/-! ### Scenario 1: the de se / de re ambiguity ([pearson-2015] eq. 75, §5.3)

John has found an old paper he wrote but does not recognise as his own; impressed, he says
"Whoever wrote this is clever." `John be yè le cleva` ('John said that *yè* was clever') is
judged **true** — yet John never self-ascribes cleverness. -/

/-- Worlds: `actual` (0) and `bel` (1), John's say-alternative world. -/
abbrev Wld := Fin 2
/-- Individuals: `john` (0) and `auth` (1), the author John takes to be someone else. -/
abbrev Ind := Fin 2

def actual : Wld := 0
def bel : Wld := 1
def john : Ind := 0
def auth : Ind := 1

/-- John's single say-alternative: world `bel`, de se center `john` (himself qua speaker). -/
def sayAlts : List (Centered Wld Ind) := [(bel, john)]

/-- The relevant res domain: just the attitude holder. -/
def dom : List Ind := [john]

/-- `clever` in the belief world `bel`: the author `auth` is clever, John is not — John
    ascribes cleverness to the author, failing to recognise the author as himself. -/
def cleverB : Wld → Ind → Bool
  | 1, 1 => true
  | _, _ => false

/-- Reducible so `decide` sees the underlying `Bool` test through the wrapper. -/
abbrev cleverP : CProp Wld Ind := fun y w => cleverB w y = true

/-- The "author of the paper" concept: returns the res `john` in the actual world (John really
    is the author) but the believed author `auth` in John's belief world. -/
def authorConcept : Concept Wld Ind := fun p => if p.1 = actual then john else auth

/-- The generator carrying the "author" concept for any res. -/
def authorGen : ConceptGenerator Wld Ind := fun _u => authorConcept

/-- John's conceptual cover: the "author of the paper" concept he is acquainted via. -/
def s1Cover : Cover (Centered Wld Ind) Ind := {authorConcept}

/-! ### The ambiguity, derived -/

/-- The **de se** reading is **false**: at John's say-alternative ⟨bel, john⟩ the de se
    centre (john) is not clever — John did not self-ascribe cleverness. -/
theorem deSe_false : ¬ sayDeSe sayAlts cleverP := by unfold sayDeSe; decide

/-- The "author" generator is **suitable** for John: reliable (returns the res `john` in the
    actual world) and acquaintance-based (its concept is in John's cover). -/
theorem authorGen_suitable : Suitable s1Cover sayAlts authorGen john actual dom := by
  refine ⟨by unfold Reliable; decide, ?_⟩
  intro u hu
  simp only [dom, List.mem_singleton] at hu; subst hu
  simp [authorGen, s1Cover]

/-- The **de re** reading is **true**: under the suitable "author" generator, at each
    say-alternative the individual it picks (the author) is clever — the de re reading rescues
    truth where de se fails. -/
theorem deRe_true : sayDeRe s1Cover sayAlts cleverP john actual dom :=
  ⟨authorGen, authorGen_suitable, by decide⟩

/-- **yè is de se / de re ambiguous** ([pearson-2015]'s central finding): the same sentence is
    **false** on the de se LF (78) but **true** on the de re LF (79). The Heim & von Stechow
    prediction of obligatory de se is thereby refuted, by construction. -/
theorem ye_de_se_de_re_ambiguous :
    ¬ sayDeSe sayAlts cleverP ∧ sayDeRe s1Cover sayAlts cleverP john actual dom :=
  ⟨deSe_false, deRe_true⟩

/-! ### Scenario 2: the Napoleon contrast ([pearson-2015] §6, eq. 80–85)

John is delusional and believes he is Napoleon; watching a TV report he does not recognise
himself, he says the patient he saw is delusional. "John claims he is delusional" (the pronoun
*yè*, de re) is **true**; "John claims Napoleon is delusional" is **false** — though John
believes he is Napoleon. A variable bound by the attitude verb (*yè*) ranges over John's
epistemic alternatives and is overwritten with John, whom John identifies via the in-cover
"patient on TV" concept; the name *Napoleon* denotes the actual-world individual, to whom John
bears **no** acquaintance — no concept in his cover reliably picks Napoleon. -/

namespace Napoleon

/-- Worlds: `actualN` (0) and `belN` (1), John's claim-alternative world. -/
abbrev Wld := Fin 2
/-- Individuals: `john` (0), the `patient` John sees on TV (1), and `napoleon` (2). -/
abbrev Ind := Fin 3

def actualN : Wld := 0
def belN : Wld := 1
def john : Ind := 0
def patient : Ind := 1
def napoleon : Ind := 2

/-- John's claim-alternatives: world `belN`, de se center `john`. -/
def claimAlts : List (Centered Wld Ind) := [(belN, john)]

/-- `delusional` in `belN`: the patient John saw on TV is delusional. -/
def delusionalB : Wld → Ind → Bool
  | 1, 1 => true
  | _, _ => false

abbrev delusionalP : CProp Wld Ind := fun y w => delusionalB w y = true

/-- The "patient I saw on TV" concept: the actual world → `john` (reliably himself), the belief
    world → `patient` (whom John takes the man on TV to be). -/
def patientConcept : Concept Wld Ind := fun p => if p.1 = actualN then john else patient

/-- The generator carrying the "patient" concept for any res. -/
def patientGen : ConceptGenerator Wld Ind := fun _u => patientConcept

/-- John's conceptual cover: the single "patient on TV" concept. He has **no** concept that
    picks out the actual-world `napoleon`. -/
def johnCover : Cover (Centered Wld Ind) Ind := {patientConcept}

/-- "John claims he is delusional" is **true** on the de re LF: the de se center (= John) is fed
    to the suitable "patient" generator, which at the claim-alternative picks the delusional
    patient. -/
theorem claimsHe_true : sayDeRe johnCover claimAlts delusionalP john actualN [john] := by
  refine ⟨patientGen, ⟨by unfold Reliable; decide, ?_⟩, by decide⟩
  intro u hu
  rw [List.mem_singleton] at hu; subst hu
  simp [patientGen, johnCover]

/-- "John claims Napoleon is delusional" is **false**: no concept in John's cover is reliable for
    the res `napoleon` (the only cover concept returns John, not Napoleon, in the actual world,
    and Napoleon is not an epistemic alternative of John). So no suitable generator exists. -/
theorem claimsNapoleon_false :
    ¬ claimDeRe johnCover claimAlts delusionalP napoleon john actualN [napoleon] := by
  rintro ⟨G, ⟨hrel, hcov⟩, -⟩
  have hmem := hcov napoleon (by simp)
  simp only [johnCover, Set.mem_singleton_iff] at hmem
  have hr := hrel napoleon (by simp)
  rw [hmem] at hr
  exact absurd hr (by decide)

/-- The **Napoleon contrast** ([pearson-2015] §6): the bound-pronoun (*yè*) reading is true while
    the name reading is false — the discrimination Pearson's suitability (reliability +
    acquaintance-based cover) delivers, and which the earlier vacuous `∃R` could not. -/
theorem napoleon_contrast :
    sayDeRe johnCover claimAlts delusionalP john actualN [john] ∧
    ¬ claimDeRe johnCover claimAlts delusionalP napoleon john actualN [napoleon] :=
  ⟨claimsHe_true, claimsNapoleon_false⟩

end Napoleon

/-! ### Grounding the `LogophoricPronoun` carrier -/

/-- *yè*'s antecedent is the **attitude holder** in both readings ([pearson-2015]: bound by
    the attitude verb's individual abstractor) — exactly the carrier's `requiredRole = .self`
    (Sells: the antecedent must be at least a *self* = an attitude holder). The de se/de re
    ambiguity above is orthogonal: both readings keep the attitude holder as antecedent. -/
theorem ye_antecedent_is_attitude_holder :
    Logophoric.requiredRole ye = LogophoricRole.self := rfl

end Pearson2015
