module

public import Linglib.Semantics.Questions.Highlighting
public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Studies.FarkasBruce2010
public import Linglib.Data.Examples.RoelofsenFarkas2015

/-!
# Roelofsen and Farkas (2015): Polarity particle responses

This file formalizes [roelofsen-farkas-2015]'s account of polarity particle responses. A sentence
expresses an inquisitive proposition and highlights possibilities, each positive or negative
(`Highlighting.Formula.proposition`, `Highlighting.Formula.highlights`): *Is the number of
planets even?* and *Is it odd?* raise the same issue (`proposition_query_even_eq_odd`) but
highlight different possibilities, and *Is it odd?* and *Is it not even?* highlight the same
worlds with opposite polarities. A polarity response hosts a relative feature, [agree] or
[reverse], and an absolute feature, [+] or [−], each presupposing something of the prejacent
(`AbsolutePresup`, `RelativePresup`, (68)–(71)): together they fix what the response expresses
from the unique possibility its antecedent highlights (`absolutePresup_and_relativePresup_iff`,
(72)–(75)). So an [agree, +] response such as *yes, it is* conveys the even answer after *Is it
even?* and the odd one after *Is it odd?* (`agreePositive_iff`, (49), (50)); *no, it isn't*
conveys that the number is not odd after *Is it odd?* and that it is not even after *Is it not
even?* (`negative_response_query_odd`, `negative_response_query_not_even`, (52), (53)); and an
alternative question highlights two possibilities and licenses no particle response
(`not_relativePresup_disj`, (51)). On a response sharing its antecedent's radical, the two
highlighting the images of one possibility under their polarities
(`Highlighting.Formula.highlights_ofPolarity`), the relative feature is the relative polarity of
[farkas-bruce-2010], [agree] when the two polarities agree (`relativePresup_smul_iff`).

Particles realize features, and which do so is language-specific (§4.2, §5.2): English *yes*
realizes [agree] and [+], *no* [reverse] and [−] (76); French *oui* [+], *non* [−] and *si* the
combination [reverse, +] (118); German *ja* and *nein* like *yes* and *no*, and *doch* [reverse,
+] (123). A particle is usable in a response when it realizes one of its features or its
combination, unless a particle dedicated to the combination blocks it (`Usable`). This yields
the English pattern (77), where both particles occur in [agree, −] and [reverse, +] responses,
and the French and German patterns (119)–(127) (`english_usable`, `french_usable`,
`german_usable`), and it predicts the judgment of every example (`judgment_iff_usable`). The
particles that do double duty, *yes* and *no*, each realize a natural class of features, the
unmarked [agree] and [+] or the marked [reverse] and [−] (`Feature.value`, `mem_english_iff`,
(78), (80)). The account agrees with what [farkas-bruce-2010] say English *yes* and *no* and
French *si* mark (`usable_english_iff_mem`, `usable_si_iff_mem_reversePositive`).

## Implementation notes

* The features' presuppositions are stated of a proposition and a set of highlighted
  possibilities, the two values of the prejacent formula; they meet only in the absolute
  features.
* The unique most salient antecedent possibility is the unique possibility highlighted by the
  antecedent utterance, the top of the stack of discourse referents of (61); the context itself,
  its table, referents and commitments, is not modelled.
* Features are polarities: a relative feature `r` is [agree] when positive and [reverse] when
  negative, so that the prejacent highlights `r • β` for the antecedent possibility `β`, the
  polarity group acting on a possibility and its polarity together.
* Blocking by a dedicated particle, stated for *si* and *doch* in §5.2, is the general clause of
  `Usable`.
* The rows are the examples (6), (7), (119)–(122) and (124)–(127), one row per particle; the
  French paradigm (8), (9) of §2 repeats (119)–(122), and its (9) prints the French sentences of
  its two lines in the opposite order to their glosses.

## TODO

* The Romanian and Hungarian systems of §5.1, with a dedicated [reverse] particle, rest on
  realization needs, the reversal scale (81) and contrastive markedness (82), none of which is
  formalized, nor are the preferences among realizable particles.

## References

* [roelofsen-farkas-2015]
* [farkas-bruce-2010]
* [roelofsen-vangool-2010]
-/

@[expose] public section

namespace RoelofsenFarkas2015

open Discourse Data.Examples

variable {W : Type*}

/-! ### Polarity features (§4.1) -/

/-- (68), (69): the absolute feature `s` presupposes that the prejacent expresses a proposition
`q` with a single possibility, which it highlights with polarity `s`. -/
def AbsolutePresup (s : Polarity) (q : Question W) (H : Set (Polarity × Set W)) : Prop :=
  ∃ α, q = Question.ofSet α ∧ H = {(s, α)}

/-- (70), (71): the relative feature `r`, [agree] when positive and [reverse] when negative,
presupposes that the antecedent highlights a unique possibility and that the prejacent
highlights its image under `r`: the same possibility with the same polarity, or its complement
with the opposite polarity. -/
def RelativePresup (r : Polarity) (H ant : Set (Polarity × Set W)) : Prop :=
  ∃ β, ant = {β} ∧ H = {r • β}

/-- (72)–(75): an absolute feature `s` and a relative feature `r` together presuppose that the
antecedent highlights a single possibility, of polarity `r * s`, and that the prejacent
expresses its image under `r`, highlighted with polarity `s`. -/
theorem absolutePresup_and_relativePresup_iff {r s : Polarity} {q : Question W}
    {H ant : Set (Polarity × Set W)} :
    AbsolutePresup s q H ∧ RelativePresup r H ant ↔
      ∃ α, ant = {(r * s, α)} ∧ q = Question.ofSet (r • α) ∧ H = {(s, r • α)} := by
  constructor
  · rintro ⟨⟨α', hq, hα'⟩, ⟨t, β⟩, hant, hH⟩
    rw [hα', Prod.smul_mk, Set.singleton_eq_singleton_iff, Prod.mk.injEq] at hH
    obtain ⟨hs, hβ⟩ := hH
    refine ⟨β, ?_, hβ ▸ hq, hβ ▸ hα'⟩
    rw [hant, hs, smul_eq_mul, ← mul_assoc, Polarity.mul_self, Polarity.positive_mul]
  · rintro ⟨α, hant, hq, hH⟩
    refine ⟨⟨_, hq, hH⟩, (r * s, α), hant, ?_⟩
    rw [hH, Prod.smul_mk, smul_eq_mul, ← mul_assoc, Polarity.mul_self, Polarity.positive_mul]

/-- On a prejacent of polarity `s` sharing the radical of an antecedent of polarity `t`, the two
highlighting the images of one possibility `x` under `s` and `t`, the relative feature is the
relative polarity of [farkas-bruce-2010] (`Discourse.Response.relative`): [agree] iff `s = t`. -/
theorem relativePresup_smul_iff {r s t : Polarity} (x : Polarity × Set W) :
    RelativePresup r {s • x} {t • x} ↔ r = s / t := by
  simp only [RelativePresup, Set.singleton_eq_singleton_iff, exists_eq_left', smul_smul,
    eq_div_iff_mul_eq']
  constructor
  · intro h
    simpa using (congrArg Prod.fst h).symm
  · rintro rfl
    rfl

/-! ### The questions of §3.3 -/

section Questions

open Highlighting Highlighting.Formula

variable {A : Type*} (v : A → Set W) {e o : A}

/-- *Is the number of planets even?* and *Is it odd?* express the same issue. -/
theorem proposition_query_even_eq_odd (hodd : v o = (v e)ᶜ) :
    (query (atom e)).proposition v = (query (atom o)).proposition v := by
  simp only [proposition, Question.query_ofSet, hodd, Question.polar_compl]

/-- (49), (50): an [agree, +] response to *Is it `a`?*, such as *yes, it is*, expresses `a`:
the even answer after *Is it even?* and the odd one after *Is it odd?*. -/
theorem agreePositive_iff (a : A) (q : Question W) (H : Set (Polarity × Set W)) :
    AbsolutePresup .positive q H ∧ RelativePresup .positive H ((query (atom a)).highlights v) ↔
      q = Question.ofSet (v a) ∧ H = {(.positive, v a)} := by
  simp only [absolutePresup_and_relativePresup_iff, highlights,
    Highlighting.project_singleton, Set.singleton_eq_singleton_iff, Prod.mk.injEq,
    Polarity.positive_mul, Polarity.positive_smul, true_and, exists_eq_left']

/-- (52): a negative response to *Is it odd?*, *no, it isn't*, expresses that the number is
not odd. -/
theorem negative_response_query_odd (hodd : v o = (v e)ᶜ) (q : Question W)
    (H : Set (Polarity × Set W)) (r : Polarity)
    (h : AbsolutePresup .negative q H ∧ RelativePresup r H ((query (atom o)).highlights v)) :
    q = Question.ofSet (v e) := by
  obtain ⟨α, hant, hq, -⟩ := absolutePresup_and_relativePresup_iff.1 h
  simp only [highlights, Highlighting.project_singleton, Set.singleton_eq_singleton_iff,
    Prod.mk.injEq] at hant
  obtain ⟨hr, rfl⟩ := hant
  cases r
  · exact absurd hr (by decide)
  · rw [hq, Polarity.negative_smul_set, hodd, compl_compl]

/-- (53): a negative response to *Is it not even?*, *no, it isn't*, expresses that the number
is not even, although the question highlights the same worlds as *Is it odd?*. -/
theorem negative_response_query_not_even (q : Question W) (H : Set (Polarity × Set W))
    (r : Polarity)
    (h : AbsolutePresup .negative q H ∧
      RelativePresup r H ((query (neg (atom e))).highlights v)) :
    q = Question.ofSet (v e)ᶜ := by
  obtain ⟨α, hant, hq, -⟩ := absolutePresup_and_relativePresup_iff.1 h
  simp only [highlights, Highlighting.neg_singleton, Highlighting.project_singleton,
    Set.singleton_eq_singleton_iff, Prod.mk.injEq] at hant
  obtain ⟨hr, rfl⟩ := hant
  cases r
  · rw [hq, Polarity.positive_smul]
  · exact absurd hr (by decide)

/-- (51): the alternative question *Is it even↑, or odd↓?* highlights two possibilities, so no
relative feature, and no particle response, is licensed after it. -/
theorem not_relativePresup_disj [Nonempty W] (hodd : v o = (v e)ᶜ) (r : Polarity)
    (H : Set (Polarity × Set W)) :
    ¬ RelativePresup r H ((inqDisj (atom e) (atom o)).highlights v) := by
  rintro ⟨β, hant, -⟩
  simp only [highlights, hodd] at hant
  have h₁ : ((.positive, v e) : Polarity × Set W) ∈ ({β} : Set _) := hant ▸ Or.inl rfl
  have h₂ : ((.positive, (v e)ᶜ) : Polarity × Set W) ∈ ({β} : Set _) := hant ▸ Or.inr rfl
  rw [Set.mem_singleton_iff] at h₁ h₂
  have hp : v e = (v e)ᶜ := congrArg Prod.snd (h₁.trans h₂.symm)
  obtain ⟨w⟩ := ‹Nonempty W›
  by_cases hw : w ∈ v e
  · exact (hp ▸ hw) hw
  · exact hw (hp ▸ hw)

end Questions

/-! ### Realization (§4.2, §5.2) -/

/-- A polarity feature: relative, [agree] when positive and [reverse] when negative, or
absolute, [+] or [−]. -/
inductive Feature where
  | relative (r : Polarity)
  | absolute (s : Polarity)
  deriving DecidableEq, Repr

/-- The polarity of a feature, positive for the unmarked [agree] and [+] and negative for the
marked [reverse] and [−] (78), (80). -/
def Feature.value : Feature → Polarity
  | .relative r => r
  | .absolute s => s

/-- What a particle can realize: a feature, or a feature combination [r, s] as a whole. -/
inductive Target where
  | feature (f : Feature)
  | combination (r s : Polarity)
  deriving DecidableEq, Repr

/-- (76): English *yes* realizes [agree] and [+], *no* [reverse] and [−]. -/
def english : English.PolarityParticle → List Target
  | .yes => [.feature (.relative .positive), .feature (.absolute .positive)]
  | .no => [.feature (.relative .negative), .feature (.absolute .negative)]

/-- (118): French *oui* realizes [+], *non* [−], and *si* the combination [reverse, +]. -/
def french : French.PolarityParticle → List Target
  | .oui => [.feature (.absolute .positive)]
  | .non => [.feature (.absolute .negative)]
  | .si => [.combination .negative .positive]

/-- (123): German *ja* realizes [agree] and [+], *nein* [reverse] and [−], and *doch* the
combination [reverse, +]. -/
def german : German.PolarityParticle → List Target
  | .ja => [.feature (.relative .positive), .feature (.absolute .positive)]
  | .nein => [.feature (.relative .negative), .feature (.absolute .negative)]
  | .doch => [.combination .negative .positive]

section Usable

variable {P : Type*} [Fintype P] (R : P → List Target)

/-- A particle can realize the combination [r, s]: one of its features, or the combination. -/
def Realizes (p : P) (r s : Polarity) : Prop :=
  .feature (.relative r) ∈ R p ∨ .feature (.absolute s) ∈ R p ∨ .combination r s ∈ R p

/-- A particle is usable in an [r, s] response when it can realize it and no particle dedicated
to the combination blocks it. -/
def Usable (p : P) (r s : Polarity) : Prop :=
  Realizes R p r s ∧ ∀ q, .combination r s ∈ R q → .combination r s ∈ R p

instance (p : P) (r s : Polarity) : Decidable (Realizes R p r s) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

instance [DecidableEq P] (p : P) (r s : Polarity) : Decidable (Usable R p r s) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Usable

/-- (77): in English, [agree, +] responses take *yes*, [reverse, −] responses *no*, and
[agree, −] and [reverse, +] responses either particle. -/
theorem english_usable (p : English.PolarityParticle) :
    (Usable english p .positive .positive ↔ p = .yes) ∧
      (Usable english p .negative .negative ↔ p = .no) ∧
      Usable english p .positive .negative ∧ Usable english p .negative .positive := by
  cases p <;> decide

/-- (119)–(122): French [agree, +] responses take *oui*, [reverse, +] responses *si*, and
[agree, −] and [reverse, −] responses *non*. -/
theorem french_usable (p : French.PolarityParticle) :
    (Usable french p .positive .positive ↔ p = .oui) ∧
      (Usable french p .negative .positive ↔ p = .si) ∧
      (Usable french p .positive .negative ↔ p = .non) ∧
      (Usable french p .negative .negative ↔ p = .non) := by
  cases p <;> decide

/-- (124)–(127): German [agree, +] responses take *ja*, [reverse, +] responses *doch*,
[reverse, −] responses *nein*, and [agree, −] responses *ja* or *nein*. -/
theorem german_usable (p : German.PolarityParticle) :
    (Usable german p .positive .positive ↔ p = .ja) ∧
      (Usable german p .negative .positive ↔ p = .doch) ∧
      (Usable german p .negative .negative ↔ p = .nein) ∧
      (Usable german p .positive .negative ↔ p ≠ .doch) := by
  cases p <;> decide

/-- (80): the English particles each realize a natural class of features, *yes* the unmarked
and *no* the marked ones. -/
theorem mem_english_iff (f : Feature) :
    (Target.feature f ∈ english .yes ↔ f.value = .positive) ∧
      (Target.feature f ∈ english .no ↔ f.value = .negative) := by
  cases f with
  | relative r => cases r <;> decide
  | absolute s => cases s <;> decide

/-- The English particles are usable in exactly the responses [farkas-bruce-2010] say they
mark: *yes* [same] or [+], *no* [reverse] or [−]. -/
theorem usable_english_iff_mem (p : English.PolarityParticle) (x : Response) :
    Usable english p x.relative x.polarity ↔ x ∈ FarkasBruce2010.english p := by
  obtain ⟨m, a, s⟩ := x
  cases m <;> cases p <;> cases a <;> cases s <;> decide

/-- French *si* is usable in exactly the [reverse, +] responses of [farkas-bruce-2010]. -/
theorem usable_si_iff_mem_reversePositive (x : Response) :
    Usable french .si x.relative x.polarity ↔ x ∈ FarkasBruce2010.reversePositive := by
  obtain ⟨m, a, s⟩ := x
  cases m <;> cases a <;> cases s <;> decide

/-! ### The examples -/

/-- The particles of the examples. -/
inductive Particle where
  | en (p : English.PolarityParticle)
  | fr (p : French.PolarityParticle)
  | de (p : German.PolarityParticle)
  deriving DecidableEq, Repr

/-- A particle is usable in an [r, s] response in its language. -/
def Particle.Usable : Particle → Polarity → Polarity → Prop
  | .en p, r, s => RoelofsenFarkas2015.Usable english p r s
  | .fr p, r, s => RoelofsenFarkas2015.Usable french p r s
  | .de p, r, s => RoelofsenFarkas2015.Usable german p r s

instance (p : Particle) (r s : Polarity) : Decidable (p.Usable r s) := by
  cases p <;> unfold Particle.Usable <;> infer_instance

/-- The particles of each language, by Glottocode and spelling. -/
def particleTable : List (String × List (String × Particle)) :=
  [("stan1293", [English.PolarityParticle.yes, .no].map fun p ↦ (p.form, .en p)),
    ("stan1290", [French.PolarityParticle.oui, .non, .si].map fun p ↦ (p.form, .fr p)),
    ("stan1295", [German.PolarityParticle.ja, .nein, .doch].map fun p ↦ (p.form, .de p))]

def polarityTable : List (String × Polarity) := [("positive", .positive), ("negative", .negative)]

/-- A particle response to an assertion: the polarities of the antecedent and of the response,
the particle, and the judgment. -/
structure Row where
  response : Response
  particle : Particle
  judgment : Judgment
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let table ← List.lookup ex.language particleTable
  let antecedent ← ex.parse? "antecedent" polarityTable
  let polarity ← ex.parse? "response" polarityTable
  let particle ← ex.parse? "particle" table
  pure ⟨⟨.assertion, antecedent, polarity⟩, particle, ex.judgment⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Every example is judged acceptable exactly when its particle is usable in its response,
whose relative feature is the relative polarity of the response to its antecedent
(`relativePresup_smul_iff`). -/
theorem judgment_iff_usable :
    ∀ r ∈ rows, (r.judgment = .acceptable ↔
      r.particle.Usable r.response.relative r.response.polarity) := by
  decide

end RoelofsenFarkas2015
