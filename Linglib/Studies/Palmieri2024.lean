import Linglib.Syntax.Reciprocal
import Linglib.Studies.Siloni2012
import Linglib.Studies.Winter2018
import Linglib.Fragments.Romance.BrazilianPortuguese.Reciprocals
import Linglib.Fragments.Romance.Catalan.Reciprocals
import Linglib.Fragments.Romance.Italian.Reciprocals
import Linglib.Fragments.Romance.Spanish.Reciprocals
import Linglib.Fragments.Swahili.Reciprocals

/-!
# Palmieri (2024): Lexical and Grammatical Reciprocity

This file formalizes the second chapter of [palmieri-2024], on lexical reciprocity in Romance.
Against the language-level parameter of [siloni-2012], on which Romance forms its reciprocals
in the syntax, verbs fall into three classes by the entries they carry: reciprocal
intransitives with a lexical reciprocal entry only, plain transitives with a transitive entry
only, and verbs like 'hug' with both, whose reciprocal reading requires *se* in most
environments but emerges without it in language-specific ones, Brazilian Portuguese finite
clauses, analytic causatives everywhere, and Spanish and Catalan absolute participials
(`VerbClass.formations`, `SeOmissible`). The columns of Table 2.1 follow from the entries: a
class combines with *se* iff it has a transitive entry and expresses reciprocity by itself
iff it has a lexical one (`table21`, `romance_not_monolithic`). The readings follow too: with
*se* the transitive entry contributes the grammatical reciprocal and reflexive readings and
the lexical entry its pseudo-reciprocal reading, so a class-3 *se*-clause is three-ways
ambiguous, and without *se* only the lexical entry contributes, so the grammatical readings
disappear and the pseudo-reciprocal reading survives exactly for the classes with a lexical
entry (`grammatical_needs_se`, `pseudo_without_se_iff`). A Romance lexical reciprocal is a
verb with some construction in which a reciprocal interpretation emerges without *se*, the
chapter's definition (44), which is having a lexical entry, in every language
(`lexicalReciprocalIn_iff`). Grammatical reciprocity is plain in the sense of [winter-2018]
for any relation, *x and y kissed each other* being *x kissed y and y kissed x* (50)
(`eachOther_plainReciprocity`), whereas the collective predicate of a lexical entry is not so
constrained, 'divorce' and 'kiss' failing one direction each (53), (54). The reciprocal
'with'-construction tracks the lexical entry, the generalization of [kemmer-1993], including
non-symmetric members and the *si*-retaining Italian cases that refine the French-based
restriction of [siloni-2012] (`withConstruction_iff_lexical`).

## Implementation notes

The entries are primitive and the class tables derived. The per-language inventories of
lexical reciprocals come from the Romance Fragments, and one theorem from the fourth
chapter's Swahili data records that lexical reciprocity need not be derivational. The Swahili
chapters and the questionnaires are not otherwise formalized.

## References

* [palmieri-2024]
* [siloni-2012]
* [winter-2018]
* [kemmer-1993]
-/

namespace Palmieri2024

open Reciprocal

/-! ### The verb classes and their entries (Table 2.1) -/

/-- The three classes of Romance verbs: 'chat', with no transitive entry (31); 'describe',
unambiguously transitive (32); and 'hug', transitive with a lexical reciprocal entry
besides (34), (38), (40), (42). -/
inductive VerbClass where
  | reciprocalIntransitive
  | plainTransitive
  | reciprocalTransitive
  deriving DecidableEq

/-- The entries a class carries, the two-entry proposal: a lexical reciprocal entry, a
transitive entry fed by the grammatical *se* strategy, or both. -/
def VerbClass.formations : VerbClass → List Formation
  | .reciprocalIntransitive => [.lexical]
  | .plainTransitive => [.syntactic]
  | .reciprocalTransitive => [.lexical, .syntactic]

/-- The first column of Table 2.1: a class combines with *se* iff it has a transitive
entry. -/
def VerbClass.CombinesWithSe (c : VerbClass) : Prop := Formation.syntactic ∈ c.formations

/-- The second column of Table 2.1: a class expresses reciprocity by itself iff it has a
lexical entry. -/
def VerbClass.ReciprocityByItself (c : VerbClass) : Prop := Formation.lexical ∈ c.formations

instance : DecidablePred VerbClass.CombinesWithSe :=
  λ c => inferInstanceAs (Decidable (Formation.syntactic ∈ c.formations))

instance : DecidablePred VerbClass.ReciprocityByItself :=
  λ c => inferInstanceAs (Decidable (Formation.lexical ∈ c.formations))

/-- Table 2.1 as printed: the intransitives express reciprocity by themselves and reject
*se*, the plain transitives the reverse, and the third class both. -/
theorem table21 :
    (¬ VerbClass.reciprocalIntransitive.CombinesWithSe ∧
        VerbClass.reciprocalIntransitive.ReciprocityByItself) ∧
      (VerbClass.plainTransitive.CombinesWithSe ∧
        ¬ VerbClass.plainTransitive.ReciprocityByItself) ∧
      (VerbClass.reciprocalTransitive.CombinesWithSe ∧
        VerbClass.reciprocalTransitive.ReciprocityByItself) := by
  decide

/-- The divergence from [siloni-2012]: Italian carries lexical reciprocal entries, class 3
*abbracciare* 'hug' (40), though the language-level parameter classifies it as syntax-set. -/
theorem romance_not_monolithic :
    VerbClass.reciprocalTransitive.ReciprocityByItself ∧
      Siloni2012.italian.formation = Formation.syntactic :=
  ⟨by decide, rfl⟩

/-- The witness grounded in the Italian Fragment: *abbracciare* carries a lexical reciprocal
entry alongside its homophonous transitive alternate. -/
theorem abbracciare_grounds_divergence :
    "abbracciare" ∈ Italian.Reciprocals.lexicalReciprocals.map Verb.form := by
  decide

/-! ### The *se*-less environments (Table 2.2) -/

/-- The four Romance languages of the chapter. -/
inductive Language where
  | brazilianPortuguese
  | italian
  | spanish
  | catalan
  deriving DecidableEq

/-- The constructions in which a class-3 verb may express reciprocity without *se* (§3):
finite clauses (34), analytic causatives (38), (40), and absolute participials (42). -/
inductive Environment where
  | finiteClause
  | analyticCausative
  | absoluteParticipial
  deriving DecidableEq

/-- Table 2.2: whether the language lets a class-3 verb receive a reciprocal interpretation
without *se* in the environment. -/
def SeOmissible : Language → Environment → Prop
  | .brazilianPortuguese, .absoluteParticipial => False
  | .brazilianPortuguese, _ => True
  | .italian, .analyticCausative => True
  | .italian, _ => False
  | .spanish, .finiteClause => False
  | .spanish, _ => True
  | .catalan, .finiteClause => False
  | .catalan, _ => True

instance : ∀ (l : Language) (e : Environment), Decidable (SeOmissible l e) := by
  intro l e; cases l <;> cases e <;> unfold SeOmissible <;> infer_instance

/-- Analytic causatives are the pan-Romance diagnostic: every language omits *se* there. -/
theorem every_language_diagnosable (l : Language) : SeOmissible l .analyticCausative := by
  cases l <;> decide

/-- Per-language inventories of lexical reciprocals, from the Fragments. -/
def inventory : Language → List Verb
  | .brazilianPortuguese => BrazilianPortuguese.Reciprocals.lexicalReciprocals
  | .italian => Italian.Reciprocals.lexicalReciprocals
  | .spanish => Spanish.Reciprocals.lexicalReciprocals
  | .catalan => Catalan.Reciprocals.lexicalReciprocals

/-! ### Readings with and without *se* (§4.3) -/

/-- The readings of a plural-subject clause: the pseudo-reciprocal reading of a lexical entry,
a single collective event, and the grammatical reciprocal and reflexive readings of a
transitive entry under *se*. -/
inductive SeReading where
  | pseudoReciprocal
  | grammaticalReciprocal
  | grammaticalReflexive
  deriving DecidableEq

/-- The readings an entry contributes under *se*: the lexical entry its pseudo-reciprocal
reading, the transitive entry the two grammatical readings (55), (56a), (57a). -/
def Formation.readingsWithSe : Formation → List SeReading
  | .lexical => [.pseudoReciprocal]
  | .syntactic => [.grammaticalReciprocal, .grammaticalReflexive]

/-- The readings an entry contributes without *se*: only the lexical entry contributes
(56b), (57b). -/
def Formation.readingsWithoutSe : Formation → List SeReading
  | .lexical => [.pseudoReciprocal]
  | .syntactic => []

/-- The readings of a *se*-clause of the class, when the class combines with *se* at all. -/
def VerbClass.readingsWithSe (c : VerbClass) : List SeReading :=
  if c.CombinesWithSe then c.formations.flatMap Formation.readingsWithSe else []

/-- The readings of a *se*-less clause of the class. -/
def VerbClass.readingsWithoutSe (c : VerbClass) : List SeReading :=
  c.formations.flatMap Formation.readingsWithoutSe

/-- A class-3 *se*-clause is three-ways ambiguous (56a), (57a). -/
theorem class3_three_ways :
    VerbClass.reciprocalTransitive.readingsWithSe =
      [.pseudoReciprocal, .grammaticalReciprocal, .grammaticalReflexive] := by
  decide

/-- Without *se* no grammatical reading survives, for any class: the reflexive and the
accumulated-events reciprocal readings need the grammatical strategy. -/
theorem grammatical_needs_se (c : VerbClass) :
    SeReading.grammaticalReciprocal ∉ c.readingsWithoutSe ∧
      SeReading.grammaticalReflexive ∉ c.readingsWithoutSe := by
  cases c <;> decide

/-- The pseudo-reciprocal reading survives without *se* exactly for the classes with a lexical
entry. -/
theorem pseudo_without_se_iff (c : VerbClass) :
    SeReading.pseudoReciprocal ∈ c.readingsWithoutSe ↔ c.ReciprocityByItself := by
  cases c <;> decide

/-- Definition (44): a class is a lexical reciprocal in a language iff some construction of
that language lets a reciprocal interpretation emerge without *se*. -/
def LexicalReciprocalIn (l : Language) (c : VerbClass) : Prop :=
  ∃ e, SeOmissible l e ∧ SeReading.pseudoReciprocal ∈ c.readingsWithoutSe

/-- Lexical reciprocity in the sense of (44) is having a lexical entry, in every language. -/
theorem lexicalReciprocalIn_iff (l : Language) (c : VerbClass) :
    LexicalReciprocalIn l c ↔ c.ReciprocityByItself :=
  ⟨λ ⟨_, _, h⟩ => (pseudo_without_se_iff c).1 h,
    λ h => ⟨.analyticCausative, every_language_diagnosable l, (pseudo_without_se_iff c).2 h⟩⟩

/-! ### Pseudo-reciprocity against plain reciprocity (§4.3) -/

/-- Grammatical reciprocity over a set of participants, *each other*: the relation holds
between every two distinct members. -/
def eachOther {A : Type*} (R : A → A → Prop) : Finset A → Prop :=
  λ s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → R x y

/-- (50): grammatical reciprocity is plain in the sense of [winter-2018] for every relation,
symmetric or not: *x and y kissed each other* iff *x kissed y and y kissed x*. -/
theorem eachOther_plainReciprocity {A : Type*} [DecidableEq A] (R : A → A → Prop) :
    Winter2018.PlainReciprocity (eachOther R) R := by
  intro x y hxy
  simp only [eachOther, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨⟨-, h₁⟩, h₂, -⟩
    exact ⟨h₁ hxy, h₂ hxy.symm⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨λ h => (h rfl).elim, λ _ => h₁⟩, λ _ => h₂, λ h => (h rfl).elim⟩

/-- A lexical entry's collective predicate is not so constrained: for any relation some
collective predicate fails plain reciprocity for it, the room in which 'divorce' fails the
collective-to-unidirectional direction (53) and 'kiss' the converse (54). -/
theorem exists_collective_not_plain (R : Bool → Bool → Prop) :
    ∃ P : Finset Bool → Prop, ¬ Winter2018.PlainReciprocity P R :=
  ⟨λ _ => ¬ (R true false ∧ R false true), λ h => iff_not_self (h true false (by decide)).symm⟩

/-! ### The reciprocal 'with'-construction (§4.4) -/

/-- Whether the class allows the reciprocal 'with'-construction, the observation of §4.4:
both classes with a lexical entry do, including non-symmetric members, *consultarsi con*,
*lasciarsi con* (59), and the attested *baciarsi con*, *abbracciarsi con* (60), and the
plain transitives do not, *ringraziarsi con* (61). Italian retains *si* in the construction,
unlike French. -/
def VerbClass.AllowsWithConstruction : VerbClass → Prop
  | .plainTransitive => False
  | _ => True

/-- The generalization of [kemmer-1993] over the class system: the 'with'-construction is
available exactly where a lexical entry is. -/
theorem withConstruction_iff_lexical (c : VerbClass) :
    c.AllowsWithConstruction ↔ c.ReciprocityByItself := by
  cases c <;> simp [VerbClass.AllowsWithConstruction, VerbClass.ReciprocityByItself,
    VerbClass.formations]

/-! ### Swahili (fourth chapter) -/

/-- Swahili lexical reciprocals may lack a binary base altogether: *jibizana* 'discuss' is in
the reciprocal inventory but in no derivational pair, so lexical reciprocity is not always
derivational, the Bantu analogue of the Romance intransitive class. -/
theorem jibizana_no_binary_base :
    "jibizana" ∈ Swahili.Reciprocals.lexicalReciprocals.map Verb.form ∧
      ∀ p ∈ Swahili.Reciprocals.derivedFrom, p.1.form ≠ "jibizana" := by
  decide

end Palmieri2024
