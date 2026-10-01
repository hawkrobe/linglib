module

public import Linglib.Semantics.Genericity.MeaningPreservation
public import Linglib.Data.Examples.Dayal2004
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.German.Determiners
public import Linglib.Fragments.Romance.Italian.Determiners
public import Linglib.Fragments.Mandarin.Determiners

/-!
# Dayal (2004): Number marking and (in)definiteness in kind terms

[dayal-2004] argues that bare nominals are kind terms or definites, never genuine indefinites, and
that number morphology decides how a kind term is marked for definiteness. Two of its claims are
about the covert type shifts of [chierchia-1998]. First, Revised Meaning Preservation, (39c),
ranks ι with ∩ above ∃, where Chierchia ranked ∩ alone on top. Wherever ι is unblocked, as in a
language without articles, a bare nominal is then a kind or a definite and never shifts by ∃
(`kind_and_definite`), even where ∩ is undefined, as for Hindi *is mashiin ke TukRe* 'parts of
this machine', (45) (`definite_not_indefinite`). Chierchia's ranking instead lets kind formation
pre-empt the definite readings that Hindi, Russian and Chinese bare nominals have, (17) and (18)
(`chierchia_not_definite`). With ι and ι^x blocked, as by English *the*, the two rankings agree
(`english_chierchia_iff_dayal`), and ∃ applies exactly where ∩ is undefined: to *parts of this
machine* but not to *spots on the floor*, (43) and (44), and so, p. 443 predicts, to a bare
singular in a language with a definite but no indefinite article (`exists_iff_not_down`). An
English bare singular has no shift at all, (88a) (`english_bare_singular`). Second, ∩ is undefined
for a singular count noun, whose kind term is instead formed by ι over the taxonomic domain,
(77d) (`kindShift`).

Section 4 places ι above ∩ on a scale of definiteness: a language's definite determiner
lexicalizes an upper part of the scale, ι alone or ι and ∩, and the Blocking Principle applies to
its canonical meaning ι and may or may not apply to ∩ (`Lexicalization`). The principles admit
exactly four types of language (`Lexicalization.classification`): no definite article (Hindi,
Russian, Chinese), ι alone lexicalized (English), ι and ∩ lexicalized and blocked (Italian), and
ι and ∩ lexicalized with only ι blocked (German, whose plural and mass kinds are optionally
definite). They rule out two of the impossible languages of Section 5
(`Lexicalization.not_englishInReverse`, `Lexicalization.not_germanInReverse`), and they predict the
kind-term judgments of (6a), (14) to (16), (46), (78), (86) and (87a) row by row (`rows_agree`).

## Implementation notes

* Availability and the two rankings are the theory layer's
  (`Semantics/Genericity/MeaningPreservation.lean`). Whether ∩ is defined is a hypothesis, since it
  fails for plural properties anchored to particular entities, fn. 1.
* The substrate's `Determiner.Inventory.Blocks` ignores the domain clause of the Blocking
  Principle, (39a): English *a* takes only singulars and so leaves ∃ open to a bare plural, but
  `Blocks .exists` holds of the English inventory outright. The bare-plural theorems therefore take
  the blocking of ∃ as a hypothesis, and the English fragment is read only for *the* and for the
  bare singular.
* Which side of the cut-off each sampled language falls on is the paper's analysis
  (`lexicalizationOf`); that ι is lexicalized exactly where the fragment has a definite article is
  checked (`iota_mem_lexicalized_iff`).
* A mass noun is number-neutral, fn. 25, and a Chinese noun has general number.

## TODO

* Sections 2.2 and 2.3: number morphology and the instantiation set, (28) and (29), and the
  sub-group readings bare plurals have and bare singulars lack, which rule out the third
  impossible language of Section 5, Hindi-in-reverse.
* Sections 3.2 and 3.3: the taxonomic domain, with the sub-kind hierarchy and the sum lattice of
  taxonomic entities kept apart, fn. 32, and the atomicity of singular kinds.
* Section 4.2 on Romance plural definites in the nuclear scope, (83) to (85), and Section 4.4 on
  bare singulars beside definite ones in Hebrew, Hungarian and Brazilian Portuguese.

## References

* [dayal-2004]
* [chierchia-1998]
-/

@[expose] public section

namespace Dayal2004

open Genericity Genericity.MeaningPreservation Determiner

/-! ### Revised Meaning Preservation (Section 2.5) -/

variable {ds : Inventory} {down : Prop}

/-- Wherever ι is unblocked, as in a language without articles, a bare nominal for which ∩ is
defined is a kind or a definite, ∩ and ι both applying, and never an indefinite, (39c). -/
theorem kind_and_definite (hι : ¬ ds.Blocks .iota) (hdown : down) :
    MaximalFor (ds.Available down) dayal .down ∧ MaximalFor (ds.Available down) dayal .iota ∧
      ¬ MaximalFor (ds.Available down) dayal .exists := by
  simp [hι, hdown]

/-- Under Chierchia's ranking kind formation pre-empts the definite, so a bare nominal for which ∩
is defined could not be a definite, against (17) and (18), where Hindi, Russian and Chinese bare
nominals are kinds and definites alike. -/
theorem chierchia_not_definite (hdown : down) :
    ¬ MaximalFor (ds.Available down) chierchia .iota := by
  simp [hdown]

/-- Where ∩ is undefined, as for *is mashiin ke TukRe* 'parts of this machine', ι still outranks
∃ under Dayal's ranking, so the Hindi bare plural is a non-familiar definite with no wide-scope
existential reading, (45); Chierchia's ranking would let ∃ apply beside ι. -/
theorem definite_not_indefinite (hι : ¬ ds.Blocks .iota) (hex : ¬ ds.Blocks .exists)
    (hdown : ¬ down) :
    MaximalFor (ds.Available down) dayal .iota ∧ ¬ MaximalFor (ds.Available down) dayal .exists ∧
      MaximalFor (ds.Available down) chierchia .exists := by
  simp [hι, hex, hdown]

/-- English *the* blocks ι and, being used anaphorically, ι^x, so the two rankings choose alike for
English bare nominals and (43) and (44) do not decide between them. -/
theorem english_chierchia_iff_dayal (down : Prop) (τ : CovertShift) :
    MaximalFor (English.Determiners.inventory.Available down) chierchia τ ↔
      MaximalFor (English.Determiners.inventory.Available down) dayal τ :=
  maximalFor_chierchia_iff_dayal (by decide) (by decide)

/-- With ι and ι^x blocked and ∃ open, ∃ applies exactly where ∩ is undefined. So an English bare
plural like *parts of this machine* shifts by ∃ and interacts in scope with negation, (43), while
*spots on the floor* takes only the narrow scope of DKP, (44); and a bare singular shifts by ∃ in
a language with a definite but no indefinite article, as p. 443 predicts, which Hebrew's (90) and
(91) support and Doron's (94) contradicts. -/
theorem exists_iff_not_down (hι : ds.Blocks .iota) (hx : ds.Blocks .iotaAnaphoric)
    (hex : ¬ ds.Blocks .exists) :
    MaximalFor (ds.Available down) dayal .exists ↔ ¬ down := by
  simp [hι, hx, hex]

/-- An English bare singular has no shift, (88a), since ∩ is undefined for it, *the* blocks ι and
ι^x, and *a* blocks ∃. -/
theorem english_bare_singular :
    ∀ τ, ¬ MaximalFor (English.Determiners.inventory.Available (DownDefined .count .singular))
      dayal τ := by
  decide

/-! ### Singular kinds (Section 3.4) -/

/-- The kind term of a nominal is formed by ∩ where ∩ is defined, and otherwise, for a singular
count noun, by ι over the taxonomic domain, which picks out the unique sub-kind, (77d). -/
def kindShift (nt : MassCount) (num : Number) : CovertShift :=
  if DownDefined nt num then .down else .iota

@[simp] theorem kindShift_singular : kindShift .count .singular = .iota := rfl

@[simp] theorem kindShift_mass (num : Number) : kindShift .mass num = .down := by
  simp [kindShift, DownDefined]

@[simp] theorem kindShift_plural (nt : MassCount) : kindShift nt .plural = .down := by
  simp [kindShift, DownDefined]

theorem kindShift_eq_down_or_iota (nt : MassCount) (num : Number) :
    kindShift nt num = .down ∨ kindShift nt num = .iota := by
  unfold kindShift; split <;> simp

/-! ### The scale of definiteness (Section 4) -/

/-- A lexicalization records the shifts a language's definite determiner encodes and the shifts
the Blocking Principle keeps from applying covertly. On the scale of definiteness ι is above ∩, so
the determiner encodes ι and possibly ∩ but never ∩ alone, p. 437, and Blocking applies to the
canonical meaning ι wherever it is lexicalized and possibly to the non-canonical ∩, p. 442. -/
@[ext] structure Lexicalization where
  /-- The shifts the definite determiner lexicalizes. -/
  lexicalized : Finset CovertShift
  /-- The shifts the Blocking Principle bars from applying covertly. -/
  blocked : Finset CovertShift
  lexicalized_subset : lexicalized ⊆ {.down, .iota}
  iota_mem_of_down_mem : .down ∈ lexicalized → .iota ∈ lexicalized
  blocked_subset : blocked ⊆ lexicalized
  iota_mem_blocked : .iota ∈ lexicalized → .iota ∈ blocked

namespace Lexicalization

/-- The lexicalization of a language without a definite determiner, as Hindi, Russian and
Chinese. -/
def articleless : Lexicalization := ⟨∅, ∅, by decide, by decide, by decide, by decide⟩

/-- The lexicalization of English, whose *the* lexicalizes ι alone. -/
def english : Lexicalization := ⟨{.iota}, {.iota}, by decide, by decide, by decide, by decide⟩

/-- The lexicalization of Italian and the Romance languages, whose definite determiner lexicalizes
and blocks ι and ∩, p. 438. -/
def romance : Lexicalization :=
  ⟨{.down, .iota}, {.down, .iota}, by decide, by decide, by decide, by decide⟩

/-- The lexicalization of German, whose definite determiner lexicalizes ι and ∩ but blocks only
the canonical ι, p. 442. -/
def german : Lexicalization :=
  ⟨{.down, .iota}, {.iota}, by decide, by decide, by decide, by decide⟩

/-- The principles admit exactly the four attested types. -/
theorem classification (l : Lexicalization) :
    l = articleless ∨ l = english ∨ l = romance ∨ l = german := by
  obtain ⟨L, B, h₁, h₂, h₃, h₄⟩ := l
  have key : ∀ L ∈ ({.down, .iota} : Finset CovertShift).powerset, ∀ B ∈ L.powerset,
      (.down ∈ L → .iota ∈ L) → (.iota ∈ L → .iota ∈ B) →
        (L = ∅ ∧ B = ∅) ∨ (L = {.iota} ∧ B = {.iota}) ∨
          (L = {.down, .iota} ∧ B = {.down, .iota}) ∨ (L = {.down, .iota} ∧ B = {.iota}) := by
    decide
  simpa [Lexicalization.ext_iff, articleless, english, romance, german] using
    key L (Finset.mem_powerset.2 h₁) B (Finset.mem_powerset.2 h₃) h₂ h₄

variable (l : Lexicalization) {nt : MassCount} {num : Number}

/-- The kind term of a nominal can take the definite determiner when its shift is lexicalized. -/
def DefiniteKind (nt : MassCount) (num : Number) : Prop := kindShift nt num ∈ l.lexicalized

/-- The kind term of a nominal can be bare when its shift is not blocked. -/
def BareKind (nt : MassCount) (num : Number) : Prop := kindShift nt num ∉ l.blocked

instance : Decidable (l.DefiniteKind nt num) := by unfold DefiniteKind; infer_instance

instance : Decidable (l.BareKind nt num) := by unfold BareKind; infer_instance

/-- Every kind term has a form, since a shift the Blocking Principle bars is lexicalized. -/
theorem bareKind_or_definiteKind : l.BareKind nt num ∨ l.DefiniteKind nt num :=
  (em _).imp_right fun h ↦ l.blocked_subset (not_not.1 h)

/-- Singular kind terms are never optionally definite, (87), since the canonical ι is blocked
wherever it is lexicalized. -/
theorem bareKind_singular_iff : l.BareKind .count .singular ↔ ¬ l.DefiniteKind .count .singular :=
  ⟨fun h h' ↦ h (l.iota_mem_blocked h'), fun h h' ↦ h (l.blocked_subset h')⟩

/-- A language can have bare singular kind terms only if it allows plural and mass kind terms to
be bare, p. 422. -/
theorem bareKind_of_bareKind_singular (h : l.BareKind .count .singular) : l.BareKind nt num := by
  rcases kindShift_eq_down_or_iota nt num with hk | hk <;> rw [BareKind, hk]
  · exact fun hd ↦ h (l.iota_mem_blocked (l.iota_mem_of_down_mem (l.blocked_subset hd)))
  · exact h

/-- English-in-reverse, p. 447, is impossible: a language forming plural kind terms with the
definite determiner while allowing singular kind terms to be bare, since ∩ is lexicalized only
with ι. -/
theorem not_englishInReverse :
    ¬ (l.DefiniteKind .count .plural ∧ l.BareKind .count .singular) := fun ⟨h, h'⟩ ↦
  h' (l.iota_mem_blocked (l.iota_mem_of_down_mem (by simpa [DefiniteKind] using h)))

/-- German-in-reverse, p. 448, is impossible: a language requiring the definite determiner on
plural and mass kind terms but leaving it optional on singular ones, since Blocking cannot spare
the canonical ι. -/
theorem not_germanInReverse :
    ¬ (¬ l.BareKind .count .plural ∧ ¬ l.BareKind .mass .general ∧
      l.BareKind .count .singular ∧ l.DefiniteKind .count .singular) :=
  fun ⟨_, _, h, h'⟩ ↦ l.bareKind_singular_iff.1 h h'

end Lexicalization

/-- The paper's analysis gives Hindi, Russian and Mandarin no definite determiner, English *the*
ι, Italian *il* ι and ∩, p. 438, and German *der* ι and ∩ with Blocking enforced for ι alone,
p. 442; a language is named by its Glottocode. -/
def lexicalizationOf : Glottocode → Option Lexicalization
  | "hind1269" | "russ1263" | "mand1415" => some .articleless
  | "stan1293" => some .english
  | "ital1282" => some .romance
  | "stan1295" => some .german
  | _ => none

open Lexicalization in
/-- ι is lexicalized exactly in the sampled languages whose fragment has a definite article. -/
theorem iota_mem_lexicalized_iff :
    (.iota ∈ english.lexicalized ↔ English.Determiners.inventory.Blocks .iota) ∧
      (.iota ∈ romance.lexicalized ↔ Italian.Determiners.inventory.Blocks .iota) ∧
      (.iota ∈ german.lexicalized ↔ German.Determiners.inventory.Blocks .iota) ∧
      (.iota ∈ articleless.lexicalized ↔ Mandarin.Determiners.inventory.Blocks .iota) := by
  decide

/-! ### The data -/

/-- A kind term is bare or carries the definite determiner. -/
inductive Form
  | bare
  | definite
  deriving DecidableEq

/-- A kind term of countability `nt` and number `num` can take the form `f` under `l`. -/
def Lexicalization.Licit (l : Lexicalization) (nt : MassCount) (num : Number) : Form → Prop
  | .bare => l.BareKind nt num
  | .definite => l.DefiniteKind nt num

instance (l : Lexicalization) (nt : MassCount) (num : Number) :
    DecidablePred (l.Licit nt num) := fun f ↦ by cases f <;> unfold Lexicalization.Licit <;>
  infer_instance

/-- A row records the language's lexicalization, the countability and number of the noun, the
form of its kind term, and the judgment. -/
structure Row where
  lexicalization : Lexicalization
  nt : MassCount
  num : Number
  form : Form
  judgment : Judgment

/-- A row from a datum's language and features. -/
def Row.ofDatum (d : Datum) : Option Row := do
  let l ← lexicalizationOf d.language
  let (nt, num) ← match d.feature? "number" with
    | some "singular" => some (MassCount.count, Number.singular)
    | some "plural" => some (.count, .plural)
    | some "general" => some (.count, .general)
    | some "mass" => some (.mass, .general)
    | _ => none
  let f ← match d.feature? "form" with
    | some "bare" => some Form.bare
    | some "definite" => some .definite
    | _ => none
  some ⟨l, nt, num, f, d.judgment⟩

/-- The kind terms of (6a), (14) to (16), (46), (78), (86) and (87a). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem ofDatum_isSome : ∀ d ∈ Examples.all, (Row.ofDatum d).isSome := by
  decide

/-- Each kind term is judged acceptable exactly where its language's lexicalization licenses its
form. -/
theorem rows_agree :
    ∀ r ∈ rows, (r.judgment = .acceptable ↔ r.lexicalization.Licit r.nt r.num r.form) := by
  decide

end Dayal2004
