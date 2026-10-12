module

public import Linglib.Data.Examples.ArregiPietraszko2021
public import Linglib.Data.Examples.HarizanovGribanova2019
public import Linglib.Data.Forms.ArregiPietraszko2021
public import Linglib.Fragments.Ndebele.Phonology
public import Linglib.Phonology.Hiatus
public import Linglib.Studies.HarizanovGribanova2019
public import Linglib.Studies.Pollock1989

/-!
# Arregi and Pietraszko (2021): The ups and downs of head displacement

Arregi and Pietraszko replace head raising and lowering by one syntactic operation, Generalized
Head Movement, in which a head shares its M-value, the morphological features that Vocabulary
Insertion spells out, with the head of its complement. The heads of a clause thus form a head
chain around one complex head, pronounced in the chain's highest strong position, or in its
highest position if none is strong. A chain that ends in a strong verb splits when a specifier
intervenes or the verb phrase is elided or fronted, and the verb's terminal, an orphan in the
half without the verb, is exponed as *do*.

## Main statements

* `HeadChain.terminals_ofHeads`, `HeadChain.isLeftComb_mvalue_ofHeads`: the Mirror Principle,
  the terminals of a complex head ordered as its heads are, each attached outside the complex
  head of the heads below it.
* `doSupport_iff`: do-support arises exactly where the chain of a strong verb splits, whether
  the complex head is otherwise pronounced low or high.
* `directionality_no_correlation`: under inversion English and Monnese both have do-support,
  though elsewhere the English verb is pronounced low and the Monnese verb high.
* `mirror_class9`, `amalgamation_class9`: regular vowel coalescence derives the Ndebele class 9
  relative prefix from the Mirror-obeying complex head and not from another bracketing of the
  same terminals, such as amalgamation builds when a head Raises into one that Lowers.

## Implementation notes

* A `Context` holds what head displacement sees of a clause: the heads related to the verb,
  whether a pronounced specifier intervenes, and what becomes of the verb phrase. A negative
  imperative, where Σ keeps C out of the verb's chain, is thereby the context of a declarative.
* Split-by-Deletion applies in every language, the possibility the paper raises for its typology
  of splitting; Split-by-Intervention is a setting.
* A language's settings record what the paper's data settle, so the form of a verb with an orphan
  T is absent where no do-support or fronting datum shows it.
* An M-value is an element of the free magma over the terminals, each product listing the lower
  constituent first. The operation leaves linear order open, and only the Ndebele prefix is
  linearized.

## TODO

* Negative Merger, the postsyntactic rule that adds contracted negation outside the complex head.

## References

* [arregi-pietraszko-2021]
* [baker-1985]
* [pollock-1989]
* [harizanov-gribanova-2019]
-/

@[expose] public section

namespace ArregiPietraszko2021

open Phonology FreeMagma

/-! ### Head chains -/

/-- The syntactic terminals of the paper's derivations are the lexical verb, an auxiliary, Σ, T,
C, and the D and linker heads above an Ndebele relative clause. -/
inductive Head
  | V | Aux | sigma | T | C | D | Lnk
  deriving DecidableEq, Repr

/-- A head chain is a sequence of syntactic terminals, lowest first, that share one M-value, a
complex head over morphological terminals. -/
structure HeadChain where
  positions : List Head
  mvalue : FreeMagma Head

namespace HeadChain

/-- The morphological terminals of the M-value, lowest first. -/
def terminals (c : HeadChain) : List Head := (FreeMagma.lift FreeMonoid.of c.mvalue).toList

/-- Generalized Head Movement, GenHM, relates a head to the chain of its complement's head. The
head joins the chain, and its morphological terminal attaches outside the shared M-value. -/
def extend (x : Head) (c : HeadChain) : HeadChain := ⟨c.positions ++ [x], c.mvalue * of x⟩

/-- The chain that cyclic GenHM builds from `bottom` up through the heads `above`. -/
def ofHeads (bottom : Head) (above : List Head) : HeadChain :=
  ⟨bottom :: above, above.foldl (· * of ·) (of bottom)⟩

theorem extend_ofHeads (bottom x : Head) (above : List Head) :
    (ofHeads bottom above).extend x = ofHeads bottom (above ++ [x]) := by
  simp [extend, ofHeads]

/-- By the **Mirror Principle**, the terminals of a complex head are ordered as its heads are. -/
theorem terminals_ofHeads (bottom : Head) (above : List Head) :
    (ofHeads bottom above).terminals = bottom :: above := by
  simp [terminals, ofHeads, toList_lift_foldl_mul_of]

/-- GenHM derives the Mirror Principle: each terminal of a complex head attaches outside the
complex head of the heads below it. -/
theorem isLeftComb_mvalue_ofHeads (bottom : Head) (above : List Head) :
    (ofHeads bottom above).mvalue.IsLeftComb :=
  (isLeftComb_foldl_mul_of _ _).mpr (isLeftComb_of _)

/-- Orphan Assignment marks a morphological terminal in a chain that does not contain its
syntactic terminal. -/
def Orphan (c : HeadChain) (x : Head) : Prop := x ∈ c.terminals ∧ x ∉ c.positions

instance (c : HeadChain) (x : Head) : Decidable (c.Orphan x) := inferInstanceAs (Decidable (_ ∧ _))

/-- GenHM creates no orphans. -/
theorem not_orphan_ofHeads (bottom x : Head) (above : List Head) :
    ¬ (ofHeads bottom above).Orphan x := by
  rw [Orphan, terminals_ofHeads]; exact fun h ↦ h.2 h.1

/-- Head Chain Pronunciation delinks every position of a chain but its highest strong one, or
its highest if none is strong. -/
def pronounced (strong : Finset Head) (c : HeadChain) : Option Head :=
  (c.positions.filter (· ∈ strong)).getLast?.or c.positions.getLast?

theorem mem_positions_of_pronounced {strong : Finset Head} {c : HeadChain} {x : Head}
    (h : c.pronounced strong = some x) : x ∈ c.positions := by
  rcases Option.or_eq_some_iff.mp h with h | ⟨-, h⟩
  · exact (List.mem_filter.mp (List.mem_of_getLast? h)).1
  · exact List.mem_of_getLast? h

/-- A chain with no strong position is pronounced in its highest, the effect of upward
displacement. -/
theorem pronounced_of_forall_not_mem {strong : Finset Head} {c : HeadChain}
    (h : ∀ x ∈ c.positions, x ∉ strong) : c.pronounced strong = c.positions.getLast? := by
  have : c.positions.filter (· ∈ strong) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx ↦ by simpa using h x hx
  rw [pronounced, this]; rfl

/-- A chain extended by a strong head is pronounced there, wherever it was pronounced before:
downward displacement feeds upward displacement. -/
theorem pronounced_extend_of_mem {strong : Finset Head} {x : Head} (hx : x ∈ strong)
    (c : HeadChain) : (c.extend x).pronounced strong = some x := by
  simp [pronounced, extend, List.filter_append, hx]

end HeadChain

/-! ### Languages -/

/-- The form of a verbal word. A verb whose T is an orphan is finite where the orphan is ignored,
a pseudo-infinitive where T takes its elsewhere exponent on a root still in its finite allomorph,
an infinitive where T is impoverished of tense and agreement, and bare where T is obliterated. -/
inductive VerbForm
  | finite | pseudoInfinitive | infinitive | bare
  deriving DecidableEq, Repr

/-- The settings of a language. -/
structure Language where
  /-- The strong terminals, the positions that hold the pronunciation of a chain down. -/
  strong : Finset Head := ∅
  /-- Whether a chain splits at a strong verb below an intervening specifier. -/
  splitByIntervention : Bool := false
  /-- Whether sentential negation is an adverbial, not the specifier of ΣP. -/
  adverbialNegation : Bool := false
  /-- The form of a verb whose T is an orphan. -/
  orphanT : Option VerbForm := none

/-- English has strong lexical verbs and Split-by-Intervention, and obliterates an orphan T. -/
def english : Language := { strong := {.V}, splitByIntervention := true, orphanT := some .bare }

/-- French has no strong head. -/
def french : Language := {}

/-- Danish has strong verbs, auxiliaries among them, and a strong C, and no
Split-by-Intervention. -/
def danish : Language := { strong := {.V, .Aux, .C} }

/-- Swedish has the Danish settings and ignores an orphan T. -/
def swedish : Language := { danish with orphanT := some .finite }

/-- Monnese has strong lexical verbs, T and C, and Split-by-Intervention; its negation is an
adverbial, and it impoverishes an orphan T. -/
def monnese : Language :=
  { strong := {.V, .T, .C}, splitByIntervention := true, adverbialNegation := true,
    orphanT := some .infinitive }

/-- Polish has weak verbs and impoverishes an orphan T. -/
def polish : Language := { orphanT := some .infinitive }

/-- Hebrew has weak verbs and impoverishes an orphan T. -/
def hebrew : Language := { orphanT := some .infinitive }

/-- Yiddish has weak verbs and gives an orphan T its elsewhere exponent. -/
def yiddish : Language := { orphanT := some .pseudoInfinitive }

/-- Spanish has no strong head in imperatives. -/
def spanish : Language := {}

/-- The Vallader of Scuol has a strong imperative T. -/
def vallader : Language := { strong := {.T} }

/-- Ndebele has a strong T. -/
def ndebele : Language := { strong := {.T} }

/-- `c.form L` is the form of the word that `c` is pronounced as, finite unless its T is an
orphan. -/
def HeadChain.form (L : Language) (c : HeadChain) : Option VerbForm :=
  if c.Orphan .T then L.orphanT else some .finite

/-! ### Contexts and chain splitting -/

/-- A verb phrase is pronounced in place, elided, or fronted. -/
inductive VPFate
  | inSitu | elided | fronted
  deriving DecidableEq, Repr

/-- A context holds what head displacement sees of a clause. -/
structure Context where
  /-- The heads GenHM relates to the verb, lowest first. -/
  above : List Head
  /-- Whether a pronounced specifier intervenes between the highest of them and the verb. -/
  intervener : Bool := false
  vp : VPFate := .inSitu
  deriving DecidableEq, Repr

namespace Context

/-- T is related to the verb, with no specifier between them. -/
def declarative : Context := { above := [.T] }

/-- Σ stands between T and the verb, and its specifier, negation or verum focus, intervenes. -/
def polarity : Context := { above := [.sigma, .T], intervener := true }

/-- Sentential negation in a language. -/
def negation (L : Language) : Context := if L.adverbialNegation then declarative else polarity

/-- C is related to T and no pronounced specifier intervenes, as in a subject question, whose
Spec,TP holds a lower copy, a subject-initial verb-second clause, and an affirmative
imperative. -/
def toC : Context := { above := [.T, .C] }

/-- C is related to T across the subject in Spec,TP. -/
def inversion : Context := { toC with intervener := true }

end Context

/-- A chain that ends in a strong verb splits at the verb when the language has
Split-by-Intervention and a specifier intervenes, or when the verb is unpronounced under ellipsis
or as the lower copy of a fronted verb phrase. -/
def Splits (L : Language) (cx : Context) (verb : Head) : Prop :=
  verb = .V ∧ .V ∈ L.strong ∧ cx.above ≠ [] ∧
    (L.splitByIntervention ∧ cx.intervener ∨ cx.vp ≠ .inSitu)

instance (L : Language) (cx : Context) (verb : Head) : Decidable (Splits L cx verb) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The head chains of a clause at Spell-Out. -/
structure Chains where
  /-- The chain of the verb's own position. -/
  verb : HeadChain
  /-- The chain of the highest head, whose word carries finite inflection. -/
  finite : HeadChain
  /-- The chain of the verb in a fronted copy of the verb phrase. -/
  fronted : Option HeadChain

/-- `derive L cx verb` holds the chains of a clause. GenHM relates the verb to the heads above
it, a split leaves the verb alone in one half, and a fronted verb phrase carries a copy of the
verb with the whole M-value. -/
def derive (L : Language) (cx : Context) (verb : Head) : Chains :=
  let c := HeadChain.ofHeads verb cx.above
  let alone : HeadChain := ⟨[verb], c.mvalue⟩
  { verb := if Splits L cx verb then alone else c
    finite := if Splits L cx verb then ⟨cx.above, c.mvalue⟩ else c
    fronted := if cx.vp = .fronted then some alone else none }

namespace Chains

/-- The position in which the finite word is pronounced. -/
def finitePosition (L : Language) (d : Chains) : Option Head := d.finite.pronounced L.strong

/-- The finite word contains an orphan verb, exponed as *do*. -/
def DoSupport (d : Chains) : Prop := d.finite.Orphan .V

instance (d : Chains) : Decidable d.DoSupport := inferInstanceAs (Decidable (HeadChain.Orphan ..))

/-- The verb's M-value contains C, which conditions the imperative allomorphs of the verb. -/
def HasC (d : Chains) : Prop := .C ∈ d.verb.terminals

instance (d : Chains) : Decidable d.HasC := inferInstanceAs (Decidable (_ ∈ _))

end Chains

variable {L : Language} {cx : Context} {verb : Head}

theorem splits_of_doSupport (h : (derive L cx verb).DoSupport) : Splits L cx verb := by
  by_contra hs
  simp only [Chains.DoSupport, derive, hs, ↓reduceIte] at h
  exact HeadChain.not_orphan_ofHeads _ _ _ h

/-- Do-support arises exactly where the chain of a strong verb splits. -/
theorem doSupport_iff (h : .V ∉ cx.above) : (derive L cx verb).DoSupport ↔ Splits L cx verb := by
  refine ⟨splits_of_doSupport, fun hs ↦ ?_⟩
  obtain rfl := hs.1
  have ht : (⟨cx.above, (HeadChain.ofHeads .V cx.above).mvalue⟩ : HeadChain).terminals =
      .V :: cx.above := HeadChain.terminals_ofHeads .V cx.above
  simp [Chains.DoSupport, derive, hs, HeadChain.Orphan, ht, h]

/-- No auxiliary takes do-support. -/
theorem not_doSupport_aux : ¬ (derive L cx .Aux).DoSupport :=
  fun h ↦ nomatch (splits_of_doSupport h).1

/-- Under ellipsis and fronting a strong verb takes do-support and a weak verb is stranded. -/
theorem doSupport_iff_strong_of_ne_inSitu (h : .V ∉ cx.above) (hne : cx.above ≠ [])
    (hvp : cx.vp ≠ .inSitu) : (derive L cx .V).DoSupport ↔ .V ∈ L.strong := by
  simp [doSupport_iff h, Splits, hne, hvp]

/-- Below an intervening specifier a verb takes do-support exactly when it is strong and the
language has Split-by-Intervention. -/
theorem doSupport_iff_of_intervener (h : .V ∉ cx.above) (hne : cx.above ≠ [])
    (hvp : cx.vp = .inSitu) (hi : cx.intervener) :
    (derive L cx .V).DoSupport ↔ .V ∈ L.strong ∧ L.splitByIntervention := by
  simp [doSupport_iff h, Splits, hne, hvp, hi]

/-- Below a weak T a verb is pronounced in V when it is strong and in T when it is weak, so the
verbs of English and Danish are low for one reason. -/
theorem finitePosition_declarative (hT : .T ∉ L.strong) :
    (derive L .declarative .V).finitePosition L = some (if .V ∈ L.strong then .V else .T) := by
  by_cases hV : Head.V ∈ L.strong <;>
    simp [Chains.finitePosition, derive, Splits, Context.declarative, HeadChain.pronounced,
      HeadChain.ofHeads, List.filter, hV, hT]

/-- The complex head of a Danish clause is pronounced in V without C and in C with it, never in
T: each step of GenHM is local, and the strong positions are not adjacent. -/
theorem danish_verb_second :
    (derive danish .declarative .V).finitePosition danish = some .V ∧
      (derive danish .inversion .V).finitePosition danish = some .C := by
  decide

/-- Do-support alternates with downward displacement in English and with upward displacement in
Monnese: without an intervener the English verb is pronounced in V and the Monnese verb in T,
and both take do-support under inversion. -/
theorem directionality_no_correlation :
    (derive english .declarative .V).finitePosition english = some .V ∧
      (derive monnese .declarative .V).finitePosition monnese = some .T ∧
      (derive english .inversion .V).DoSupport ∧ (derive monnese .inversion .V).DoSupport := by
  decide

/-- Danish has do-support under ellipsis in a verb-second clause, where its verb is otherwise
pronounced in C, and none under inversion. -/
theorem danish_do_support :
    (derive danish { Context.toC with vp := .elided } .V).DoSupport ∧
      ¬ (derive danish .inversion .V).DoSupport := by
  decide

/-- The paper predicts of Monnese, which has no attested verb phrase ellipsis, that under
ellipsis its verb would take do-support though it is otherwise pronounced in T. -/
theorem monnese_ellipsis :
    (derive monnese { Context.declarative with vp := .elided } .V).DoSupport := by
  decide

/-- Negation blocks the relation of the verb to C in an imperative whether that relation would
displace the verb upward, as in Spanish, or downward, as in Vallader: the affirmative verb has C
in its M-value and is pronounced in C in Spanish and in T in Vallader. -/
theorem imperatives :
    (derive spanish .toC .V).finitePosition spanish = some .C ∧
      (derive vallader .toC .V).finitePosition vallader = some .T ∧
      (∀ L, (derive L .toC .V).HasC ∧ ¬ (derive L .declarative .V).HasC) := by
  refine ⟨by decide, by decide, fun L ↦ ?_⟩
  simp [Chains.HasC, derive, Splits, Context.toC, Context.declarative,
    HeadChain.terminals_ofHeads]

/-! ### The paper's examples -/

/-- The settings of a row's language, by Glottocode. -/
def languages : List (String × Language) :=
  [("stan1293", english), ("stan1290", french), ("dani1285", danish), ("swed1254", swedish),
    ("lomb1257", monnese), ("poli1260", polish), ("hebr1245", hebrew), ("east2295", yiddish),
    ("stan1288", spanish), ("lowe1386", vallader)]

/-- The context each label of the rows names in a language. The elided verb-second clause is
subject-initial, and in the fronting ones the subject follows the finite verb. -/
def contexts (L : Language) : List (String × Context) :=
  [("declarative", .declarative), ("negation", .negation L), ("verum", .polarity),
    ("inversion", .inversion), ("v2", .inversion), ("subjectWh", .toC),
    ("imperativeAff", .toC), ("imperativeNeg", .declarative),
    ("ellipsis", { Context.declarative with vp := .elided }),
    ("ellipsisV2", { Context.toC with vp := .elided }),
    ("fronting", { Context.declarative with vp := .fronted }),
    ("frontingV2", { Context.inversion with vp := .fronted })]

/-- The rows' labels for positions, verb forms and truth values. -/
def headLabels : List (String × Head) := [("V", .V), ("T", .T), ("C", .C)]

@[inherit_doc headLabels]
def formLabels : List (String × VerbForm) :=
  [("finite", .finite), ("pseudoInfinitive", .pseudoInfinitive), ("infinitive", .infinitive),
    ("bare", .bare)]

@[inherit_doc headLabels]
def boolLabels : List (String × Bool) := [("true", true), ("false", false)]

/-- A row that records `key` records under it the value `y`. -/
def Agrees {α : Type*} (r : Datum) (key : String) (table : List (String × α)) (y : Option α) :
    Prop :=
  r.feature? key = none ∨ ∃ x ∈ r.parse? key table, y = some x

instance {α : Type*} [DecidableEq α] (r : Datum) (key : String) (table : List (String × α))
    (y : Option α) : Decidable (Agrees r key table y) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The surface properties a row records are those of the chains. -/
def Chains.Matches (L : Language) (d : Chains) (r : Datum) : Prop :=
  Agrees r "finitePosition" headLabels (d.finitePosition L) ∧
    Agrees r "doSupport" boolLabels (some (decide d.DoSupport)) ∧
    Agrees r "verbForm" formLabels (d.verb.form L) ∧
    Agrees r "imperativeForm" boolLabels (some (decide d.HasC)) ∧
    Agrees r "frontedForm" formLabels (d.fronted.bind (·.form L))

instance (L : Language) (d : Chains) (r : Datum) : Decidable (d.Matches L r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The settings of a row's language and the chains of its clause. -/
def derivation? (r : Datum) : Option (Language × Chains) := do
  let L ← languages.lookup r.language
  let cx ← r.parse? "context" (contexts L)
  let verb ← r.parse? "verbType" [("lexical", Head.V), ("auxiliary", .Aux)]
  pure (L, derive L cx verb)

/-- Every verb placement, do-support, imperative, ellipsis and fronting example of the paper
surfaces as the settings of its language derive. -/
theorem rows_derived :
    ∀ r ∈ Examples.all, r.language ≠ "nort2795" → ∃ p ∈ derivation? r, p.2.Matches p.1 r := by
  decide +kernel

/-! ### Pollock's paradigm -/

/-- The settings of the languages Pollock compares. -/
def ofPollock : Pollock1989.Language → Language
  | .french => french
  | .english => english

/-- In the finite clauses of French and English the finite word is pronounced in T exactly where
Pollock's verb reaches T, and negation brings do-support exactly where his tense affix needs
*do*: a strong verb is a verb below his opaque Agr. -/
theorem pollock_finite (l : Pollock1989.Language) (v : Pollock1989.Verb) :
    let verb : Head := match v with | .lexical => .V | .auxiliary => .Aux
    ((derive (ofPollock l) .declarative verb).finitePosition (ofPollock l) = some .T ↔
        Pollock1989.top ⟨l, true⟩ v = .tense) ∧
      ((derive (ofPollock l) (.negation (ofPollock l)) verb).DoSupport ↔
        Pollock1989.NeedsDo ⟨l, true⟩ v) := by
  cases l <;> cases v <;> decide

/-! ### Ndebele relative prefixes -/

/-- The chain of an Ndebele relative clause holds T, a null C, the augment in D and the linker. -/
def relative : HeadChain := .ofHeads .T [.C, .D, .Lnk]

/-- The relative prefix is pronounced low, in the strong T below the subject, as the example
with an overt subject shows. -/
theorem relative_low :
    relative.pronounced ndebele.strong = some .T ∧ ∀ r ∈ Examples.all,
      Agrees r "relPrefixPosition" headLabels (relative.pronounced ndebele.strong) := by
  decide +kernel

/-- Where two vowels meet, identical vowels merge, /a/ coalesces with a following /i/ into /e/
and with a following /u/ into /o/, and /e/ elides before a vowel. -/
def resolve (j : Hiatus.Juncture) : List Segment :=
  if j.v1 = j.v2 ∨ j.v1 = Ndebele.e then j.elideV1
  else if j.v1 = Ndebele.a ∧ j.v2 = Ndebele.i then j.coalesce Ndebele.e
  else if j.v1 = Ndebele.a ∧ j.v2 = Ndebele.u then j.coalesce Ndebele.o
  else j.input

/-- Two exponents joined, with the hiatus between them resolved if there is one. -/
def join (x y : List Segment) : List Segment :=
  match x.reverse, y with
  | v₁ :: stem, v₂ :: suffix =>
    if h : v₁.IsVowel ∧ v₂.IsVowel then resolve ⟨stem.reverse, v₁, v₂, suffix, h.1, h.2⟩
    else x ++ y
  | _, _ => x ++ y

/-- `spellOut e` spells out a complex head of prefixes cyclically from the exponents `e` of its
terminals, a constituent before the one containing it and the higher constituent before the
lower. -/
def spellOut (e : Head → List Segment) : FreeMagma Head → List Segment
  | .of h => e h
  | .mul x y => join (spellOut e y) (spellOut e x)

/-- The segments the letters of the prefix table write. -/
def letters : List (Char × Segment) :=
  [('a', Ndebele.a), ('e', Ndebele.e), ('i', Ndebele.i), ('o', Ndebele.o), ('u', Ndebele.u),
    ('s', Ndebele.s), ('l', Ndebele.l)]

/-- A string of the prefix table as segments. -/
def transcribe? : List Char → Option (List Segment)
  | [] => some []
  | c :: cs => do pure ((← letters.lookup c) :: (← transcribe? cs))

/-- The exponents a row of the prefix table gives the heads of the relative prefix. -/
def exponents? (f : Data.Forms.Form) : Option (Head → List Segment) := do
  let lnk ← transcribe? (← f.column? "Lnk").toList
  let d ← transcribe? (← f.column? "D").toList
  let t ← transcribe? (← f.column? "T").toList
  pure fun | .Lnk => lnk | .D => d | .T => t | _ => []

/-- Cyclic coalescence over the Mirror-obeying complex head derives the relative prefix of each
class, free of the hiatus its exponents present. -/
theorem relative_prefixes :
    ∀ f ∈ Forms.all, ∃ e ∈ exponents? f,
      some (spellOut e relative.mvalue) = transcribe? f.form.toList ∧
        Hiatus.Free (spellOut e relative.mvalue) ∧
        ¬ Hiatus.Free (relative.terminals.reverse.flatMap e) := by
  decide +kernel

/-- The same terminals in the same order with the opposite bracketing, the linker innermost. -/
def nonMirror : FreeMagma Head := of .T * (of .C * (of .D * of .Lnk))

/-- In class 9 the Mirror-obeying complex head spells out as the attested *e-* and the opposite
bracketing of the same terminals as *i-*. -/
theorem mirror_class9 :
    (FreeMagma.lift FreeMonoid.of nonMirror).toList = relative.terminals ∧
      ∀ f ∈ Forms.all, f.parameterId = "rel_cl9" → ∃ e ∈ exponents? f,
        spellOut e relative.mvalue = [Ndebele.e] ∧ spellOut e nonMirror = [Ndebele.i] := by
  decide +kernel

/-! ### Amalgamation -/

section Amalgamation

open HarizanovGribanova2019

/-- Harizanov and Gribanova's amalgamation builds the complex head of GenHM when each head
Lowers, and another bracketing of the same terminals in the same order when a head Raises into a
head that then Lowers: it allows the Mirror Principle and does not derive it. -/
theorem amalgamation_bracketing (x y z : Head) :
    amalgamateSpine [.single z none, .single y (some .lowering), .single x (some .lowering)] =
        some [⟨z, (HeadChain.ofHeads z [y, x]).mvalue, none⟩] ∧
      amalgamateSpine [.single z none, .single y (some .raising), .single x (some .lowering)] =
        some [⟨z, of z * (of y * of x), none⟩] :=
  ⟨rfl, rfl⟩

/-- With C, D and the linker all Lowering, amalgamation builds the complex head of the Ndebele
relative chain. With D Raising into the linker before the linker Lowers, it builds a complex
head with the same terminals in the same order that spells out the class 9 prefix as *i-*. -/
theorem amalgamation_class9 :
    amalgamateSpine [.single .T none, .single .C (some .lowering), .single .D (some .lowering),
        .single .Lnk (some .lowering)] = some [⟨.T, relative.mvalue, none⟩] ∧
      ∃ a, amalgamateSpine [.single .T none, .single .C (some .lowering),
          .single .D (some .raising), .single .Lnk (some .lowering)] = some [a] ∧
        a.members = relative.terminals ∧ a.complex ≠ relative.mvalue ∧
        ∀ f ∈ Forms.all, f.parameterId = "rel_cl9" → ∃ e ∈ exponents? f,
          spellOut e a.complex = [Ndebele.i] :=
  ⟨rfl, _, rfl, rfl, by decide, by decide +kernel⟩

/-- The two accounts meet on a single complex head. Wherever a chain is pronounced, [M] features
that Raise the heads below that position and Lower the heads above it make amalgamation build
the same complex head there. -/
theorem amalgamation_at_pronounced {lo hi rest : List Head} {s b : Head}
    (h : lo ++ s :: hi = b :: rest) (hnd : (b :: rest).Nodup) :
    (HeadChain.ofHeads b rest).pronounced {s} = some s ∧
      amalgamateSpine (lo.map (.single · (some .raising)) ++ .single s none ::
          hi.map (.single · (some .lowering))) =
        some [⟨s, (HeadChain.ofHeads b rest).mvalue, none⟩] := by
  refine ⟨?_, amalgamateSpine_raising_lowering h⟩
  have hs : s ∉ lo ++ hi := (List.nodup_cons.mp (List.nodup_middle.mp (h ▸ hnd))).1
  have h₁ : lo.filter (· = s) = [] :=
    List.filter_eq_nil_iff.mpr fun a ha ↦ by simpa using fun h : a = s ↦ hs (by simp [← h, ha])
  have h₂ : hi.filter (· = s) = [] :=
    List.filter_eq_nil_iff.mpr fun a ha ↦ by simpa using fun h : a = s ↦ hs (by simp [← h, ha])
  simp [HeadChain.pronounced, HeadChain.ofHeads, ← h, List.filter_append, h₁, h₂]

/-- Whatever [M] features V and T bear, amalgamation pronounces a verb in the same position with
C above it as without, since heads added above a spine do not change where its heads are
pronounced. The amalgamation account of Danish verb second therefore moves V in the syntax,
across T, where the GenHM chain is pronounced in its strong C. -/
theorem amalgamation_keeps_verb_site (m : Head → Option Direction)
    {out out' : List (Amalgam Head)} {a a' : Amalgam Head}
    (h : amalgamateSpine ([Head.V, .T].map fun x ↦ .single x (m x)) = some out)
    (h' : amalgamateSpine ([Head.V, .T, .C].map fun x ↦ .single x (m x)) = some out')
    (ha : a ∈ out) (ha' : a' ∈ out') (hV : .V ∈ a.members) (hV' : .V ∈ a'.members) :
    a'.site = a.site :=
  site_eq_of_append (extra := [Amalgam.single Head.C (m .C)]) h h'
    (by simp [Amalgam.members, Amalgam.single]) ha ha' hV hV'

/-- Do-support turns on a specifier. A strong verb in a language with Split-by-Intervention
takes it when the subject intervenes between C and the verb, and not when the same heads are
related across a lower copy of the subject. A spine of heads is the same in both clauses, and
Harizanov and Gribanova leave the union of English T with its verb to another operation. -/
theorem doSupport_iff_intervener {L : Language} (hV : .V ∈ L.strong)
    (hs : L.splitByIntervention) :
    Context.inversion.above = Context.toC.above ∧ (derive L .inversion .V).DoSupport ∧
      ¬ (derive L .toC .V).DoSupport := by
  refine ⟨rfl, (doSupport_iff (by decide)).mpr ⟨rfl, hV, by decide, .inl ⟨hs, rfl⟩⟩, fun h ↦ ?_⟩
  simpa [Splits, Context.toC] using splits_of_doSupport h

/-- The settings and context of a French or Danish clause among the verb-placement examples of
the amalgamation study. -/
def clauseOf (r : Datum) : Option (Language × Context) :=
  let cx (L : Language) : Context :=
    if r.feature? "diagnostic" = some "negation" then .negation L else .declarative
  match r.language, r.feature? "clause" with
  | "stan1290", none => some (french, cx french)
  | "dani1285", some "embedded" => some (danish, cx danish)
  | "dani1285", some "root" => some (danish, .toC)
  | _, _ => none

/-- On the French and Danish verb-placement examples of the amalgamation study the two accounts
agree. Each example is acceptable in exactly the order that the position of the finite word
predicts, whether the finite verb is a lexical verb or an auxiliary. -/
theorem amalgamation_rows :
    ∀ r ∈ HarizanovGribanova2019.Examples.all,
      r.feature? "phenomenon" = some "finiteVerbPlacement" →
      r.feature? "diagnostic" ≠ some "coordination" → r.language ≠ "russ1263" →
        ∃ p ∈ clauseOf r, ∃ b ∈ r.parse? "verbPrecedes" boolLabels, ∀ verb ∈ [Head.V, .Aux],
          (r.judgment = .acceptable ↔
            (b = true ↔ (derive p.1 p.2 verb).finitePosition p.1 ∈ [some .T, some .C])) := by
  decide +kernel

end Amalgamation

end ArregiPietraszko2021
