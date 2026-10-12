module

public import Linglib.Data.Examples.ArregiPietraszko2021
public import Linglib.Data.Forms.ArregiPietraszko2021
public import Linglib.Fragments.Ndebele.Phonology
public import Linglib.Morphology.Word.Tree
public import Linglib.Phonology.Hiatus
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

* `HeadChain.toList_mvalue_ofHeads_after`, `HeadChain.toList_mvalue_ofHeads_before`: the Mirror
  Principle, the terminals of a complex head ordered outward as its heads are ordered upward.
* `doSupport_iff`: do-support arises exactly where the chain of a strong verb splits, whether
  the complex head is otherwise pronounced low or high.
* `directionality_no_correlation`: under inversion English and Monnese both have do-support,
  though elsewhere the English verb is pronounced low and the Monnese verb high.
* `mirror_class9`: regular vowel coalescence derives the Ndebele class 9 relative prefix from
  the Mirror-obeying complex head and not from the opposite bracketing of the same terminals.

## Implementation notes

* A `Context` holds what head displacement sees of a clause: the heads related to the verb,
  whether a pronounced specifier intervenes, and what becomes of the verb phrase. A negative
  imperative, where Σ keeps C out of the verb's chain, is thereby the context of a declarative.
* Split-by-Deletion applies in every language, the possibility the paper raises for its typology
  of splitting; Split-by-Intervention is a setting.
* A language's settings record what the paper's data settle, so the form of a verb with an orphan
  T is absent where no do-support or fronting datum shows it.

## TODO

* Negative Merger, the postsyntactic rule that adds contracted negation outside the complex head.
* The comparison with Harizanov and Gribanova's amalgamation, where a raising step feeding a
  lowering step builds a complex head that violates the Mirror Principle:
  `HarizanovGribanova2019.Amalgam` lists the members of a complex head without their bracketing.

## References

* [arregi-pietraszko-2021]
* [baker-1985]
* [pollock-1989]
* [harizanov-gribanova-2019]
-/

@[expose] public section

namespace ArregiPietraszko2021

open Morphology Morphology.Word Phonology

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
  mvalue : Tree Head

namespace HeadChain

/-- Generalized Head Movement relates a head to the chain of its complement's head. The head
joins the chain, and its morphological terminal attaches outside the shared M-value. -/
def genHM (side : Morph.Side) (x : Head) (c : HeadChain) : HeadChain :=
  ⟨c.positions ++ [x], c.mvalue.attach side x⟩

/-- The chain that cyclic GenHM builds from `bottom` up through the heads `above`. -/
def ofHeads (side : Morph.Side) (bottom : Head) (above : List Head) : HeadChain :=
  ⟨bottom :: above, .attachAll bottom (above.map (side, ·))⟩

theorem genHM_ofHeads (side : Morph.Side) (bottom x : Head) (above : List Head) :
    (ofHeads side bottom above).genHM side x = ofHeads side bottom (above ++ [x]) := by
  simp [genHM, ofHeads, Tree.attachAll_concat]

/-- By the **Mirror Principle**, the suffixal terminals of a complex head follow the root in the
order of their heads. -/
theorem toList_mvalue_ofHeads_after (bottom : Head) (above : List Head) :
    (ofHeads .after bottom above).mvalue.toList = bottom :: above := by
  simp [ofHeads, Tree.toList_attachAll, List.filter_map, Function.comp_def]

/-- By the **Mirror Principle**, the prefixal terminals of a complex head precede the root in the
reverse of the order of their heads. -/
theorem toList_mvalue_ofHeads_before (bottom : Head) (above : List Head) :
    (ofHeads .before bottom above).mvalue.toList = above.reverse ++ [bottom] := by
  simp [ofHeads, Tree.toList_attachAll, List.filter_map, Function.comp_def]

theorem mem_toList_mvalue_ofHeads {side : Morph.Side} {bottom x : Head} {above : List Head} :
    x ∈ (ofHeads side bottom above).mvalue.toList ↔ x ∈ bottom :: above := by
  cases side <;> simp [toList_mvalue_ofHeads_before, toList_mvalue_ofHeads_after, or_comm]

/-- Orphan Assignment marks a morphological terminal in a chain that does not contain its
syntactic terminal. -/
def Orphan (c : HeadChain) (x : Head) : Prop := x ∈ c.mvalue.toList ∧ x ∉ c.positions

instance (c : HeadChain) (x : Head) : Decidable (c.Orphan x) := inferInstanceAs (Decidable (_ ∧ _))

/-- GenHM creates no orphans. -/
theorem not_orphan_ofHeads (side : Morph.Side) (bottom x : Head) (above : List Head) :
    ¬ (ofHeads side bottom above).Orphan x :=
  fun h ↦ h.2 (mem_toList_mvalue_ofHeads.mp h.1)

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
theorem pronounced_genHM_of_mem {strong : Finset Head} {x : Head} (hx : x ∈ strong)
    (side : Morph.Side) (c : HeadChain) : (c.genHM side x).pronounced strong = some x := by
  simp [pronounced, genHM, List.filter_append, hx]

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
  let c := HeadChain.ofHeads .after verb cx.above
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
def HasC (d : Chains) : Prop := .C ∈ d.verb.mvalue.toList

instance (d : Chains) : Decidable d.HasC := inferInstanceAs (Decidable (_ ∈ _))

end Chains

variable {L : Language} {cx : Context} {verb : Head}

theorem splits_of_doSupport (h : (derive L cx verb).DoSupport) : Splits L cx verb := by
  by_contra hs
  simp only [Chains.DoSupport, derive, hs, ↓reduceIte] at h
  exact HeadChain.not_orphan_ofHeads _ _ _ _ h

/-- Do-support arises exactly where the chain of a strong verb splits. -/
theorem doSupport_iff (h : .V ∉ cx.above) : (derive L cx verb).DoSupport ↔ Splits L cx verb := by
  refine ⟨splits_of_doSupport, fun hs ↦ ?_⟩
  obtain rfl := hs.1
  simpa [Chains.DoSupport, derive, hs, HeadChain.Orphan, HeadChain.toList_mvalue_ofHeads_after]
    using h

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
    HeadChain.toList_mvalue_ofHeads_after]

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

/-- The chain of an Ndebele relative clause holds T, a null C, the augment in D and the linker,
each a prefix on the complex head below it. -/
def relative : HeadChain := .ofHeads .before .T [.C, .D, .Lnk]

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

/-- Cyclic spell-out of a complex head spells out a constituent before the one containing it.
Operations other than attachment, which GenHM does not perform, concatenate. -/
def spellOut : Tree (List Segment) → List Segment
  | .root x => x
  | .prefixed x t => join x (spellOut t)
  | .suffixed t x => join (spellOut t) x
  | t => t.toList.flatten

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
      some (spellOut (relative.mvalue.map e)) = transcribe? f.form.toList ∧
        Hiatus.Free (spellOut (relative.mvalue.map e)) ∧
        ¬ Hiatus.Free (relative.mvalue.map e).toList.flatten := by
  decide +kernel

/-- The same terminals in the same order with the opposite bracketing, the linker innermost. -/
def nonMirror : Tree Head := .attachAll .Lnk [(.after, .D), (.after, .C), (.after, .T)]

/-- In class 9 the Mirror-obeying complex head spells out as the attested *e-* and the opposite
bracketing of the same terminals as *i-*. -/
theorem mirror_class9 :
    nonMirror.toList = relative.mvalue.toList ∧
      ∀ f ∈ Forms.all, f.parameterId = "rel_cl9" → ∃ e ∈ exponents? f,
        spellOut (relative.mvalue.map e) = [Ndebele.e] ∧
          spellOut (nonMirror.map e) = [Ndebele.i] := by
  decide +kernel

end ArregiPietraszko2021
