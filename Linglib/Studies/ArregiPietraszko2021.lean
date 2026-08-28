import Linglib.Data.Examples.ArregiPietraszko2021
import Mathlib.Data.List.Basic

/-!
# Arregi & Pietraszko 2021: the ups and downs of head displacement

Upward and downward head displacement are one syntactic operation, Generalized Head Movement:
a head bearing the feature [hm] shares a single M-value — the bundle of morphological features
Vocabulary Insertion targets — with the head of its complement, so that successive applications
build a complex head whose internal structure obeys the Mirror Principle and whose terminals
form a head chain. Where the complex head is pronounced is postsyntactic: Head Chain
Pronunciation delinks every position but the highest strong one, or the highest of all if none is
strong. French finite verbs and auxiliaries everywhere surface in T because no position is
strong; English lexical verbs are strong and so surface low; Danish verbs are strong but so is
C, so the same chain surfaces in C under verb-second and in V otherwise. Do-support is what a
strong V does to a chain that gets split — by a [+P] specifier intervening between the chain's
top and V*, or by V* being marked [−P] under ellipsis or as the lower copy of a fronted VP: each
half keeps the whole M-value, morphological terminals whose syntactic terminal is no longer in
their chain become orphans, an orphan V is exponed as *do*, and an orphan T is obliterated,
impoverished, ignored, or given its elsewhere allomorph according to the language. Hence
do-support alternates with downward displacement in English but with upward displacement in
Monnese, where T is strong too; Mainland Scandinavian lacks Split-by-Intervention and so shows
do-support only under ellipsis and fronting; and the Ndebele relative prefix, pronounced low,
has the Mirror-obeying bracketing its vowel coalescence requires.

## Main definitions

* `MValue`, `HeadChain`: the complex head GenHM builds and the positions sharing it, with
  `HeadChain.orphans` the terminals Orphan Assignment marks.
* `Language`: strength, the availability of Split-by-Intervention, and the fate of an orphan T.
* `pronounce`, `split`, `derive`: Head Chain Pronunciation, chain splitting, and the surface
  a context and verb type yield in a language.
* `coalesce`: Ndebele vowel coalescence over a complex head.

## References

* [arregi-pietraszko-2021]
* [baker-1985] — the Mirror Principle
* [pollock-1989] — the French/English verb-placement contrast
-/

namespace ArregiPietraszko2021

open Data.Examples

/-! ### Head chains and M-values (§2) -/

/-- The syntactic terminals that enter head chains: the verbal heads, Σ, T, C, and the D and
linker heads of the Ndebele relative. -/
inductive Head
  | V
  | Aux
  | sigma
  | T
  | C
  | D
  | Lnk
  deriving DecidableEq, Repr

/-- A complex head: the M-value GenHM builds by adding the higher head's morphological
terminal outside the lower chain's M-value. -/
inductive MValue
  | leaf (h : Head)
  | node (outer inner : MValue)
  deriving DecidableEq, Repr

/-- The morphological terminals of a complex head. -/
def MValue.terminals : MValue → List Head
  | .leaf h => [h]
  | .node o i => o.terminals ++ i.terminals

/-- The M-value of a chain listed from its lowest head up, by cyclic GenHM. -/
def chainMValue : List Head → MValue
  | [] => .leaf .V
  | h :: rest => rest.foldl (fun m x => .node (.leaf x) m) (.leaf h)

/-- A head chain: its positions from the bottom up and the M-value they share. -/
structure HeadChain where
  positions : List Head
  mvalue : MValue
  deriving DecidableEq, Repr

/-- Orphan Assignment: the morphological terminals whose syntactic terminal is not in the
chain. -/
def HeadChain.orphans (c : HeadChain) : List Head :=
  c.mvalue.terminals.filter (· ∉ c.positions)

/-- The chain GenHM builds over the given positions. -/
def HeadChain.ofPositions (ps : List Head) : HeadChain := ⟨ps, chainMValue ps⟩

/-- Every terminal of the M-value built over `acc` by the heads `l` comes from `acc` or from
`l`. -/
theorem mem_of_mem_terminals_foldl {x : Head} : ∀ (l : List Head) (acc : MValue),
    x ∈ (l.foldl (fun m y => MValue.node (.leaf y) m) acc).terminals →
      x ∈ acc.terminals ∨ x ∈ l
  | [], _, h => Or.inl h
  | y :: l, acc, h => by
    rcases mem_of_mem_terminals_foldl l (.node (.leaf y) acc) h with h' | h'
    · simp only [MValue.terminals, List.singleton_append, List.mem_cons] at h'
      rcases h' with rfl | h'
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem _ h')

/-- A chain GenHM builds has no orphans. -/
theorem orphans_ofPositions (h : Head) (rest : List Head) :
    (HeadChain.ofPositions (h :: rest)).orphans = [] := by
  refine List.filter_eq_nil_iff.mpr fun x hx => ?_
  simp only [HeadChain.ofPositions, decide_eq_true_eq, not_not]
  rcases mem_of_mem_terminals_foldl rest (.leaf h) hx with h' | h'
  · simp only [MValue.terminals, List.mem_singleton] at h'
    exact h' ▸ List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ h'

/-! ### Pronunciation and splitting (§2, §4) -/

/-- How a language treats an orphan T: Table 1. -/
inductive OrphanT
  | ignored
  | elsewhere
  | impoverish
  | obliterate
  deriving DecidableEq, Repr

/-- The form of the verb an orphan T yields: finite in Swedish, the pseudo-infinitive in
Yiddish, the true infinitive in Polish and Monnese, bare in English. -/
inductive VerbForm
  | finite
  | pseudoInfinitive
  | infinitive
  | bare
  deriving DecidableEq, Repr

def OrphanT.form : OrphanT → VerbForm
  | .ignored => .finite
  | .elsewhere => .pseudoInfinitive
  | .impoverish => .infinitive
  | .obliterate => .bare

/-- A language's settings: which heads are strong, whether Split-by-Intervention is active,
whether sentential negation is a [+P] specifier, and the fate of an orphan T. -/
structure Language where
  strong : Head → Bool
  splitByIntervention : Bool
  negIntervenes : Bool
  orphanT : OrphanT

/-- Head Chain Pronunciation: the highest strong position, otherwise the highest. -/
def pronounce (L : Language) (ps : List Head) : Option Head :=
  (ps.filter L.strong).getLast? <|> ps.getLast?

/-- Chain splitting at V*: by a [+P] intervener when the language has Split-by-Intervention,
or by V* being [−P]; the two halves keep the whole M-value. -/
def split (L : Language) (intervener elided : Bool) (c : HeadChain) : List HeadChain :=
  match c.positions with
  | .V :: rest =>
    if L.strong .V ∧ rest ≠ [] ∧ ((intervener ∧ L.splitByIntervention) ∨ elided) then
      [⟨[.V], c.mvalue⟩, ⟨rest, c.mvalue⟩]
    else [c]
  | _ => [c]

/-- The contexts the paper's derivations cover. -/
inductive Ctx
  | declarative
  | negation
  | verum
  | inversion
  | subjectWh
  | v2
  | imperative (negated : Bool)
  | ellipsis (v2 : Bool)
  | fronting (v2 : Bool)
  deriving DecidableEq, Repr

/-- The heads GenHM relates in a context, from the verb up. -/
def Ctx.positions (L : Language) (verb : Head) : Ctx → List Head
  | .declarative => [verb, .T]
  | .negation => if L.negIntervenes then [verb, .sigma, .T] else [verb, .T]
  | .verum => [verb, .sigma, .T]
  | .inversion | .subjectWh | .v2 => [verb, .T, .C]
  | .imperative false => [verb, .T, .C]
  | .imperative true => [verb, .T]
  | .ellipsis isV2 | .fronting isV2 => if isV2 then [verb, .T, .C] else [verb, .T]

/-- Whether a [+P] specifier intervenes between the chain's top and the verb: negation where
it is a specifier, the covert verum specifier, the subject under inversion and verb-second;
not a subject's lower copy. -/
def Ctx.intervener (L : Language) : Ctx → Bool
  | .negation => L.negIntervenes
  | .verum | .inversion | .v2 => true
  | .ellipsis isV2 | .fronting isV2 => isV2
  | _ => false

/-- Whether the verb's position is marked [−P]: under ellipsis, or as the lower copy of a
fronted VP. -/
def Ctx.elided : Ctx → Bool
  | .ellipsis _ | .fronting _ => true
  | _ => false

/-- What surfaces: where the finite M-value is pronounced, whether it contains an orphan V
(*do*), the form of a separately pronounced verb, whether C is in the verb's chain (imperative
allomorphy), and the form of a fronted verb. -/
structure Surface where
  finitePosition : Option Head
  doSupport : Bool
  verbForm : Option VerbForm
  cInChain : Bool
  frontedForm : Option VerbForm
  deriving DecidableEq, Repr

/-- The derivation of a context with a lexical or auxiliary verb. -/
def derive (L : Language) (c : Ctx) (verb : Head) : Surface :=
  let chain := HeadChain.ofPositions (c.positions L verb)
  let chains := split L (c.intervener L) c.elided chain
  let upper := chains.getLast?.getD chain
  let lower := chains.headD chain
  { finitePosition := pronounce L upper.positions
    doSupport := .V ∈ upper.orphans
    verbForm := if chains.length = 2 ∧ ¬ c.elided then some L.orphanT.form else none
    cInChain := .C ∈ lower.positions
    frontedForm :=
      match c with
      | .fronting _ =>
        some (if .T ∈ (HeadChain.mk [.V] chain.mvalue).orphans then L.orphanT.form else .finite)
      | _ => none }

/-! ### Languages -/

/-- English: strong lexical V, Split-by-Intervention, negation a specifier, orphan T
obliterated. -/
def english : Language := ⟨(· = .V), true, true, .obliterate⟩

/-- French: no strong head. -/
def french : Language := ⟨fun _ => false, false, true, .obliterate⟩

/-- Danish: strong V and C, no Split-by-Intervention. -/
def danish : Language := ⟨fun h => h = .V ∨ h = .C, false, true, .ignored⟩

/-- Swedish: as Danish, with an orphan T ignored. -/
def swedish : Language := danish

/-- Monnese: strong V, T, and C, Split-by-Intervention, negation not a specifier, orphan T
impoverished. -/
def monnese : Language := ⟨fun h => h = .V ∨ h = .T ∨ h = .C, true, false, .impoverish⟩

/-- Polish: weak V, orphan T impoverished. -/
def polish : Language := ⟨fun _ => false, false, true, .impoverish⟩

/-- Hebrew: as Polish. -/
def hebrew : Language := polish

/-- Yiddish: weak V, orphan T given its elsewhere allomorph. -/
def yiddish : Language := ⟨fun _ => false, false, true, .elsewhere⟩

/-- Spanish: no strong head. -/
def spanish : Language := french

/-- Vallader Romansh: strong imperative T. -/
def vallader : Language := ⟨(· = .T), false, true, .obliterate⟩

/-- Ndebele: strong T. -/
def ndebele : Language := vallader

/-- The language of a row, by glottocode. -/
def Language.ofRow (r : LinguisticExample) : Option Language :=
  match r.language with
  | "stan1293" => some english
  | "stan1290" => some french
  | "dani1285" => some danish
  | "swed1254" => some swedish
  | "lomb1257" => some monnese
  | "poli1260" => some polish
  | "hebr1245" => some hebrew
  | "east2295" => some yiddish
  | "stan1288" => some spanish
  | "lowe1386" => some vallader
  | _ => none

def Ctx.parse? : String → Option Ctx
  | "declarative" => some .declarative
  | "negation" => some .negation
  | "verum" => some .verum
  | "inversion" => some .inversion
  | "subjectWh" => some .subjectWh
  | "v2" => some .v2
  | "imperativeAff" => some (.imperative false)
  | "imperativeNeg" => some (.imperative true)
  | "ellipsis" => some (.ellipsis false)
  | "ellipsisV2" => some (.ellipsis true)
  | "fronting" => some (.fronting false)
  | "frontingV2" => some (.fronting true)
  | _ => none

def Head.parse? : String → Option Head
  | "V" => some .V
  | "T" => some .T
  | "C" => some .C
  | _ => none

def VerbForm.parse? : String → Option VerbForm
  | "finite" => some .finite
  | "pseudoInfinitive" => some .pseudoInfinitive
  | "infinitive" => some .infinitive
  | "bare" => some .bare
  | _ => none

/-- A row's surface features agree with a derived surface. -/
def Surface.Matches (s : Surface) (r : LinguisticExample) : Prop :=
  (∀ p ∈ (r.feature? "finitePosition" >>= Head.parse?).toList, s.finitePosition = some p) ∧
  (∀ d ∈ (r.feature? "doSupport").toList, (d = "true") = s.doSupport) ∧
  (∀ f ∈ (r.feature? "verbForm" >>= VerbForm.parse?).toList, s.verbForm = some f) ∧
  (∀ b ∈ (r.feature? "imperativeForm").toList, (b = "true") = s.cInChain) ∧
  (∀ f ∈ (r.feature? "frontedForm" >>= VerbForm.parse?).toList, s.frontedForm = some f)

instance (s : Surface) (r : LinguisticExample) : Decidable (s.Matches r) := by
  unfold Surface.Matches; infer_instance

/-- Every verb-placement, do-support, imperative, ellipsis, and fronting example of the paper
surfaces as its language's settings derive. -/
theorem rows_derived :
    ∀ r ∈ Examples.all, ∀ L ∈ (Language.ofRow r).toList,
      ∀ c ∈ (r.feature? "context" >>= Ctx.parse?).toList,
        (derive L c (if r.feature? "verbType" = some "auxiliary" then .Aux else .V)).Matches r := by
  decide +kernel

/-- The same chain surfaces in C under verb-second and in V otherwise: downward displacement
feeds upward displacement without a step in T. -/
theorem danish_v2 :
    pronounce danish [.V, .T, .C] = some .C ∧ pronounce danish [.V, .T] = some .V := by decide

/-- Do-support alternates with downward displacement in English but with upward displacement
in Monnese: without an intervener the English verb surfaces in V and the Monnese verb in T,
and both get *do* under inversion. -/
theorem directionality_no_correlation :
    (derive english .declarative .V).finitePosition = some .V ∧
      (derive monnese .declarative .V).finitePosition = some .T ∧
      (derive english .inversion .V).doSupport ∧ (derive monnese .inversion .V).doSupport := by
  decide

/-- The typology of (73): Split-by-Intervention gives English but not Danish do-support under
inversion; Split-by-Deletion gives both do-support under ellipsis. -/
theorem split_typology :
    (derive english .inversion .V).doSupport ∧ ¬ (derive danish .v2 .V).doSupport ∧
      (derive english (.ellipsis false) .V).doSupport ∧
      (derive danish (.ellipsis true) .V).doSupport := by
  decide

/-! ### Ndebele relative prefixes (§3.1) -/

/-- A vowel of the Ndebele exponents. -/
def isVowel (c : Char) : Bool := c ∈ ['a', 'e', 'i', 'o', 'u']

/-- Vowel coalescence at a morpheme boundary (18): identical vowels merge, `a + i` gives `e`,
`a + u` gives `o`, and `e` yields to a following vowel. -/
def join (a b : List Char) : List Char :=
  match a.getLast?, b with
  | some x, y :: rest =>
    if isVowel x ∧ isVowel y then
      if x = y then a ++ rest
      else if x = 'a' ∧ y = 'i' then a.dropLast ++ 'e' :: rest
      else if x = 'a' ∧ y = 'u' then a.dropLast ++ 'o' :: rest
      else if x = 'e' then a.dropLast ++ b
      else a ++ b
    else a ++ b
  | _, _ => a ++ b

/-- A complex head over exponents, bracketed as GenHM builds it. -/
inductive Exponents
  | leaf (s : String)
  | node (outer inner : Exponents)

/-- Cyclic coalescence: each constituent of the complex head is spelled out before the one
containing it. -/
def coalesce : Exponents → List Char
  | .leaf s => s.toList
  | .node o i => join (coalesce o) (coalesce i)

/-- The relative prefix as the Mirror-obeying complex head `[Lnk [D [C T]]]` with a null C. -/
def relPrefix (linker augment agreement : String) : Exponents :=
  .node (.leaf linker) (.node (.leaf augment) (.node (.leaf "") (.leaf agreement)))

/-- Table (19): the relative prefixes of classes 1, 9, 7, and 11 coalesce from their linker,
augment, and agreement components in the Mirror-obeying bracketing. -/
theorem rows_relative_prefix :
    ∀ r ∈ Examples.all, ∀ l ∈ (r.feature? "linker").toList, ∀ a ∈ (r.feature? "augment").toList,
      ∀ g ∈ (r.feature? "agreement").toList, ∀ rel ∈ (r.feature? "rel").toList,
        coalesce (relPrefix l a g) = rel.toList := by
  decide +kernel

/-- The non-mirroring bracketing `[[Lnk D] T]` of (21) derives *i* for class 9, not the
attested *e*. -/
theorem nonmirror_class9 :
    coalesce (.node (.node (.leaf "a") (.leaf "i")) (.leaf "i")) = ['i'] ∧
      coalesce (relPrefix "a" "i" "i") = ['e'] := by
  decide

/-- The relative complex head is pronounced low, in strong T, after the subject in Spec,TP. -/
theorem ndebele_low : pronounce ndebele [.T, .C, .D, .Lnk] = some .T := by decide

end ArregiPietraszko2021
