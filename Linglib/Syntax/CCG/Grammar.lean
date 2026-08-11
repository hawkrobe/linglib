import Linglib.Syntax.CCG.Derivation
import Mathlib.Data.Set.Defs

/-!
# CCG grammars and their languages

This file defines CCG grammars and their string languages. A grammar is a finite
lexicon, a start atom, and its *rule system*, given as permission gates on the
generalized composition schema; the formalisms of the literature are choices of
gate. `Grammar.targetRestricted` is VW-CCG ([vijay-shanker-weir-1994],
[weir-joshi-1988]), where the grammar owns a degree bound and a target restriction;
`Grammar.multimodal` is the radically lexicalized modern formalism
([baldridge-2002], [steedman-2019]), whose rule system is universal — a grammar is
nothing but its lexicon and start symbol. The restriction modelled is the one
[kuhlmann-koller-satta-2015]'s generative-capacity results turn on, a *target
restriction*: a rule fires only when the target of its primary input category (the
leftmost atom, after stripping all arguments) is a distinguished atom `s`.

Rules are the generalized-composition schema `CCG.Cat.generalizedForwardComp` /
`CCG.Cat.generalizedBackwardComp`, gated on the target: a derivation node records
only its degree and direction, per the [vijay-shanker-weir-1994] rule form — degree
0 is application, and the harmonic/crossed distinction is a consequence of the slash
directions rather than a separate rule class. The schema is modality-blind (VW-CCG
predates slash typing); grammars instantiate categories at the unrestricted
modality.

The two rule-control mechanisms differ in expressive power
([kuhlmann-koller-satta-2015]): with target restrictions VW-CCG is weakly equivalent
to TAG, without them it is strictly weaker, and the slash-typing variant is likewise
slightly less expressive than TAG. [schiffer-maletti-2021] upgrade the equivalence to
*strong* equivalence (the same tree languages, modulo relabeling) for the modern
capacity object: CCG without empty-string lexicon entries and with rules of degree at
most 2 — with unbounded degree the formalism is Turing-complete. The `Grammar` of this file is that
object (yields are token lists, so ε-entries are inexpressible by construction), and
this file is the substrate for the constructions of CCGs for non-context-free
languages in `Studies/KuhlmannKollerSatta2015`.

## Main definitions

* `CCG.Grammar`: a lexicon, a start atom, and rule-permission gates.
* `CCG.Grammar.targetRestricted`, `CCG.Grammar.multimodal`: the two rule systems of
  the literature, as gate choices.
* `CCG.Grammar.Derives`: the derivability relation — `G.Derives c w` says the
  grammar derives token string `w` at category `c`; `Grammar.language` is the set of
  strings derived at the distinguished atom.

## Main statements

* `CCG.Grammar.multimodal_derives_iff`: a multimodal grammar derives `w` at `c` iff
  some intrinsically typed `CCG.Derivation` over its lexicon has yield `w` — the
  relation is the string-language shadow of the tree calculus.

## Implementation notes

Derivability is an inductive `Prop`, mathlib's form for grammar formalisms
(`ContextFreeGrammar.Derives`), in contrast to the intrinsically typed
`CCG.Derivation` of the interpreted theory: capacity arguments quantify over all
derivations, and induction on `Derives` is exactly that quantification.
-/

namespace CCG

variable {α : Type*}

/-! ### Grammars and their languages -/

/-- A CCG grammar: a finite lexicon, a distinguished start atom, and the grammar's
rule system, given as permission gates — `allowsFwd n a b` says forward composition
of degree `n` may combine primary `a` with secondary `b` (mirrored by `allowsBwd`).
The formalisms of the literature are choices of gate: `Grammar.targetRestricted`
(VW-CCG) and `Grammar.multimodal` (the universal modality-controlled rules). -/
structure Grammar (α : Type*) where
  /-- Lexical entries, pairing a token with a category. -/
  lexicon : List (String × Cat α)
  /-- The distinguished atom: the language collects derivations of this category. -/
  start : α
  /-- May forward composition of degree `n` combine primary `a` with secondary `b`? -/
  allowsFwd : Nat → Cat α → Cat α → Prop
  /-- May backward composition of degree `n` combine secondary `a` with primary `b`? -/
  allowsBwd : Nat → Cat α → Cat α → Prop

/-- A target-restricted (VW-CCG) grammar ([vijay-shanker-weir-1994],
[kuhlmann-koller-satta-2015]): rules up to a degree bound, gated on the primary
input's target (`degree = 2` in [schiffer-maletti-2021]'s normal form). -/
def Grammar.targetRestricted (lexicon : List (String × Cat α)) (start : α)
    (degree : Nat) : Grammar α where
  lexicon := lexicon
  start := start
  allowsFwd := fun n a _ => n ≤ degree ∧ Cat.target a = start
  allowsBwd := fun n _ b => n ≤ degree ∧ Cat.target b = start

/-- The universal rule system of multimodal CCG ([baldridge-2002], [steedman-2019]):
degree at most 2, harmonic and crossing composition gated by the primary slash's
modality, uniform secondary spines. -/
def Multimodal.allowsFwd : Nat → Cat α → Cat α → Prop
  | 0, _, _ => True
  | 1, .rslash _ m _, .rslash _ _ _ => m ≤ Modality.diamond
  | 1, .rslash _ m _, .lslash _ _ _ => m ≤ Modality.cross
  | 2, .rslash _ m _, .rslash (.rslash _ _ _) _ _ => m ≤ Modality.diamond
  | 2, .rslash _ m _, .lslash (.lslash _ _ _) _ _ => m ≤ Modality.cross
  | _, _, _ => False

/-- The mirror of `Multimodal.allowsFwd`. -/
def Multimodal.allowsBwd : Nat → Cat α → Cat α → Prop
  | 0, _, _ => True
  | 1, .lslash _ _ _, .lslash _ m _ => m ≤ Modality.diamond
  | 1, .rslash _ _ _, .lslash _ m _ => m ≤ Modality.cross
  | 2, .lslash (.lslash _ _ _) _ _, .lslash _ m _ => m ≤ Modality.diamond
  | 2, .rslash (.rslash _ _ _) _ _, .lslash _ m _ => m ≤ Modality.cross
  | _, _, _ => False

/-- A multimodal grammar: the radically lexicalized formalism of [steedman-2019],
where a grammar is nothing but a lexicon and a start symbol — its rule system is the
universal modality-controlled one. Strictly less expressive than the
target-restricted grammars ([kuhlmann-koller-satta-2015]). -/
def Grammar.multimodal (lexicon : List (String × Cat α)) (start : α) : Grammar α where
  lexicon := lexicon
  start := start
  allowsFwd := Multimodal.allowsFwd
  allowsBwd := Multimodal.allowsBwd

/-- `G.Derives c w`: the grammar derives token string `w` at category `c` — a lexical
entry, or a generalized composition of two adjacent derivations permitted by the
grammar's gates. Capacity arguments proceed by induction on this relation. -/
inductive Grammar.Derives [DecidableEq α] (G : Grammar α) :
    Cat α → List String → Prop where
  /-- A lexical entry derives its token. -/
  | lex {w : String} {c : Cat α} : (w, c) ∈ G.lexicon → G.Derives c [w]
  /-- Forward composition of degree `n` (`>Bⁿ`; degree 0 is application), if the
  grammar's gate permits it. -/
  | fc (n : Nat) {a b c : Cat α} {u v : List String} :
      G.Derives a u → G.Derives b v → G.allowsFwd n a b →
      Cat.generalizedForwardComp n a b = some c → G.Derives c (u ++ v)
  /-- Backward composition of degree `n` (`<Bⁿ`; degree 0 is application), if the
  grammar's gate permits it. -/
  | bc (n : Nat) {a b c : Cat α} {u v : List String} :
      G.Derives a u → G.Derives b v → G.allowsBwd n a b →
      Cat.generalizedBackwardComp n a b = some c → G.Derives c (u ++ v)

/-- The string language of a grammar: the token strings derived at the distinguished
atom. Strings are token lists, so empty-string lexical entries are inexpressible —
the ε-freeness of [schiffer-maletti-2021]'s normal form holds by construction. -/
def Grammar.language [DecidableEq α] (G : Grammar α) : Set (List String) :=
  { w | G.Derives (.atom G.start) w }

/-! ### The multimodal gate and the tree calculus

A multimodal grammar's derivability coincides with the existence of an intrinsically
typed `Derivation` tree over its lexicon: the trees are the proof-relevant calculus
(what `Derivation.interp` consumes), the relation is its string-language shadow. -/

/-- Every `Derivation` tree over the lexicon witnesses multimodal derivability. -/
theorem Derivation.derives_multimodal [DecidableEq α] {L : List (String × Cat α)}
    {s : α} : {c : Cat α} → (d : Derivation α c) → d.LexIn L →
    (Grammar.multimodal L s).Derives c d.yield
  | _, .lex f c, h => .lex h
  | _, .node ru d₁ d₂, h => by
    obtain ⟨h₁, h₂⟩ := h
    have ih₁ := d₁.derives_multimodal (s := s) h₁
    have ih₂ := d₂.derives_multimodal (s := s) h₂
    cases ru with
    | fapp => exact .fc 0 ih₁ ih₂ trivial (by simp [Cat.generalizedForwardComp])
    | bapp => exact .bc 0 ih₁ ih₂ trivial (by simp [Cat.generalizedBackwardComp])
    | fcomp hm => exact .fc 1 ih₁ ih₂ hm (by simp [Cat.generalizedForwardComp])
    | bcomp hm => exact .bc 1 ih₁ ih₂ hm (by simp [Cat.generalizedBackwardComp])
    | fcompx hm => exact .fc 1 ih₁ ih₂ hm (by simp [Cat.generalizedForwardComp])
    | bcompx hm => exact .bc 1 ih₁ ih₂ hm (by simp [Cat.generalizedBackwardComp])
    | fcomp2 hm => exact .fc 2 ih₁ ih₂ hm (by simp [Cat.generalizedForwardComp])
    | bcomp2 hm => exact .bc 2 ih₁ ih₂ hm (by simp [Cat.generalizedBackwardComp])
    | fcompx2 hm => exact .fc 2 ih₁ ih₂ hm (by simp [Cat.generalizedForwardComp])
    | bcompx2 hm => exact .bc 2 ih₁ ih₂ hm (by simp [Cat.generalizedBackwardComp])


/-- Multimodal derivability yields a `Derivation` tree over the lexicon: the gate and
the schema equation jointly force the shape of a rule of the modern inventory. -/
theorem Grammar.Derives.to_derivation [DecidableEq α] {L : List (String × Cat α)}
    {s : α} {c₀ : Cat α} {w : List String}
    (h : (Grammar.multimodal L s).Derives c₀ w) :
    ∃ d : Derivation α c₀, d.LexIn L ∧ d.yield = w := by
  induction h with
  | @lex w' c' hmem => exact ⟨.lex w' c', hmem, rfl⟩
  | @fc n a b c u v _ _ hgate hc iha ihb =>
    obtain ⟨da, hla, rfl⟩ := iha
    obtain ⟨db, hlb, rfl⟩ := ihb
    rcases n with _ | _ | _ | n
    · rcases a with a | ⟨x, m, y⟩ | ⟨x, m, y⟩ <;> simp [Cat.generalizedForwardComp] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨.node .fapp da db, ⟨hla, hlb⟩, rfl⟩
    · rcases a with a | ⟨x, m, y⟩ | ⟨x, m, y⟩ <;> try exact hgate.elim
      rcases b with b | ⟨y', n', z⟩ | ⟨y', n', z⟩ <;> try exact hgate.elim
      · simp [Cat.generalizedForwardComp] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨.node (.fcomp hgate) da db, ⟨hla, hlb⟩, rfl⟩
      · simp [Cat.generalizedForwardComp] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨.node (.fcompx hgate) da db, ⟨hla, hlb⟩, rfl⟩
    · rcases a with a | ⟨x, m, y⟩ | ⟨x, m, y⟩ <;> try exact hgate.elim
      rcases b with b | ⟨b, p, w'⟩ | ⟨b, p, w'⟩ <;> try exact hgate.elim
      · rcases b with b | ⟨y', n', z⟩ | ⟨y', n', z⟩ <;> try exact hgate.elim
        simp [Cat.generalizedForwardComp] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨.node (.fcomp2 hgate) da db, ⟨hla, hlb⟩, rfl⟩
      · rcases b with b | ⟨y', n', z⟩ | ⟨y', n', z⟩ <;> try exact hgate.elim
        simp [Cat.generalizedForwardComp] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨.node (.fcompx2 hgate) da db, ⟨hla, hlb⟩, rfl⟩
    · exact hgate.elim
  | @bc n a b c u v _ _ hgate hc iha ihb =>
    obtain ⟨da, hla, rfl⟩ := iha
    obtain ⟨db, hlb, rfl⟩ := ihb
    rcases n with _ | _ | _ | n
    · rcases b with b | ⟨x, m, y⟩ | ⟨x, m, y⟩ <;> simp [Cat.generalizedBackwardComp] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨.node .bapp da db, ⟨hla, hlb⟩, rfl⟩
    · rcases a with a | ⟨y', n', z⟩ | ⟨y', n', z⟩ <;> try exact hgate.elim
      · rcases b with b | ⟨x, m, y⟩ | ⟨x, m, y⟩ <;> try exact hgate.elim
        simp [Cat.generalizedBackwardComp] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨.node (.bcompx hgate) da db, ⟨hla, hlb⟩, rfl⟩
      · rcases b with b | ⟨x, m, y⟩ | ⟨x, m, y⟩ <;> try exact hgate.elim
        simp [Cat.generalizedBackwardComp] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨.node (.bcomp hgate) da db, ⟨hla, hlb⟩, rfl⟩
    · rcases a with a | ⟨a, p, w'⟩ | ⟨a, p, w'⟩ <;> try exact hgate.elim
      · rcases a with a | ⟨y', n', z⟩ | ⟨y', n', z⟩ <;> try exact hgate.elim
        rcases b with b | ⟨x, m, y⟩ | ⟨x, m, y⟩ <;> try exact hgate.elim
        simp [Cat.generalizedBackwardComp] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨.node (.bcompx2 hgate) da db, ⟨hla, hlb⟩, rfl⟩
      · rcases a with a | ⟨y', n', z⟩ | ⟨y', n', z⟩ <;> try exact hgate.elim
        rcases b with b | ⟨x, m, y⟩ | ⟨x, m, y⟩ <;> try exact hgate.elim
        simp [Cat.generalizedBackwardComp] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨.node (.bcomp2 hgate) da db, ⟨hla, hlb⟩, rfl⟩
    · exact hgate.elim

/-- **Multimodal derivability is the tree calculus**: `G.Derives c w` for a
multimodal grammar iff some intrinsically typed derivation over its lexicon has
yield `w`. -/
theorem Grammar.multimodal_derives_iff [DecidableEq α] {L : List (String × Cat α)}
    {s : α} {c : Cat α} {w : List String} :
    (Grammar.multimodal L s).Derives c w ↔
      ∃ d : Derivation α c, d.LexIn L ∧ d.yield = w :=
  ⟨Grammar.Derives.to_derivation, fun ⟨d, hl, hy⟩ => hy ▸ d.derives_multimodal hl⟩

end CCG