module

public import Linglib.Syntax.CCG.Derivation
public import Mathlib.Data.Set.Defs

/-!
# CCG grammars and their languages

A CCG grammar is a finite lexicon, a start atom and a rule system, given as permission gates on
the generalized composition schema, so the formalisms of the literature are choices of gate. In
the classical formalism of Weir and Joshi and of Vijay-Shanker and Weir
(`Grammar.targetRestricted`) a grammar owns a degree bound and a target restriction, under which
a rule fires only when the target of its primary input is the start atom. In the multimodal
formalism of Baldridge and Steedman (`Grammar.multimodal`) the rule system is universal, and a
grammar is nothing but its lexicon and start atom. A derivation step records only its degree and
direction: degree 0 is application, and the harmonic/crossed distinction follows from the slash
directions. The schema is modality-blind, so target-restricted grammars use the unrestricted
modality.

Kuhlmann, Koller and Satta show that with target restrictions the classical formalism is weakly
equivalent to tree-adjoining grammar and without them strictly weaker, and that the multimodal
formalism is likewise less expressive than TAG. Schiffer and Maletti upgrade the equivalence to
strong equivalence for grammars without empty lexical entries and with rules of degree at most 2.
Strings here are token lists, so empty lexical entries are inexpressible.

## Main definitions

* `CCG.Grammar`: a lexicon, a start atom, and rule-permission gates.
* `CCG.Grammar.targetRestricted`, `CCG.Grammar.multimodal`: the two rule systems of the
  literature, as gate choices.
* `CCG.Grammar.Derives`: the derivability relation, with `Grammar.language` the set of strings
  derived at the start atom.

## Main statements

* `CCG.Grammar.multimodal_derives_iff`: a multimodal grammar derives `w` at `c` iff some
  `CCG.Derivation` over its lexicon has yield `w`.

## Implementation notes

Derivability is an inductive `Prop`, mathlib's form for grammar formalisms
(`ContextFreeGrammar.Derives`), in contrast to the intrinsically typed `CCG.Derivation` of the
interpreted theory: capacity arguments quantify over all derivations, and induction on `Derives`
is exactly that quantification.

## References

* [weir-joshi-1988]
* [vijay-shanker-weir-1994]
* [baldridge-2002]
* [steedman-2019]
* [kuhlmann-koller-satta-2015]
* [schiffer-maletti-2021]
-/

@[expose] public section

namespace CCG

variable {α : Type*}

/-! ### Grammars and their languages -/

/-- A CCG grammar has a finite lexicon, a distinguished start atom, and a rule system given as
permission gates, where `allowsFwd n a b` says forward composition of degree `n` may combine
primary `a` with secondary `b` (mirrored by `allowsBwd`). -/
structure Grammar (α : Type*) where
  /-- Lexical entries, pairing a token with a category. -/
  lexicon : List (String × Cat α)
  /-- The distinguished atom, at which the language collects derivations. -/
  start : α
  /-- May forward composition of degree `n` combine primary `a` with secondary `b`? -/
  allowsFwd : Nat → Cat α → Cat α → Prop
  /-- May backward composition of degree `n` combine secondary `a` with primary `b`? -/
  allowsBwd : Nat → Cat α → Cat α → Prop

/-- A target-restricted (VW-CCG) grammar ([vijay-shanker-weir-1994],
[kuhlmann-koller-satta-2015]) admits rules up to a degree bound whose primary input has the start
atom as target. The normal form of [schiffer-maletti-2021] has `degree = 2`. -/
def Grammar.targetRestricted (lexicon : List (String × Cat α)) (start : α)
    (degree : Nat) : Grammar α where
  lexicon := lexicon
  start := start
  allowsFwd := fun n a _ => n ≤ degree ∧ Cat.target a = start
  allowsBwd := fun n _ b => n ≤ degree ∧ Cat.target b = start

/-- The universal rule system of multimodal CCG ([baldridge-2002], [steedman-2019]) admits
degree at most 2, with harmonic and crossing composition gated by the primary slash's modality
and uniform secondary spines. -/
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

/-- A multimodal grammar, in the radically lexicalized formalism of [steedman-2019], is a
lexicon and a start atom under the universal modality-controlled rule system. It is strictly less
expressive than the target-restricted grammars ([kuhlmann-koller-satta-2015]). -/
def Grammar.multimodal (lexicon : List (String × Cat α)) (start : α) : Grammar α where
  lexicon := lexicon
  start := start
  allowsFwd := Multimodal.allowsFwd
  allowsBwd := Multimodal.allowsBwd

/-- `G.Derives c w` says the grammar derives the token string `w` at category `c`, by a lexical
entry or by a generalized composition of two adjacent derivations that the grammar's gates
permit. -/
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

/-- The string language of a grammar is the set of token strings derived at the start atom.
Strings are token lists, so the ε-freeness of [schiffer-maletti-2021]'s normal form holds by
construction. -/
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

/-- Multimodal derivability yields a `Derivation` tree over the lexicon, since the gate and
the argument sequence of the secondary input force a rule of the modern inventory. -/
theorem Grammar.Derives.to_derivation [DecidableEq α] {L : List (String × Cat α)}
    {s : α} {c₀ : Cat α} {w : List String}
    (h : (Grammar.multimodal L s).Derives c₀ w) :
    ∃ d : Derivation α c₀, d.LexIn L ∧ d.yield = w := by
  induction h with
  | @lex w' c' hmem => exact ⟨.lex w' c', hmem, rfl⟩
  | @fc n a b c u v _ _ hgate hc iha ihb =>
    obtain ⟨da, hla, rfl⟩ := iha
    obtain ⟨db, hlb, rfl⟩ := ihb
    obtain ⟨x, m, y, β, rfl, rfl, rfl, rfl⟩ := Cat.generalizedForwardComp_eq_some_iff.mp hc
    rcases β with _ | ⟨⟨_ | _, _, _⟩, _ | ⟨⟨_ | _, _, _⟩, _ | _⟩⟩
    all_goals first
      | exact hgate.elim
      | exact ⟨.node .fapp da db, ⟨hla, hlb⟩, rfl⟩
      | exact ⟨.node (.fcomp hgate) da db, ⟨hla, hlb⟩, rfl⟩
      | exact ⟨.node (.fcompx hgate) da db, ⟨hla, hlb⟩, rfl⟩
      | exact ⟨.node (.fcomp2 hgate) da db, ⟨hla, hlb⟩, rfl⟩
      | exact ⟨.node (.fcompx2 hgate) da db, ⟨hla, hlb⟩, rfl⟩
  | @bc n a b c u v _ _ hgate hc iha ihb =>
    obtain ⟨da, hla, rfl⟩ := iha
    obtain ⟨db, hlb, rfl⟩ := ihb
    obtain ⟨x, m, y, β, rfl, rfl, rfl, rfl⟩ := Cat.generalizedBackwardComp_eq_some_iff.mp hc
    rcases β with _ | ⟨⟨_ | _, _, _⟩, _ | ⟨⟨_ | _, _, _⟩, _ | _⟩⟩
    all_goals first
      | exact hgate.elim
      | exact ⟨.node .bapp da db, ⟨hla, hlb⟩, rfl⟩
      | exact ⟨.node (.bcomp hgate) da db, ⟨hla, hlb⟩, rfl⟩
      | exact ⟨.node (.bcompx hgate) da db, ⟨hla, hlb⟩, rfl⟩
      | exact ⟨.node (.bcomp2 hgate) da db, ⟨hla, hlb⟩, rfl⟩
      | exact ⟨.node (.bcompx2 hgate) da db, ⟨hla, hlb⟩, rfl⟩

/-- Multimodal derivability is the tree calculus: a multimodal grammar derives `w` at `c` iff
some derivation over its lexicon has yield `w`. -/
theorem Grammar.multimodal_derives_iff [DecidableEq α] {L : List (String × Cat α)}
    {s : α} {c : Cat α} {w : List String} :
    (Grammar.multimodal L s).Derives c w ↔
      ∃ d : Derivation α c, d.LexIn L ∧ d.yield = w :=
  ⟨Grammar.Derives.to_derivation, fun ⟨d, hl, hy⟩ => hy ▸ d.derives_multimodal hl⟩

end CCG