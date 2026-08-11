import Linglib.Syntax.CCG.Basic
import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Intensional.Conjunction
import Linglib.Semantics.Composition.CoordinatorOp
import Linglib.Semantics.Composition.Combinator

/-!
# CCG Syntax-Semantics Interface

Syntactic categories directly encode semantic types and the combinatory rules
correspond to function application and composition ([steedman-2000]), so a
derivation's meaning is read off compositionally from its structure.

## Main definitions

- `catToTy` — maps CCG categories to semantic types
- `SemLexEntry`, `SemLexicon` — lexical entries with semantics
- `DerivStep.interp` — computes a meaning from a derivation compositionally:
  application is function application, composition is the `B` combinator,
  type-raising is the `T` combinator, coordination is generalized
  conjunction ([partee-rooth-1983])

## Main statements

- `DerivStep.cat_of_interp` — soundness: over a well-typed lexicon, a derivation's
  meaning is assigned at exactly the category `DerivStep.cat` derives.
- `DerivStep.interp_fcomp_assoc`, `interp_fapp_fcomp` (and backward mirrors) —
  spurious ambiguity: reassociating a composition-application chain cannot change a
  constituent's interpretation.

Worked toy-fragment derivations and the non-constituent-coordination
semantics theorems live in `Studies/Steedman2000.lean`.
-/

namespace CCG

open Intensional
open Intensional.Conjunction
open Combinator

/-! ### Type correspondence -/

/-- Map CCG categories to semantic types -/
def catToTy : Cat Atom → Ty
  | .atom .S => .t
  | .atom .NP => .e
  | .atom .N => .e ⇒ .t    -- common nouns are properties
  | .atom .PP => .e ⇒ .t   -- PPs are modifiers (simplified)
  | .rslash x y => catToTy y ⇒ catToTy x
  | .lslash x y => catToTy y ⇒ catToTy x

/-- A CCG lexical entry with semantics -/
structure SemLexEntry (E W : Type) where
  form : String
  cat : Cat Atom
  sem : Denot E W (catToTy cat)

/-! ### Type preservation

CCG combinatory rules preserve semantic well-typedness: if the syntactic
combination succeeds, the semantic combination is well-typed. -/

/-- Forward application preserves semantic typing:
    if X/Y combines with Y to give X, then (σ→τ) applied to σ gives τ. -/
theorem forward_app_type_preservation (x y : Cat Atom) :
    catToTy (x.rslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Backward application preserves semantic typing:
    if Y combines with X\Y to give X, then (σ→τ) applied to σ gives τ. -/
theorem backward_app_type_preservation (x y : Cat Atom) :
    catToTy (x.lslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Type correspondence for transitive verbs -/
theorem tv_type_is_relation :
    catToTy TV = (.e ⇒ .e ⇒ .t) := rfl

/-- Type correspondence for intransitive verbs -/
theorem iv_type_is_property :
    catToTy IV = (.e ⇒ .t) := rfl

/-! ### Derivation interpretation -/

/-- A semantic interpretation: category paired with its meaning -/
structure Interp (E W : Type) where
  cat : Cat Atom
  meaning : Denot E W (catToTy cat)

/-- Semantic lexicon: maps words to interpretations -/
def SemLexicon (E W : Type) := String → Cat Atom → Option (Interp E W)

/--
Interpret a CCG derivation, computing its meaning from the lexicon.

Every combinatory rule corresponds to a semantic operation: application is
function application, composition is the `B` combinator, type-raising is the
`T` combinator, and coordination is generalized conjunction (restricted to
conjoinable types). Returns `none` if the derivation is ill-formed or uses
unknown words.
-/
def DerivStep.interp {E W : Type} (d : DerivStep Atom) (lex : SemLexicon E W)
    : Option (Interp E W) :=
  match d with
  | .lex entry => lex entry.form entry.cat

  | .fapp d1 d2 => do
      -- Forward application: X/Y Y → X
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, m1 with
      | .rslash x y, m1 =>
          if h : c2 = y then
            let m2' : Denot E W (catToTy y) := h ▸ m2
            some ⟨x, m1 m2'⟩
          else none
      | _, _ => none

  | .bapp d1 d2 => do
      -- Backward application: Y X\Y → X
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c2, m2 with
      | .lslash x y, m2 =>
          if h : c1 = y then
            let m1' : Denot E W (catToTy y) := h ▸ m1
            some ⟨x, m2 m1'⟩
          else none
      | _, _ => none

  | .fcomp d1 d2 => do
      -- Forward composition: X/Y + Y/Z → X/Z, semantically B (f ∘ g)
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, m1 with
      | .rslash x y1, m1 =>
          match c2, m2 with
          | .rslash y2 z, m2 =>
              if h : y1 = y2 then
                let m2' : Denot E W (catToTy z ⇒ catToTy y1) :=
                  h ▸ m2
                some ⟨x / z, B m1 m2'⟩
              else none
          | _, _ => none
      | _, _ => none

  | .bcomp d1 d2 => do
      -- Backward composition: Y\Z + X\Y → X\Z, semantically B (f ∘ g)
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, m1 with
      | .lslash y1 z, m1 =>
          match c2, m2 with
          | .lslash x y2, m2 =>
              if h : y1 = y2 then
                let m1' : Denot E W (catToTy z ⇒ catToTy y2) :=
                  h ▸ m1
                some ⟨x \ z, B m2 m1'⟩
              else none
          | _, _ => none
      | _, _ => none

  | .fcompx d1 d2 => do
      -- Forward crossed composition: X/Y + Y\Z → X\Z, semantically B (f ∘ g)
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, m1 with
      | .rslash x y1, m1 =>
          match c2, m2 with
          | .lslash y2 z, m2 =>
              if h : y1 = y2 then
                let m2' : Denot E W (catToTy z ⇒ catToTy y1) :=
                  h ▸ m2
                some ⟨x \ z, B m1 m2'⟩
              else none
          | _, _ => none
      | _, _ => none

  | .ftr d t => do
      -- Forward type-raising: X → T/(T\X), semantically T (λf. f x)
      let ⟨x, m⟩ ← d.interp lex
      some ⟨x.forwardTypeRaise t, T m⟩

  | .btr d t => do
      -- Backward type-raising: X → T\(T/X), semantically T (λf. f x)
      let ⟨x, m⟩ ← d.interp lex
      some ⟨x.backwardTypeRaise t, T m⟩

  | .coord c d1 d2 => do
      -- Coordination: X c X → X, via the Coordinator API — the meaning is `Coordinator.op`
      -- of the coordinator's own `role` (runtime form `engineOp`; = generalized conjunction
      -- [partee-rooth-1983] at `.j`), restricted to conjoinable types. The `role` is read off
      -- the coordinator the derivation carries, so *which* coordinator is used is
      -- truth-conditionally load-bearing.
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      if h : c1 = c2 then
        let ty := catToTy c1
        if ty.isConjoinable then
          let m2' : Denot E W (catToTy c1) := h ▸ m2
          some ⟨c1, Coordinator.engineOp c.role ty E W m1 m2'⟩
        else none
      else none

/-! ### Soundness: interpretation refines category assignment -/

/-- A semantic lexicon is *well-typed* when every interpretation it returns is at the
queried category. -/
def SemLexicon.WellTyped {E W : Type} (lex : SemLexicon E W) : Prop :=
  ∀ w c i, lex w c = some i → i.cat = c

/-- Soundness of the interface: over a well-typed lexicon, `DerivStep.interp` and
`DerivStep.cat` agree — a derivation that receives a meaning receives it at exactly the
category the syntax derives. -/
theorem DerivStep.cat_of_interp {E W : Type} {lex : SemLexicon E W}
    (hlex : lex.WellTyped) {d : DerivStep Atom} :
    ∀ {i : Interp E W}, d.interp lex = some i → d.cat = some i.cat := by
  induction d with
  | lex e =>
    intro i h
    simp only [DerivStep.interp] at h
    simp [DerivStep.cat, hlex _ _ _ h]
  | fapp d1 d2 ih1 ih2 =>
    intro i h
    rcases h1 : d1.interp lex with _ | ⟨c1, m1⟩
    · simp [DerivStep.interp, h1] at h
    rcases h2 : d2.interp lex with _ | ⟨c2, m2⟩
    · simp [DerivStep.interp, h1, h2] at h
    simp only [DerivStep.interp] at h
    rw [h1, h2] at h
    rcases c1 with _ | ⟨x, y⟩ | ⟨x, y⟩ <;>
      try (change (none : Option (Interp E W)) = some i at h; simp at h)
    change (if h' : c2 = y then
        some (⟨x, m1 (h' ▸ m2)⟩ : Interp E W) else none) = some i at h
    by_cases hc : c2 = y
    · rw [dif_pos hc] at h
      injection h with h; subst h; subst hc
      show (d1.fapp d2).cat = some x
      simp [DerivStep.cat, ih1 h1, ih2 h2]
    · rw [dif_neg hc] at h
      simp at h
  | bapp d1 d2 ih1 ih2 =>
    intro i h
    rcases h1 : d1.interp lex with _ | ⟨c1, m1⟩
    · simp [DerivStep.interp, h1] at h
    rcases h2 : d2.interp lex with _ | ⟨c2, m2⟩
    · simp [DerivStep.interp, h1, h2] at h
    simp only [DerivStep.interp] at h
    rw [h1, h2] at h
    rcases c2 with _ | ⟨x, y⟩ | ⟨x, y⟩ <;>
      try (change (none : Option (Interp E W)) = some i at h; simp at h)
    change (if h' : c1 = y then
        some (⟨x, m2 (h' ▸ m1)⟩ : Interp E W) else none) = some i at h
    by_cases hc : c1 = y
    · rw [dif_pos hc] at h
      injection h with h; subst h; subst hc
      show (d1.bapp d2).cat = some x
      simp [DerivStep.cat, ih1 h1, ih2 h2]
    · rw [dif_neg hc] at h
      simp at h
  | fcomp d1 d2 ih1 ih2 =>
    intro i h
    rcases h1 : d1.interp lex with _ | ⟨c1, m1⟩
    · simp [DerivStep.interp, h1] at h
    rcases h2 : d2.interp lex with _ | ⟨c2, m2⟩
    · simp [DerivStep.interp, h1, h2] at h
    simp only [DerivStep.interp] at h
    rw [h1, h2] at h
    rcases c1 with _ | ⟨x, y⟩ | ⟨x, y⟩ <;> rcases c2 with _ | ⟨y', z⟩ | ⟨y', z⟩ <;>
      try (change (none : Option (Interp E W)) = some i at h; simp at h)
    change (if h' : y = y' then
        some (⟨x / z, B m1 (h' ▸ m2)⟩ : Interp E W) else none) = some i at h
    by_cases hc : y = y'
    · rw [dif_pos hc] at h
      injection h with h; subst h; subst hc
      show (d1.fcomp d2).cat = some (x / z)
      simp [DerivStep.cat, ih1 h1, ih2 h2]
    · rw [dif_neg hc] at h
      simp at h
  | bcomp d1 d2 ih1 ih2 =>
    intro i h
    rcases h1 : d1.interp lex with _ | ⟨c1, m1⟩
    · simp [DerivStep.interp, h1] at h
    rcases h2 : d2.interp lex with _ | ⟨c2, m2⟩
    · simp [DerivStep.interp, h1, h2] at h
    simp only [DerivStep.interp] at h
    rw [h1, h2] at h
    rcases c1 with _ | ⟨y, z⟩ | ⟨y, z⟩ <;> rcases c2 with _ | ⟨x, y'⟩ | ⟨x, y'⟩ <;>
      try (change (none : Option (Interp E W)) = some i at h; simp at h)
    change (if h' : y = y' then
        some (⟨x \ z, B m2 (h' ▸ m1)⟩ : Interp E W) else none) = some i at h
    by_cases hc : y = y'
    · rw [dif_pos hc] at h
      injection h with h; subst h; subst hc
      show (d1.bcomp d2).cat = some (x \ z)
      simp [DerivStep.cat, ih1 h1, ih2 h2]
    · rw [dif_neg hc] at h
      simp at h
  | fcompx d1 d2 ih1 ih2 =>
    intro i h
    rcases h1 : d1.interp lex with _ | ⟨c1, m1⟩
    · simp [DerivStep.interp, h1] at h
    rcases h2 : d2.interp lex with _ | ⟨c2, m2⟩
    · simp [DerivStep.interp, h1, h2] at h
    simp only [DerivStep.interp] at h
    rw [h1, h2] at h
    rcases c1 with _ | ⟨x, y⟩ | ⟨x, y⟩ <;> rcases c2 with _ | ⟨y', z⟩ | ⟨y', z⟩ <;>
      try (change (none : Option (Interp E W)) = some i at h; simp at h)
    change (if h' : y = y' then
        some (⟨x \ z, B m1 (h' ▸ m2)⟩ : Interp E W) else none) = some i at h
    by_cases hc : y = y'
    · rw [dif_pos hc] at h
      injection h with h; subst h; subst hc
      show (d1.fcompx d2).cat = some (x \ z)
      simp [DerivStep.cat, ih1 h1, ih2 h2]
    · rw [dif_neg hc] at h
      simp at h
  | ftr d t ih =>
    intro i h
    rcases h1 : d.interp lex with _ | ⟨x, m⟩
    · simp [DerivStep.interp, h1] at h
    simp only [DerivStep.interp, h1] at h
    injection h with h; subst h
    simp [DerivStep.cat, ih h1]
  | btr d t ih =>
    intro i h
    rcases h1 : d.interp lex with _ | ⟨x, m⟩
    · simp [DerivStep.interp, h1] at h
    simp only [DerivStep.interp, h1] at h
    injection h with h; subst h
    simp [DerivStep.cat, ih h1]
  | coord c d1 d2 ih1 ih2 =>
    intro i h
    rcases h1 : d1.interp lex with _ | ⟨c1, m1⟩
    · simp [DerivStep.interp, h1] at h
    rcases h2 : d2.interp lex with _ | ⟨c2, m2⟩
    · simp [DerivStep.interp, h1, h2] at h
    simp only [DerivStep.interp] at h
    rw [h1, h2] at h
    change (if h' : c1 = c2 then
        (if (catToTy c1).isConjoinable then
          some (⟨c1, Coordinator.engineOp c.role (catToTy c1) E W m1 (h' ▸ m2)⟩ : Interp E W)
        else none) else none) = some i at h
    by_cases hc : c1 = c2
    · rw [dif_pos hc] at h
      by_cases hconj : (catToTy c1).isConjoinable
      · rw [if_pos hconj] at h
        injection h with h; subst h; subst hc
        show (DerivStep.coord c d1 d2).cat = some c1
        simp [DerivStep.cat, ih1 h1, ih2 h2]
      · rw [if_neg hconj] at h
        simp at h
    · rw [dif_neg hc] at h
      simp at h

/-! ### Spurious ambiguity

Composition is semantically associative, so left- and right-branching derivations of
the same composition-application chain receive the same interpretation — category and
meaning alike, with no assumption on the lexicon. This is the local source of CCG's
"spurious ambiguity" ([steedman-2000]; the matching-entry tests of [karttunen-1989]
and [pareschi-steedman-1987] exploit exactly this invariance): a chart parser may keep
one derivation per equivalence class, because reassociating `fcomp`/`fapp` (or
`bcomp`/`bapp`) nodes cannot change what a constituent means. -/

set_option maxHeartbeats 800000 in
/-- Reassociating a forward-composition chain preserves interpretation: `B` is
semantically associative. -/
theorem DerivStep.interp_fcomp_assoc {E W : Type} (lex : SemLexicon E W)
    (d₁ d₂ d₃ : DerivStep Atom) :
    (DerivStep.fcomp (.fcomp d₁ d₂) d₃).interp lex
      = (DerivStep.fcomp d₁ (.fcomp d₂ d₃)).interp lex := by
  simp only [DerivStep.interp]
  rcases d₁.interp lex with _ | ⟨c₁, m₁⟩
  · rfl
  rcases d₂.interp lex with _ | ⟨c₂, m₂⟩
  · rfl
  rcases d₃.interp lex with _ | ⟨c₃, m₃⟩
  · rcases c₁ with _ | ⟨x, y⟩ | ⟨x, y⟩
    · rfl
    · rcases c₂ with _ | ⟨y', z⟩ | ⟨y', z⟩
      · rfl
      · by_cases h : y = y' <;> simp [h]
      · rfl
    · rfl
  rcases c₁ with _ | ⟨x, y⟩ | ⟨x, y⟩
  · rcases c₂ with _ | ⟨y', z⟩ | ⟨y', z⟩
    · rfl
    · rcases c₃ with _ | ⟨z', w⟩ | ⟨z', w⟩
      · rfl
      · by_cases h : z = z' <;> simp [h]
      · rfl
    · rfl
  · rcases c₂ with _ | ⟨y', z⟩ | ⟨y', z⟩
    · rfl
    · rcases c₃ with _ | ⟨z', w⟩ | ⟨z', w⟩
      · by_cases h : y = y' <;> simp [h]
      · by_cases hy : y = y' <;> by_cases hz : z = z'
        · subst hy; subst hz; simp
          rfl
        · simp [hy, hz]
        · simp [hy, hz]
        · simp [hy, hz]
      · by_cases h : y = y' <;> simp [h]
    · rfl
  · rcases c₂ with _ | ⟨y', z⟩ | ⟨y', z⟩
    · rfl
    · rcases c₃ with _ | ⟨z', w⟩ | ⟨z', w⟩
      · rfl
      · by_cases h : z = z' <;> simp [h]
      · rfl
    · rfl

/-- Composing before applying is the same as applying twice: `B f g x = f (g x)`,
lifted to derivations. -/
theorem DerivStep.interp_fapp_fcomp {E W : Type} (lex : SemLexicon E W)
    (d₁ d₂ d₃ : DerivStep Atom) :
    (DerivStep.fapp (.fcomp d₁ d₂) d₃).interp lex
      = (DerivStep.fapp d₁ (.fapp d₂ d₃)).interp lex := by
  simp only [DerivStep.interp]
  rcases d₁.interp lex with _ | ⟨c₁, m₁⟩
  · rfl
  rcases d₂.interp lex with _ | ⟨c₂, m₂⟩
  · rfl
  rcases d₃.interp lex with _ | ⟨c₃, m₃⟩
  · rcases c₁ with _ | ⟨x, y⟩ | ⟨x, y⟩
    · rfl
    · rcases c₂ with _ | ⟨y', z⟩ | ⟨y', z⟩
      · rfl
      · by_cases h : y = y' <;> simp [h]
      · rfl
    · rfl
  rcases c₁ with _ | ⟨x, y⟩ | ⟨x, y⟩
  · rcases c₂ with _ | ⟨y', z⟩ | ⟨y', z⟩
    · rfl
    · by_cases h : c₃ = z <;> simp [h]
    · rfl
  · rcases c₂ with _ | ⟨y', z⟩ | ⟨y', z⟩
    · rfl
    · by_cases hy : y = y' <;> by_cases hz : c₃ = z
      · subst hy; subst hz; simp
      · simp [hy, hz, eq_comm]
      · simp [hy, hz, eq_comm]
      · simp [hy, hz, eq_comm]
    · rfl
  · rcases c₂ with _ | ⟨y', z⟩ | ⟨y', z⟩
    · rfl
    · by_cases h : c₃ = z <;> simp [h]
    · rfl

set_option maxHeartbeats 800000 in
/-- Reassociating a backward-composition chain preserves interpretation — the mirror
of `interp_fcomp_assoc`. -/
theorem DerivStep.interp_bcomp_assoc {E W : Type} (lex : SemLexicon E W)
    (d₁ d₂ d₃ : DerivStep Atom) :
    (DerivStep.bcomp (.bcomp d₁ d₂) d₃).interp lex
      = (DerivStep.bcomp d₁ (.bcomp d₂ d₃)).interp lex := by
  simp only [DerivStep.interp]
  rcases d₁.interp lex with _ | ⟨c₁, m₁⟩
  · rfl
  rcases d₂.interp lex with _ | ⟨c₂, m₂⟩
  · rfl
  rcases d₃.interp lex with _ | ⟨c₃, m₃⟩
  · rcases c₁ with _ | ⟨a, b⟩ | ⟨a, b⟩
    · rfl
    · rfl
    · rcases c₂ with _ | ⟨c, e⟩ | ⟨c, e⟩
      · rfl
      · rfl
      · by_cases h : a = e <;> simp [h]
  rcases c₁ with _ | ⟨a, b⟩ | ⟨a, b⟩
  · rcases c₂ with _ | ⟨c, e⟩ | ⟨c, e⟩
    · rfl
    · rfl
    · rcases c₃ with _ | ⟨v, w⟩ | ⟨v, w⟩
      · rfl
      · rfl
      · by_cases h : c = w <;> simp [h]
  · rcases c₂ with _ | ⟨c, e⟩ | ⟨c, e⟩
    · rfl
    · rfl
    · rcases c₃ with _ | ⟨v, w⟩ | ⟨v, w⟩
      · rfl
      · rfl
      · by_cases h : c = w <;> simp [h]
  · rcases c₂ with _ | ⟨c, e⟩ | ⟨c, e⟩
    · rfl
    · rfl
    · rcases c₃ with _ | ⟨v, w⟩ | ⟨v, w⟩
      · by_cases h : a = e <;> simp [h]
      · by_cases h : a = e <;> simp [h]
      · by_cases h₁ : a = e <;> by_cases h₂ : c = w
        · subst h₁; subst h₂; simp
          rfl
        · simp [h₁, h₂]
        · simp [h₁, h₂]
        · simp [h₁, h₂]

/-- Applying twice is the same as backward-composing first — the mirror of
`interp_fapp_fcomp`. -/
theorem DerivStep.interp_bapp_bcomp {E W : Type} (lex : SemLexicon E W)
    (d₁ d₂ d₃ : DerivStep Atom) :
    (DerivStep.bapp (.bapp d₁ d₂) d₃).interp lex
      = (DerivStep.bapp d₁ (.bcomp d₂ d₃)).interp lex := by
  simp only [DerivStep.interp]
  rcases d₁.interp lex with _ | ⟨c₁, m₁⟩
  · rfl
  rcases d₂.interp lex with _ | ⟨c₂, m₂⟩
  · rfl
  rcases d₃.interp lex with _ | ⟨c₃, m₃⟩
  · rcases c₂ with _ | ⟨x, y⟩ | ⟨x, y⟩
    · rfl
    · rfl
    · by_cases h : c₁ = y <;> simp [h]
  rcases c₂ with _ | ⟨x, y⟩ | ⟨x, y⟩
  · rfl
  · rfl
  · rcases c₃ with _ | ⟨v, w⟩ | ⟨v, w⟩
    · by_cases h : c₁ = y <;> simp [h]
    · by_cases h : c₁ = y <;> simp [h]
    · by_cases h₁ : c₁ = y <;> by_cases h₂ : x = w
      · subst h₁; subst h₂; simp
      · simp [h₁, h₂]
      · simp [h₁, h₂]
      · simp [h₁, h₂]

/-- Extract a sentence meaning (category S) from an interpretation result. -/
def getMeaning {E W : Type} (result : Option (Interp E W)) : Option Prop :=
  match result with
  | some ⟨.atom .S, m⟩ => some m
  | _ => none

/-- Extract a predicate meaning (category S/NP) from an interpretation result. -/
def getPredicateMeaning {E W : Type} (result : Option (Interp E W))
    : Option (E → Prop) :=
  match result with
  | some ⟨.rslash (.atom .S) (.atom .NP), m⟩ => some m
  | _ => none

end CCG
