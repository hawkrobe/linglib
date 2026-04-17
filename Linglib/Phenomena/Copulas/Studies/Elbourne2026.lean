import Linglib.Theories.Semantics.Gradability.Classification

/-!
# Elbourne (2026): Adjectives without syntactic categories
@cite{elbourne-2026}

Published online: 12 March 2026, *Natural Language & Linguistic Theory* 44:17.

Adjectives are uniformly type ⟨et,et⟩ — functions from noun denotations
to noun denotations. This eliminates Predicate Modification for
adjective-noun combination (FA suffices) and supports the program of
eliminating syntactic categories in favor of semantic types
("Meaning-Dependent Grammar", building on @cite{elbourne-2024}).

## Key result

`Classification.lean` already defines `AdjMeaning W E = Property W E →
Property W E`, which IS the ⟨et,et⟩ type. The Kamp hierarchy there
(intersective, subsective, privative) classifies adjectives by meaning
postulates *within* that type — not by assigning different types to
different classes. The present file makes this explicit and adds
Elbourne's copula semantics.

## Copula BE

Elbourne's copula takes a tense relation R and an ⟨et,et⟩ adjective G,
applies G to the trivially true noun `λt.λx. ⊤`, and existentially
quantifies over a time satisfying R. This contrasts with
@cite{partee-1987}'s BE (a type-shifting operation `⟨⟨e,t⟩,t⟩ → ⟨e,t⟩`
for nominal predication) — a different function for a different
construction.

## Sections

1. ⟨et,et⟩ adjective meanings (intersective)
2. Copula BE
3. FA-sufficiency: FA on ⟨et,et⟩ = PM on ⟨e,t⟩; PM limitation
4. "Fido was cute" derivation
5. Connection to Classification hierarchy
6. Former: non-subsective `AdjMeaning` + PM failure + end-to-end chain
7. Compulsory E_R: attributive-only adjectives
-/

namespace Elbourne2026

open Semantics.Gradability.Classification
  (Property AdjMeaning isIntersective isSubsective)

-- ════════════════════════════════════════════════════════
-- § 1. ⟨et,et⟩ Adjective Denotations
-- ════════════════════════════════════════════════════════

section AdjDenotations

variable {I E : Type*}

/-- The trivially true noun meaning: `λt.λx. ⊤`.
    The copula applies an ⟨et,et⟩ adjective to this to extract
    the adjective's inherent content. -/
def trivialNoun : Property I E := λ _ _ => true

/-- Intersective ⟨et,et⟩ adjective: `λN.λt.λx. N(t)(x) ∧ Q(t)(x)`.

    @cite{elbourne-2026} (24b)/(59):
    `/cute/ :: λf⟨e,it⟩.λx.λt. f(x)(t) & cute(x)(t)` -/
def intersective (Q : Property I E) : AdjMeaning I E :=
  λ N t x => N t x && Q t x

/-- Applying an intersective adjective to the trivial noun recovers
    the underlying property Q. This is what the copula exploits. -/
theorem intersective_trivial (Q : Property I E) :
    intersective Q trivialNoun = Q := by
  funext t x; simp [intersective, trivialNoun]

end AdjDenotations

-- ════════════════════════════════════════════════════════
-- § 2. Copula BE
-- ════════════════════════════════════════════════════════

section Copula

variable {I E : Type*}

/-- Elbourne's copula BE.

    Takes a tense relation `R` and an ⟨et,et⟩ adjective `G`, applies G
    to the trivial noun, and existentially quantifies over a time
    satisfying R.

    @cite{elbourne-2026} (8)/(27c):
    `BE :: λR⟨i,it⟩.λG⟨eit,eit⟩.λx.λt. ∃t'(R(t')(t) & G(λy.λt''.⊤)(x)(t'))` -/
def copulaBE (R : I → I → Prop) (G : AdjMeaning I E)
    (x : E) (t : I) : Prop :=
  ∃ t', R t' t ∧ G trivialNoun t' x = true

/-- BE applied to an intersective adjective produces the expected
    truth conditions: `∃t'. R(t',t) ∧ Q(t')(x)`. -/
theorem copulaBE_intersective (Q : Property I E) (R : I → I → Prop)
    (x : E) (t : I) :
    copulaBE R (intersective Q) x t ↔
    ∃ t', R t' t ∧ Q t' x = true := by
  simp [copulaBE, intersective_trivial]

end Copula

-- ════════════════════════════════════════════════════════
-- § 3. FA-Sufficiency
-- ════════════════════════════════════════════════════════

section FASufficiency

variable {I E : Type*}

/-- **Core theorem**: FA on ⟨et,et⟩ adjective = PM on ⟨e,t⟩ property.

    The LHS is the FA attributive derivation: an intersective ⟨et,et⟩
    adjective applied to a noun via function application. The RHS is
    Predicate Modification: conjunction of the underlying adjective
    property with the noun. Since FA reproduces PM for intersective
    adjectives, PM is unnecessary for adjective-noun combination.

    @cite{elbourne-2026} (25)–(26):
    `⟦cute donkey⟧ = λx.λt. donkey(x)(t) & cute(x)(t)` -/
theorem fa_eq_pm (Q N : Property I E) :
    intersective Q N = (λ t x => Q t x && N t x) := by
  funext t x; exact Bool.and_comm (N t x) (Q t x)

/-- PM always produces **intersective** results: the composition
    `λN.λt.λx. A(t)(x) ∧ N(t)(x)` satisfies `Classification.isIntersective`
    with witness `A`. This means PM is too restrictive even for merely
    subsective adjectives like `skillful` — not just non-subsective ones.

    @cite{elbourne-2026} (p. 13): under ⟨e,t⟩, "a rule like Predicate
    Modification is presumably necessary; but this would impose the
    intersective semantics that we have just seen is inappropriate for
    merely subsective adjectives." -/
theorem pm_always_intersective (A : Property I E) :
    isIntersective (λ N t x => A t x && N t x) :=
  ⟨A, λ _ _ _ => rfl⟩

/-- Corollary: PM always yields subsective results (`A ∧ N` entails
    `N`). Follows from `pm_always_intersective` via the hierarchy
    (`intersective → subsective`), but also provable directly. -/
theorem pm_always_subsective (A N : Property I E) (t : I) (x : E)
    (h : (A t x && N t x) = true) : N t x = true := by
  simp only [Bool.and_eq_true] at h; exact h.2

end FASufficiency

-- ════════════════════════════════════════════════════════
-- § 4. "Fido was cute" Derivation
-- ════════════════════════════════════════════════════════

section Derivation

variable {I E : Type*}

/-- Truth conditions for "Fido was cute":
    `∃t'(t' < t ∧ cute(Fido)(t'))`.

    Step-by-step derivation (@cite{elbourne-2026} (28)–(30)):
    1. `⟦BE PAST⟧ = λG.λx.λt. ∃t'(t' < t ∧ G(⊤)(x)(t'))`
    2. `⟦[BE PAST] cute⟧ = λx.λt. ∃t'(t' < t ∧ cute(x)(t'))`
    3. `⟦Fido [[BE PAST] cute]⟧ = λt. ∃t'(t' < t ∧ cute(Fido)(t'))` -/
theorem fido_was_cute (Q : Property I E) (lt : I → I → Prop)
    (fido : E) (t : I) :
    copulaBE lt (intersective Q) fido t ↔
    ∃ t', lt t' t ∧ Q t' fido = true := by
  simp [copulaBE, intersective_trivial]

end Derivation

-- ════════════════════════════════════════════════════════
-- § 5. Connection to Classification Hierarchy
-- ════════════════════════════════════════════════════════

section HierarchyConnection

variable {I E : Type*}

/-- Intersective ⟨et,et⟩ adjectives satisfy
    `Classification.isIntersective`. The witness is the underlying
    property Q. -/
theorem intersective_is_classified (Q : Property I E) :
    isIntersective (intersective Q) :=
  ⟨Q, λ N t x => Bool.and_comm (N t x) (Q t x)⟩

/-- Intersective ⟨et,et⟩ adjectives are subsective:
    `cute N` entails `N`. -/
theorem intersective_is_subsective (Q : Property I E) :
    isSubsective (intersective Q) := by
  intro N t x h
  simp only [intersective, Bool.and_eq_true] at h
  exact h.1

/-- Attributive combination (FA on ⟨et,et⟩ adj + noun) and predicative
    extraction (copula applies adj to trivial noun) use the SAME
    adjective denotation. The copula adds tense; FA does not.

    "cute donkey" (attributive) = `intersective Q donkey`
    "Fido was cute" (predicative) uses `intersective Q` applied to `⊤`

    The adjective meaning `intersective Q` is identical in both. -/
theorem attributive_predicative_same_denotation (Q : Property I E)
    (noun : Property I E) :
    -- Attributive: adj applied to noun via FA
    let attr := intersective Q noun
    -- Predicative: copula extracts Q by applying adj to trivial noun
    let pred := intersective Q trivialNoun
    -- The extracted predicate equals Q itself
    pred = Q ∧
    -- The attributive result conjoins Q with the noun
    attr = (λ t x => noun t x && Q t x) := by
  exact ⟨intersective_trivial Q, rfl⟩

end HierarchyConnection

-- ════════════════════════════════════════════════════════
-- § 6. Former — Non-Subsective ⟨et,et⟩ Adjective
-- ════════════════════════════════════════════════════════

section Former

/-- Concrete 2-time model witnessing that `former` is non-subsective:
    Joe was a judge (at `past`) but is not a judge (at `now`),
    so Joe is a former judge at `now` — yet he is not a judge. -/
private inductive T2 | past | now deriving DecidableEq
private inductive E1 | joe deriving DecidableEq

private def judge : Property T2 E1
  | .past, .joe => true
  | .now, .joe => false

/-- Non-subsective ⟨et,et⟩ adjective: `former`.
    Computable over a finite list of time points via `List.any`.

    `formerAdj times ltb N t x = true` iff some earlier time `t'`
    satisfies `ltb t' t ∧ N t' x` and `N t x = false`.

    @cite{elbourne-2026} (44)/(60):
    `λf⟨e,it⟩.λx.λt. ∃t'(< (t')(t) & f(x)(t') & ¬f(x)(t))` -/
def formerAdj {I E : Type*} (times : List I)
    (ltb : I → I → Bool) : AdjMeaning I E :=
  λ N t x => times.any (λ t' => ltb t' t && N t' x) && !(N t x)

private def ltb2 : T2 → T2 → Bool
  | .past, .now => true
  | _, _ => false

private def allT2 : List T2 := [.past, .now]

/-- `formerAdj` produces the expected truth value at `(now, joe)`:
    Joe is a former judge. -/
theorem former_adj_holds :
    formerAdj allT2 ltb2 judge .now .joe = true := by native_decide

/-- `formerAdj` is not subsective — connecting directly to
    `Classification.isSubsective`. This is a genuine `AdjMeaning`,
    so it integrates with the full Classification hierarchy. -/
theorem former_adj_not_subsective :
    ¬isSubsective (formerAdj (E := E1) allT2 ltb2) := by
  intro h
  have := h judge .now .joe former_adj_holds
  simp [judge] at this

-- ────────────────────────────────────────────────────
-- PM failure: why ⟨e,t⟩ theory cannot handle former
-- ────────────────────────────────────────────────────

/-- No ⟨e,t⟩ adjective property, combined with `judge` via PM, can
    yield a true result at `(now, joe)` — because `judge(now)(joe)`
    is `false` and PM includes the noun in the conjunction.

    Contrast with `former_adj_holds`: the ⟨et,et⟩ theory CAN
    produce a true `former judge` result while `judge` is false. -/
theorem pm_cannot_produce_former :
    ¬∃ (A : Property T2 E1),
      (A .now .joe && judge .now .joe) = true := by
  intro ⟨_, h⟩; simp [judge] at h

/-- **End-to-end chain**: the ⟨et,et⟩ theory strictly subsumes
    ⟨e,t⟩ + PM for adjective-noun composition.

    1. For intersective adjectives, FA on ⟨et,et⟩ reproduces PM
       (`fa_eq_pm`).
    2. For non-subsective adjectives, ⟨et,et⟩ succeeds
       (`former_adj_holds` ∧ `judge .now .joe = false`).
    3. For non-subsective adjectives, ⟨e,t⟩ + PM fails
       (`pm_cannot_produce_former`). -/
theorem etet_subsumes_et :
    (∀ (Q N : Property T2 E1),
      intersective Q N = (λ t x => Q t x && N t x)) ∧
    (formerAdj allT2 ltb2 judge .now .joe = true ∧ judge .now .joe = false) ∧
    (¬∃ (A : Property T2 E1), (A .now .joe && judge .now .joe) = true) :=
  ⟨fa_eq_pm, ⟨former_adj_holds, rfl⟩, pm_cannot_produce_former⟩

/-- Applying `formerAdj` to the trivial noun gives `false` everywhere:
    `⊤` can never "formerly" hold (it always holds). The copula applies
    adjectives to `⊤`, so `former` in predicative position would be
    vacuously false — a semantic reason for the attributive-only
    restriction (complementing compulsory E_R in § 7). -/
theorem formerAdj_trivialNoun {I E : Type*} (times : List I)
    (ltb : I → I → Bool) (t : I) (x : E) :
    formerAdj times ltb trivialNoun t x = false := by
  simp [formerAdj, trivialNoun]

end Former

-- ════════════════════════════════════════════════════════
-- § 7. Compulsory E_R (Attributive-Only Adjectives)
-- ════════════════════════════════════════════════════════

section CompulsoryER

/-- Whether an adjective requires a noun argument (E_R feature status).

    Under the ⟨et,et⟩ theory ALL adjectives are the same type; the
    attributive/predicative distinction is syntactic, not semantic.
    - **Optional E_R** (`cute`, `tall`): attributive or predicative.
    - **Compulsory E_R** (`former`, `mere`, `alleged`): attributive only.

    @cite{elbourne-2026} § 3.2: the copula derivation requires the
    adjective to appear WITHOUT an E_R feature; adjectives bearing
    compulsory E_R cannot be taken as argument by [BE PAST]. -/
inductive ERStatus where
  | optional    -- cute, tall, happy: both positions
  | compulsory  -- former, mere, alleged: attributive only
  deriving DecidableEq, Repr

def canBePredicate (s : ERStatus) : Bool := s == .optional

theorem cute_can_be_predicative : canBePredicate .optional = true := rfl
theorem former_attributive_only : canBePredicate .compulsory = false := rfl

end CompulsoryER

end Elbourne2026
