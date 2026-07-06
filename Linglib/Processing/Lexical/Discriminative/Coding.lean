import Linglib.Processing.Lexical.Discriminative.Defs
import Linglib.Core.Computability.Subregular.Language.Boundary
import Linglib.Core.Data.List.Factors

/-!
# Form and meaning coding for the DLM
[heitmeier-chuang-baayen-2026]

The interfaces by which linguistic objects feed the discriminative lexicon
([heitmeier-chuang-baayen-2026] ch. 4-5). A `Linearizable` type yields a
symbol string; its cues are the `k`-factors of the boundary-augmented
string — the same windowing as subregular locality (`Subregular.SLGrammar`)
— and its form vector is the binary cue indicator (Box 4.2: the `C` matrix
holds only 1s and 0s, not counts; the count refinement is where strict
locality's unit margin lives, `Subregular.SLGrammar`). A `SemanticPrimitives`
type yields a multiset of atomic semantic primitives — a lexeme plus
inflectional-function tags (the book's term, ch. 5) — and `conceptualize`
builds its meaning vector as the sum of primitive embeddings: the book's
additive decomposition (eq. 5.3) and its verb for the operation (§16.3).

`conceptualize_analogy` is the general form of proportional analogy: a
linear map respects every multiset-level relation among primitive
decompositions. The stem-exponent fourth proportional of
`Studies/HeitmeierChuangBaayen2026` is the two-primitive case.
-/

namespace Processing.Lexical.Discriminative

open Subregular

/-! ### Form side -/

/-- A form type that linearizes to a symbol string — the domain of the
    DLM's cue coding. -/
class Linearizable (W : Type*) (Sym : outParam Type*) where
  symbols : W → List Sym

instance {α : Type*} : Linearizable (List α) α := ⟨id⟩

variable {W Sym : Type*} [Linearizable W Sym]

/-- The `k`-gram cues of a form: `k`-factors of the boundary-augmented
    symbol string. -/
def cues (k : ℕ) (w : W) : List (Augmented Sym) :=
  List.kFactors k (boundary k (Linearizable.symbols w))

/-- The binary cue-indicator vector over a fixed cue inventory. -/
def cueVector [DecidableEq Sym] (k : ℕ) {N : ℕ} (inv : Fin N → Augmented Sym)
    (w : W) : FormVec N :=
  fun j => if inv j ∈ cues k w then 1 else 0

/-- A lexicon is **discriminable** at width `k` when cue coding separates
    its forms; failures are homographs
    ([heitmeier-chuang-baayen-2026] ch. 7). -/
def Discriminable (k : ℕ) (lexicon : Set W) : Prop :=
  Set.InjOn (cues (Sym := Sym) k) lexicon

/-! ### Meaning side -/

/-- A meaning type with atomic semantic primitives — a lexeme and
    inflectional-function tags. -/
class SemanticPrimitives (M : Type*) (Prim : outParam Type*) where
  primitives : M → Multiset Prim

export SemanticPrimitives (primitives)

variable {M Prim : Type*} [SemanticPrimitives M Prim] {d n : ℕ}

/-- **Conceptualization**: the meaning vector of an object is the sum of its
    primitives' vectors. -/
def conceptualize (emb : Prim → MeaningVec d) (m : M) : MeaningVec d :=
  ((primitives m).map emb).sum

theorem conceptualize_add_of_primitives_add (emb : Prim → MeaningVec d)
    {m₁ m₂ m₃ m₄ : M}
    (h : primitives m₁ + primitives m₂ = primitives m₃ + primitives m₄) :
    conceptualize emb m₁ + conceptualize emb m₂
      = conceptualize emb m₃ + conceptualize emb m₄ := by
  unfold conceptualize
  rw [← Multiset.sum_add, ← Multiset.map_add, h, Multiset.map_add,
      Multiset.sum_add]

/-- **Generic proportional analogy**: any linear map respects every
    multiset-level relation among primitive decompositions. The
    stem-exponent fourth proportional is the case
    `{lex, PL} + {lex', SG} = {lex, SG} + {lex', PL}`. -/
theorem conceptualize_analogy (emb : Prim → MeaningVec d)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) {m₁ m₂ m₃ m₄ : M}
    (h : primitives m₁ + primitives m₂ = primitives m₃ + primitives m₄) :
    G (conceptualize emb m₁) + G (conceptualize emb m₂)
      = G (conceptualize emb m₃) + G (conceptualize emb m₄) := by
  rw [← map_add, conceptualize_add_of_primitives_add emb h, map_add]

end Processing.Lexical.Discriminative
