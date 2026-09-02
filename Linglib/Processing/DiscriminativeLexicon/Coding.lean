import Linglib.Processing.DiscriminativeLexicon.Defs
import Linglib.Phonology.Subregular.Boundary
import Linglib.Core.Data.List.Factors
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Form and meaning coding for the DLM

How linguistic objects feed the discriminative lexicon ([heitmeier-chuang-baayen-2026] ch. 4
and 5). A form is a symbol string; its **cues** are the `n`-grams of the string padded with one
boundary symbol on each side (`#a aa ap p#`, `#aa aap ap#`), and its row of the form matrix `C`
is the multiple-hot indicator of those cues over the cue inventory (Box 4.2: `C` holds only 1s
and 0s). The padding is one boundary symbol whatever the width, unlike the `k − 1` of strictly
local grammars (`boundary`), so DLM trigrams are not the 3-factors of subregular phonology. A
meaning is a multiset of atomic **semantic primitives**, a lexeme and its inflectional functions,
and **conceptualization** builds its vector as the sum of the primitives' vectors (eq. 5.3): a
novel inflected word is conceptualized from known primitives (eq. 5.5, §16.3). Conceptualization
is additive in the multiset by construction, which is what makes a linear mapping respect
proportional analogy (`Studies/HeitmeierChuangBaayen2026`).

## Main declarations

- `cues k w`: the `k`-gram cues of the string `w`.
- `multiHot inv p`: the indicator row of the units satisfying `p` over an inventory `inv`.
- `cueVector k inv w`: the row of `C` for `w`.
- `conceptualize emb`: the additive map from primitive multisets to meaning vectors;
  `imputed σ ε` is the resulting semantics of a lexeme at a cell.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

namespace DiscriminativeLexicon

variable {Sym : Type*}

/-! ### Form side -/

/-- The `k`-gram cues of a form: the `k`-factors of the string padded with one boundary symbol
on each side, JudiLing's `make_cue_matrix` with `grams = k`. -/
def cues (k : ℕ) (w : List Sym) : List (Augmented Sym) := (boundary 2 w).kFactors k

/-- The multiple-hot row over an inventory `inv` of the units satisfying `p`. -/
def multiHot {N : ℕ} {α : Type*} (inv : Fin N → α) (p : α → Prop) [DecidablePred p] :
    Fin N → ℝ :=
  fun j => if p (inv j) then 1 else 0

/-- The row of the form matrix `C` for the form `w`: the indicator of its cues over the cue
inventory. -/
def cueVector [DecidableEq Sym] (k : ℕ) {N : ℕ} (inv : Fin N → Augmented Sym) (w : List Sym) :
    FormVec N :=
  multiHot inv (· ∈ cues k w)

/-! ### Meaning side -/

variable {Prim V : Type*} [AddCommMonoid V]

/-- **Conceptualization**: the meaning vector of a multiset of semantic primitives is the sum of
the primitives' vectors, additive in the multiset. -/
def conceptualize (emb : Prim → V) : Multiset Prim →+ V :=
  Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom emb)

@[simp] theorem conceptualize_apply (emb : Prim → V) (ps : Multiset Prim) :
    conceptualize emb ps = (ps.map emb).sum := rfl

/-- Conceptualizing a lexeme with one inflectional function is the sum of their vectors — the
imputed additive semantics of a paradigm cell (eq. 5.3). -/
@[simp] theorem conceptualize_pair {A B : Type*} (σ : A → V) (ε : B → V) (a : A) (b : B) :
    conceptualize (Sum.elim σ ε) {Sum.inl a, Sum.inr b} = σ a + ε b := by
  simp

/-- **Imputed semantics**: the meaning of a lexeme at a cell conceptualized from the lexeme's
vector and the inflectional function's vector (eq. 5.3; the constructed meaning-to-form route of
Table 12.7, which §16.6 calls imputed embeddings for stems and exponents). -/
def imputed {A B : Type*} (σ : A → V) (ε : B → V) (a : A) (b : B) : V :=
  conceptualize (Sum.elim σ ε) {Sum.inl a, Sum.inr b}

@[simp] theorem imputed_apply {A B : Type*} (σ : A → V) (ε : B → V) (a : A) (b : B) :
    imputed σ ε a b = σ a + ε b :=
  conceptualize_pair σ ε a b

end DiscriminativeLexicon
