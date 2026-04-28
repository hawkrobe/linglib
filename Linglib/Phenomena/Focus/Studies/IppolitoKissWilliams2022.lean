import Linglib.Theories.Semantics.Questions.Probabilistic

/-!
# Ippolito, Kiss & Williams 2022: Discourse Function of Adversative Conjunction
@cite{ippolito-kiss-williams-2022}

The Sinn und Bedeutung 26 paper that introduces the doxastic-evidential
notions of **SUPPORT**, **AGREEMENT**, and **DISAGREEMENT** which the
follow-up paper @cite{ippolito-kiss-williams-2025} reuses for discourse
*only*. The 2022 paper itself targets adversative *but*; the SUPPORT /
AGREE / DISAGREE apparatus is the part of that account both papers share.

This file currently formalizes only the shared apparatus — the *but*
analysis itself is not yet formalized. The recap below follows the
conceptual statement that @cite{ippolito-kiss-williams-2025} §4 (p. 225)
gives explicitly: *"Following Ippolito et al. (2022) we define the
notion of AGREEMENT (and DISAGREEMENT) and the notion of SUPPORT, on
which the former notion is based."*

## SUPPORT

A sentence `S` supports a proposition `r` (in context `c`) iff some
alternative `q ∈ ⟦S⟧` is doxastically grounded for the speaker
(`dox_sp ⊆ q`) and provides evidence for `r`. The doxastic anchor
is what derives the @cite{ippolito-kiss-williams-2025} §5.2
interrogative-left-argument restriction: a speaker who doesn't believe
any alternative cannot use the sentence to support anything.

**Project-canonical refinement.** The original 2022 statement leaves
"q provides evidence for r" deliberately informal. We formalize it as
`IsPositiveEvidence q r μ` (Bayesian conditional-probability shift,
see `Theories/Semantics/Questions/Probabilistic.lean`). This is a
strengthening; the §5.2 architectural derivations carry over but rest
on the strengthened relation. A flavor-agnostic version parameterized
by an abstract evidence relation could be added if a sibling theory
needs it.

## AGREEMENT / DISAGREEMENT

Two sentences agree on a QUD if they support a common alternative; they
disagree if each supports some alternative but no shared one witnesses
agreement. Both relations are symmetric in their `S`/`S'` arguments.

-/

namespace Phenomena.Focus.Studies.IppolitoKissWilliams2022

open Core Core.Question Semantics.Questions.Probabilistic

variable {W : Type*}

/-! ## SUPPORT (paper ex. (13) of @cite{ippolito-kiss-williams-2025},
    restating the 2022 definition) -/

/-- `S` **supports** `r` from doxastic state `dox` under prior `μ`:
    some alternative `q ∈ alt S` is doxastically grounded (`dox ⊆ q`)
    and provides positive evidence for `r`.

    Refines the 2022 informal "q provides evidence for r" as
    `IsPositiveEvidence` (conditional-probability shift). -/
def Supports (dox : Set W) (S : Question W) (r : Set W) (μ : PMF W) : Prop :=
  ∃ q ∈ alt S, dox ⊆ q ∧ IsPositiveEvidence q r μ

/-- An info-seeking speaker — one who doesn't believe any alternative of
    `S` — cannot use `S` to support anything. The architectural
    derivation of @cite{ippolito-kiss-williams-2025} §5.2's
    interrogative-left-argument restriction: the failure isn't a
    clause-type filter but a doxastic consequence of `Supports`. -/
theorem Supports.of_no_belief_fails {dox : Set W} {S : Question W}
    {r : Set W} {μ : PMF W}
    (h : ∀ q ∈ alt S, ¬ (dox ⊆ q)) :
    ¬ Supports dox S r μ := by
  rintro ⟨q, hq, hdox, _⟩
  exact h q hq hdox

/-- `Supports dox S r μ` exposes a doxastically-grounded alternative
    of `S` containing `dox`. The bridge from probabilistic support to
    pure inquisitive `Resolves`-style witnesses. -/
theorem Supports.exists_dox_alt {dox : Set W} {S : Question W}
    {r : Set W} {μ : PMF W}
    (h : Supports dox S r μ) :
    ∃ p ∈ alt S, dox ⊆ p := by
  obtain ⟨p, hp, hdox, _⟩ := h
  exact ⟨p, hp, hdox⟩

/-! ## AGREEMENT and DISAGREEMENT (paper ex. (14) of
    @cite{ippolito-kiss-williams-2025}, restating the 2022 definitions) -/

/-- Two sentences `S` and `S'` **agree** on QUD `Q` from doxastic state
    `dox` iff some alternative `α ∈ alt Q` is supported by both. -/
def Agree (dox : Set W) (S S' Q : Question W) (μ : PMF W) : Prop :=
  ∃ α ∈ alt Q, Supports dox S α μ ∧ Supports dox S' α μ

/-- Two sentences `S` and `S'` **disagree** on QUD `Q` from doxastic
    state `dox` iff each supports some answer but no shared alternative
    witnesses agreement. -/
def Disagree (dox : Set W) (S S' Q : Question W) (μ : PMF W) : Prop :=
  (∃ α ∈ alt Q, Supports dox S α μ) ∧
  (∃ α ∈ alt Q, Supports dox S' α μ) ∧
  ¬ Agree dox S S' Q μ

/-- `Agree` is symmetric in its `S`/`S'` arguments. -/
theorem Agree.symm {dox : Set W} {S S' Q : Question W} {μ : PMF W}
    (h : Agree dox S S' Q μ) : Agree dox S' S Q μ := by
  obtain ⟨α, hMem, hS, hS'⟩ := h
  exact ⟨α, hMem, hS', hS⟩

/-- `Disagree` is symmetric in its `S`/`S'` arguments. -/
theorem Disagree.symm {dox : Set W} {S S' Q : Question W} {μ : PMF W}
    (h : Disagree dox S S' Q μ) : Disagree dox S' S Q μ := by
  obtain ⟨hS, hS', hNotAgree⟩ := h
  exact ⟨hS', hS, fun hAgree => hNotAgree hAgree.symm⟩

end Phenomena.Focus.Studies.IppolitoKissWilliams2022
