import Linglib.Logic.Team.Inquisitive
import Mathlib.Tactic.DeriveFintype

/-!
# Ciardelli 2022: Inquisitive Logic — questions under modalities

[ciardelli-2022] builds inquisitive logic on support at information states: questions join
statements in one language through the inquisitive disjunction `\\/`, entailment among
questions is dependency, and the proposition a formula expresses is a downward-closed set of
states (Chapters 2–3). Chapter 8 previews the modal extension. The Kripke modality `□` applied
to a question is a statement whose truth at `w` is the support of the question by the successor
state `R[w]`, so that under the epistemic reading `□?p` says the agent knows whether `p`, and
knowing whether `p` amounts to knowing that `p` or knowing that `¬p`: `□?p ≡ □p ∨ □¬p`, an
instance of the pseudo-commutation `□(φ \\/ ψ) ≡ □φ ∨ □ψ` (§8.2). The properly inquisitive
modality `⊞`, interpreted over a relation from worlds to states `Σ(w)`, is supported when every
state in `Σ(w)` supports its argument; on statements it collapses onto `□`, but on questions it
expresses issue-directed attitudes: `¬□μ ∧ ⊞μ`, [ciardelli-roelofsen-2015]'s wondering about
`μ`, holds when the agent's information does not settle `μ` while every state settling the
agent's issues does. Fig. 8.1 exhibits three inquisitive states of an agent over the four
worlds for `p` and `q`: in (a) the agent knows that `p` and has no open issue, in (b) knows
nothing and is interested in whether `p`, in (c) knows nothing and is interested in whether
`q`; the agent knows whether `p` in (a), wonders whether `p` in (b), and neither in (c). The
same state (b) shows that `⊞` does not pseudo-commute: `⊞?p` holds there while `⊞p ∨ ⊞¬p`
fails (§8.3).

The substrate `Logic/Team/Inquisitive.lean` carries the logic — support, persistence,
truth-conditionality, the proposition expressed and the modal validities. This file states
the chapter's illustrations at it: `nec_polarQ` is the knowing-whether equation, `fig81a`,
`fig81b` and `fig81c` are the three models of Fig. 8.1 with `wonders` the formula of wondering,
and the three classifications and the failure of pseudo-commutation for `⊞` are decided on
them.

## References

* [I. Ciardelli, *Inquisitive Logic: Consequence and Inference in the Realm of Questions*
  (2022)][ciardelli-2022]
* [I. Ciardelli and F. Roelofsen, *Inquisitive dynamic epistemic logic*
  (2015)][ciardelli-roelofsen-2015]
-/

namespace Ciardelli2022

open ModalLogic.Inquisitive

/-! ### Knowing whether (§8.2) -/

variable {W A : Type*} [DecidableEq W] (M : InquisitiveModalModel W A) (φ : Formula A)
  (s : Finset W)

/-- (3b): knowing whether `φ` is knowing that `φ` or knowing that `¬φ`, the polar instance of
`support_nec_inqDisj`. -/
theorem nec_polarQ :
    support M (.nec φ.polarQ) s ↔ support M ((Formula.nec φ).disj (.nec φ.neg)) s :=
  support_nec_inqDisj M φ φ.neg s

/-- `¬□μ ∧ ⊞μ`: the agent wonders about `μ` ([ciardelli-roelofsen-2015]; §8.3). -/
abbrev wonders (μ : Formula A) : Formula A := (Formula.nec μ).neg.conj (.ent μ)

/-! ### Fig. 8.1: knowing, wondering and neither (§8.3) -/

/-- The four worlds `w_pq`, `w_p¬q`, `w_¬pq`, `w_¬p¬q` of Fig. 8.1. -/
inductive World
  | pq | pnq | npq | npnq
  deriving DecidableEq, Fintype

inductive Atom
  | p | q
  deriving DecidableEq

/-- The valuation of Fig. 8.1. -/
def val : Atom → World → Bool
  | .p, .pq | .p, .pnq | .q, .pq | .q, .npq => true
  | _, _ => false

/-- `p` as a formula. -/
abbrev p : Formula Atom := .atom .p

/-- Fig. 8.1a: `Σ(w) = {{w_pq, w_p¬q}}↓`, the agent knows that `p` and has no open issue. -/
def fig81a : InquisitiveModalModel World Atom :=
  ⟨fun _ => ({.pq, .pnq} : Finset World).powerset, val⟩

/-- Fig. 8.1b: `Σ(w) = {{w_pq, w_p¬q}, {w_¬pq, w_¬p¬q}}↓`, the agent knows nothing and is
interested in whether `p`. -/
def fig81b : InquisitiveModalModel World Atom :=
  ⟨fun _ => ({.pq, .pnq} : Finset World).powerset ∪ ({.npq, .npnq} : Finset World).powerset,
    val⟩

/-- Fig. 8.1c: `Σ(w) = {{w_pq, w_¬pq}, {w_p¬q, w_¬p¬q}}↓`, the agent knows nothing and is
interested in whether `q`. -/
def fig81c : InquisitiveModalModel World Atom :=
  ⟨fun _ => ({.pq, .npq} : Finset World).powerset ∪ ({.pnq, .npnq} : Finset World).powerset,
    val⟩

/-- In (a) the agent knows that `p`, hence knows whether `p`. -/
theorem fig81a_knows : ∀ w, support fig81a (.nec p) {w} ∧ support fig81a (.nec p.polarQ) {w} := by
  decide

/-- In (b) the agent wonders whether `p`. -/
theorem fig81b_wonders : ∀ w, support fig81b (wonders p.polarQ) {w} := by decide

/-- In (c) the agent neither knows whether `p` nor wonders about it. -/
theorem fig81c_neither :
    ∀ w, support fig81c ((Formula.nec p.polarQ).neg.conj (Formula.ent p.polarQ).neg) {w} := by
  decide

/-- `⊞` does not pseudo-commute: in (b) the agent entertains whether `p` without entertaining
`p` or entertaining `¬p`. -/
theorem fig81b_ent_polarQ_not_disj :
    ∀ w, support fig81b (.ent p.polarQ) {w} ∧
      ¬ support fig81b ((Formula.ent p).disj (.ent p.neg)) {w} := by
  decide

end Ciardelli2022
