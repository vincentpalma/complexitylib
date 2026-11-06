/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.Finset.Card

/-!
# Finite clauses

Mathematical clauses are finite sets of literals. Equality ignores order and repetition, and width
is cardinality. `Clause` and `CNF` remain list syntax for algorithms and encodings.

## Main definitions

* `Cslib.Logic.PL.FiniteClause`: a finite set of literals.
* `Cslib.Logic.PL.FiniteClause.eval`: satisfaction as a Boolean.
* `Cslib.Logic.PL.FiniteClause.width`: the number of distinct literals.

## Main results

* `Cslib.Logic.PL.FiniteClause.eval_toFinset`: forgetting literal order and repetition preserves
  satisfaction of list syntax.
-/

public section

namespace Cslib.Logic.PL

/-- A mathematical clause, with no ordering or repeated literals. -/
abbrev FiniteClause (V : Type*) := Finset (Literal V)

namespace FiniteClause

variable {V : Type*}

/-- An assignment satisfies a clause when it makes one of its literals true. -/
@[expose] def Sat (c : FiniteClause V) (σ : V → Bool) : Prop :=
  ∃ l ∈ c, σ l.1 = l.2

/-- Satisfaction of a finite clause is decidable. -/
instance (c : FiniteClause V) (σ : V → Bool) : Decidable (c.Sat σ) :=
  inferInstanceAs (Decidable (∃ l ∈ c, σ l.1 = l.2))

/-- Boolean evaluation of a finite clause. -/
@[expose] def eval (σ : V → Bool) (c : FiniteClause V) : Bool := decide (c.Sat σ)

/-- A clause evaluates to true exactly when it has a true literal. -/
@[simp] theorem eval_eq_true_iff (σ : V → Bool) (c : FiniteClause V) :
    c.eval σ = true ↔ ∃ l ∈ c, σ l.1 = l.2 := by
  exact ⟨of_decide_eq_true, fun h => decide_eq_true h⟩

/-- The empty clause is false under every assignment. -/
@[simp] theorem eval_empty (σ : V → Bool) : (∅ : FiniteClause V).eval σ = false := rfl

/-- A singleton clause has the value of its literal. -/
@[simp] theorem eval_singleton (σ : V → Bool) (l : Literal V) :
    FiniteClause.eval σ {l} = l.eval σ := by
  rw [Bool.eq_iff_iff, eval_eq_true_iff, Literal.eval_eq_true_iff]
  simp

/-- The width of a mathematical clause is its number of literals. -/
@[expose] def width (c : FiniteClause V) : ℕ := c.card

/-- Adding at most one literal increases width by at most one. -/
theorem width_le_width_add_one {c d : FiniteClause V} {x : Literal V}
    (h : ∀ l ∈ c, l ∈ d ∨ l = x) : c.width ≤ d.width + 1 := by
  classical
  refine (Finset.card_le_card (t := insert x d) fun l hl => ?_).trans
    (Finset.card_insert_le _ _)
  rcases h l hl with h | rfl
  · exact Finset.mem_insert_of_mem h
  · exact Finset.mem_insert_self _ _

/-- Forgetting order and repetition preserves satisfaction of list clause syntax. -/
@[simp] theorem eval_toFinset [DecidableEq V] (σ : V → Bool) (c : Clause V) :
    FiniteClause.eval σ c.toFinset = c.eval σ := by
  rw [Bool.eq_iff_iff, eval_eq_true_iff, Clause.eval_eq_true_iff]
  simp only [List.mem_toFinset]

end FiniteClause

namespace Clause

variable {V : Type*} [DecidableEq V]

/-- Compare list clauses by their literals, independently of order and repetition.
This is an executable comparison for representations of finite clauses. -/
@[expose] def sameLiterals (c d : Clause V) : Bool :=
  c.all (fun l => decide (l ∈ d)) && d.all (fun l => decide (l ∈ c))

/-- The executable comparison tests equality of the represented finite clauses. -/
@[simp] theorem sameLiterals_eq_true_iff (c d : Clause V) :
    c.sameLiterals d = true ↔ c.toFinset = d.toFinset := by
  simp only [sameLiterals, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hcd, hdc⟩
    apply Finset.Subset.antisymm
    · intro l hl
      exact List.mem_toFinset.2 (hcd l (List.mem_toFinset.1 hl))
    · intro l hl
      exact List.mem_toFinset.2 (hdc l (List.mem_toFinset.1 hl))
  · intro h
    constructor
    · intro l hl
      exact List.mem_toFinset.1 (h ▸ List.mem_toFinset.2 hl)
    · intro l hl
      exact List.mem_toFinset.1 (h.symm ▸ List.mem_toFinset.2 hl)

end Clause

end Cslib.Logic.PL
