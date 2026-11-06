/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF

/-!
# Evaluating a formula restricted by a partial assignment

The restriction `φ.restrictBy ρ` of a CNF formula by a partial assignment `ρ`
(`Cslib.Logic.PL.CNF.restrictBy`) drops the clauses that `ρ` satisfies and removes the literals of
the variables that `ρ` fixes from the others. This file relates it to `φ` under the total
assignments that extend `ρ`.

## Main results

* `Cslib.Logic.PL.CNF.eval_restrictBy`: under an assignment that extends `ρ`, the restricted
  formula has the value of `φ`.
* `Cslib.Logic.PL.CNF.length_le_of_mem_restrictBy`: restriction does not widen clauses.
* `Cslib.Logic.PL.CNF.exists_preimage_restrictBy`: a list of clauses of the restricted formula
  comes, clause by clause, from a list of clauses of `φ` with the same value under every
  extension of `ρ`.
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*} {φ : CNF V} {ρ : V → Option Bool} {γ : V → Bool}

/-- Restrict list syntax to one fixed variable, preserving the order and occurrences of the
remaining clauses and literals. This operation does not define a proof calculus. -/
@[expose] def CNF.restrict [DecidableEq V] (φ : CNF V) (v : V) (b : Bool) : CNF V :=
  (φ.filter fun c => (v, b) ∉ c).map (List.filter (· ≠ (v, !b)))

/-- A restricted clause comes from an unsatisfied input clause by removing the false pivot. -/
@[simp] theorem CNF.mem_restrict [DecidableEq V] {v : V} {b : Bool} {c : Clause V} :
    c ∈ φ.restrict v b ↔ ∃ d ∈ φ, (v, b) ∉ d ∧ d.filter (· ≠ (v, !b)) = c := by
  simp [CNF.restrict, and_assoc]

/-- Restrict list syntax by a partial assignment, retaining the order and occurrences of all
surviving clauses and literals. -/
@[expose] def CNF.restrictBy (φ : CNF V) (ρ : V → Option Bool) : CNF V :=
  (φ.filter fun c => decide (∀ l ∈ c, ρ l.1 ≠ some l.2)).map
    (List.filter fun l => decide (ρ l.1 = none))

/-- Membership in list-syntax restriction records an unsatisfied input clause and its filter. -/
@[simp] theorem CNF.mem_restrictBy {c : Clause V} :
    c ∈ φ.restrictBy ρ ↔
      ∃ d ∈ φ, (∀ l ∈ d, ρ l.1 ≠ some l.2) ∧ d.filter (fun l => decide (ρ l.1 = none)) = c := by
  simp [CNF.restrictBy, and_assoc]

/-- Every surviving literal has an unassigned variable. -/
theorem CNF.eq_none_of_mem_restrictBy {c : Clause V} (hc : c ∈ φ.restrictBy ρ)
    {l : Literal V} (hl : l ∈ c) : ρ l.1 = none := by
  obtain ⟨d, -, -, rfl⟩ := CNF.mem_restrictBy.1 hc
  simpa using (List.mem_filter.1 hl).2

/-- Under an assignment that extends `ρ`, a clause that `ρ` does not satisfy has the value of its
literals on the variables that `ρ` does not fix. -/
theorem Clause.eval_filter_of_extends (hγ : ∀ v b, ρ v = some b → γ v = b) {d : Clause V}
    (hd : ∀ l ∈ d, ρ l.1 ≠ some l.2) :
    Clause.eval γ (d.filter fun l => decide (ρ l.1 = none)) = d.eval γ := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  constructor
  · rintro ⟨l, hl, hls⟩
    exact ⟨l, (List.mem_filter.1 hl).1, hls⟩
  · rintro ⟨l, hl, hls⟩
    cases hρ : ρ l.1 with
    | none => exact ⟨l, List.mem_filter.2 ⟨hl, by simp [hρ]⟩, hls⟩
    | some b =>
      rw [← hγ _ _ hρ, hls] at hρ
      exact absurd hρ (hd l hl)

/-- **Restriction preserves the value under extensions**: an assignment that extends `ρ` satisfies
`φ.restrictBy ρ` exactly when it satisfies `φ`. -/
theorem CNF.eval_restrictBy (hγ : ∀ v b, ρ v = some b → γ v = b) :
    (φ.restrictBy ρ).eval γ = φ.eval γ := by
  rw [Bool.eq_iff_iff, CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
  constructor
  · intro h d hd
    by_cases hsat : ∀ l ∈ d, ρ l.1 ≠ some l.2
    · rw [← Clause.eval_filter_of_extends hγ hsat]
      exact h _ (CNF.mem_restrictBy.2 ⟨d, hd, hsat, rfl⟩)
    · push Not at hsat
      obtain ⟨l, hl, hρ⟩ := hsat
      exact (Clause.eval_eq_true_iff γ d).2 ⟨l, hl, hγ _ _ hρ⟩
  · intro h c hc
    obtain ⟨d, hd, hsat, rfl⟩ := CNF.mem_restrictBy.1 hc
    rw [Clause.eval_filter_of_extends hγ hsat]
    exact h d hd

/-- Restriction does not widen clauses. -/
theorem CNF.length_le_of_mem_restrictBy {k : ℕ} (hlen : ∀ c ∈ φ, c.length ≤ k) :
    ∀ c ∈ φ.restrictBy ρ, c.length ≤ k := by
  intro c hc
  obtain ⟨d, hd, -, rfl⟩ := CNF.mem_restrictBy.1 hc
  exact Nat.le_trans (List.length_filter_le _ _) (hlen d hd)

/-- **Preimages of restricted clauses**: a list of clauses of `φ.restrictBy ρ` has, clause by
clause, a list of clauses of `φ` of the same length with the same value under every extension of
`ρ`. -/
theorem CNF.exists_preimage_restrictBy :
    ∀ {ψ : CNF V}, (∀ c ∈ ψ, c ∈ φ.restrictBy ρ) →
      ∃ χ : CNF V, (∀ d ∈ χ, d ∈ φ) ∧ χ.length = ψ.length ∧
        ∀ γ : V → Bool, (∀ v b, ρ v = some b → γ v = b) → χ.eval γ = ψ.eval γ
  | [], _ => ⟨[], by simp, rfl, fun _ _ => rfl⟩
  | c :: ψ, hψ => by
    obtain ⟨d, hd, hsat, rfl⟩ := CNF.mem_restrictBy.1 (hψ c List.mem_cons_self)
    obtain ⟨χ, hχ, hlen, heval⟩ :=
      CNF.exists_preimage_restrictBy fun c hc => hψ c (List.mem_cons_of_mem _ hc)
    refine ⟨d :: χ, ?_, by rw [List.length_cons, List.length_cons, hlen], fun γ hγ => ?_⟩
    · rintro e he
      rcases List.mem_cons.1 he with rfl | he
      exacts [hd, hχ e he]
    · rw [CNF.eval_cons, CNF.eval_cons, Clause.eval_filter_of_extends hγ hsat, heval γ hγ]

end Cslib.Logic.PL
