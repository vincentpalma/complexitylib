/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Restriction
public import Complexity.Logics.Propositional.Resolution.Proof

/-!
# Restriction and the syntax boundary

Mathematical restriction agrees with interpretation of restricted list syntax. Restriction
preserves satisfaction under total assignments extending the partial one. The line-count and
width guarantees for restricted proofs are in `Resolution.Proof`.

## Main results

* `Cslib.Logic.PL.CNF.toClauseSet_restrict`, `Cslib.Logic.PL.CNF.toClauseSet_restrictBy`:
  list-syntax restriction agrees with mathematical restriction.
* `Cslib.Logic.PL.ClauseSet.eval_restrictBy`: evaluation under extending assignments.
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-- Restriction of syntax commutes with its interpretation as a clause set. -/
@[simp] theorem CNF.toClauseSet_restrict (φ : CNF V) (v : V) (b : Bool) :
    (φ.restrict v b).toClauseSet = φ.toClauseSet.restrict v b := by
  ext c
  constructor
  · intro hc
    obtain ⟨d, hd, rfl⟩ := CNF.mem_toClauseSet.1 hc
    obtain ⟨e, he, hv, rfl⟩ := CNF.mem_restrict.1 hd
    refine ClauseSet.mem_restrict.2 ⟨e.toFinset, CNF.mem_toClauseSet.2 ⟨e, he, rfl⟩,
      by simpa using hv, ?_⟩
    ext l
    simp
  · intro hc
    obtain ⟨d, hd, hv, rfl⟩ := ClauseSet.mem_restrict.1 hc
    obtain ⟨e, he, rfl⟩ := CNF.mem_toClauseSet.1 hd
    refine CNF.mem_toClauseSet.2 ⟨e.filter (· ≠ (v, !b)),
      CNF.mem_restrict.2 ⟨e, he, by simpa using hv, rfl⟩, ?_⟩
    ext l
    simp

/-- Partial-assignment restriction commutes with the syntax interpretation. -/
@[simp] theorem CNF.toClauseSet_restrictBy (φ : CNF V) (ρ : V → Option Bool) :
    (φ.restrictBy ρ).toClauseSet = φ.toClauseSet.restrictBy ρ := by
  ext c
  constructor
  · intro hc
    obtain ⟨d, hd, rfl⟩ := CNF.mem_toClauseSet.1 hc
    obtain ⟨e, he, hv, rfl⟩ := CNF.mem_restrictBy.1 hd
    refine ClauseSet.mem_restrictBy.2 ⟨e.toFinset, CNF.mem_toClauseSet.2 ⟨e, he, rfl⟩,
      by simpa using hv, ?_⟩
    ext l
    simp
  · intro hc
    obtain ⟨d, hd, hv, rfl⟩ := ClauseSet.mem_restrictBy.1 hc
    obtain ⟨e, he, rfl⟩ := CNF.mem_toClauseSet.1 hd
    refine CNF.mem_toClauseSet.2 ⟨e.filter (fun l => decide (ρ l.1 = none)),
      CNF.mem_restrictBy.2 ⟨e, he, by simpa using hv, rfl⟩, ?_⟩
    ext l
    simp

omit [DecidableEq V] in
/-- An unsatisfied clause keeps its value after deleting assigned variables. -/
theorem FiniteClause.eval_filter_of_extends {ρ : V → Option Bool} {γ : V → Bool}
    (hγ : ∀ v b, ρ v = some b → γ v = b) {d : FiniteClause V}
    (hd : ∀ l ∈ d, ρ l.1 ≠ some l.2) :
    FiniteClause.eval γ (d.filter fun l => ρ l.1 = none) = d.eval γ := by
  rw [Bool.eq_iff_iff, FiniteClause.eval_eq_true_iff, FiniteClause.eval_eq_true_iff]
  constructor
  · rintro ⟨l, hl, hls⟩
    exact ⟨l, (Finset.mem_filter.1 hl).1, hls⟩
  · rintro ⟨l, hl, hls⟩
    cases hρ : ρ l.1 with
    | none => exact ⟨l, Finset.mem_filter.2 ⟨hl, hρ⟩, hls⟩
    | some b =>
      rw [← hγ _ _ hρ, hls] at hρ
      exact absurd hρ (hd l hl)

/-- Under an extending assignment, restriction preserves the value of a clause set. -/
theorem ClauseSet.eval_restrictBy {φ : ClauseSet V} {ρ : V → Option Bool} {γ : V → Bool}
    (hγ : ∀ v b, ρ v = some b → γ v = b) :
    (φ.restrictBy ρ).eval γ = φ.eval γ := by
  rw [Bool.eq_iff_iff, ClauseSet.eval_eq_true_iff, ClauseSet.eval_eq_true_iff]
  constructor
  · intro h d hd
    by_cases hsat : ∀ l ∈ d, ρ l.1 ≠ some l.2
    · rw [← FiniteClause.eval_filter_of_extends hγ hsat]
      exact h _ (ClauseSet.mem_restrictBy.2 ⟨d, hd, hsat, rfl⟩)
    · push Not at hsat
      obtain ⟨l, hl, hρ⟩ := hsat
      exact (FiniteClause.eval_eq_true_iff γ d).2 ⟨l, hl, hγ _ _ hρ⟩
  · intro h c hc
    obtain ⟨d, hd, hsat, rfl⟩ := ClauseSet.mem_restrictBy.1 hc
    rw [FiniteClause.eval_filter_of_extends hγ hsat]
    exact h d hd

end Cslib.Logic.PL
