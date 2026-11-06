/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Proof

/-!
# Resolution proofs with explicit sharing

A DAG proof lists finite clauses in the same last-to-first order as `ClauseSet.IsProof`. Each
line records either an input justification or two indices into its earlier tail and a pivot.
Premises can be reused arbitrarily, including using the same line twice. Successful lookup
ensures both edges point to earlier lines, so cycles and out-of-range references are invalid.

The correspondence with `ClauseSet.IsProof` preserves the entire clause sequence, including
repeated lines, and therefore preserves line count and every line's finite-cardinal width.

## Main definitions

* `Cslib.Logic.PL.Resolution.Annotation`: input or two premise indices with a pivot.
* `Cslib.Logic.PL.Resolution.DAGLine`, `Cslib.Logic.PL.Resolution.DAG`: annotated finite clauses.
* `Cslib.Logic.PL.Resolution.DAG.Valid`: validation against a finite clause set.

## Main results

* `Cslib.Logic.PL.ClauseSet.isProof_iff_exists_dag`: exact clause-sequence correspondence.
* `Cslib.Logic.PL.Resolution.DAG.Valid.isProof`: erasing annotations gives a line proof.
-/

public section

namespace Cslib.Logic.PL.Resolution

variable {V : Type*}

/-- `none` marks an input clause. `some (i, j, v)` resolves the positive premise at `i` with
the negative premise at `j`, on pivot `v`. Indices are zero-based in the line's earlier tail. -/
abbrev Annotation (V : Type*) := Option (ℕ × ℕ × V)

/-- A finite clause with its explicit justification. -/
structure DAGLine (V : Type*) where
  /-- The mathematical clause. -/
  clause : FiniteClause V
  /-- Its input justification or resolution premises and pivot. -/
  annotation : Annotation V

/-- A resolution DAG in reverse topological order, allowing arbitrary sharing of premises. -/
abbrev DAG (V : Type*) := List (DAGLine V)

/-- Validate one annotation against the input formula and the earlier clauses. -/
@[expose] def Annotation.Valid [DecidableEq V] (φ : ClauseSet V) (earlier : List (FiniteClause V))
    (c : FiniteClause V) : Annotation V → Prop
  | none => c ∈ φ
  | some (i, j, v) => ∃ c₁ c₂,
      earlier[i]? = some c₁ ∧ earlier[j]? = some c₂ ∧
      (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c = c₁.resolvent c₂ v

namespace DAG

/-- Erase justifications without changing the order or multiplicity of clauses. -/
@[expose] def clauses (d : DAG V) : List (FiniteClause V) := d.map DAGLine.clause

/-- The number of nodes, counting repeated lines separately. -/
@[expose] def size (d : DAG V) : ℕ := d.length

/-- Every line has finite-cardinal width at most `w`. -/
@[expose] def WidthLE (d : DAG V) (w : ℕ) : Prop := ∀ c ∈ d.clauses, c.width ≤ w

/-- Validate every line against its earlier tail. -/
@[expose] def Valid [DecidableEq V] (φ : ClauseSet V) : DAG V → Prop
  | [] => True
  | line :: earlier => Valid φ earlier ∧ line.annotation.Valid φ (clauses earlier) line.clause

/-- Annotation erasure preserves the exact number of lines. -/
@[simp] theorem length_clauses (d : DAG V) : d.clauses.length = d.size := List.length_map ..

variable [DecidableEq V]

/-- Every valid explicit DAG erases to a proof in the sole mathematical line calculus. -/
theorem Valid.isProof {φ : ClauseSet V} {d : DAG V} (h : d.Valid φ) :
    φ.IsProof d.clauses := by
  induction d with
  | nil => exact .nil
  | cons line earlier ih =>
    obtain ⟨h, hline⟩ := h
    have he := ih h
    cases line with
    | mk c a =>
      cases a with
      | none => exact he.mem hline
      | some a =>
        rcases a with ⟨i, j, v⟩
        obtain ⟨c₁, c₂, h₁, h₂, hv₁, hv₂, rfl⟩ := hline
        exact he.resolvent v (List.mem_of_getElem? h₁) (List.mem_of_getElem? h₂) hv₁ hv₂

end DAG

variable [DecidableEq V]

/-- Any legal line justification can be recorded by explicit indices and a pivot. -/
theorem exists_annotation_iff {φ : ClauseSet V} {earlier : List (FiniteClause V)}
    {c : FiniteClause V} :
    (∃ a : Annotation V, a.Valid φ earlier c) ↔
      c ∈ φ ∨ ∃ c₁ ∈ earlier, ∃ c₂ ∈ earlier, ∃ v,
        (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c = c₁.resolvent c₂ v := by
  constructor
  · rintro ⟨a, ha⟩
    cases a with
    | none => exact Or.inl ha
    | some a =>
      rcases a with ⟨i, j, v⟩
      obtain ⟨c₁, c₂, h₁, h₂, hv₁, hv₂, hc⟩ := ha
      exact Or.inr ⟨c₁, List.mem_of_getElem? h₁, c₂, List.mem_of_getElem? h₂,
        v, hv₁, hv₂, hc⟩
  · rintro (hc | ⟨c₁, h₁, c₂, h₂, v, hv₁, hv₂, hc⟩)
    · exact ⟨none, hc⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h₁
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h₂
      exact ⟨some (i, j, v), c₁, c₂, hi, hj, hv₁, hv₂, hc⟩

end Cslib.Logic.PL.Resolution

namespace Cslib.Logic.PL.ClauseSet

open Resolution

variable {V : Type*} [DecidableEq V] {φ : ClauseSet V} {ls : List (FiniteClause V)}

/-- Adding explicit premises preserves the exact clause sequence. This is an existence theorem;
executable annotation of list representations is supplied by the certificate scanner. -/
theorem IsProof.exists_dag (h : φ.IsProof ls) :
    ∃ d : DAG V, d.Valid φ ∧ d.clauses = ls := by
  induction h with
  | nil => exact ⟨[], trivial, rfl⟩
  | @mem ls c _ hc ih =>
    obtain ⟨d, hd, rfl⟩ := ih
    exact ⟨⟨c, none⟩ :: d, ⟨hd, hc⟩, rfl⟩
  | @resolvent ls c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨d, hd, rfl⟩ := ih
    obtain ⟨a, ha⟩ := exists_annotation_iff.mpr (Or.inr ⟨c₁, h₁, c₂, h₂, v, hv₁, hv₂, rfl⟩)
    exact ⟨⟨c₁.resolvent c₂ v, a⟩ :: d, ⟨hd, ha⟩, rfl⟩

/-- Explicit DAG proofs and bare line proofs have exactly the same clause sequences. -/
theorem isProof_iff_exists_dag :
    φ.IsProof ls ↔ ∃ d : DAG V, d.Valid φ ∧ d.clauses = ls :=
  ⟨IsProof.exists_dag, fun ⟨_, hd, he⟩ => he ▸ hd.isProof⟩

/-- The DAG correspondence preserves a size bound without adding any lines. -/
theorem refutableInSize_iff_exists_dag (s : ℕ) :
    φ.RefutableInSize s ↔
      ∃ d : DAG V, d.Valid φ ∧ ∅ ∈ d.clauses ∧ d.size ≤ s := by
  constructor
  · rintro ⟨ls, h, he, hs⟩
    obtain ⟨d, hd, rfl⟩ := h.exists_dag
    exact ⟨d, hd, he, (d.length_clauses ▸ hs)⟩
  · rintro ⟨d, hd, he, hs⟩
    exact ⟨d.clauses, hd.isProof, he, d.length_clauses.symm ▸ hs⟩

/-- The DAG correspondence preserves every finite-cardinal width bound. -/
theorem refutableInWidth_iff_exists_dag (w : ℕ) :
    φ.RefutableInWidth w ↔
      ∃ d : DAG V, d.Valid φ ∧ ∅ ∈ d.clauses ∧ d.WidthLE w := by
  constructor
  · rintro ⟨ls, h, he, hw⟩
    obtain ⟨d, hd, rfl⟩ := h.exists_dag
    exact ⟨d, hd, he, hw⟩
  · rintro ⟨d, hd, he, hw⟩
    exact ⟨d.clauses, hd.isProof, he, hw⟩

end Cslib.Logic.PL.ClauseSet
