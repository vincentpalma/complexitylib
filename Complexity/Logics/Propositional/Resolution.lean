/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Satisfiable
public import Mathlib.Data.Finset.Card

/-!
# Finite-set resolution

The mathematical calculus acts on `FiniteClause`, finite sets of literals, and `ClauseSet`, finite
sets of clauses. Resolution erases the positive pivot from the first premise and the negative
pivot from the second, then takes the union. Both pivots must occur in their respective premises.
There is no weakening rule; literal order and multiplicity have no role in derivability.

`ClauseSet.Derives` records derivability only. Proof objects and their combinatorial measures are
separate. List-based `CNF` syntax enters the calculus through `CNF.toClauseSet`.

## Main definitions

* `Cslib.Logic.PL.FiniteClause.resolvent`: resolution by erasure and union.
* `Cslib.Logic.PL.ClauseSet.Derives`: mathematical resolution derivability.
* `Cslib.Logic.PL.ClauseSet.restrict`: fixing one variable.
* `Cslib.Logic.PL.ClauseSet.vars`: finite variable support.

## Main results

* `Cslib.Logic.PL.ClauseSet.Derives.not_satisfiable`: soundness.
* `Cslib.Logic.PL.ClauseSet.derives_empty_iff_not_satisfiable`: refutation completeness.
* `Cslib.Logic.PL.ClauseSet.Derives.exists_of_restrict`: lifting restricted derivations.

Completeness follows variable elimination [DavisPutnam1960] to prove ground refutation
completeness [Robinson1965].

## References

* [J. A. Robinson, *A machine-oriented logic based on the resolution principle*][Robinson1965]
* [M. Davis, H. Putnam, *A computing procedure for quantification theory*][DavisPutnam1960]
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-! ### The resolution rule -/

/-- The resolvent of `c₁` and `c₂` on `v`: the literals of `c₁` other than `v` and those of `c₂`
other than `¬v`. -/
@[expose] def FiniteClause.resolvent (c₁ c₂ : FiniteClause V) (v : V) : FiniteClause V :=
  c₁.erase (v, true) ∪ c₂.erase (v, false)

/-- A literal belongs to `c₁.resolvent c₂ v` iff it belongs to `c₁` and is not `(v, true)`, or
belongs to `c₂` and is not `(v, false)`. -/
@[simp] theorem FiniteClause.mem_resolvent {c₁ c₂ : FiniteClause V} {v : V} {l : Literal V} :
    l ∈ c₁.resolvent c₂ v ↔ (l ∈ c₁ ∧ l ≠ (v, true)) ∨ (l ∈ c₂ ∧ l ≠ (v, false)) := by
  simp only [resolvent, Finset.mem_union, Finset.mem_erase, and_comm]

/-- The resolvent has at most as many literals as its parents together. -/
theorem FiniteClause.card_resolvent_le (c₁ c₂ : FiniteClause V) (v : V) :
    (c₁.resolvent c₂ v).card ≤ c₁.card + c₂.card :=
  (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_erase_le Finset.card_erase_le)

/-- **Soundness of one resolution step**: an assignment satisfying both parents satisfies the
resolvent. -/
theorem FiniteClause.eval_resolvent {σ : V → Bool} {c₁ c₂ : FiniteClause V} (v : V)
    (h₁ : c₁.eval σ = true) (h₂ : c₂.eval σ = true) : (c₁.resolvent c₂ v).eval σ = true := by
  rw [FiniteClause.eval_eq_true_iff] at h₁ h₂ ⊢
  obtain ⟨l₁, hl₁, he₁⟩ := h₁
  obtain ⟨l₂, hl₂, he₂⟩ := h₂
  cases hv : σ v
  · refine ⟨l₁, mem_resolvent.2 (Or.inl ⟨hl₁, ?_⟩), he₁⟩
    rintro rfl
    simp [hv] at he₁
  · refine ⟨l₂, mem_resolvent.2 (Or.inr ⟨hl₂, ?_⟩), he₂⟩
    rintro rfl
    simp [hv] at he₂

namespace ClauseSet

/-- Boolean evaluation of a clause set using its satisfaction predicate. -/
@[expose] def eval (σ : V → Bool) (φ : ClauseSet V) : Bool := decide (φ.Sat σ)

omit [DecidableEq V] in
/-- A clause set is true exactly when each of its clauses is true. -/
@[simp] theorem eval_eq_true_iff (σ : V → Bool) (φ : ClauseSet V) :
    φ.eval σ = true ↔ ∀ c ∈ φ, FiniteClause.eval σ c = true := by
  exact ⟨fun h c hc => (FiniteClause.eval_eq_true_iff σ c).2 (of_decide_eq_true h c hc),
    fun h => decide_eq_true fun c hc => (FiniteClause.eval_eq_true_iff σ c).1 (h c hc)⟩

/-- The finite set of variables mentioned by a clause set. -/
@[expose] def vars (φ : ClauseSet V) : Finset V :=
  φ.biUnion fun c => c.image Prod.fst

/-- A variable occurs when one of its signed literals occurs in an input clause. -/
@[simp] theorem mem_vars {φ : ClauseSet V} {v : V} :
    v ∈ φ.vars ↔ ∃ c ∈ φ, ∃ b, (v, b) ∈ c := by
  constructor
  · intro h
    obtain ⟨c, hc, l, hl, heq⟩ := (by
      simpa only [vars, Finset.mem_biUnion, Finset.mem_image] using h)
    rcases l with ⟨u, b⟩
    dsimp at heq
    subst u
    exact ⟨c, hc, b, hl⟩
  · rintro ⟨c, hc, b, hb⟩
    exact Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_image.2 ⟨(v, b), hb, rfl⟩⟩

end ClauseSet

/-- Passing from list syntax to a clause set preserves its variable support. -/
@[simp] theorem CNF.vars_toClauseSet (φ : CNF V) : φ.toClauseSet.vars = φ.vars.toFinset := by
  ext v
  rw [ClauseSet.mem_vars, List.mem_toFinset, CNF.mem_vars]
  constructor
  · rintro ⟨c, hc, b, hb⟩
    obtain ⟨d, hd, rfl⟩ := CNF.mem_toClauseSet.1 hc
    exact ⟨d, hd, b, List.mem_toFinset.1 hb⟩
  · rintro ⟨c, hc, b, hb⟩
    exact ⟨c.toFinset, CNF.mem_toClauseSet.2 ⟨c, hc, rfl⟩, b, List.mem_toFinset.2 hb⟩

/-! ### Derivations and soundness -/

/-- The clauses derivable from `φ` by resolution: the clauses of `φ`, and the resolvents of
derivable clauses. -/
inductive ClauseSet.Derives (φ : ClauseSet V) : FiniteClause V → Prop
  /-- A clause of `φ` is derivable. -/
  | mem {c : FiniteClause V} (hc : c ∈ φ) : ClauseSet.Derives φ c
  /-- The resolvent of two derivable clauses on a variable occurring positively in the first and
  negatively in the second is derivable. -/
  | resolvent {c₁ c₂ : FiniteClause V} (v : V) (h₁ : ClauseSet.Derives φ c₁)
      (h₂ : ClauseSet.Derives φ c₂)
      (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) :
      ClauseSet.Derives φ (c₁.resolvent c₂ v)

namespace ClauseSet.Derives

variable {φ ψ : ClauseSet V} {c : FiniteClause V}

/-- A derivable clause is true under every assignment satisfying the formula. -/
theorem eval_eq_true (h : φ.Derives c) {σ : V → Bool} (hσ : φ.eval σ = true) :
    c.eval σ = true := by
  induction h with
  | mem hc => exact (ClauseSet.eval_eq_true_iff σ φ).1 hσ _ hc
  | resolvent v _ _ _ _ ih₁ ih₂ => exact FiniteClause.eval_resolvent v ih₁ ih₂

/-- **Soundness of resolution**: a formula from which the empty clause is derivable is
unsatisfiable. -/
theorem not_satisfiable (h : φ.Derives ∅) : ¬ φ.Satisfiable := fun ⟨_, hσ⟩ => by
  have hc := h.eval_eq_true ((ClauseSet.eval_eq_true_iff _ _).2 fun c hc =>
    (FiniteClause.eval_eq_true_iff _ _).2 (hσ c hc))
  simp at hc

/-- Derivations survive adding clauses. -/
theorem mono (h : φ.Derives c) (hφψ : φ ⊆ ψ) : ψ.Derives c := by
  induction h with
  | mem hc => exact mem (hφψ hc)
  | resolvent v _ _ hv₁ hv₂ ih₁ ih₂ => exact resolvent v ih₁ ih₂ hv₁ hv₂

end ClauseSet.Derives

/-! ### Completeness -/

/-- `φ` with the variable `v` fixed to `b`: the clauses satisfied by `v = b` are dropped, and the
literal of `v` falsified by `v = b` is removed from the others. -/
@[expose] def ClauseSet.restrict (φ : ClauseSet V) (v : V) (b : Bool) : ClauseSet V :=
  (φ.filter fun c => (v, b) ∉ c).image fun c => c.filter (· ≠ (v, !b))

namespace ClauseSet

variable {φ : ClauseSet V} {v : V} {b : Bool}

/-- A clause belongs to `φ.restrict v b` iff it is obtained from a clause of `φ` not containing
`(v, b)` by removing `(v, !b)`. -/
@[simp] theorem mem_restrict {c : FiniteClause V} :
    c ∈ φ.restrict v b ↔ ∃ d ∈ φ, (v, b) ∉ d ∧ d.filter (· ≠ (v, !b)) = c := by
  simp [restrict, and_assoc]

/-- A restricted formula no longer mentions the fixed variable. -/
theorem fst_ne_of_mem_restrict {c : FiniteClause V} (hc : c ∈ φ.restrict v b) {l : Literal V}
    (hl : l ∈ c) : l.1 ≠ v := by
  obtain ⟨d, -, hvd, rfl⟩ := mem_restrict.1 hc
  obtain ⟨hld, hl⟩ := Finset.mem_filter.1 hl
  rintro hlv
  obtain ⟨u, a⟩ := l
  subst hlv
  cases a <;> cases b <;> simp_all

/-- The variables of a restricted formula are variables of the formula other than the fixed one. -/
theorem vars_restrict_subset : (φ.restrict v b).vars ⊆ φ.vars.erase v := by
  intro u hu
  obtain ⟨c, hc, a, ha⟩ := mem_vars.1 hu
  refine Finset.mem_erase.2 ⟨fst_ne_of_mem_restrict hc ha, ?_⟩
  obtain ⟨d, hd, -, rfl⟩ := mem_restrict.1 hc
  exact mem_vars.2 ⟨d, hd, a, (Finset.mem_filter.1 ha).1⟩

/-- If `σ` satisfies the restricted formula, then `σ` with `v` set to `b` satisfies the formula. -/
theorem eval_update_of_eval_restrict {σ : V → Bool} (h : (φ.restrict v b).eval σ = true) :
    φ.eval (Function.update σ v b) = true := by
  rw [ClauseSet.eval_eq_true_iff] at h ⊢
  intro d hd
  by_cases hvd : (v, b) ∈ d
  · exact (FiniteClause.eval_eq_true_iff _ _).2 ⟨_, hvd, by simp⟩
  · have hc := h _ (mem_restrict.2 ⟨d, hd, hvd, rfl⟩)
    obtain ⟨l, hl, he⟩ := (FiniteClause.eval_eq_true_iff _ _).1 hc
    refine (FiniteClause.eval_eq_true_iff _ _).2 ⟨l, (Finset.mem_filter.1 hl).1, ?_⟩
    have hlv := fst_ne_of_mem_restrict (mem_restrict.2 ⟨d, hd, hvd, rfl⟩) hl
    obtain ⟨u, a⟩ := l
    simpa [Function.update_of_ne hlv] using he

/-- Fixing a variable of an unsatisfiable formula leaves an unsatisfiable formula. -/
theorem not_satisfiable_restrict (h : ¬ φ.Satisfiable) : ¬ (φ.restrict v b).Satisfiable :=
  fun ⟨_, hσ⟩ => h ⟨_, fun d hd => (FiniteClause.eval_eq_true_iff _ _).1
    ((eval_eq_true_iff _ _).1 (eval_update_of_eval_restrict
      ((eval_eq_true_iff _ _).2 fun c hc => (FiniteClause.eval_eq_true_iff _ _).2 (hσ c hc))) d hd)⟩

/-- **Lifting a derivation**: a clause derivable from `φ` with `v` fixed to `b` is contained in a
clause derivable from `φ` that may also contain the literal of `v` falsified by `b`. -/
theorem Derives.exists_of_restrict {c : FiniteClause V} (h : (φ.restrict v b).Derives c) :
    ∃ d, φ.Derives d ∧ (∀ l ∈ d, l ∈ c ∨ l = (v, !b)) ∧ ∀ l ∈ c, l ∈ d := by
  induction h with
  | mem hc =>
    obtain ⟨d, hd, -, rfl⟩ := mem_restrict.1 hc
    refine ⟨d, .mem hd, fun l hl => ?_, fun l hl => (Finset.mem_filter.1 hl).1⟩
    by_cases hlv : l = (v, !b)
    · exact Or.inr hlv
    · exact Or.inl (Finset.mem_filter.2 ⟨hl, by simpa using hlv⟩)
  | @resolvent c₁ c₂ u _ _ hu₁ hu₂ ih₁ ih₂ =>
    obtain ⟨d₁, hd₁, h₁, h₁'⟩ := ih₁
    obtain ⟨d₂, hd₂, h₂, h₂'⟩ := ih₂
    refine ⟨d₁.resolvent d₂ u, .resolvent u hd₁ hd₂ (h₁' _ hu₁) (h₂' _ hu₂), fun l hl => ?_,
      fun l hl => ?_⟩
    · rcases FiniteClause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact (h₁ l hl).imp_left fun hl' => FiniteClause.mem_resolvent.2 (Or.inl ⟨hl', hne⟩)
      · exact (h₂ l hl).imp_left fun hl' => FiniteClause.mem_resolvent.2 (Or.inr ⟨hl', hne⟩)
    · rcases FiniteClause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact FiniteClause.mem_resolvent.2 (Or.inl ⟨h₁' l hl, hne⟩)
      · exact FiniteClause.mem_resolvent.2 (Or.inr ⟨h₂' l hl, hne⟩)

/-- A formula without variables is unsatisfiable only if it has the empty clause. -/
private theorem empty_mem_of_vars_eq_empty (hφ : φ.vars = ∅) (h : ¬ φ.Satisfiable) : ∅ ∈ φ := by
  by_contra hnil
  refine h ⟨fun _ => false, fun c hc => ?_⟩
  obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.2 fun hc' => hnil (hc' ▸ hc)
  have : l.1 ∈ φ.vars := mem_vars.2 ⟨c, hc, l.2, hl⟩
  simp [hφ] at this

/-- **Refutation completeness of resolution**: the empty clause is derivable from every
unsatisfiable formula. -/
theorem derives_empty_of_not_satisfiable {φ : ClauseSet V} (h : ¬ φ.Satisfiable) : φ.Derives ∅ := by
  by_cases hφ : φ.vars = ∅
  · exact .mem (empty_mem_of_vars_eq_empty hφ h)
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hφ
  -- derivations from both restrictions, by induction on the number of variables
  have hlt (b : Bool) : (φ.restrict v b).vars.card < φ.vars.card :=
    (Finset.card_le_card vars_restrict_subset).trans_lt (Finset.card_erase_lt_of_mem hv)
  obtain ⟨d₀, hd₀, h₀, -⟩ := (derives_empty_of_not_satisfiable (φ := φ.restrict v false)
    (not_satisfiable_restrict h)).exists_of_restrict
  obtain ⟨d₁, hd₁, h₁, -⟩ := (derives_empty_of_not_satisfiable (φ := φ.restrict v true)
    (not_satisfiable_restrict h)).exists_of_restrict
  -- `d₀` only has `v` and `d₁` only has `¬v`; either one is empty, or they resolve to `∅`
  have h₀' : ∀ l ∈ d₀, l = (v, true) := fun l hl => (h₀ l hl).resolve_left (by simp)
  have h₁' : ∀ l ∈ d₁, l = (v, false) := fun l hl => (h₁ l hl).resolve_left (by simp)
  by_cases hv₀ : (v, true) ∈ d₀
  · by_cases hv₁ : (v, false) ∈ d₁
    · convert Derives.resolvent v hd₀ hd₁ hv₀ hv₁ using 1
      refine (Finset.eq_empty_iff_forall_notMem.2 fun l hl => ?_).symm
      rcases FiniteClause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact hne (h₀' l hl)
      · exact hne (h₁' l hl)
    · convert hd₁ using 1
      exact (Finset.eq_empty_iff_forall_notMem.2 fun l hl => hv₁ (h₁' l hl ▸ hl)).symm
  · convert hd₀ using 1
    exact (Finset.eq_empty_iff_forall_notMem.2 fun l hl => hv₀ (h₀' l hl ▸ hl)).symm
termination_by φ.vars.card
decreasing_by
  · exact hlt false
  · exact hlt true

/-- **Resolution refutes exactly the unsatisfiable formulas.** -/
theorem derives_empty_iff_not_satisfiable : φ.Derives ∅ ↔ ¬ φ.Satisfiable :=
  ⟨Derives.not_satisfiable, derives_empty_of_not_satisfiable⟩

end ClauseSet

end Cslib.Logic.PL
