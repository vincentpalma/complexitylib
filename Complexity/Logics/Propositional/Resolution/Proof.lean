/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution

/-!
# Resolution proofs

Derivability by resolution (`Cslib.Logic.PL.ClauseSet.Derives`) records only that a clause can be
derived. Proof complexity measures derivations, so this file gives them their usual line-based
form: a *resolution proof* from a formula `φ` is a sequence of clauses, each of which is a clause of
`φ` or the resolvent (`Cslib.Logic.PL.FiniteClause.resolvent`) of two earlier clauses on a variable
occurring positively in the first and negatively in the second (`Cslib.Logic.PL.ClauseSet.IsProof`).
Proofs are listed from their last line to their first, so that a proof grows by adding a line in
front. A clause is derivable exactly when it is a line of some proof
(`Cslib.Logic.PL.ClauseSet.derives_iff_exists_isProof`).

A *refutation* is a proof with the empty clause among its lines. Its *size* is its number of lines,
and its *width* the largest width of a line, where the width of a clause
(`Cslib.Logic.PL.FiniteClause.width`) is its number of distinct literals [Ben-Sasson and Wigderson]
[BenSassonWigderson2001]. Each line is a finite set, so repeated occurrences and literal order
  cannot affect any measure.

Fixing a variable transforms proofs in both directions:

* a proof from `φ` becomes a proof from the restricted formula `φ.restrict v b`
  (`Cslib.Logic.PL.ClauseSet.IsProof.restrict`). It has at most as many lines; every line of the
    original
  proof that `v = b` does not satisfy is replaced by a line with a subset of its literals, and a
  line of the new proof is wider than any given bound only if the line it replaces is;
* a proof from `φ.restrict v b` lifts to a proof from `φ`
  (`Cslib.Logic.PL.ClauseSet.IsProof.lift`) whose
  lines contain the lines they lift and, besides their literals, at most the literal of `v` that
  `b` falsifies. This is `Cslib.Logic.PL.ClauseSet.Derives.exists_of_restrict` for proofs, keeping
  track of the lines.

Proofs also compose: a proof from `ψ` replays on top of a proof from `φ` among whose lines are the
clauses of `ψ` (`Cslib.Logic.PL.ClauseSet.IsProof.comp`).

## Main definitions

* `Cslib.Logic.PL.FiniteClause.width`: the number of distinct literals of a clause.
* `Cslib.Logic.PL.ClauseSet.IsProof`: resolution proofs.
* `Cslib.Logic.PL.ClauseSet.RefutableInSize`, `Cslib.Logic.PL.ClauseSet.RefutableInWidth`:
  refutability by a
  refutation with a bounded number of lines, or with lines of bounded width.
* `Cslib.Logic.PL.ClauseSet.restrictBy`: restricting a formula by a partial assignment.

## Main results

* `Cslib.Logic.PL.ClauseSet.derives_iff_exists_isProof`: derivable clauses are the lines of proofs.
* `Cslib.Logic.PL.ClauseSet.exists_refutableInSize_iff_not_satisfiable`: resolution refutes
  exactly the
  unsatisfiable formulas.
* `Cslib.Logic.PL.ClauseSet.IsProof.restrict`, `Cslib.Logic.PL.ClauseSet.IsProof.lift`,
  `Cslib.Logic.PL.ClauseSet.IsProof.restrictBy`: restricting and lifting proofs along a fixed
    variable or
  a partial assignment.
* `Cslib.Logic.PL.ClauseSet.IsProof.comp`: composing proofs.

## References

* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [J. A. Robinson, *A machine-oriented logic based on the resolution principle*][Robinson1965]
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-! ### Proofs -/

/-- A **resolution proof** from `φ`, listed from its last line to its first: every line is a
clause of `φ`, or the resolvent of two lines below it on a variable occurring positively in the
first and negatively in the second. -/
inductive ClauseSet.IsProof (φ : ClauseSet V) : List (FiniteClause V) → Prop
  /-- The empty proof. -/
  | nil : ClauseSet.IsProof φ []
  /-- A clause of `φ` is a new line. -/
  | mem {ls : List (FiniteClause V)} {c : FiniteClause V} (h : ClauseSet.IsProof φ ls) (hc : c ∈
    φ) :
      ClauseSet.IsProof φ (c :: ls)
  /-- The resolvent of two lines, on a variable occurring positively in the first and negatively in
  the second, is a new line. -/
  | resolvent {ls : List (FiniteClause V)} {c₁ c₂ : FiniteClause V} (v : V) (h : ClauseSet.IsProof
    φ ls)
      (h₁ : c₁ ∈ ls) (h₂ : c₂ ∈ ls) (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) :
      ClauseSet.IsProof φ (c₁.resolvent c₂ v :: ls)

/-- `φ` has a resolution refutation with at most `s` lines. -/
@[expose] def ClauseSet.RefutableInSize (φ : ClauseSet V) (s : ℕ) : Prop :=
  ∃ ls, φ.IsProof ls ∧ ∅ ∈ ls ∧ ls.length ≤ s

/-- `φ` has a resolution refutation all of whose lines have width at most `w`. -/
@[expose] def ClauseSet.RefutableInWidth (φ : ClauseSet V) (w : ℕ) : Prop :=
  ∃ ls, φ.IsProof ls ∧ ∅ ∈ ls ∧ ∀ c ∈ ls, c.width ≤ w

namespace ClauseSet

variable {φ ψ : ClauseSet V} {ls ls' : List (FiniteClause V)} {c : FiniteClause V}

namespace IsProof

/-- A line is justified by an input clause or by a pivot and two preceding lines. -/
theorem cons_iff : φ.IsProof (c :: ls) ↔ φ.IsProof ls ∧
    (c ∈ φ ∨ ∃ c₁ ∈ ls, ∃ c₂ ∈ ls, ∃ v,
      (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c = c₁.resolvent c₂ v) := by
  constructor
  · intro h
    cases h with
    | mem h hc => exact ⟨h, Or.inl hc⟩
    | resolvent v h h₁ h₂ hv₁ hv₂ => exact ⟨h, Or.inr ⟨_, h₁, _, h₂, v, hv₁, hv₂, rfl⟩⟩
  · rintro ⟨h, hc | ⟨c₁, h₁, c₂, h₂, v, hv₁, hv₂, rfl⟩⟩
    · exact h.mem hc
    · exact h.resolvent v h₁ h₂ hv₁ hv₂

/-- Every line of a proof is derivable. -/
theorem derives (h : φ.IsProof ls) (hc : c ∈ ls) : φ.Derives c := by
  induction h generalizing c with
  | nil => simp at hc
  | mem _ hc' ih =>
    rcases List.mem_cons.1 hc with rfl | hc
    exacts [.mem hc', ih hc]
  | resolvent v _ h₁ h₂ hv₁ hv₂ ih =>
    rcases List.mem_cons.1 hc with rfl | hc
    exacts [.resolvent v (ih h₁) (ih h₂) hv₁ hv₂, ih hc]

/-- A proof placed above another proof from the same formula gives a proof. -/
theorem append (h : φ.IsProof ls) (h' : φ.IsProof ls') : φ.IsProof (ls ++ ls') := by
  induction h with
  | nil => exact h'
  | mem _ hc ih => exact ih.mem hc
  | resolvent v _ h₁ h₂ hv₁ hv₂ ih =>
    exact ih.resolvent v (List.mem_append_left _ h₁) (List.mem_append_left _ h₂) hv₁ hv₂

/-- Proofs survive adding clauses to the formula. -/
theorem mono (h : φ.IsProof ls) (hφψ : φ ⊆ ψ) : ψ.IsProof ls := by
  induction h with
  | nil => exact .nil
  | mem _ hc ih => exact ih.mem (hφψ hc)
  | resolvent v _ h₁ h₂ hv₁ hv₂ ih => exact ih.resolvent v h₁ h₂ hv₁ hv₂

/-- The lines of a proof only mention variables of the formula. -/
theorem fst_mem_vars (h : φ.IsProof ls) (hc : c ∈ ls) {l : Literal V} (hl : l ∈ c) :
    l.1 ∈ φ.vars := by
  induction h generalizing c with
  | nil => simp at hc
  | mem _ hc' ih =>
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ClauseSet.mem_vars.2 ⟨c, hc', l.2, hl⟩
    · exact ih hc hl
  | resolvent v _ h₁ h₂ _ _ ih =>
    rcases List.mem_cons.1 hc with rfl | hc
    · rcases FiniteClause.mem_resolvent.1 hl with ⟨hl, -⟩ | ⟨hl, -⟩
      exacts [ih h₁ hl, ih h₂ hl]
    · exact ih hc hl

end IsProof

/-- A derivable clause is a line of some proof. -/
theorem Derives.exists_isProof (h : φ.Derives c) : ∃ ls, φ.IsProof ls ∧ c ∈ ls := by
  induction h with
  | mem hc => exact ⟨[_], IsProof.nil.mem hc, List.mem_singleton_self _⟩
  | resolvent v _ _ hv₁ hv₂ ih₁ ih₂ =>
    obtain ⟨ls₁, h₁, hc₁⟩ := ih₁
    obtain ⟨ls₂, h₂, hc₂⟩ := ih₂
    exact ⟨_, (h₁.append h₂).resolvent v (List.mem_append_left _ hc₁)
      (List.mem_append_right _ hc₂) hv₁ hv₂, List.mem_cons_self⟩

/-- **Derivable clauses are the lines of proofs.** -/
theorem derives_iff_exists_isProof : φ.Derives c ↔ ∃ ls, φ.IsProof ls ∧ c ∈ ls :=
  ⟨Derives.exists_isProof, fun ⟨_, h, hc⟩ => h.derives hc⟩

/-- **Resolution refutes exactly the unsatisfiable formulas**, by refutations of some size. -/
theorem exists_refutableInSize_iff_not_satisfiable :
    (∃ s, φ.RefutableInSize s) ↔ ¬ φ.Satisfiable := by
  rw [← derives_empty_iff_not_satisfiable, derives_iff_exists_isProof]
  exact ⟨fun ⟨_, ls, h, hnil, _⟩ => ⟨ls, h, hnil⟩, fun ⟨ls, h, hnil⟩ => ⟨_, ls, h, hnil, le_rfl⟩⟩

/-- A refutation within some width is a refutation of some size. -/
theorem RefutableInWidth.exists_refutableInSize {w : ℕ} (h : φ.RefutableInWidth w) :
    ∃ s, φ.RefutableInSize s :=
  let ⟨ls, h, hnil, _⟩ := h
  ⟨_, ls, h, hnil, le_rfl⟩

/-- `RefutableInSize` is monotone in the size bound. -/
theorem RefutableInSize.mono {s t : ℕ} (h : φ.RefutableInSize s) (hst : s ≤ t) :
    φ.RefutableInSize t :=
  let ⟨ls, h, hnil, hlen⟩ := h
  ⟨ls, h, hnil, hlen.trans hst⟩

/-- `RefutableInWidth` is monotone in the width bound. -/
theorem RefutableInWidth.mono {w w' : ℕ} (h : φ.RefutableInWidth w) (hww' : w ≤ w') :
    φ.RefutableInWidth w' :=
  let ⟨ls, h, hnil, hw⟩ := h
  ⟨ls, h, hnil, fun c hc => (hw c hc).trans hww'⟩

/-! ### Restricting and lifting proofs -/

private theorem countP_cons_le_cons {α β : Type*} {p : α → Bool} {q : β → Bool} {a : α} {b : β}
    {l : List α} {l' : List β} (h : l.countP p ≤ l'.countP q) (hab : p a = true → q b = true) :
    (a :: l).countP p ≤ (b :: l').countP q := by
  rw [List.countP_cons, List.countP_cons]
  by_cases ha : p a = true
  · simp only [ha, hab ha, ↓reduceIte]
    omega
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    split <;> omega

private theorem countP_le_cons {α β : Type*} {p : α → Bool} {q : β → Bool} {b : β} {l : List α}
    {l' : List β} (h : l.countP p ≤ l'.countP q) : l.countP p ≤ (b :: l').countP q := by
  rw [List.countP_cons]
  omega

/-- The lines of a proof from a formula with `v` fixed do not mention `v`. -/
theorem IsProof.fst_ne_of_restrict {v : V} {b : Bool} (h : (φ.restrict v b).IsProof ls)
    (hc : c ∈ ls) {l : Literal V} (hl : l ∈ c) : l.1 ≠ v :=
  (Finset.mem_erase.1 (vars_restrict_subset (h.fst_mem_vars hc hl))).1

/-- **Restricting a proof.** A proof from `φ` becomes a proof from `φ` with `v` fixed to `b`, with
at most as many lines. Every line of the original proof that does not contain the literal `(v, b)`
is replaced by a line of the new proof with a subset of its literals, and for every `w` the new
proof has at most as many lines wider than `w` as the original proof has lines without `(v, b)`
wider than `w`. -/
theorem IsProof.restrict (h : φ.IsProof ls) (v : V) (b : Bool) :
    ∃ ls', (φ.restrict v b).IsProof ls' ∧ ls'.length ≤ ls.length ∧
      (∀ c ∈ ls, (v, b) ∉ c → ∃ c' ∈ ls', ∀ l ∈ c', l ∈ c) ∧
      ∀ w, ls'.countP (fun c => w < c.width) ≤ ls.countP (fun c => (v, b) ∉ c ∧ w < c.width) := by
  induction h with
  | nil => exact ⟨[], .nil, le_rfl, by simp, by simp⟩
  | @mem ls c _ hc ih =>
    obtain ⟨ls', h', hlen, hsub, hcount⟩ := ih
    by_cases hvc : (v, b) ∈ c
    · refine ⟨ls', h', hlen.trans (Nat.le_succ _), fun e he hve => ?_,
        fun w => countP_le_cons (hcount w)⟩
      rcases List.mem_cons.1 he with rfl | he
      exacts [absurd hvc hve, hsub e he hve]
    · refine ⟨c.filter (· ≠ (v, !b)) :: ls', h'.mem (mem_restrict.2 ⟨c, hc, hvc, rfl⟩),
        Nat.succ_le_succ hlen, fun e he hve => ?_, fun w => countP_cons_le_cons (hcount w) ?_⟩
      · rcases List.mem_cons.1 he with rfl | he
        · exact ⟨_, List.mem_cons_self, fun l hl => (Finset.mem_filter.1 hl).1⟩
        · obtain ⟨c', hc', hsub'⟩ := hsub e he hve
          exact ⟨c', List.mem_cons_of_mem _ hc', hsub'⟩
      · intro hw
        simp only [decide_eq_true_eq] at hw ⊢
        exact ⟨hvc, hw.trans_le (Finset.card_le_card fun l hl => (Finset.mem_filter.1
          hl).1)⟩
  | @resolvent ls c₁ c₂ u _ h₁ h₂ hu₁ hu₂ ih =>
    obtain ⟨ls', h', hlen, hsub, hcount⟩ := ih
    by_cases hvc : (v, b) ∈ c₁.resolvent c₂ u
    · refine ⟨ls', h', hlen.trans (Nat.le_succ _), fun e he hve => ?_,
        fun w => countP_le_cons (hcount w)⟩
      rcases List.mem_cons.1 he with rfl | he
      exacts [absurd hvc hve, hsub e he hve]
    -- the new line to add, if any: a subclause of the resolvent derivable from `ls'`
    have key : ∃ c', (c' ∈ ls' ∨ ∃ c₁' c₂', c₁' ∈ ls' ∧ c₂' ∈ ls' ∧ (u, true) ∈ c₁' ∧
        (u, false) ∈ c₂' ∧ c' = c₁'.resolvent c₂' u) ∧ ∀ l ∈ c', l ∈ c₁.resolvent c₂ u := by
      have hne (c' : FiniteClause V) (hc' : c' ∈ ls') (l : Literal V) (hl : l ∈ c') :
          l.1 ≠ v := h'.fst_ne_of_restrict hc' hl
      by_cases hv₁ : (v, b) ∈ c₁
      · -- `v = u` and `b = true`: the second premise is not satisfied, and its subclause will do
        have huv : (v, b) = (u, true) := by
          by_contra hne'
          exact hvc (FiniteClause.mem_resolvent.2 (Or.inl ⟨hv₁, hne'⟩))
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
        obtain ⟨c₂', hc₂', hsub₂⟩ := hsub c₂ h₂ fun hv₂ =>
          hvc (FiniteClause.mem_resolvent.2 (Or.inr ⟨hv₂, by simp⟩))
        refine ⟨c₂', Or.inl hc₂', fun l hl => FiniteClause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl,
          ?_⟩)⟩
        rintro rfl
        exact hne _ hc₂' _ hl rfl
      by_cases hv₂ : (v, b) ∈ c₂
      · have huv : (v, b) = (u, false) := by
          by_contra hne'
          exact hvc (FiniteClause.mem_resolvent.2 (Or.inr ⟨hv₂, hne'⟩))
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
        obtain ⟨c₁', hc₁', hsub₁⟩ := hsub c₁ h₁ hv₁
        refine ⟨c₁', Or.inl hc₁', fun l hl => FiniteClause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl,
          ?_⟩)⟩
        rintro rfl
        exact hne _ hc₁' _ hl rfl
      obtain ⟨c₁', hc₁', hsub₁⟩ := hsub c₁ h₁ hv₁
      obtain ⟨c₂', hc₂', hsub₂⟩ := hsub c₂ h₂ hv₂
      by_cases hu₁' : (u, true) ∈ c₁'
      · by_cases hu₂' : (u, false) ∈ c₂'
        · refine ⟨_, Or.inr ⟨c₁', c₂', hc₁', hc₂', hu₁', hu₂', rfl⟩, fun l hl => ?_⟩
          rcases FiniteClause.mem_resolvent.1 hl with ⟨hl, hne'⟩ | ⟨hl, hne'⟩
          · exact FiniteClause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl, hne'⟩)
          · exact FiniteClause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl, hne'⟩)
        · refine ⟨c₂', Or.inl hc₂', fun l hl => FiniteClause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl,
          ?_⟩)⟩
          rintro rfl
          exact hu₂' hl
      · refine ⟨c₁', Or.inl hc₁', fun l hl => FiniteClause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl,
        ?_⟩)⟩
        rintro rfl
        exact hu₁' hl
    obtain ⟨c', hc' | ⟨c₁', c₂', hc₁', hc₂', hu₁', hu₂', rfl⟩, hsub'⟩ := key
    · refine ⟨ls', h', hlen.trans (Nat.le_succ _), fun e he hve => ?_,
        fun w => countP_le_cons (hcount w)⟩
      rcases List.mem_cons.1 he with rfl | he
      exacts [⟨c', hc', hsub'⟩, hsub e he hve]
    · refine ⟨_ :: ls', h'.resolvent u hc₁' hc₂' hu₁' hu₂', Nat.succ_le_succ hlen,
        fun e he hve => ?_, fun w => countP_cons_le_cons (hcount w) ?_⟩
      · rcases List.mem_cons.1 he with rfl | he
        · exact ⟨_, List.mem_cons_self, hsub'⟩
        · obtain ⟨e', he', hsub''⟩ := hsub e he hve
          exact ⟨e', List.mem_cons_of_mem _ he', hsub''⟩
      · intro hw
        simp only [decide_eq_true_eq] at hw ⊢
        exact ⟨hvc, hw.trans_le (Finset.card_le_card hsub')⟩

/-- **Lifting a proof.** A proof from `φ` with `v` fixed to `b` lifts to a proof from `φ`. Every
line of the original proof is contained in a line of the lifted proof that has, besides its
literals, at most the literal `(v, !b)` falsified by `b`, and every line of the lifted proof has,
besides the literals of a line of the original proof, at most that literal. The number of lines
is preserved exactly. -/
theorem IsProof.lift {v : V} {b : Bool} (h : (φ.restrict v b).IsProof ls') :
    ∃ ls, φ.IsProof ls ∧
      (∀ c' ∈ ls', ∃ c ∈ ls, (∀ l ∈ c', l ∈ c) ∧ ∀ l ∈ c, l ∈ c' ∨ l = (v, !b)) ∧
      (∀ c ∈ ls, ∃ c' ∈ ls', ∀ l ∈ c, l ∈ c' ∨ l = (v, !b)) ∧
      ls.length = ls'.length := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp, rfl⟩
  | @mem ls' c' _ hc' ih =>
    obtain ⟨ls, h, hup, hdown, hlen⟩ := ih
    obtain ⟨d, hd, -, rfl⟩ := mem_restrict.1 hc'
    have hd' : ∀ l ∈ d, l ∈ d.filter (· ≠ (v, !b)) ∨ l = (v, !b) := fun l hl => by
      by_cases hlv : l = (v, !b)
      · exact Or.inr hlv
      · exact Or.inl (Finset.mem_filter.2 ⟨hl, by simpa using hlv⟩)
    refine ⟨d :: ls, h.mem hd, fun e he => ?_, fun e he => ?_, congrArg Nat.succ hlen⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨d, List.mem_cons_self, fun l hl => (Finset.mem_filter.1 hl).1, hd'⟩
      · obtain ⟨e', he', h₁, h₂⟩ := hup e he
        exact ⟨e', List.mem_cons_of_mem _ he', h₁, h₂⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨_, List.mem_cons_self, hd'⟩
      · obtain ⟨e', he', h₁⟩ := hdown e he
        exact ⟨e', List.mem_cons_of_mem _ he', h₁⟩
  | @resolvent ls' c₁' c₂' u _ h₁ h₂ hu₁ hu₂ ih =>
    obtain ⟨ls, h, hup, hdown, hlen⟩ := ih
    obtain ⟨d₁, hd₁, hsub₁, hsup₁⟩ := hup c₁' h₁
    obtain ⟨d₂, hd₂, hsub₂, hsup₂⟩ := hup c₂' h₂
    have hd : ∀ l ∈ d₁.resolvent d₂ u, l ∈ c₁'.resolvent c₂' u ∨ l = (v, !b) := fun l hl => by
      rcases FiniteClause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact (hsup₁ l hl).imp_left fun hl' => FiniteClause.mem_resolvent.2 (Or.inl ⟨hl', hne⟩)
      · exact (hsup₂ l hl).imp_left fun hl' => FiniteClause.mem_resolvent.2 (Or.inr ⟨hl', hne⟩)
    refine ⟨_ :: ls, h.resolvent u hd₁ hd₂ (hsub₁ _ hu₁) (hsub₂ _ hu₂), fun e he => ?_,
      fun e he => ?_, congrArg Nat.succ hlen⟩
    · rcases List.mem_cons.1 he with rfl | he
      · refine ⟨_, List.mem_cons_self, fun l hl => ?_, hd⟩
        rcases FiniteClause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
        · exact FiniteClause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl, hne⟩)
        · exact FiniteClause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl, hne⟩)
      · obtain ⟨e', he', h₁, h₂⟩ := hup e he
        exact ⟨e', List.mem_cons_of_mem _ he', h₁, h₂⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨_, List.mem_cons_self, hd⟩
      · obtain ⟨e', he', h₁⟩ := hdown e he
        exact ⟨e', List.mem_cons_of_mem _ he', h₁⟩

/-- **Composing proofs.** A proof from `ψ` replays on top of a proof from `φ` among whose lines are
all clauses of `ψ`. The lines added are lines of the proof from `ψ`, and every line of the proof
from `ψ` is a line of the result. -/
theorem IsProof.comp (hψ : ψ.IsProof ls') (h : φ.IsProof ls) (hψφ : ∀ c ∈ ψ, c ∈ ls) :
    ∃ ls'', φ.IsProof (ls'' ++ ls) ∧ (∀ c ∈ ls', c ∈ ls'' ++ ls) ∧ ∀ c ∈ ls'', c ∈ ls' := by
  induction hψ with
  | nil => exact ⟨[], h, by simp, by simp⟩
  | @mem ls' c _ hc ih =>
    obtain ⟨ls'', h'', hup, hdown⟩ := ih
    refine ⟨ls'', h'', fun e he => ?_, fun e he => List.mem_cons_of_mem _ (hdown e he)⟩
    rcases List.mem_cons.1 he with rfl | he
    exacts [List.mem_append_right _ (hψφ _ hc), hup e he]
  | @resolvent ls' c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨ls'', h'', hup, hdown⟩ := ih
    refine ⟨_ :: ls'', h''.resolvent v (hup _ h₁) (hup _ h₂) hv₁ hv₂, fun e he => ?_,
      fun e he => ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hup e he)]
    · rcases List.mem_cons.1 he with rfl | he
      exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hdown e he)]

/-! ### Restricting proofs by partial assignments -/

/-- `φ` restricted by the partial assignment `ρ`, which fixes every variable `v` with
`ρ v = some b` to `b`: the clauses that `ρ` satisfies are dropped, and the literals of fixed
variables are removed from the others. -/
@[expose] def restrictBy (φ : ClauseSet V) (ρ : V → Option Bool) : ClauseSet V :=
  (φ.filter fun c => ∀ l ∈ c, ρ l.1 ≠ some l.2).image
    (Finset.filter fun l => ρ l.1 = none)

/-- A clause belongs to `φ.restrictBy ρ` iff it is obtained from a clause of `φ` not satisfied by
`ρ` by keeping only the literals on variables where `ρ` is `none`. -/
@[simp] theorem mem_restrictBy {ρ : V → Option Bool} :
    c ∈ φ.restrictBy ρ ↔
      ∃ d ∈ φ, (∀ l ∈ d, ρ l.1 ≠ some l.2) ∧ d.filter (fun l => ρ l.1 = none) = c := by
  simp [restrictBy, and_assoc]

/-- A formula restricted by `ρ` mentions only variables that `ρ` does not fix. -/
theorem eq_none_of_mem_restrictBy {ρ : V → Option Bool} (hc : c ∈ φ.restrictBy ρ)
    {l : Literal V} (hl : l ∈ c) : ρ l.1 = none := by
  simp only [restrictBy, Finset.mem_image, Finset.mem_filter] at hc
  obtain ⟨d, -, rfl⟩ := hc
  simpa using (Finset.mem_filter.1 hl).2

/-- The lines of a proof from a formula restricted by `ρ` mention only variables that `ρ` does not
fix. -/
theorem IsProof.eq_none_of_restrictBy {ρ : V → Option Bool} (h : (φ.restrictBy ρ).IsProof ls)
    (hc : c ∈ ls) {l : Literal V} (hl : l ∈ c) : ρ l.1 = none := by
  obtain ⟨d, hd, b, hb⟩ := mem_vars.1 (h.fst_mem_vars hc hl)
  exact eq_none_of_mem_restrictBy (l := (l.1, b)) hd hb

/-- **Restricting a proof by a partial assignment.** A proof from `φ` becomes a proof from `φ`
restricted by `ρ`. Every line of the original proof that `ρ` does not satisfy is replaced by a line
of the new proof with a subset of its literals, and the lines of the new proof have, in order,
subsets of the literals of distinct lines of the original proof that `ρ` does not satisfy. In
particular the new proof has at most as many lines with any property inherited by clauses with
more literals as the original proof has unsatisfied lines with that property. -/
theorem IsProof.restrictBy (h : φ.IsProof ls) (ρ : V → Option Bool) :
    ∃ ls', (φ.restrictBy ρ).IsProof ls' ∧
      (∀ c ∈ ls, (∀ l ∈ c, ρ l.1 ≠ some l.2) → ∃ c' ∈ ls', ∀ l ∈ c', l ∈ c) ∧
      ∃ ks, ks.Sublist ls ∧ (∀ c ∈ ks, ∀ l ∈ c, ρ l.1 ≠ some l.2) ∧
        List.Forall₂ (fun c' c => ∀ l ∈ c', l ∈ c) ls' ks := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, [], .slnil, by simp, .nil⟩
  | @mem ls c _ hc ih =>
    obtain ⟨ls', h', hsub, ks, hks, hfree, hF⟩ := ih
    by_cases hsat : ∀ l ∈ c, ρ l.1 ≠ some l.2
    · refine ⟨c.filter (fun l => ρ l.1 = none) :: ls',
        h'.mem (mem_restrictBy.2 ⟨c, hc, hsat, rfl⟩), fun e he hfe => ?_, c :: ks, hks.cons_cons c,
        fun e he => ?_, .cons (fun l hl => (Finset.mem_filter.1 hl).1) hF⟩
      · rcases List.mem_cons.1 he with rfl | he
        · exact ⟨_, List.mem_cons_self, fun l hl => (Finset.mem_filter.1 hl).1⟩
        · obtain ⟨c', hc', hsub'⟩ := hsub e he hfe
          exact ⟨c', List.mem_cons_of_mem _ hc', hsub'⟩
      · rcases List.mem_cons.1 he with rfl | he
        exacts [hsat, hfree e he]
    · refine ⟨ls', h', fun e he hfe => ?_, ks, hks.cons c, hfree, hF⟩
      rcases List.mem_cons.1 he with rfl | he
      exacts [absurd hfe hsat, hsub e he hfe]
  | @resolvent ls c₁ c₂ u _ h₁ h₂ hu₁ hu₂ ih =>
    obtain ⟨ls', h', hsub, ks, hks, hfree, hF⟩ := ih
    by_cases hsat : ∀ l ∈ c₁.resolvent c₂ u, ρ l.1 ≠ some l.2
    swap
    · refine ⟨ls', h', fun e he hfe => ?_, ks, hks.cons _, hfree, hF⟩
      rcases List.mem_cons.1 he with rfl | he
      exacts [absurd hfe hsat, hsub e he hfe]
    have hne (c' : FiniteClause V) (hc' : c' ∈ ls') (l : Literal V) (hl : l ∈ c') : ρ l.1 = none :=
      h'.eq_none_of_restrictBy hc' hl
    -- the new line to add, if any: a subclause of the resolvent derivable from `ls'`
    have key : ∃ c', (c' ∈ ls' ∨ ∃ c₁' c₂', c₁' ∈ ls' ∧ c₂' ∈ ls' ∧ (u, true) ∈ c₁' ∧
        (u, false) ∈ c₂' ∧ c' = c₁'.resolvent c₂' u) ∧ ∀ l ∈ c', l ∈ c₁.resolvent c₂ u := by
      by_cases hv₁ : ∀ l ∈ c₁, ρ l.1 ≠ some l.2
      swap
      · -- `ρ` satisfies the first premise only through `u = true`, so not the second premise
        push Not at hv₁
        obtain ⟨l, hl, hρl⟩ := hv₁
        have hlu : l = (u, true) := by
          by_contra hlu
          exact hsat l (FiniteClause.mem_resolvent.2 (Or.inl ⟨hl, hlu⟩)) hρl
        subst hlu
        obtain ⟨c₂', hc₂', hsub₂⟩ := hsub c₂ h₂ fun l hl hρ => by
          by_cases hl' : l = (u, false)
          · subst hl'
            exact absurd (hρl.symm.trans hρ) (by simp)
          · exact hsat l (FiniteClause.mem_resolvent.2 (Or.inr ⟨hl, hl'⟩)) hρ
        refine ⟨c₂', Or.inl hc₂', fun l hl => FiniteClause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl,
          ?_⟩)⟩
        rintro rfl
        exact absurd (hρl.symm.trans (hne _ hc₂' (u, false) hl)) (by simp)
      by_cases hv₂ : ∀ l ∈ c₂, ρ l.1 ≠ some l.2
      swap
      · -- `ρ` satisfies the second premise only through `u = false`
        push Not at hv₂
        obtain ⟨l, hl, hρl⟩ := hv₂
        have hlu : l = (u, false) := by
          by_contra hlu
          exact hsat l (FiniteClause.mem_resolvent.2 (Or.inr ⟨hl, hlu⟩)) hρl
        subst hlu
        obtain ⟨c₁', hc₁', hsub₁⟩ := hsub c₁ h₁ hv₁
        refine ⟨c₁', Or.inl hc₁', fun l hl => FiniteClause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl,
          ?_⟩)⟩
        rintro rfl
        exact absurd (hρl.symm.trans (hne _ hc₁' (u, true) hl)) (by simp)
      obtain ⟨c₁', hc₁', hsub₁⟩ := hsub c₁ h₁ hv₁
      obtain ⟨c₂', hc₂', hsub₂⟩ := hsub c₂ h₂ hv₂
      by_cases hu₁' : (u, true) ∈ c₁'
      · by_cases hu₂' : (u, false) ∈ c₂'
        · refine ⟨_, Or.inr ⟨c₁', c₂', hc₁', hc₂', hu₁', hu₂', rfl⟩, fun l hl => ?_⟩
          rcases FiniteClause.mem_resolvent.1 hl with ⟨hl, hne'⟩ | ⟨hl, hne'⟩
          · exact FiniteClause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl, hne'⟩)
          · exact FiniteClause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl, hne'⟩)
        · refine ⟨c₂', Or.inl hc₂', fun l hl => FiniteClause.mem_resolvent.2 (Or.inr ⟨hsub₂ l hl,
          ?_⟩)⟩
          rintro rfl
          exact hu₂' hl
      · refine ⟨c₁', Or.inl hc₁', fun l hl => FiniteClause.mem_resolvent.2 (Or.inl ⟨hsub₁ l hl,
        ?_⟩)⟩
        rintro rfl
        exact hu₁' hl
    obtain ⟨c', hc' | ⟨c₁', c₂', hc₁', hc₂', hu₁', hu₂', rfl⟩, hsub'⟩ := key
    · refine ⟨ls', h', fun e he hfe => ?_, ks, hks.cons _, hfree, hF⟩
      rcases List.mem_cons.1 he with rfl | he
      exacts [⟨c', hc', hsub'⟩, hsub e he hfe]
    · refine ⟨_ :: ls', h'.resolvent u hc₁' hc₂' hu₁' hu₂', fun e he hfe => ?_, _ :: ks,
        hks.cons_cons _, fun e he => ?_, .cons hsub' hF⟩
      · rcases List.mem_cons.1 he with rfl | he
        · exact ⟨_, List.mem_cons_self, hsub'⟩
        · obtain ⟨e', he', hsub''⟩ := hsub e he hfe
          exact ⟨e', List.mem_cons_of_mem _ he', hsub''⟩
      · rcases List.mem_cons.1 he with rfl | he
        exacts [hsat, hfree e he]

end ClauseSet

end Cslib.Logic.PL
