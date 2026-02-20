/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import Mathlib.Tactic

/-!
# Formulas for NMMS and NMMS^ctr

This file defines the formula type used in the sequent calculi NMMS and NMMS^ctr
(from Hlobil & Brandom, *Reasons for Logic, Logic for Reasons*, Ch. 3).

The language consists of:
- Atomic sentences (parameterized by a base type `α`)
- Conjunction `∧`, disjunction `∨`, negation `¬`, and the conditional `→`

Note: the conditional `→` is **primitive** in these calculi, not defined as `¬A ∨ B`.

## References

* Hlobil, U. and Brandom, R. (2024). *Reasons for Logic, Logic for Reasons*. Ch. 3.
-/

universe u

/-- The inductive type of formulas over an atomic type `α`.

Connectives: conjunction (`and`), disjunction (`or`), negation (`neg`),
and the conditional (`imp`). The conditional is primitive, not defined as `¬A ∨ B`. -/
inductive Formula (α : Type u) where
  /-- An atomic formula. -/
  | atom : α → Formula α
  /-- Conjunction: `A ∧ B`. -/
  | and  : Formula α → Formula α → Formula α
  /-- Disjunction: `A ∨ B`. -/
  | or   : Formula α → Formula α → Formula α
  /-- Negation: `¬A`. -/
  | neg  : Formula α → Formula α
  /-- Conditional: `A → B`. -/
  | imp  : Formula α → Formula α → Formula α
  deriving DecidableEq, Repr

namespace Formula

variable {α : Type u}

/-- The size of a formula (number of connective symbols + 1). Used in soundness proofs
to show that conclusions are strictly larger than premiss subformulas. -/
def size : Formula α → ℕ
  | atom _   => 1
  | and A B  => A.size + B.size + 1
  | or A B   => A.size + B.size + 1
  | neg A    => A.size + 1
  | imp A B  => A.size + B.size + 1

theorem size_pos (A : Formula α) : 0 < A.size := by
  induction A <;> simp [size]

/-- A compound formula is not equal to any of its proper subformulas. -/
theorem ne_and_left (A B : Formula α) : and A B ≠ A := fun h => by
  have : (and A B).size = A.size := congrArg size h
  simp [size] at this; omega

theorem ne_and_right (A B : Formula α) : and A B ≠ B := fun h => by
  have : (and A B).size = B.size := congrArg size h
  simp [size] at this; have := size_pos A; omega

theorem ne_or_left (A B : Formula α) : or A B ≠ A := fun h => by
  have : (or A B).size = A.size := congrArg size h
  simp [size] at this; have := size_pos B; omega

theorem ne_or_right (A B : Formula α) : or A B ≠ B := fun h => by
  have : (or A B).size = B.size := congrArg size h
  simp [size] at this; have := size_pos A; omega

theorem ne_neg (A : Formula α) : neg A ≠ A := fun h => by
  have : (neg A).size = A.size := congrArg size h
  simp [size] at this

theorem ne_imp_left (A B : Formula α) : imp A B ≠ A := fun h => by
  have : (imp A B).size = A.size := congrArg size h
  simp [size] at this; have := size_pos B; omega

theorem ne_imp_right (A B : Formula α) : imp A B ≠ B := fun h => by
  have : (imp A B).size = B.size := congrArg size h
  simp [size] at this; have := size_pos A; omega

end Formula
