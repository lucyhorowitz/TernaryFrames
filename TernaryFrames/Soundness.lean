/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import TernaryFrames.NMMS
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

/-!
# Soundness and Completeness of NMMS (Theorem 76)

This file states the soundness and completeness theorem for NMMS with respect to
**b-models** (implication-space-semantics models fit for a base), following
Hlobil & Brandom, *Reasons for Logic, Logic for Reasons* (RLLR), Ch. 3, Theorem 76.

## The setting

A **base** `𝔅` consists of:
- A base consequence relation `base : Finset (Formula α) → Finset (Formula α) → Prop`
  (in the book: `⊢_𝔅` on the base lexicon `𝔏_𝔅`).

A **b-model** (model fit for the base) is a consequence space `M` (an implication-space
structure) such that every base sequent is valid in `M`: for all `Γ`, `Δ`,
`base Γ Δ → M ⊨ Γ ⊢ Δ`.

Model-theoretic consequence relative to `base` (**b-validity**): a sequent `Γ ⊢ Δ` is
**b-valid** (`bValid base Γ Δ`) iff `Γ ⊢ Δ` holds in every b-model.

## Theorem 76 (RLLR, p. 222)

> *For any base `𝔅` and sentences `Γ`, `Δ` in the logically extended lexicon,*
> *`Γ ⊢^b Δ` if and only if `Γ ⊳ Δ` is derivable in NMMS_𝔅.*

In Lean:
```
NMMS base Γ Δ ↔ bValid base Γ Δ
```

**Soundness** (`→`): every NMMS-derivable sequent is b-valid.
**Completeness** (`←`): every b-valid sequent is NMMS-derivable.

## Status

The full formalization of the implication-space semantics (ISS) framework — including
the definition of implication spaces, the satisfaction relation `M ⊨ Γ ⊢ Δ`, and
b-models — is out of scope for this file. The theorem statements below are given with
`sorry` as placeholders, pending a fuller development of the ISS framework.

## References

* Hlobil, U. and Brandom, R. (2024). *Reasons for Logic, Logic for Reasons*. Ch. 3,
  Theorem 76 (p. 222).
-/

universe u

open Formula Finset

variable {α : Type u} [DecidableEq α]

/-! ## Placeholder for the ISS semantic framework

The following definitions sketch the semantic framework required for Theorem 76.
A full formalization would define implication spaces, the satisfaction relation, and
the notion of a model fitting a base. Here we use `sorry` axioms as stand-ins.
-/

/-- A **consequence space** (implication-space model) validates sequents `Γ ⊢ Δ`.
This is a placeholder for the full ISS definition; the actual definition requires
specifying the underlying set of states and the consequence relation. -/
axiom ConsequenceSpace (α : Type u) : Type u

/-- Satisfaction: `M ⊨ Γ ⊢ Δ` means the sequent `Γ ⊢ Δ` holds in model `M`.

In the book (RLLR, Ch. 3), this is defined in terms of the implication-space
semantics: a state `s ∈ M` validates `+A` iff `A ∈ s`; the sequent `Γ ⊢ Δ` holds
in `M` iff for every state `s`, if `s ⊨ Γ` then `s ⊨ Δ` (or equivalently, the
position `{+A | A ∈ Γ} ∪ {-A | A ∈ Δ}` is incoherent in the incoherence space). -/
axiom Satisfies {α : Type u} (M : ConsequenceSpace α)
    (Γ Δ : Finset (Formula α)) : Prop

/-- A model `M` **fits** the base `base` if every base sequent holds in `M`.

In RLLR (Def. 75, p. 221), a b-model is an implication-space `⟨C, ⟦·⟧⟩` such that
for every `⟨Γ, Δ⟩ ∈ ⊢_𝔅`, `⟦Γ⟧ ⊩ ⟦Δ⟧` holds in `C`. -/
def FitsBase (base : Finset (Formula α) → Finset (Formula α) → Prop)
    (M : ConsequenceSpace α) : Prop :=
  ∀ Γ Δ, base Γ Δ → Satisfies M Γ Δ

/-- **b-validity**: `Γ ⊢^b Δ` holds iff `Γ ⊢ Δ` is satisfied in every model fitting
the base. This is the model-theoretic consequence relation relative to `base`
(RLLR, Ch. 3, p. 221). -/
def bValid (base : Finset (Formula α) → Finset (Formula α) → Prop)
    (Γ Δ : Finset (Formula α)) : Prop :=
  ∀ M : ConsequenceSpace α, FitsBase base M → Satisfies M Γ Δ

/-! ## Theorem 76: Soundness and Completeness of NMMS -/

/-- **NMMS Soundness** (Theorem 76, `→` direction, RLLR p. 222):
Every sequent derivable in NMMS is b-valid: it holds in every model fitting the base.

The proof goes by induction on the derivation. Each logical rule is shown to preserve
b-validity (the rules are sound for the ISS consequence relation). The axiom rule is
sound by definition of `FitsBase`. -/
theorem NMMS_sound {Γ Δ : Finset (Formula α)}
    (base : Finset (Formula α) → Finset (Formula α) → Prop)
    (h : NMMS base Γ Δ) : bValid base Γ Δ := by
  sorry

/-- **NMMS Completeness** (Theorem 76, `←` direction, RLLR p. 222):
Every b-valid sequent is derivable in NMMS.

The proof uses a canonical model construction: the principal b-model for `base` is
the consequence space whose states are the NMMS-derivable sequents (or equivalently,
the Lindenbaum–Tarski algebra of NMMS). Every b-valid sequent is then realized as
an NMMS-derivable one. -/
theorem NMMS_complete {Γ Δ : Finset (Formula α)}
    (base : Finset (Formula α) → Finset (Formula α) → Prop)
    (h : bValid base Γ Δ) : NMMS base Γ Δ := by
  sorry

/-- **Theorem 76** (RLLR, p. 222): NMMS derivability coincides exactly with b-validity.

> *For any base `𝔅` and sentences `Γ`, `Δ` in the logically extended lexicon,*
> *`Γ ⊢^b Δ` if and only if `Γ ⊳ Δ` is derivable in `NMMS_𝔅`.*
-/
theorem NMMS_iff_bValid {Γ Δ : Finset (Formula α)}
    (base : Finset (Formula α) → Finset (Formula α) → Prop) :
    NMMS base Γ Δ ↔ bValid base Γ Δ :=
  ⟨NMMS_sound base, NMMS_complete base⟩
