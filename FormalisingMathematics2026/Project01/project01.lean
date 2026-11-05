/-
Copyright (c) 2026 Wei Jia Ng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wei Jia Ng
-/
module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Céa's Lemma

We consider a Hilbert space `V` over `ℝ` equipped with a bounded bilinear form
`b : V →L[ℝ] V →L[ℝ] ℝ` and a bounded linear functional `f : V →L[ℝ] ℝ`.
Let `Vh ⊆ V` be a closed subspace.

Recall that `b` is *coercive* with constant `γ` iff
  `∃ γ, 0 < γ ∧ ∀ v, γ * ‖v‖ * ‖v‖ ≤ b v v`,
and *continuous* with constant `M` iff
  `∀ x y, |b x y| ≤ M * ‖x‖ * ‖y‖`.

Let `u ∈ V` solve the linear variational problem
  `b u v = f v`    for all `v ∈ V`, and
let `uh ∈ Vh` solve the corresponding Galerkin problem
  `b uh vh = f vh` for all `vh ∈ Vh`.
Under the hypothesis that `b` is coercive and continuous, we prove Céa's estimate:
  `‖u - uh‖ ≤ (M / γ) * ‖u - v‖` for every `v ∈ Vh`,
and hence Céa's lemma
  `‖u - uh‖ ≤ (M / γ) * ⨅ v : Vh, ‖u - v‖`,
with the infimum attained by the orthogonal projection of `u` onto `Vh`.

## Main results

* `galerkin_orthogonality`: `b (u - uh) v = 0` for all `v ∈ Vh`.
* `cea_estimate`: the bound `γ * ‖u - uh‖ ≤ M * ‖u - v‖` for all `v ∈ Vh`.
* `cea`: Céa's lemma, with the minimum over `Vh`.

## References

* We follow the definition and steps of lecture notes from
  MATH60022: Finite Elements: numerical analysis and implementation
  Source: https://finite-element.github.io/L5_convergence.html#thm-cea
* Also used LaxMilgram Theorem definition as reference
-/

@[expose] public section

namespace Cea

/- Define Hilbert Space V -/
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
/- Define bilinear function B -/
variable {B : V →L[ℝ] V →L[ℝ] ℝ}
/- Define linear function f -/
variable {f : V →L[ℝ] ℝ}
/- Vh is a subspace of V-/
variable {Vh : Subspace ℝ V}
/- u ∈ V and uh ∈ Vh (automatically true) -/
variable {u uh : V}

omit [CompleteSpace V] in
theorem galerkin_orthogonality (hu : ∀ v, B u v = f v) (huh : ∀ v ∈ Vh, B uh v = f v) :
  ∀ v ∈ Vh, B (u - uh) v = 0 := by
  -- take a v in Vh which is a subset of V which means its in both and applies to both functions
  intro v hv
  simp only [map_sub, sub_apply]
  rw [hu v, huh v hv]
  rw [sub_self]

/-- A bounded bilinear form `B` is *continuous*
if there is some positive constant M such that `∀ x y, |b x y| ≤ M * ‖x‖ * ‖y‖`.
-/
def IsContinuous (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop :=
  ∃M, 0 < M ∧ ∀ x y, |B x y| ≤ M * ‖x‖ * ‖y‖

/-- A bounded bilinear form `B` is *coercive*
if there is some constant `γ` such that `∃ γ, 0 < γ ∧ ∀ v, γ * ‖v‖ * ‖v‖ ≤ b v v`
-/
def IsCoercive (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop :=
  ∃γ, 0 < γ ∧ ∀ u, γ * ‖u‖ * ‖u‖ ≤ B u u

omit [CompleteSpace V] in
/--
* `cea_estimate`: the bound `γ * ‖u - uh‖ ≤ M * ‖u - v‖` for all `v ∈ Vh`.
-/
theorem cea_estimate
    (continuous : IsContinuous B) (coercive : IsCoercive B)
    (hu : ∀ v, B u v = f v) (huh : ∀ v ∈ Vh, B uh v = f v)
    (huh_mem : (uh : V) ∈ Vh) : -- why name huh_mem?
    ∃ M γ, 0 < M ∧ 0 < γ ∧ ∀ v ∈ Vh, γ * ‖u - uh‖ ≤ M * ‖u - v‖ := by
  rcases coercive with ⟨γ, γ_ge_0, coercivity⟩
  rcases continuous with ⟨M, M_ge_0, continuity⟩
  refine ⟨M, γ, M_ge_0, γ_ge_0, ?_⟩
  intro v hv
  have hortho := galerkin_orthogonality hu huh
  have hsub : v - uh ∈ Vh := Vh.sub_mem hv huh_mem
  specialize coercivity (u - uh)
  have hmain : γ * ‖u - uh‖ * ‖u - uh‖ ≤ M * ‖u - uh‖ * ‖u - v‖ :=
    calc γ * ‖u - uh‖ * ‖u - uh‖
        ≤ B (u - uh) (u - uh) := coercivity                  -- coercivity
      _ = B (u - uh) (u - v) + B (u - uh) (v - uh) := by     -- linearity
        simp only [map_sub, sub_apply]
        ring
      _ = B (u - uh) (u - v) := by rw [hortho _ hsub, add_zero] -- orthogonality
      _ ≤ |B (u - uh) (u - v)| := le_abs_self _
      _ ≤ M * ‖u - uh‖ * ‖u - v‖ := continuity _ _              -- continuity
  -- split on whether `‖u - v‖ > 0` or `‖u - v‖ = 0`
  by_cases hnormzero: ‖u - uh‖ = 0
  · rw [hnormzero, mul_zero]
    exact mul_nonneg M_ge_0.le (norm_nonneg _)
  · have huh : 0 < ‖u - uh‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormzero)
    nlinarith

/-- A closed subspace of a Hilbert space contains a point closest to any `u`. -/
theorem exists_minimizer (hVh : IsClosed (Vh : Set V)) (u : V) :
    ∃ v ∈ Vh, ∀ w ∈ Vh, ‖u - v‖ ≤ ‖u - w‖ := by
  have hcomplete : IsComplete (Vh : Set V) := hVh.isComplete
  rcases Vh.exists_norm_eq_iInf_of_complete_subspace hcomplete u with ⟨v, hv, hmin⟩
  have hmin_le : ∀ w : Vh, (⨅ z : Vh, ‖u - (z : V)‖) ≤ ‖u - w‖ := by
    intro w
    exact ciInf_le
      ⟨0, Set.forall_mem_range.2 fun z : Vh => norm_nonneg (u - (z : V))⟩ w
  refine ⟨v, hv, ?_⟩
  intro w hw
  calc
    ‖u - v‖ = ⨅ z : Vh, ‖u - (z : V)‖ := hmin
    _ ≤ ‖u - w‖ := hmin_le ⟨w, hw⟩

/-- **Céa's lemma**: the Galerkin solution is quasi-optimal, and the best
approximation in `Vh` exists. -/
theorem cea (continuous : IsContinuous B) (coercive : IsCoercive B)
    (hu : ∀ v, B u v = f v) (huh : ∀ v ∈ Vh, B uh v = f v)
    (huh_mem : uh ∈ Vh) (hVh : IsClosed (Vh : Set V)) :
    ∃ M γ, 0 < M ∧ 0 < γ ∧
      ∃ v ∈ Vh, (∀ w ∈ Vh, ‖u - v‖ ≤ ‖u - w‖) ∧ ‖u - uh‖ ≤ M / γ * ‖u - v‖ := by
  rcases cea_estimate continuous coercive hu huh huh_mem with
    ⟨M, γ, continuity, coercivity, h_estimate⟩
  refine ⟨M, γ, continuity, coercivity, ?_⟩
  rcases exists_minimizer hVh u with ⟨v, hv, hmin⟩
  refine ⟨v, hv, hmin, ?_⟩
  have hbound := h_estimate v hv
  field_simp [ne_of_gt coercivity]
  nlinarith [hbound]

/--
For completeness, we show solution exists with Lax-Milgram.
We change Lax-Milgram in the form we need: a coercive form and a functional
have a solution of `B u v = f v`.
Lax-Milgram only accepts the Mathlib version of IsCoercive so I couldn't use mine.
-/
theorem exists_solution {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W] {B : W →L[ℝ] W →L[ℝ] ℝ} (hB : _root_.IsCoercive B)
    (f : W →L[ℝ] ℝ) : ∃ u, ∀ v, B u v = f v := by
  refine ⟨hB.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ W).symm f),
    fun v => ?_⟩
  have h := hB.continuousLinearEquivOfBilin_apply
    (hB.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ W).symm f)) v
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [← h]
  exact InnerProductSpace.toDual_symm_apply

omit [CompleteSpace V] in
/-- Restricting `B` to a subspace gives a bilinear form on the subspace. -/
theorem exists_restrict (B : V →L[ℝ] V →L[ℝ] ℝ) (Vh : Submodule ℝ V) :
    ∃ Bh : Vh →L[ℝ] Vh →L[ℝ] ℝ, ∀ x y : Vh, Bh x y = B x y :=
  ⟨((ContinuousLinearMap.compL ℝ Vh V ℝ).flip Vh.subtypeL).comp (B.comp Vh.subtypeL),
    fun _ _ => rfl⟩

omit [CompleteSpace V] in
/-- Restricting coercivity to a subspace preserves the coercivity bound. -/
theorem IsCoercive.restrict (coercive : IsCoercive B)
    (Bh : Vh →L[ℝ] Vh →L[ℝ] ℝ) (hBh : ∀ x y : Vh, Bh x y = B x y) :
    IsCoercive Bh := by
  rcases coercive with ⟨γ, γ_ge_0, coercivity⟩
  refine ⟨γ, γ_ge_0, ?_⟩
  intro x
  rw [hBh]
  simpa using coercivity (x : V)

/-- Existence of both the exact solution and the Galerkin solution. -/
theorem exists_solutions (coercive : IsCoercive B)
    (f : V →L[ℝ] ℝ) (hVh : IsClosed (Vh : Set V)) :
    ∃ u uh : V, (∀ v, B u v = f v) ∧ uh ∈ Vh ∧ ∀ v ∈ Vh, B uh v = f v := by
  rcases exists_solution coercive f with ⟨u, hu⟩
  haveI : CompleteSpace Vh := hVh.completeSpace_coe
  rcases exists_restrict B Vh with ⟨Bh, hBh⟩
  rcases exists_solution (coercive.restrict Bh hBh) (f.comp Vh.subtypeL) with ⟨uh, huh⟩
  refine ⟨u, uh, hu, uh.2, fun v hv => ?_⟩
  have hGalerkin := huh ⟨v, hv⟩
  rw [hBh] at hGalerkin
  simpa using hGalerkin
end Cea
