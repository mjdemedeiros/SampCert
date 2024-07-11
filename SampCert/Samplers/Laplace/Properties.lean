/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform.Basic
import SampCert.Samplers.Bernoulli.Basic
import SampCert.Samplers.BernoulliNegativeExponential.Basic
import SampCert.Samplers.Geometric.Basic
import Mathlib.Data.ENNReal.Inv
import SampCert.Samplers.Laplace.Code

set_option linter.unusedTactic false

/-!
# ``DiscreteLaplaceSample`` Properties

This file proves evaluation and normalization properties of ``DiscreteLaplaceSample``.
-/

noncomputable section

open Classical PMF Nat Real BigOperators Finset

namespace SLang

@[simp]
theorem DiscreteLaplaceSampleLoopIn1Aux_normalizes (t : PNat) :
  (∑' x : ℕ × Bool, (DiscreteLaplaceSampleLoopIn1Aux t) x) = 1 := by
  simp only [DiscreteLaplaceSampleLoopIn1Aux, Bind.bind, Pure.pure, SLang.bind_apply,
    SLang.pure_apply, tsum_bool,  NNReal.coe_natCast,
     ENNReal.tsum_prod', Prod.mk.injEq, mul_ite, mul_one, mul_zero,
    and_true, and_false, ↓reduceIte, add_zero, zero_add]
  conv =>
    left
    right
    intro a
    congr
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
  simp only [↓reduceIte, NNReal.coe_natCast]
  have A : forall x a, (@ite ENNReal (x = a) (Classical.propDecidable (x = a)) 0
      (if a = x then UniformSample t x * BernoulliExpNegSample x t false else 0)) = 0 := by
    intro x a
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  have B : forall x a, (@ite ENNReal (x = a) (Classical.propDecidable (x = a)) 0
      (if a = x then UniformSample t x * BernoulliExpNegSample x t true else 0)) = 0 := by
    intro x a
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    intro a
    congr
    . right
      right
      intro x
      rw [A]
    . right
      right
      intro x
      rw [B]
  clear A B
  simp only [ NNReal.coe_natCast, tsum_zero, add_zero]
  conv =>
    left
    right
    intro a
    rw [← mul_add]
  have A : ∀ a, BernoulliExpNegSample a t false + BernoulliExpNegSample a t true = 1 := by
    intro a
    rw [← tsum_bool]
    rw [BernoulliExpNegSample_normalizes]
  conv =>
    left
    right
    intro a
    rw [A]
  clear A
  simp


theorem DiscreteLaplaceSampleLoopIn1Aux_apply_true (t : PNat) (n : ℕ) :
  DiscreteLaplaceSampleLoopIn1Aux t (n, true)
    = if n < t then ENNReal.ofReal (rexp (- (n / t))) / t else 0 := by
  simp [DiscreteLaplaceSampleLoopIn1Aux]
  conv =>
    left
    right
    intro a
    rw [tsum_bool]
  simp only [and_false, ↓reduceIte, and_true,  NNReal.coe_natCast,
    zero_add, mul_ite, mul_zero]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  have A : ∀ x, (@ite ENNReal (x = n) (propDecidable (x = n)) 0
      (@ite ENNReal (n = x) (instDecidableEqNat n x) (UniformSample t x * BernoulliExpNegSample x t true) 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro x
    rw [A]
  simp only [↓reduceIte, NNReal.coe_natCast, tsum_zero, add_zero]
  rw [UniformSample_apply']
  rw [BernoulliExpNegSample_apply_true n]
  simp
  rw [mul_comm]
  rw [← division_def]

theorem DiscreteLaplaceSampleLoopIn1Aux_apply_false (t : PNat) (n : ℕ) :
  DiscreteLaplaceSampleLoopIn1Aux t (n, false)
    = if n < t then (1 - ENNReal.ofReal (rexp (- (n / t)))) / t else 0 := by
  simp [DiscreteLaplaceSampleLoopIn1Aux]
  conv =>
    left
    right
    intro a
    rw [tsum_bool]
  simp only [and_true,  NNReal.coe_natCast, and_false,
    ↓reduceIte, add_zero, mul_ite, mul_zero]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  have A : ∀ x, (@ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
      (@ite ENNReal (n = x) (instDecidableEqNat n x) (UniformSample t x * BernoulliExpNegSample x t false) 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro x
    rw [A]
  simp only [↓reduceIte, NNReal.coe_natCast, tsum_zero,
    add_zero]
  rw [UniformSample_apply']
  rw [BernoulliExpNegSample_apply_false]
  simp
  rw [mul_comm]
  rw [← division_def]

theorem DiscreteLaplaceSampleLoopIn1_apply_pre (t : PNat) (n : ℕ) :
  (DiscreteLaplaceSampleLoopIn1 t) n =
    DiscreteLaplaceSampleLoopIn1Aux t (n, true) * (∑' (a : ℕ), DiscreteLaplaceSampleLoopIn1Aux t (a, true))⁻¹ := by
  simp only [DiscreteLaplaceSampleLoopIn1, Bind.bind, Pure.pure, SLang.bind_apply, ite_mul, zero_mul, SLang.pure_apply]
  conv =>
    left
    right
    intro a
    rw [probUntil_apply_norm _ _ _ (DiscreteLaplaceSampleLoopIn1Aux_normalizes t)]
  simp only [ENNReal.summable, forall_const, tsum_prod', ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp only [tsum_bool, ↓reduceIte, zero_add, tsum_zero]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  simp only [↓reduceIte, mul_one]
  have A : ∀ x, (@ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
            (DiscreteLaplaceSampleLoopIn1Aux t (x, true) * (∑' (b : ℕ), DiscreteLaplaceSampleLoopIn1Aux t (b, true))⁻¹ *
            @ite ENNReal (n = x) (Classical.propDecidable (n = (x, true).1)) 1 0)) = 0 := by
    intro x
    split
    . simp only
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp only [mul_zero]
  conv =>
    left
    right
    right
    intro x
    rw [A]
  clear A
  simp only [tsum_zero, add_zero]

theorem DiscreteLaplaceSampleLoopIn1_apply (t : PNat) (n : ℕ) (support : n < t) :
  (DiscreteLaplaceSampleLoopIn1 t) n = (ENNReal.ofReal ((rexp (-ENNReal.toReal (n / t))) * ((1 - rexp (- 1 / t)) / (1 - rexp (- 1))))) := by
  rw [DiscreteLaplaceSampleLoopIn1_apply_pre]
  rw [DiscreteLaplaceSampleLoopIn1Aux_apply_true]
  simp only [support, ↓reduceIte]
  conv =>
    left
    right
    right
    right
    intro a
    rw [DiscreteLaplaceSampleLoopIn1Aux_apply_true]

  rw [← @sum_add_tsum_nat_add' ENNReal _ _ _ _ _ t ENNReal.summable]
  have B : ∀ i : ℕ, (@ite ENNReal (i + ↑t < ↑t) (decLt (i + ↑t) ↑t) ((ENNReal.ofReal (rexp (- (↑(i + ↑t) / ↑↑t)))) / ↑↑t) 0) = 0 := by
    intro i
    split
    . rename_i h
      simp only [add_lt_iff_neg_right, not_lt_zero'] at h
    . simp only
  conv =>
    left
    right
    right
    right
    right
    intro i
    rw [B]
  clear B
  simp only [tsum_zero, add_zero]

  rw [sum_ite]
  simp only [mem_range, imp_self, forall_const, filter_true_of_mem, not_lt, not_le,
    filter_false_of_mem, sum_const_zero, add_zero]

  conv =>
    left
    right
    right
    right
    intro x
    rw [division_def]

  have A := @sum_mul ℕ ENNReal _ (Finset.range t) (fun x => ENNReal.ofReal (rexp (- (↑x / ↑↑t)))) ((↑↑t)⁻¹)
  rw [← A]
  clear A

  rw [ENNReal.ofReal_mul (exp_nonneg (-ENNReal.toReal (↑n / ↑↑t)))]
  rw [division_def]
  rw [mul_assoc]
  congr

  . rw [ENNReal.toReal_div]
    simp only [ENNReal.toReal_nat]

  . have A : ∀ i ∈ range t, 0 ≤ rexp (- (i / t)) := by
      intro i _
      apply exp_nonneg (-(↑i / ↑↑t))

    rw [← ENNReal.ofReal_sum_of_nonneg A]
    clear A

    have A : rexp (- 1 / t) ≠ 1 := by
      rw [← Real.exp_zero]
      by_contra h
      simp only [exp_zero, exp_eq_one_iff, div_eq_zero_iff, neg_eq_zero, one_ne_zero, cast_eq_zero,
        PNat.ne_zero, or_self] at h
    have X := @geom_sum_Ico' ℝ _ (rexp (- 1 / t)) A 0 t (Nat.zero_le t)
    simp only [Ico_zero_eq_range, _root_.pow_zero] at X
    rw [← exp_nat_mul] at X
    rw [mul_div_cancel₀ _ (NeZero.natCast_ne ↑t ℝ)] at X

    conv =>
      left
      right
      right
      left
      right
      right
      intro i
      rw [division_def]
      rw [neg_mul_eq_mul_neg]
      rw [Real.exp_nat_mul]
      rw [inv_eq_one_div]
      rw [neg_div']

    rw [X]
    clear X
    rw [ENNReal.mul_inv]
    . rw [mul_comm]
      rw [mul_assoc]
      rw [ENNReal.inv_mul_cancel]
      . rw [← ENNReal.ofReal_inv_of_pos]
        . rw [inv_div]
          simp only [mul_one]
        . apply div_pos
          . rw [Real.exp_neg]
            simp only [sub_pos]
            rw [inv_lt_one_iff]
            right
            rw [one_lt_exp_iff]
            simp only [zero_lt_one]
          . simp only [sub_pos, exp_lt_one_iff]
            rw [← neg_div']
            simp only [one_div, Left.neg_neg_iff, inv_pos, cast_pos, PNat.pos]
      . simp only [ne_eq, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, not_false_eq_true]
      . simp only [ne_eq, ENNReal.inv_eq_top, cast_eq_zero, PNat.ne_zero, not_false_eq_true]
    . simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, ENNReal.inv_eq_top, cast_eq_zero,
      PNat.ne_zero, not_false_eq_true, or_true]
    . simp only [ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true, ENNReal.inv_eq_zero,
      ENNReal.natCast_ne_top, or_self]

@[simp]
theorem DiscreteLaplaceSampleLoopIn2_eq (num : Nat) (den : PNat) :
  DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat)
    = probGeometric (BernoulliExpNegSample num den) := by
  unfold DiscreteLaplaceSampleLoopIn2
  unfold DiscreteLaplaceSampleLoopIn2Aux
  unfold probGeometric
  unfold geoLoopCond
  unfold geoLoopBody
  rfl



@[simp]
theorem DiscreteLaplaceSampleLoop_apply (num : PNat) (den : PNat) (n : ℕ) (b : Bool) :
  (DiscreteLaplaceSampleLoop num den) (b,n)
    = ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ n * (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) * ((2 : ℕ+): ENNReal)⁻¹ := by
  simp [DiscreteLaplaceSampleLoop, tsum_bool]
  rw [ENNReal.tsum_eq_add_tsum_ite (n + 1)]
  simp only [add_eq_zero, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right, and_true]
  have A : ∀ x, (@ite ENNReal (x = n + 1) (Classical.propDecidable (x = n + 1)) 0
      (@ite ENNReal (x = 0) (instDecidableEqNat x 0) 0
  (ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ (x - 1) * (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) *
    ((@ite ENNReal (b = false ∧ n = x - 1) instDecidableAnd 2⁻¹ 0 : ENNReal) + @ite ENNReal (b = true ∧ n = x - 1) instDecidableAnd 2⁻¹ 0 : ENNReal))) ) = 0 := by
    intro x
    split
    . simp only
    . split
      . simp only
      . split
        . split
          . rename_i h1 h2 h3 h4
            cases h3
            cases h4
            rename_i h5 h6 h7 h8
            subst h7
            contradiction
          . rename_i h1 h2 h3 h4
            cases h3
            simp only [not_and] at h4
            rename_i h5 h6
            subst h6
            have B : x = x - 1 + 1 := by
              exact (succ_pred h2).symm
            contradiction
        . split
          . rename_i h1 h2 h3 h4
            cases h4
            rename_i h5 h6
            subst h6
            have B : x = x - 1 + 1 := by
              exact (succ_pred h2).symm
            contradiction
          . rename_i h1 h2 h3 h4
            simp only [not_and, add_zero, mul_zero] at *

  conv =>
    left
    right
    right
    intro x
    rw [A]
  clear A

  simp only [tsum_zero, add_zero]
  congr
  split
  . rename_i h
    simp only [h, ↓reduceIte, add_zero]
  . simp only [zero_add, ite_eq_left_iff, Bool.not_eq_true]
    rename_i h1
    intro h2
    contradiction

@[simp]
theorem ite_simpl_1 (x y : ℕ) (a : ENNReal) : ite (x = y) 0 (ite (y = x) a 0) = 0 := by
  split
  . simp
  . rename_i h
    simp [h]
    intro h
    subst h
    contradiction

@[simp]
theorem ite_simpl_2 (x y : ℕ) (a : ENNReal) : ite (x = 0) 0 (ite ((y : ℤ) = -(x : ℤ)) a 0) = 0 := by
  split
  . simp
  . split
    . rename_i h1 h2
      have A : (y : ℤ) ≥ 0 := Int.NonNeg.mk (y + 0)
      rw [h2] at A
      simp at *
      subst A
      contradiction
    . simp

@[simp]
theorem ite_simpl_3 (x y : ℕ) (a : ENNReal) : ite (x = y + 1) 0 (ite (x = 0) 0 (ite (y = x - 1) a 0)) = 0 := by
  split
  . simp
  . split
    . simp
    . split
      . rename_i h1 h2 h3
        subst h3
        cases x
        . contradiction
        . simp at h1
      . simp

@[simp]
theorem ite_simpl_4 (x y : ℕ) (a : ENNReal) : ite ((x : ℤ) = - (y : ℤ)) (ite (y = 0) 0 a) 0 = 0 := by
  split
  . split
    . simp
    . rename_i h1 h2
      have B : (y : ℤ) ≥ 0 := by exact Int.NonNeg.mk (y + 0)
      have C : -(y : ℤ) ≥ 0 := by exact le_iff_exists_sup.mpr (Exists.intro (Int.ofNat x) (id h1.symm))
      cases y
      . contradiction
      . rename_i n
        simp at C
        contradiction
  . simp

@[simp]
theorem ite_simpl_5 (n c : ℕ) (a : ENNReal) (h : n ≠ 0) : ite (- (n : ℤ) = (c : ℤ)) a 0 = 0 := by
  split
  . rename_i h'
    have A : (n : ℤ) ≥ 0 := by exact Int.NonNeg.mk (n + 0)
    have B : -(n : ℤ) ≥ 0 := by exact le_iff_exists_sup.mpr (Exists.intro (Int.ofNat c) h')
    cases n
    . contradiction
    . rename_i n
      simp at B
      contradiction
  . simp

@[simp]
theorem DiscreteLaplaceSampleLoop_normalizes (num : PNat) (den : PNat) :
  (∑' x, (DiscreteLaplaceSampleLoop num den) x) = 1 := by
  simp only [DiscreteLaplaceSampleLoop, Bind.bind, DiscreteLaplaceSampleLoopIn2_eq, Pure.pure,
    SLang.bind_apply,
    NNReal.coe_natCast,  cast_one,
    one_div, SLang.pure_apply, ite_mul, tsum_bool, ↓reduceIte, zero_mul, ENNReal.tsum_prod',
    Prod.mk.injEq, mul_ite, mul_one, mul_zero, true_and, false_and, add_zero, zero_add]
  conv =>
    left
    left
    right
    intro b
    rw [ENNReal.tsum_eq_add_tsum_ite 0]
    rw [ENNReal.tsum_eq_add_tsum_ite (b + 1)]
    right
    right
    simp
  conv =>
    left
    right
    right
    intro b
    rw [ENNReal.tsum_eq_add_tsum_ite 0]
    rw [ENNReal.tsum_eq_add_tsum_ite (b + 1)]
    right
    right
    simp

  simp only [add_tsub_cancel_right, ↓reduceIte,  add_eq_zero, one_ne_zero,
    and_false,  NNReal.coe_natCast,
     cast_one, one_div, ite_mul, zero_mul]

  simp only [add_zero]

  have A : probGeometric (BernoulliExpNegSample (↑den) num) 0 = 0 := by simp
  rw [A]
  simp only [ge_iff_le, _root_.zero_le, tsub_eq_zero_of_le, ↓reduceIte,
    cast_one, one_div, zero_mul, ite_self,  add_eq_zero, one_ne_zero,
    and_false, NNReal.coe_natCast, add_tsub_cancel_right,
     zero_add]

  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_mul_right]
  rw [← mul_add]
  have A := BernoulliSample_normalizes' 1 2 (by exact NeZero.one_le)
  simp only [Fintype.univ_bool, cast_one, one_div, mem_singleton,
    not_false_eq_true, sum_insert, ↓reduceIte, sum_singleton] at A
  rw [add_comm] at A
  rw [A]
  clear A
  rw [mul_one]
  apply probGeometric_normalizes'
  . have A := BernoulliExpNegSample_normalizes den num
    rw [tsum_bool] at A
    trivial
  . simp

theorem avoid_double_counting (num den : PNat) :
  (∑' (x : Bool × ℕ), if x.1 = true → ¬x.2 = 0 then DiscreteLaplaceSampleLoop num den x else 0)
    = (((2 : ℕ+) : ENNReal))⁻¹ * (1 + ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) := by
  simp only [ENNReal.tsum_prod', DiscreteLaplaceSampleLoop_apply, tsum_bool, IsEmpty.forall_iff,
    ↓reduceIte, forall_true_left, ite_not]
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_mul_right]
  rw [tsum_shift'_1]
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_mul_right]
  rw [mul_comm]
  conv =>
    left
    right
    rw [mul_comm]
  rw [← mul_add]
  conv =>
    left
    right
    rw [mul_comm]
  conv =>
    left
    right
    right
    rw [mul_comm]
  rw [← mul_add]

  rw [ENNReal.tsum_geometric]
  conv =>
    left
    right
    right
    right
    right
    intro i
    rw [pow_add]
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_geometric]
  rw [mul_add]
  have B : (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) ≠ 0 := by
    simp only [ne_eq, tsub_eq_zero_iff_le, ENNReal.one_le_ofReal, one_le_exp_iff,
      Left.nonneg_neg_iff, not_le]
    rw [div_pos_iff]
    left
    simp only [cast_pos, PNat.pos, and_self]
  have C : (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) ≠ ⊤ := by
    simp only [ne_eq, ENNReal.sub_eq_top_iff, ENNReal.one_ne_top, ENNReal.ofReal_ne_top,
      not_false_eq_true, and_true]
  conv =>
    left
    right
    left
    rw [mul_comm]
  rw [ENNReal.inv_mul_cancel B C]
  conv =>
    left
    right
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  rw [ENNReal.inv_mul_cancel B C]
  rw [one_mul]
  rw [pow_one]

theorem laplace_normalizer_swap (num den : ℕ+) :
  (1 - rexp (-(↑↑den / ↑↑num))) * (1 + rexp (-(↑↑den / ↑↑num)))⁻¹ =
  (rexp (↑↑den / ↑↑num) - 1) * (rexp (↑↑den / ↑↑num) + 1)⁻¹ := by

  have X : 0 ≤ rexp (-(↑↑den / ↑↑num)) := by apply exp_nonneg (-(↑↑den / ↑↑num))
  have Y : 0 ≤ rexp ((↑↑den / ↑↑num)) := by apply exp_nonneg ((↑↑den / ↑↑num))

  have A : rexp (↑↑den / ↑↑num) + 1 ≠ 0 := by
    apply _root_.ne_of_gt
    apply Right.add_pos_of_nonneg_of_pos Y
    simp
  have B : 1 + rexp (-(↑↑den / ↑↑num)) ≠ 0 := by
    apply _root_.ne_of_gt
    apply Right.add_pos_of_pos_of_nonneg _ X
    simp

  rw [← division_def]
  rw [div_eq_iff B]
  rw [mul_comm]
  rw [← mul_assoc]
  rw [← division_def]

  apply Eq.symm
  rw [div_eq_iff A]

  rw [mul_add]
  rw [_root_.sub_mul]
  rw [_root_.sub_mul]
  rw [add_mul]
  rw [_root_.mul_sub]
  rw [_root_.mul_sub]

  simp only [one_mul, mul_one]

  rw [← exp_add]
  simp

/--
Closed form for the evaluation of the ``SLang`` Laplace sampler.
-/
@[simp]
theorem DiscreteLaplaceSample_apply (num den : PNat) (x : ℤ) :
  (DiscreteLaplaceSample num den) x = ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs x / ((num : NNReal) / (den : NNReal)))))) := by
  simp only [DiscreteLaplaceSample, Bind.bind, not_and, Pure.pure, SLang.bind_apply,
     decide_eq_true_eq, ENNReal.summable,
    Bool.forall_bool, and_self, tsum_prod', tsum_bool, IsEmpty.forall_iff, ↓reduceIte, tsum_zero,
    forall_true_left, ite_not, zero_add, ite_mul, zero_mul, SLang.pure_apply, mul_ite, mul_one,
    mul_zero, one_div, Int.cast_abs]
  rw [← Complex.abs_ofReal]

  have OR : x ≥ 0 ∨ x < 0 := by exact le_or_gt 0 x
  cases OR
  . rename_i h1
    lift x to ℕ using h1
    conv =>
      left
      left
      rw [ENNReal.tsum_eq_add_tsum_ite x]

    simp only [DiscreteLaplaceSampleLoop_normalizes, probUntil_apply_norm]
    simp (config := { contextual := true }) only [↓reduceIte, IsEmpty.forall_iff, decide_True,
      DiscreteLaplaceSampleLoop_apply, decide_eq_true_eq, Nat.cast_inj, ite_simpl_1, tsum_zero,
      add_zero, forall_true_left, decide_not, Bool.not_eq_true', decide_eq_false_iff_not, ite_not,
      ite_mul, zero_mul, ite_simpl_4, NNReal.coe_natCast, inv_div, Int.cast_ofNat,
      Complex.abs_natCast]
    conv =>
      right
      simp only [PNat.val_ofNat, reduceSucc, cast_ofNat, Int.cast_natCast, Complex.ofReal_natCast,
        Complex.abs_natCast]
    conv =>
      right
      right
      left
      rw [division_def]
    rw [avoid_double_counting]
    rw [ENNReal.mul_inv]
    . simp only [inv_inv]

      have A : 0 ≤ rexp (-(↑↑den / ↑↑num)) := by apply exp_nonneg (-(↑↑den / ↑↑num))
      have B : 0 ≤ rexp ((↑↑den / ↑↑num)) := by apply exp_nonneg ((↑↑den / ↑↑num))


      -- Start of first rewrite

      rw [ENNReal.ofReal_mul]
      conv =>
        right
        rw [mul_comm]
        left
        right
        rw [division_def]
        rw [neg_mul_eq_mul_neg]
        rw [exp_nat_mul]
        rw [inv_div]

      rw [ENNReal.ofReal_pow]

      conv =>
        left
        left
        rw [mul_assoc]
      conv =>
        left
        rw [mul_assoc]

      congr

      --end of first rewrite

      have X : ((2 : ℕ+) : ENNReal) ≠ 0 := by simp
      have Y : ((2 : ℕ+) : ENNReal) ≠ ⊤ := by simp

      rw [← mul_assoc]
      conv =>
        left
        left
        rw [mul_assoc]
        right
        rw [ENNReal.inv_mul_cancel X Y]

      simp only [mul_one]

      clear X Y

      -- end of second rewrite

      rw [ENNReal.ofReal_one.symm]
      rw [← ENNReal.ofReal_add]
      rw [← ENNReal.ofReal_sub]
      rw [← ENNReal.ofReal_inv_of_pos]
      rw [← ENNReal.ofReal_mul]

      congr 1

      -- end of 3rd rewrite
      rw [laplace_normalizer_swap]

      . simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]
        rw [div_nonneg_iff]
        left
        simp only [cast_nonneg, and_self]
      . refine Right.add_pos_of_pos_of_nonneg ?inl.intro.e_a.ha A
        simp only [zero_lt_one] -- 0 < 1 + rexp (-(↑↑den / ↑↑num))
      . exact A
      . simp only [zero_le_one] -- 0 ≤ 1
      . exact A
      . exact A
      . have X : 0 ≤ (rexp (↑↑den / ↑↑num) - 1) := by
          simp only [sub_nonneg, one_le_exp_iff]
          rw [div_nonneg_iff]
          left
          simp only [cast_nonneg, and_self]
        have Y : 0 ≤ (rexp (↑↑den / ↑↑num) + 1)⁻¹ := by
          rw [inv_nonneg]
          refine Right.add_nonneg B ?hb
          simp only [zero_le_one]
        exact mul_nonneg X Y
    . left
      simp only [PNat.val_ofNat, reduceSucc, cast_ofNat, ne_eq, ENNReal.inv_eq_zero,
        ENNReal.two_ne_top, not_false_eq_true]
    . left
      simp only [ne_eq, ENNReal.inv_eq_top, cast_eq_zero, PNat.ne_zero, not_false_eq_true]
  . rename_i h1
    have A : ∃ n : ℕ, - n = x := by
      cases x
      . contradiction
      . rename_i a
        exists (a + 1)
    cases A
    rename_i n h2
    conv =>
      left
      right
      rw [ENNReal.tsum_eq_add_tsum_ite n]

    simp only [DiscreteLaplaceSampleLoop_normalizes, probUntil_apply_norm]
    subst h2
    have X : n ≠ 0 := by
      by_contra h
      subst h
      simp only [CharP.cast_eq_zero, neg_zero, lt_self_iff_false] at h1
    simp (config := { contextual := true }) only [IsEmpty.forall_iff, decide_True, ↓reduceIte,
      DiscreteLaplaceSampleLoop_apply, decide_eq_true_eq, ne_eq, X, not_false_eq_true, ite_simpl_5,
      tsum_zero, forall_true_left, neg_inj, Nat.cast_inj, decide_not, Bool.not_eq_true',
      decide_eq_false_iff_not, ite_not, ite_mul, zero_mul, ite_simpl_1, add_zero, zero_add,
      NNReal.coe_natCast, inv_div, Int.cast_neg, Int.cast_ofNat, AbsoluteValue.map_neg,
      Complex.abs_natCast]
    conv =>
      right
      simp only [PNat.val_ofNat, reduceSucc, cast_ofNat, Int.cast_natCast, Complex.ofReal_neg,
        Complex.ofReal_natCast, map_neg_eq_map, Complex.abs_natCast]
    conv =>
      right
      right
      left
      rw [division_def]
    rw [avoid_double_counting]
    rw [ENNReal.mul_inv]
    . simp only [inv_inv]

      have A : 0 ≤ rexp (-(↑↑den / ↑↑num)) := by apply exp_nonneg (-(↑↑den / ↑↑num))
      have B : 0 ≤ rexp ((↑↑den / ↑↑num)) := by apply exp_nonneg ((↑↑den / ↑↑num))


      -- Start of first rewrite

      rw [ENNReal.ofReal_mul]
      conv =>
        right
        rw [mul_comm]
        left
        right
        rw [division_def]
        rw [neg_mul_eq_mul_neg]
        rw [exp_nat_mul]
        rw [inv_div]

      rw [ENNReal.ofReal_pow]

      conv =>
        left
        left
        rw [mul_assoc]
      conv =>
        left
        rw [mul_assoc]

      congr

      --end of first rewrite

      have X : ((2 : ℕ+) : ENNReal) ≠ 0 := by simp
      have Y : ((2 : ℕ+) : ENNReal) ≠ ⊤ := by simp

      rw [← mul_assoc]
      conv =>
        left
        left
        rw [mul_assoc]
        right
        rw [ENNReal.inv_mul_cancel X Y]

      simp only [mul_one]

      clear X Y

      -- end of second rewrite

      rw [ENNReal.ofReal_one.symm]
      rw [← ENNReal.ofReal_add]
      rw [← ENNReal.ofReal_sub]
      rw [← ENNReal.ofReal_inv_of_pos]
      rw [← ENNReal.ofReal_mul]

      congr 1

      rw [laplace_normalizer_swap]
      . simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]
        rw [div_nonneg_iff]
        left
        simp only [cast_nonneg, and_self]
      . apply Right.add_pos_of_pos_of_nonneg
        simp only [zero_lt_one]
        exact A
      . exact A
      . simp only [zero_le_one] -- 0 ≤ 1
      . exact A
      . exact A
      . have X : 0 ≤ (rexp (↑↑den / ↑↑num) - 1) := by
          simp only [sub_nonneg, one_le_exp_iff]
          rw [div_nonneg_iff]
          left
          simp only [cast_nonneg, and_self]
        have Y : 0 ≤ (rexp (↑↑den / ↑↑num) + 1)⁻¹ := by
          rw [inv_nonneg]
          refine Right.add_nonneg B ?hb
          simp only [zero_le_one]
        exact mul_nonneg X Y

    . left
      simp only [PNat.val_ofNat, reduceSucc, cast_ofNat, ne_eq, ENNReal.inv_eq_zero,
        ENNReal.two_ne_top, not_false_eq_true]
    . left
      simp only [ne_eq, ENNReal.inv_eq_top, cast_eq_zero, PNat.ne_zero, not_false_eq_true]

/--
``SLang`` Laplace sampler is a proper distribution.
-/
@[simp]
theorem DiscreteLaplaceSample_normalizes (num den : PNat) :
  ∑' x : ℤ, (DiscreteLaplaceSample num den) x = 1 := by
  simp only [DiscreteLaplaceSample, Bind.bind, not_and, Pure.pure, SLang.bind_apply]
  have A := DiscreteLaplaceSampleLoop_normalizes num den
  conv =>
    left
    right
    intro x
    right
    intro a
    rw [probUntil_apply_norm _ _ _ A]
  simp only [ENNReal.tsum_prod']

  -- Commuting the integer and natural summand makes the proof simpler
  rw [ENNReal.tsum_comm]
  conv =>
    left
    right
    intro b
    rw [ENNReal.tsum_comm]

  simp only [decide_eq_true_eq, tsum_bool, IsEmpty.forall_iff, ↓reduceIte, forall_true_left,
    ite_not, ite_mul, zero_mul, SLang.pure_apply, mul_ite, mul_one, mul_zero, tsum_ite_eq]

  have B : ∀ a, (@ite ENNReal (a = 0) (instDecidableEqNat a 0) 0
  (DiscreteLaplaceSampleLoop num den (true, a) *
    (∑' (b : ℕ), DiscreteLaplaceSampleLoop num den (false, b) +
        ∑' (b : ℕ), if b = 0 then 0 else DiscreteLaplaceSampleLoop num den (true, b))⁻¹))
        = (@ite ENNReal (a = 0) (instDecidableEqNat a 0) 0
    (DiscreteLaplaceSampleLoop num den (true, a))) * ((∑' (b : ℕ), DiscreteLaplaceSampleLoop num den (false, b) +
        ∑' (b : ℕ), if b = 0 then 0 else DiscreteLaplaceSampleLoop num den (true, b))⁻¹) := by
    intro a
    simp

  conv =>
    left
    right
    right
    intro a
    rw [B]
  clear B

  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_mul_right]
  rw [← add_mul]

  rw [ENNReal.mul_inv_cancel]
  . simp only [DiscreteLaplaceSampleLoop_apply, ne_eq, add_eq_zero, ENNReal.tsum_eq_zero,
    _root_.mul_eq_zero, pow_eq_zero_iff', ENNReal.ofReal_eq_zero, tsub_eq_zero_iff_le,
    ENNReal.one_le_ofReal, one_le_exp_iff, Left.nonneg_neg_iff, ENNReal.inv_eq_zero,
    ENNReal.natCast_ne_top, or_false, ite_eq_left_iff, not_and, not_forall, exists_prop]
    intro _
    existsi 1
    simp
    apply exp_pos (-(↑↑den / ↑↑num))
  . rw [← @ENNReal.tsum_add]
    rw [ne_iff_lt_or_gt]
    left
    have B : (∑' (a : ℕ), (DiscreteLaplaceSampleLoop num den (false, a) + if a = 0 then 0 else DiscreteLaplaceSampleLoop num den (true, a))) ≤ (∑' (x : Bool × ℕ), DiscreteLaplaceSampleLoop num den x) := by
      rw [ENNReal.tsum_prod']
      rw [ENNReal.tsum_comm]
      conv =>
        right
        right
        intro b
        rw [tsum_bool]
      apply ENNReal.tsum_le_tsum
      intro a
      split
      . simp
      . simp

    have E : (∑' (x : Bool × ℕ), DiscreteLaplaceSampleLoop num den x) < ⊤ := by simp

    apply LE.le.trans_lt B E

-- set_option pp.coercions false
-- set_option pp.notation false
-- set_option pp.all true


/--
PMF for the geometric distribution as seen in literature
-/
def Geo (r : ℝ) (n : ℕ) : ENNReal := (1 - ENNReal.ofReal r) ^ n * ENNReal.ofReal r

/-
``probGeometric`` in terms of ``Geo``
-/
lemma probGeometric_apply_Geo (t : SLang Bool) (trial_spec : t false + t true = 1) (trial_spec' : t true < 1) (x : ℕ) :
      probGeometric t x = if x = 0 then 0 else Geo (ENNReal.toReal (1 - t true)) (x - 1) := by
  rw [probGeometric_apply]
  split <;> try simp
  rw [Geo]
  congr
  · simp
    rw [ENNReal.sub_sub_cancel] <;> try simp
    exact le_of_lt trial_spec'
  · simp
    exact trial_one_minus t trial_spec

-- set_option pp.coercions false
-- set_option pp.notation false
-- set_option pp.all true

lemma nat_div_eq_le_lt_iff {a b c : ℕ} (Hc : 0 < c) : a = b / c <-> (a * c ≤ b ∧ b < (a +  1) * c) := by
  apply Iff.intro
  · intro H
    apply And.intro
    · apply (Nat.le_div_iff_mul_le Hc).mp
      exact Nat.le_of_eq H
    · apply (Nat.div_lt_iff_lt_mul Hc).mp
      apply Nat.lt_succ_iff.mpr
      exact Nat.le_of_eq (id (Eq.symm H))
  · intro ⟨ H1, H2 ⟩
    apply LE.le.antisymm
    · apply (Nat.le_div_iff_mul_le Hc).mpr
      apply H1
    · apply Nat.lt_succ_iff.mp
      simp
      apply (Nat.div_lt_iff_lt_mul Hc).mpr
      apply H2


lemma euc_decomp (n : ℕ) (D : ℕ) : ∃ n1 n2 : ℕ, (n2 < D) ∧ n = n1 * D + n2 := sorry



/--
Equivalence between the optimized an unoptimized sampling loops
-/
theorem DiscreteLaplaceSampleLoop_equiv (num : PNat) (den : PNat) :
  DiscreteLaplaceSampleLoop num den = DiscreteLaplaceSampleLoop' num den := by
  apply SLang.ext
  intro ⟨ b, n ⟩

  -- Apply DiscreteLaplaceSampleLoop spec and simplify
  simp [DiscreteLaplaceSampleLoop_apply]
  simp only [DiscreteLaplaceSampleLoop'] -- DiscreteLaplaceSampleLoopIn2_eq, Pure.pure, bind_apply]

  -- FIXME: Refactor this to a calc proof?

  -- Evaluate the indepenent Bern(1/2) sample
  have H :
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← DiscreteLaplaceSampleLoopIn2 1 1
        let B ← BernoulliSample 1 2 DiscreteLaplaceSampleLoop'.proof_3
        Pure.pure (B, (U + ↑num * (v - 1)) / ↑den)) (b, n) =
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← DiscreteLaplaceSampleLoopIn2 1 1
        Pure.pure (U + ↑num * (v - 1)) / ↑den) (n) * 2⁻¹ := by
      simp
      rw [<- ENNReal.tsum_mul_right]
      congr
      apply funext
      intro x
      rw [mul_assoc]
      congr
      rw [<- ENNReal.tsum_mul_right]
      congr
      apply funext
      intro y
      split <;> try simp
      repeat rw [mul_assoc]
      congr
      split
      all_goals sorry
  rw [H]
  clear H
  congr

  -- Evaluate the DiscreteSampleLoopIn2 term to geometric distribution and reindex
  have H :
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← DiscreteLaplaceSampleLoopIn2 1 1
        Pure.pure (U + ↑num * (v - 1)) / ↑den) n =
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← Geo (1 - Real.exp (- 1))
        Pure.pure (U + ↑num * v) / ↑den) n := by
    simp only [Bind.bind, DiscreteLaplaceSampleLoopIn2_eq, bind_apply] -- probGeometric_apply, BernoulliExpNegSample_apply_true]
    apply tsum_congr
    intro a
    congr 1
    have S1 : BernoulliExpNegSample 1 1 false + BernoulliExpNegSample 1 1 true = 1 := sorry
    have S2 : BernoulliExpNegSample 1 1 true < 1 := sorry
    conv =>
      enter [1, 1, b]
      rw [probGeometric_apply_Geo _ S1 S2]
    conv =>
      enter [2]
      rw [<- tsum_shift_1]
    apply tsum_congr
    intro b
    split <;> try simp
    congr
    rw [eq_sub_iff_add_eq]
    rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
    case G1 =>
      apply ENNReal.ofReal_le_one.mpr
      apply exp_le_one_iff.mpr
      simp
    case G2 => simp
    rw [ENNReal.toReal_ofReal']
    rw [max_eq_left ?G1]
    case G1 => exact exp_nonneg (-1)
    simp
  rw [H]
  clear H

  -- Decompose n with Euclidean division
  rcases (euc_decomp n num) with ⟨ vx, ux, Hux, Hn ⟩
  rw [Hn]
  simp only [Bind.bind, Pure.pure, Pi.natCast_def, bind_apply, Pi.div_apply, pure_apply]


  -- Simplify and evaluate singleton sum
  conv =>
    enter [2, 1, a]
    rw [<- ENNReal.tsum_mul_left]
  rw [<- ENNReal.tsum_prod]
  rw [tsum_eq_single (vx, ux) ?G1]
  case G1 =>
    intro b' Hb'
    apply Classical.by_contradiction
    simp
    intro H1 _ Hk
    apply H1
    simp [DiscreteLaplaceSampleLoopIn1]
    rw [DiscreteLaplaceSampleLoopIn1Aux_apply_true]
    split
    · exfalso
      apply Hb'
      -- Euclidean division uniqueness
      sorry
    · rfl

  skip
  sorry


  -- rw [<- @tsum_subtype_eq_of_support_subset ENNReal (ℕ × ℕ) _ _ _ ({(ux, vx)} : Set (ℕ × ℕ)) ?G1]
  -- case G1 =>
  --   simp [Function.support]
  --   intro a b H1 _ H3
  --   have H4 : (a < num) := by
  --     apply Nat.lt_of_not_ge
  --     intro HK
  --     apply H1
  --   -- Euclidean division uniqueness
  --   sorry
  -- simp [tsum_def]


--   rw [@HasSum.tsum_eq _ _ _ _ _ ((fun p => DiscreteLaplaceSampleLoopIn1 num p.2 *(Geo (1 - rexp (-1)) p.1 * (1 / ↑↑den))) (ux, vx)) _ ?GEq]
--   case GEq =>
--     #check @hasSum_single _ _ _ _ (fun (p : ℕ × ℕ) => DiscreteLaplaceSampleLoopIn1 num p.2 *(Geo (1 - rexp (-1)) p.1 * (1 / ↑↑den))) _ ?G2
--
--
--     -- apply
--     sorry
--     -- all_goals sorry
--

  -- have HS : HasSum
  --   (fun (p : ℕ × ℕ) => DiscreteLaplaceSampleLoopIn1 num p.1 * (Geo (1 - rexp (-1)) p.2 * ((if vx * ↑num + ux = p.1 + ↑num * p.2 then 1 else 0) / ↑↑den)))
  --   (DiscreteLaplaceSampleLoopIn1 num (ux, vx).1 * (Geo (1 - rexp (-1)) (ux, vx).2 * ((if vx * ↑num + ux = (ux, vx).1 + ↑num * (ux, vx).2 then 1 else 0) / ↑↑den))) := by
  --   apply hasSum_single
  --   intro b'
  --   rcases b' with ⟨ a,  b ⟩
  --   intro Hb'
  --   simp
  --   apply Classical.by_contradiction
  --   simp
  --   intro H1 _ Hk
  --   apply H1
  --   skip
  --   simp [DiscreteLaplaceSampleLoopIn1]
  --   rw [DiscreteLaplaceSampleLoopIn1Aux_apply_true]
  --   split
  --   · exfalso
  --     apply Hb'
  --     simp
  --     -- Euclidean division uniqueness
  --     sorry
  --   · rfl
  -- rw [HS]

  -- rw []


  -- -- Evaluate the singleton sum



  /-

  simp only [DiscreteLaplaceSampleLoop', Bind.bind, DiscreteLaplaceSampleLoopIn2_eq, Pure.pure, bind_apply]
  have H (a c : ℕ) :
    ((if b = false ∧ n = (a + (num : ℕ) * (c - 1)) / (den : ℕ) then (2⁻¹ : ENNReal) else 0) +
      if b = true ∧ n = (a + (num : ℕ) * (c - 1)) / (den : ℕ) then (2⁻¹ : ENNReal) else 0) =
    ( (if n = (a + (num : ℕ) * (c - 1)) / (den : ℕ) then (1 : ENNReal) else 0) * (2⁻¹ : ENNReal)) := by
    cases b <;> simp

  -- Eliminate the 1/2
  conv =>
    enter [2, 1, a, 2, 1, c, 2]
    rw [tsum_bool]
    simp
    rw [H]
  clear H
  conv =>
    enter [2, 1, a, 2, 1, c]
    rw [<- mul_assoc]
  conv =>
    enter [2, 1, a, 2]
    rw [ENNReal.tsum_mul_right]
  conv =>
    enter [2, 1, a]
    rw [<- mul_assoc]
  rw [ENNReal.tsum_mul_right]
  congr

  -- Convert LHS into Geometric PMF
  have H :
    ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ n * (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) =
    (Geo (1 - rexp (- (den / num))) n) := by
    unfold Geo
    rw [ENNReal.ofReal_sub]
    case hq => apply exp_nonneg
    simp
    congr
    generalize HW : rexp (-(↑↑den / ↑↑num)) = W
    rw [Subtype.val]
    simp
    rw [NNReal.coe_sub_def]
    rw [max_eq_left ?G1]
    case G1 =>
      apply sub_nonneg.mpr
      rw [<- HW]
      simp
      apply div_nonneg <;> apply cast_nonneg
    simp only [NNReal.coe_one, coe_toNNReal', sub_sub_cancel]
    rw [max_eq_left ?G1]
    rw [<- HW]
    apply exp_nonneg
  rw [H]
  clear H

  -- Convert the RHS probGeometric into Geo as well
  have SC1 : BernoulliExpNegSample 1 1 false + BernoulliExpNegSample 1 1 true = 1 := sorry
  have SC2 : BernoulliExpNegSample 1 1 true < 1 := sorry
  conv =>
    enter [2, 1, a, 2, 1, b, 1]
    rw [probGeometric_apply_Geo _ SC1 SC2]
  clear SC1 SC2

  -- Reindex and simplify the inner sum on the RHS
  have H (a : ℕ) :
    ∑' (b : ℕ), ((if b = 0 then 0 else Geo (1 - BernoulliExpNegSample 1 1 true).toReal (b - 1)) * if n = (a + ↑num * (b - 1)) / ↑den then 1 else 0) =
    ∑' (b : ℕ), ((Geo (1 - BernoulliExpNegSample 1 1 true).toReal b) * if n = (a + ↑num * b) / ↑den then 1 else 0) := by
    apply (tsum_eq_tsum_of_ne_zero_bij ?Bij)
    case Bij => exact (fun z => z + 1)
    · intro _ _ H
      simp at H
      exact SetCoe.ext H
    · simp
      intro z Hn Hz HGeo
      exists (z - 1)
      apply And.intro
      · apply And.intro
        · exact Hn
        · exact HGeo
      · exact succ_pred_eq_of_ne_zero Hz
    · simp
  conv =>
    enter [2, 1, a, 2]
    rw [H]
  clear H
  simp only [BernoulliExpNegSample_apply_true, cast_one, NNReal.coe_one, PNat.val_ofNat, ne_eq, one_ne_zero, not_false_eq_true, div_self]

  -- Split up outermost series so that we can expand DiscreteLaplaceSampleLoopIn1
  have Hsup1 : Function.support (fun a => DiscreteLaplaceSampleLoopIn1 num a * (∑' (b : ℕ), Geo (1 - ENNReal.ofReal (rexp (-1))).toReal b * if n = (a + (num : ℕ) * b) / (den : ℕ) then 1 else 0))  ⊆ { n' : ℕ | n' < (num : ℕ)} := by
    simp [Function.support]
    intro a H1 x _ _
    apply Classical.by_contradiction
    intro Hk
    apply H1
    simp [DiscreteLaplaceSampleLoopIn1]
    simp [DiscreteLaplaceSampleLoopIn1Aux]
    intro i
    cases Classical.em (i < (num : ℕ))
    · right
      intro Hk'
      exfalso
      linarith
    · left
      apply UniformSample_apply_out
      apply Nat.le_of_not_lt
      assumption
  rewrite [<- tsum_subtype_eq_of_support_subset Hsup1]
  clear Hsup1
  have SC1 (x : {n' | n' < num.val}.Elem) : (x.val < num.val) := by
    simp_all only [Set.mem_setOf_eq]
    obtain ⟨val, property⟩ := x
    simp_all only
    simp_all only [Set.mem_setOf_eq]
  conv =>
    enter [2, 1, x, 1]
    rw [DiscreteLaplaceSampleLoopIn1_apply]
    · skip
    · apply SC1


  -- CHECKPOINT:
  -- Here is where things start going sideways
  -- Intead of



  -- Simplify ite expression
  have H1 (a b : ℕ) :
    (if n = (a + ↑num * b) / ↑den then (1 : ENNReal) else 0) =
    (if (n * (den) ≤ (a + ↑num * b) ∧ (a + ↑num * b) < (n +  1) * den) then (1 : ENNReal) else (0)) := by
    congr
    rw [propext (nat_div_eq_le_lt_iff (PNat.pos den))]
  have H2 (a b : ℕ) :
    (if (n * (den) ≤ (a + ↑num * b) ∧ (a + ↑num * b) < (n +  1) * den) then (1 : ENNReal) else (0)) =
    (if ((a + ↑num * b) < (n +  1) * den) then (1 : ENNReal) else 0) -  (if (n * (den) ≤ (a + ↑num * b)) then (0 : ENNReal) else 1) := by
      cases (Classical.em ((a + ↑num * b) < (n +  1) * den))
      · simp_all
        split
        · simp only [tsub_zero]
        · simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le]
      · rename_i h
        rw [ite_and]
        split
        · simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le]
        · exfalso
          linarith
  conv =>
    enter [2, 1, x, 2, 1, b, 2]
    rw [H1]
    rw [H2]
  clear H1 H2

  -- have HIndicatorInequality (a b : ℕ) :
  --   ((if n * ↑den ≤ ↑a + ↑num * b then 0 else 1) ≤ (if ↑a + ↑num * b < (n + 1) * ↑den then 1 else 0)) := by sorry

  -- Distribute series; split into partial series
  have R2 (a b : ℕ) :=
    @ENNReal.mul_sub
      (Geo (1 - ENNReal.ofReal (rexp (-1))).toReal b)
      (if ↑a + ↑num * b < (n + 1) * ↑den then 1 else 0)
      (if n * ↑den ≤ ↑a + ↑num * b then 0 else 1)
      ?G2
  case G2 =>
    intro _ _
    rw [Geo]
    simp
    exact ne_of_beq_false rfl
  conv =>
    enter [2, 1, a, 2, 1, b]
    rw [R2]
  clear R2

  have S1 (a : ℕ) : (∑' (i : ℕ), Geo (1 - ENNReal.ofReal (rexp (-1))).toReal i * if n * ↑den ≤ ↑a + ↑num * i then 0 else 1) ≠ ⊤ := by
    simp
    intro HK
    -- Prove that Geo never has a top sum
    sorry
  have S2 (a : ℕ) : (fun b => Geo (1 - ENNReal.ofReal (rexp (-1))).toReal b * if n * ↑den ≤ ↑a + ↑num * b then 0 else 1) ≤ fun b => Geo (1 - ENNReal.ofReal (rexp (-1))).toReal b * if ↑a + ↑num * b < (n + 1) * ↑den then 1 else 0 := by
    intro x
    simp
    split
    · split
      · simp
      · simp
    · split
      · simp
      · exfalso
        linarith
  conv =>
    enter [2, 1, a, 2]
    rw [ENNReal.tsum_sub ]
    · skip
    · apply S1
    · apply S2
  -- Err... is this on the right track? Or is there an easier way to get to the second last step?

  -- Rewrite the partial sums by their subtypes (so that it's easy to get a common formula for them )
  -- Formula for geometric sums

  -- (???) Complete by simplficiation
  -/

end SLang
