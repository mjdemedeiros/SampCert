/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Samplers.LaplaceGen.Code
import SampCert.Samplers.Laplace.Basic
import SampCert.Util.Shift

noncomputable section

open Classical PMF Nat Real

namespace SLang

@[simp]
theorem DiscreteLaplaceGenSample_apply (num : Nat) (den : PNat) (μ x : ℤ) :
  (DiscreteLaplaceGenSample num den μ) x =
  ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs (x - μ) / ((num : NNReal) / (den : NNReal)))))) := by
  simp [DiscreteLaplaceGenSample]
  -- rw [tsum_eq_single (x - μ) (by aesop)]
  -- simp
  skip
  sorry

theorem DiscreteLaplaceGenSample_periodic (num : Nat) (Hnum : 0 < num) (den : PNat) (μ x : ℤ) :
  (DiscreteLaplaceGenSample num den μ) x =
    (DiscreteLaplaceSample ⟨ num , Hnum  ⟩ den) (x - μ) := by
  simp [DiscreteLaplaceGenSample]
  -- rw [tsum_eq_single (x - μ) (by aesop)]
  -- simp
  sorry

/--
Discrete Laplace has sum 1
-/
theorem DiscreteLaplaceGenSample_sum (num : Nat) (den : PNat) (μ : ℤ) : HasSum (DiscreteLaplaceGenSample num den μ) 1 := by
  rw [DiscreteLaplaceGenSample]
  split
  · rename_i Hpos
    rw [Summable.hasSum_iff ENNReal.summable]
    sorry

    -- ??
    -- have HR1 := DiscreteLaplaceGenSample_periodic num Hpos den μ
    -- simp only [DiscreteLaplaceGenSample] at HR1
    -- simp only [DiscreteLaplaceSample_apply] at HR1
    -- skip
    -- conv at HR1 =>
    --   enter [x, 1]
    --   rw [dite_eq_left_iff.mpr]
    --   skip


    -- conv =>
    --   enter [1, 1, b]
    --   rw [DiscreteLaplaceGenSample_periodic]
    -- rw [<- DiscreteLaplaceSample_normalizes ⟨ num, Hpos ⟩ den]
    -- apply tsum_eq_tsum_of_ne_zero_bij ?Bij
    -- case Bij => exact (fun w => w + μ)
    -- · intro _ _ H
    --   simp at H
    --   exact SetCoe.ext H
    -- · simp
    --   intro z HZ
    --   exists (z - μ)
    --   simp
    --   apply HZ
    -- · simp
    -- all_goals intro w; apply Hpos
  · rw [Summable.hasSum_iff ENNReal.summable]
    sorry

/--
Discrete Laplace as a PMF
-/
def DiscreteLaplaceGenSamplePMF (num : Nat) (den : PNat) (μ : ℤ) : PMF ℤ :=
  ⟨ DiscreteLaplaceGenSample num den μ , DiscreteLaplaceGenSample_sum num den μ ⟩

end SLang
