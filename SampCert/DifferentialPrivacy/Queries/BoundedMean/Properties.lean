/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.DifferentialPrivacy.Queries.Count.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedMean.Code

open Classical Nat Int Real Rat

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]

def NoisedBoundedAvgQuery' (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℚ :=
  let X := Compose (NoisedBoundedSumQuery U ε₁ (2 * ε₂)) (NoisedCountingQuery ε₁ (2 * ε₂))
  PostProcess X (fun z => z.1 / z.2) l

theorem NoisedBoundedAvgQueryIdentical (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  NoisedBoundedAvgQuery' U ε₁ ε₂ = NoisedBoundedAvgQuery U ε₁ ε₂  := by
  ext l x
  cases x
  rename_i n d h1 h2
  simp [NoisedBoundedAvgQuery, NoisedBoundedAvgQuery', Compose, PostProcess]

theorem BoundedSumQueryDP (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  dps.prop (NoisedBoundedAvgQuery U ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  rw [← NoisedBoundedAvgQueryIdentical]
  apply dps.postprocess_prop
  . unfold Function.Surjective
    intro b
    cases b
    rename_i n d h1 h2
    simp
    exists n
    exists d
    rw [intCast_div_eq_divInt]
    simp [mkRat, h1, Rat.normalize, h2]
  . have A : (ε₁ : ℝ) / ((2 * ε₂) : ℕ+) + (ε₁ : ℝ) / ((2 * ε₂) : ℕ+) = (ε₁ : ℝ) / (ε₂ : ℝ) := by
      field_simp
      ring_nf
    rw [← A]
    apply dps.compose_prop
    . apply NoisedBoundedSumQueryDP
    . apply NoisedCountingQueryDP

end SLang
