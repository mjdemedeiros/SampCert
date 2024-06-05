/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP

/-!
# zCDP Adaptive Composition

This file builds up to a zCDP bound on adaptively composed zCDP queries.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

variable { T U V : Type }
variable [HU : Inhabited U]
variable [HV : Inhabited V]


/--
Bound on Renyi divergence on adaptively composed queries
-/
lemma primComposeAdaptive_renyi_bound {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (α : ℝ) (Hα : 1 < α) :
 RenyiDivergence (privComposeAdaptive' nq1 nq2 l₁) (privComposeAdaptive' nq1 nq2 l₂) α ≤ RenyiDivergence (nq1 l₁) (nq1 l₂) α + ⨆ u, RenyiDivergence (nq2 u l₁) (nq2 u l₂) α := by
  apply (RenyiDivergence_mono_sum _ _ α Hα)
  rw [RenyiDivergence_exp (privComposeAdaptive' nq1 nq2 l₁)  (privComposeAdaptive' nq1 nq2 l₂) Hα]
  rw [left_distrib]
  rw [Real.exp_add]

  have hmono_1 : rexp ((α - 1) * ⨆ u, RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) = ⨆ u, rexp ((α - 1) * RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) := by
    sorry
  rw [hmono_1]
  clear hmono_1
  rw [RenyiDivergence_exp (nq1 l₁) (nq1 l₂) Hα]
  rw [mul_comm]
  rw [<- (ENNReal.toReal_ofReal_mul _ _ ?h)]
  case h =>
    refine Real.iSup_nonneg ?hf
    intro i
    exact exp_nonneg ((α - 1) * RenyiDivergence (nq2 i l₁) (nq2 i l₂) α)
  rw [mul_comm]
  rw [← ENNReal.tsum_mul_right]

  apply (@LE.le.trans _ _ _ ((∑' (i : U), nq1 l₁ i ^ α * nq1 l₂ i ^ (1 - α) * ENNReal.ofReal (rexp ((α - 1) * RenyiDivergence (nq2 i l₁) (nq2 i l₂) α))).toReal) _ _ ?goal2)
  case goal2 =>
    -- Can I do this without summability?
    apply toReal_mono'
    · apply tsum_le_tsum
      · intro i
        refine (ENNReal.mul_le_mul_left ?h.h.h0 ?h.h.hinf).mpr ?h.h.a
        · sorry
        · sorry
        · apply ENNReal.ofReal_le_ofReal
          sorry
      · sorry
      · sorry
    · sorry

  -- After this point the argument is tight
  apply Eq.le
  conv =>
    rhs
    congr
    congr
    intro i
    rw [RenyiDivergence_exp (nq2 i l₁) (nq2 i l₂) Hα]

  conv =>
    lhs
    congr
    congr
    intro
    rw [privComposeChainRule]
    rw [privComposeChainRule]

  have test : ∀ i, ENNReal.ofReal (∑' (x : V), nq2 i l₁ x ^ α * nq2 i l₂ x ^ (1 - α)).toReal = ∑' (x : V), nq2 i l₁ x ^ α * nq2 i l₂ x ^ (1 - α) := by
    intro i
    apply ofReal_toReal
    -- Need a summability thing here... try to avoid this lemma if possible
    sorry
  conv =>
    rhs
    congr
    congr
    intro
    rw [test]
    rw [← ENNReal.tsum_mul_left]
  clear test

  rw [<- ENNReal.tsum_prod]
  congr
  apply funext
  intro p
  rcases p with ⟨ u , v ⟩
  simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ ?sc1]
  case sc1 =>
    sorry
  rw [ENNReal.mul_rpow_of_nonneg _ _ ?sc2]
  case sc2 =>
    sorry
  rw [mul_mul_mul_comm]

/--
Adaptively Composed queries satisfy zCDP Renyi divergence bound.
-/
theorem privComposeAdaptive_zCDPBound {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} {ε₁ ε₂ ε₃ ε₄ : ℕ+} (h1 : zCDPBound nq1 ((ε₁ : ℝ) / ε₂))  (h2 : ∀ u, zCDPBound (nq2 u) ((ε₃ : ℝ) / ε₄)) (nn1 : NonZeroNQ nq1) (nn2 : ∀ u, NonZeroNQ (nq2 u)) (nt1 : NonTopRDNQ nq1) (nt2 : ∀ u, NonTopRDNQ (nq2 u)) (nts1 : NonTopNQ nq1) (nts2 : ∀ u, NonTopNQ (nq2 u)) :
  zCDPBound (privComposeAdaptive' nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  rw [zCDPBound]
  intro α Hα l₁ l₂ Hneighbours
  -- Loose step
  apply (@LE.le.trans _ _ _ (1/2 * (↑↑ε₁ / ↑↑ε₂)^2 * α + 1/2 * (↑↑ε₃ / ↑↑ε₄)^2 * α) _ _ ?case_sq)
  case case_sq =>
    -- Binomial bound
    sorry
  -- Rewrite the upper bounds in terms of Renyi divergences of nq1/nq2
  rw [zCDPBound] at h1
  have marginal_ub := h1 α Hα l₁ l₂ Hneighbours
  have conditional_ub : (⨆ (u : U),  RenyiDivergence (nq2 u l₁) (nq2 u l₂) α ≤ 1 / 2 * (↑↑ε₃ / ↑↑ε₄) ^ 2 * α) :=
    ciSup_le fun x => h2 x α Hα l₁ l₂ Hneighbours
  apply (@LE.le.trans _ _ _ (RenyiDivergence (nq1 l₁) (nq1 l₂) α + ⨆ (u : U),  RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) _ _ ?case_alg)
  case case_alg => linarith
  apply (primComposeAdaptive_renyi_bound _ Hα)

/--
Adaptive composed query distribution is nowhere zero
-/
theorem privComposeAdaptive_NonZeroNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonZeroNQ nq1) (nt2 : ∀ u, NonZeroNQ (nq2 u)) :
  NonZeroNQ (privComposeAdaptive' nq1 nq2) := by
  simp [NonZeroNQ] at *
  simp [privComposeAdaptive']
  aesop

/--
All outputs of a adaptive composed query have finite probability.
-/
theorem privComposeAdaptive_NonTopNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonTopNQ nq1) (nt2 : ∀ u, NonTopNQ (nq2 u)) :
  NonTopNQ (privComposeAdaptive' nq1 nq2) := by
  simp [NonTopNQ] at *
  intros l u v
  rw [privComposeChainRule]
  apply ENNReal.mul_ne_top
  · aesop
  · aesop

/--
Adaptive composed query is a proper distribution
-/
theorem privComposeAdaptive_NonTopSum {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonTopSum nq1) (nt2 : ∀ u, NonTopSum (nq2 u)) :
  NonTopSum (privComposeAdaptive' nq1 nq2) := by
  rw [NonTopSum] at *
  -- Chain rule won't help here
  admit


/--
Renyi divergence beteeen adaptive composed queries on neighbours are finite.
-/
theorem privComposeAdaptive_NonTopRDNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonTopRDNQ nq1) (nt2 : ∀ u, NonTopRDNQ (nq2 u)) (nn1 : NonTopNQ nq1) (nn2 : ∀ u, NonTopNQ (nq2 u)) :
  NonTopRDNQ (privComposeAdaptive' nq1 nq2) := by
  rw [NonTopRDNQ] at *
  admit
  -- simp [NonTopRDNQ] at *
  -- intro α h1 l₁ l₂ h2
  -- replace nt1 := nt1 α h1 l₁ l₂ h2
  -- replace nt2 := nt2 α h1 l₁ l₂ h2
  -- simp [privCompose]
  -- rw [ENNReal.tsum_prod']
  -- simp
  -- conv =>
  --   right
  --   left
  --   right
  --   intro x
  --   right
  --   intro y
  --   congr
  --   . left
  --     rw [compose_sum_rw]
  --   . left
  --     rw [compose_sum_rw]
  -- conv =>
  --   right
  --   left
  --   right
  --   intro x
  --   right
  --   intro y
  --   rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (lt_trans zero_lt_one h1))]
  --   rw [ENNReal.mul_rpow_of_ne_top (nn1 l₂ x) (nn2 l₂ y)]
  --   rw [mul_assoc]
  --   right
  --   rw [mul_comm]
  --   rw [mul_assoc]
  --   right
  --   rw [mul_comm]
  -- conv =>
  --   right
  --   left
  --   right
  --   intro x
  --   right
  --   intro y
  --   rw [← mul_assoc]
  -- conv =>
  --   right
  --   left
  --   right
  --   intro x
  --   rw [ENNReal.tsum_mul_left]
  -- rw [ENNReal.tsum_mul_right]
  -- intro H
  -- rw [mul_eq_top] at H
  -- cases H
  -- . rename_i h3
  --   cases h3
  --   rename_i h4 h5
  --   contradiction
  -- . rename_i h3
  --   cases h3
  --   rename_i h4 h5
  --   contradiction

/--
``privComposeAdaptive`` satisfies zCDP
-/
theorem privComposeAdaptive_zCDP (nq1 : List T → SLang U) (nq2 : U -> List T → SLang V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h : zCDP nq1 ((ε₁ : ℝ) / ε₂))  (h' : ∀ u, zCDP (nq2 u) ((ε₃ : ℝ) / ε₄)) :
  zCDP (privComposeAdaptive' nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [zCDP] at *
  repeat any_goals constructor
  · apply privComposeAdaptive_zCDPBound <;> aesop
  · apply privComposeAdaptive_NonZeroNQ <;> aesop
  · apply privComposeAdaptive_NonTopSum <;> aesop
  · apply privComposeAdaptive_NonTopNQ <;> aesop
  · apply privComposeAdaptive_NonTopRDNQ <;> aesop

end SLang
