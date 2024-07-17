/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Neighbours
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.Util.Log

noncomputable section

open Classical

variable { T : Type }

namespace SLang

def DP' (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) ≤ δ + ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0)

def ApproximateDP (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  DP' m ε δ

-- def ApproximateDP_singleton (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
--   ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ x : U,
--   (m l₁ x) ≤ δ + ENNReal.ofReal (Real.exp ε) * (m l₂ x)
--
-- theorem ApproximateDP_singleton_to_event (m : Mechanism T U) (ε : ℝ) (δ : NNReal) (h : ApproximateDP_singleton m ε δ) :
--   ApproximateDP m ε δ := by
--   simp [ApproximateDP]
--   simp [ApproximateDP_singleton] at h
--   intros l₁ l₂ h1 S
--   replace h1 := h l₁ l₂ h1
--   have A : ∀ (x : U), (if x ∈ S then m l₁ x else 0)  ≤ δ + ENNReal.ofReal ε.exp * (if x ∈ S then m l₂ x else 0) := by
--     aesop
--   have B : ∀ b : ENNReal, b ≠ 0 ∨ ENNReal.ofReal ε.exp ≠ ⊤ := by
--     aesop
--   have C : ∀ b : ENNReal, b ≠ ⊤ ∨ ENNReal.ofReal ε.exp ≠ 0 := by
--     intro b
--     right
--     simp
--     exact Real.exp_pos ε
--   have E := fun x : U => (A x)
--   have F := ENNReal.tsum_le_tsum E
--   apply le_trans F
--   -- I'm doubtful that that this is true when |U| > 1
--   sorry
--   -- rw [ENNReal.tsum_mul_left] at F
--   -- rw [← ENNReal.div_le_iff_le_mul] at F
--   -- . clear h1 A B C D
--   --   trivial
--   -- . aesop
--   -- . right
--   --   simp
--   --   exact Real.exp_pos ε
--
-- theorem approximate_event_to_singleton (m : Mechanism T U) (ε : ℝ) (δ : NNReal) (h : ApproximateDP m ε δ) :
--   ApproximateDP_singleton m ε δ := by
--   sorry
--   -- simp [DP_singleton]
--   -- simp [DP] at h
--   -- intros l₁ l₂ h1 x
--   -- replace h1 := h l₁ l₂ h1 {x}
--   -- simp at h1
--   -- rw [tsum_eq_single x] at h1
--   -- . simp at h1
--   --   rw [tsum_eq_single x] at h1
--   --   . simp at h1
--   --     trivial
--   --   . aesop
--   -- . aesop
--
-- theorem approximate_event_eq_singleton (m : Mechanism T U) (ε : ℝ) (δ : NNReal) :
--   ApproximateDP m ε δ ↔ ApproximateDP_singleton m ε δ := by
--   sorry
--   -- constructor
--   -- . apply event_to_singleton
--   -- . apply singleton_to_event





theorem ApproximateDP_of_DP (m : Mechanism T U) (ε : ℝ) (h : DP m ε) :
  ∀ δ : NNReal, DP' m ε δ := by
  simp [DP] at h
  simp [DP']
  intros δ l₁ l₂ neighs S
  replace h := h l₁ l₂ neighs S
  cases (Classical.em ((∑' (x : U), if x ∈ S then (m l₂) x else 0) = ⊤))
  · rename_i HT
    rw [HT]
    simp_all
    rw [ENNReal.mul_top']
    split <;> simp
    -- Edge case: 0-DP with SLang term that doens't normalize
    -- Does the same thing break the singleton event proof?
    sorry
  · rename_i HNT
    rw [ENNReal.div_le_iff_le_mul ?G1 ?G2] at h
    case G1 =>
      right
      simp
    case G2 =>
      left
      apply HNT
    apply le_trans h
    simp



theorem ApproximateDP_of_zCDP (m : Mechanism T U) (ε : ℝ) (h : zCDPBound m ε) :
  ∀ δ : NNReal, DP' m ε δ := by
  simp [zCDPBound] at h
  simp [DP']
  intros δ l₁ l₂ neighs S
  replace h := h



  -- Privacy loss random variable
  -- Why isn't elog importing?
  -- #check elog
  let z (x : U) : ENNReal := (fun _ => 0) ((m l₁ x) / (m l₂ x))

  -- Separate the indicator function
  conv =>
    enter [1, 1, a]
    rw [<- mul_one ((m l₁) a)]
    rw [<- mul_zero ((m l₁) a)]
    rw [<- mul_ite]


  -- Multiply by indicator function for z
  have HK (x : U) : (1 : ENNReal) = (if (z x ≤ ENNReal.ofReal ε) then 1 else 0) + (if (z x > ENNReal.ofReal ε) then 1 else 0) := by
    split
    · simp
      rw [ite_eq_right_iff.mpr]
      · simp
      · intro
        exfalso
        sorry
    · simp
      rw [ite_eq_left_iff.mpr]
      simp
      apply lt_of_not_ge
      trivial
  conv =>
    enter [1, 1, a]
    rw [<- mul_one (_ * _)]
    rw [mul_assoc]
    enter [2, 2]
    rw [HK a]
  clear HK

  -- Distribute
  conv =>
    enter [1, 1, a]
    rw [mul_add]
    rw [mul_add]
  rw [ENNReal.tsum_add]

  -- Bound right term above
  have HB :
      ∑' (a : U), (m l₁) a * ((if a ∈ S then 1 else 0) * if z a > ENNReal.ofReal ε then 1 else 0) ≤
      ∑' (a : U), (m l₁) a * (if z a > ENNReal.ofReal ε then 1 else 0) := by
    apply ENNReal.tsum_le_tsum
    intro x
    apply mul_le_mul'
    · rfl
    split
    · simp
    · simp
  apply (le_trans (add_le_add_left HB _))
  clear HB

  -- Don't actually need this (yet)
  -- -- Later, we need the sum to be finite. Can we reduce?
  -- cases (Classical.em (∑' (a : U), ((m l₁) a) * (if a ∈ S then 1 else 0) = ⊤))
  -- · rename_i Ht
  --   -- Not sure if this is provable but we might need to restruc this to PMFs anyways
  --   sorry
  -- rename_i Hnt

  -- Bound right term above
  -- FIXME: Refactor to lemma
  have HMarkov : (∑' (a : U), (m l₁) a * if z a > ENNReal.ofReal ε then 1 else 0) ≤ δ := by
    sorry
  apply (le_trans (add_le_add_left HMarkov _))
  clear HMarkov

  -- -- Bound left term above (err.. no)
  -- have HB :
  --     ∑' (a : U), (m l₁) a * ((if a ∈ S then 1 else 0) * if z a ≤ ENNReal.ofReal ε then 1 else 0) ≤
  --     ∑' (a : U), (m l₁) a *  (if a ∈ S then 1 else 0) := by
  --   apply ENNReal.tsum_le_tsum
  --   intro x
  --   apply mul_le_mul'
  --   · rfl
  --   rw [mul_comm]
  --   split
  --   · simp
  --   · simp
  -- apply (le_trans (add_le_add_right HB _))
  -- clear HB

  -- Bound left term above
  have HDP :
      ∑' (a : U), (m l₁) a * ((if a ∈ S then 1 else 0) * if z a ≤ ENNReal.ofReal ε then 1 else 0) ≤
      ENNReal.ofReal (Real.exp ε) * ∑' (a : U), (m l₂) a * (if a ∈ S then 1 else 0) := by
    -- How? Must come from a choice of α with the RD bound
    sorry
  apply (le_trans (add_le_add_right HDP _))
  clear HDP

  -- Conclude by simplification
  rw [add_comm]
  apply add_le_add_left
  apply (ENNReal.mul_le_mul_left ?G1 ?G2).mpr
  case G1 =>
    -- Doesn't work for ε = 0. Can I get this bound separately in this case?
    sorry
  case G2 => exact ENNReal.ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro a
  split <;> simp

end SLang