/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import Init.Data.Fin.Basic
import Mathlib.Data.Vector.Basic

/-!
# ``privMax`` Implementation

This file implements a query for the noised max of a list, using the sparse vector technique.

In principle this can produce better pure DP bounds than the maximum obtained by the differentially
private histogram, and furthermore it does not require choosing a failure threshold a priori.
-/

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]


/--
Sum over a list, clipping each element to a maximum.

Similar to exactBoundedSum, however exactClippedSum allows m = 0.
-/
def exactClippedSum (m : ℕ) (l : List ℕ) : ℤ :=
  List.sum (List.map (fun n : ℕ => (Nat.min n m)) l)

/--
Rate at which a given clipping thresold is impacting the accuracy of the sum.

Always negative or zero.
-/
def exactDiffSum (m : ℕ) (l : List ℕ) : ℤ := exactClippedSum m l - exactClippedSum (m + 1) l

/--
Noise the constant 0 value using the abstract noise function.

This looks strange, but will specialize to Lap(ε₁/ε₂, 0) in the pure DP case.
-/
def privNoiseZero (ε₁ ε₂ : ℕ+) : SLang ℤ := dps.noise (fun _ => 0) 1 ε₁ ε₂ []

/--
Return the maximum element in the list, with some amount of noising.
-/
def privMax_eval (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- privNoiseZero ε₁ (2 * ε₂)
  let (k, _) <-
    -- Invariant: When the loop state is (i, vi), we are about
    -- to check if i is the noised max.

    probWhile
      -- Terminate when exactDiffSum k l + vk >= τ
      -- Continue  when exactDiffSum k l + vk < τ
      (fun (k, vk) => exactDiffSum k l + vk < τ)

      -- Increase k, and sample the next vk
      (fun (km1, _) => do
        let k := km1 + 1
        let vk <- privNoiseZero ε₁ (4 * ε₂)
        return (k, vk))

      -- Start with 0, v0
      (0, <- privNoiseZero ε₁ (4 * ε₂))
  return k


/--
privMax is a PMF.

Using the Laplace mechanism, privMax is (ε₁/ε₂)-DP.
-/
def privMaxPMF (ε₁ ε₂ : ℕ+) (l : List ℕ) : PMF ℕ :=
  ⟨ privMax_eval ε₁ ε₂ l,
    sorry⟩

end SLang