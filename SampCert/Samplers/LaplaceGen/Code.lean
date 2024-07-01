/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.SLang
import SampCert.Samplers.Laplace.Code

noncomputable section

namespace SLang


-- FIXME: dite vs ite with Nat.toPNat'? Which breaks fewer things downstream?
def DiscreteLaplaceGenSample (num : Nat) (den : PNat) (μ : ℤ) : SLang ℤ :=
    dite (0 < num)
      (fun Hnz => do
        let s ← DiscreteLaplaceSample ⟨ num, Hnz ⟩ den
        return s + μ)
      (fun _ => return μ)

end SLang
