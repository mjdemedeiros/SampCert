/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.SLang

open SLang

-- MiniML-like language of terms which are well-behaved from the point of view of extraction.
-- If the constants extract, programs written in the language itself should also extract.

-- Iterate the loop at most fuel times, and explicitly indicate if fuel has run out
def iter [Monad m] (body : T -> m T) (cond : T -> Bool) (fuel : Nat) (t : T) : (OptionT m) T
  := match fuel with
     | Nat.zero => failure
     | Nat.succ fuel' =>
        if cond t
          then (body t) >>= (iter body cond fuel')
          else pure t

class MiniML (m : Type u → Type v) extends Monad m : Type (max (u+1) v) where
  -- Constants are should be extracted separately (thinking UniformPowerOfTwo)
  constants (T : Type u) : List (m T)
  -- constants_extraction (T : Type u) : ∀ t : m T, t ∈ constants T -> True

  -- MiniML.loop will also be compiled separately, wherever it occurs in the term
  loop (T: Type u) (body : T -> m T) (cond : T -> Bool) : T -> m T

  -- Operational specification for the partial correctness of loop
  -- This should give us confidence that extracting to a While loop is correct
  -- Can we prove it?
  loop_spec (T : Type u) (body : T -> m T) (cond : T -> Bool) :
    ∀ t0 : T, ∃ i : Nat, ((∀ j : Nat, j < i -> iter body cond j t0 = failure) ∧ ¬ (iter body cond i t0 = failure))
    -> iter body cond i t0 = loop T body cond t0



#check SLang


-- lemma loop_spec_slang (T : Type u) (body : T -> SLang T) (cond : T -> Bool)  :
--     ∀ t0 : T, ∃ i : Nat, ((∀ j : Nat, j < i -> iter body cond j t0 = failure) ∧ ¬ (iter body cond i t0 = failure))
--     -> iter body cond i t0 = probWhile body cond t0 := by sorry
