/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert
import SampCert.SLang


def nat_pnat_dirty (n : ℕ) : IO (ℕ+) :=
  dite
    (0 < n)
    (fun hp => return (Nat.toPNat _ hp))
    (fun _ => throw (IO.userError "Bad pnat"))

/--
Profile uniform sampler.

Executes a function, and records a summary of the FFI calls to disk
-/
def profile_ffi (args : List String) : IO Unit :=
  match (String.toNat? <$> args) with
  | [some num, some den, some mix] => do
      let num <- nat_pnat_dirty num
      let den <- nat_pnat_dirty den
      let _ <- PMF.run <| (SLang.DiscreteGaussianPMF num den mix)
      return ()
  | _ => throw (IO.userError "Bad argument list")

def check_byte_sampler : IO Unit := do
  -- Check if FFI is working
  IO.print "Sampling bytes: "
  for _ in [:10000] do
    let x <- PMF.run <| SLang.probUniformByte_PMF
    IO.println x


def main (args : List String):  IO Unit := do
  profile_ffi args
  -- check_byte_sampler
