import Lean
import SampCert.Extension

open System IO.FS

namespace Lean.ToDafny

def destination : String := "/Users/trjohnb/Code/Dafny-VMC/src/New-VMC.dfy"

def writeLn (ln : String) : IO Unit := do
  let h ← Handle.mk destination Mode.append
  h.putStr "\n"
  h.putStr ln
  h.putStr "\n"

elab "#print_dafny_exports" : command => do
  writeFile destination ""
  writeLn "module NewVMC {"
  writeLn "  import opened UniformPowerOfTwo"
  writeLn "  type pos = x : nat | x > 0 witness 1"
  writeLn "  class DRandomExternUniformPowerOfTwo extends  UniformPowerOfTwo.Implementation.TraitExtern {\n"
  writeLn "    constructor {:extern} ()"
  let { decls, .. } := extension.getState (← getEnv)
  for decl in decls.reverse do
    IO.println decl
    let h ← Handle.mk destination Mode.append
    h.putStr decl
  writeLn "}"
  writeLn "}"

end Lean.ToDafny