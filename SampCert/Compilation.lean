/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert

/-
# Compilation

This file defines the compilation between SLang terms and nondeterministic values

To compile SLang terms, we want to interpret a value ``v : SLang T`` as
some probabalistically chosen ``v : T``. Not all terms of type ``SLang T`` will
be compilable: to compile a ``SLang`` term,

The subset of ``SLang`` terms we can compile are represented in the ``isComp``
datatype. Many are translated directly into lean terms, however the nondeterministic
and nonterminating ``SLang`` terms are compiled via an external function. Multiple
compilations for the same SLang term (for example, optimized and unoptimized Laplace
sampling) are supported by constructing different ``isComp`` terms.

``isComp`` terms should not be used outside of establishing other ``isComp`` terms.

can I enforce this somehow?

-/
namespace SComp

/--
External compilation of the uniform random power of 2 sampler.
-/
-- MARKUSDE: Remove the body of this function.
def uniformP2_external (_ : ℕ+) : ℕ := 0

/--
External compilation of a while loop
-/
-- MARKUSDE: Remove the body of this function.
def while_external (cond : T -> Bool) (vBody : T -> T) (init : T) : T := sorry

/--
Inductive datatype which defines how primitive SLang functions can translate into
into a value.
-/
inductive isComp : {T : Type} -> SLang T -> T -> (Type 1)
| uniformP2 (n : ℕ+) :
    @isComp ℕ (SLang.UniformPowerOfTwoSample n) (uniformP2_external n)
| pure {T : Type} {v : T} :
    @isComp T (SLang.probPure v) v
| bind {P Q : Type} {p : P} {q : P -> Q} (s1 : SLang P) (s2 : P -> SLang Q) :
    @isComp P s1 p ->
    @isComp Q (s2 p) (q p) ->
    @isComp Q (SLang.probBind s1 s2) (let v := p; q v)
| while {T : Type} (cond : T -> Bool) (body : T -> SLang T) (vBody : T -> T) (init : T) :
    (∀ t : T, @isComp T (body t) (vBody t)) ->
    @isComp T (SLang.probWhile cond body init) (while_external cond vBody init)

/--
A SLang term can be compiled.

Note that this term is proof-relevant: different canCompile terms represent different compilations.
-/
def canCompile {T : Type} (s : SLang T) : Type 1 := Σ (v : T), @isComp T s v

/--
Top-level function for compilation.
-/
def compile {T : Type} (s : SLang T) (C : canCompile s) : T := C.fst


-- MARKUSDE: Establish terms for compiling mechanisms, etc


/-
## Helper functions for establishing canCompile
-/
namespace SLang

/--
Default `probPure` compilation
-/
def probPure_canCompile {T : Type} {v : T} : canCompile (SLang.probPure v) :=
  ⟨ v, isComp.pure ⟩

/--
Default `probPure` compilation
-/
def probBind_canCompile {T U : Type} {p : SLang T} {f : T -> SLang U}
  (C1 : canCompile p) (C2 : ∀ t, canCompile (f t)) :
  canCompile (SLang.probBind p f) :=
  ⟨ (C2 C1.fst).fst,
    by
      rcases C1 with ⟨ v1, H1 ⟩
      simp only []
      rcases (C2 v1) with ⟨ v2, H2 ⟩
      simp only []
      apply (isComp.bind p f H1 H2) ⟩


/--
Default `UniformPowerOfTwoSample` compilation
-/
def UniformPowerOfTwoSample_canCompile (n : ℕ+) : canCompile (SLang.UniformPowerOfTwoSample n) :=
  ⟨ uniformP2_external n, isComp.uniformP2 n ⟩


/--
Default `probWhile` compilation
-/
def probWhile_canCompile {T : Type} (cond : T -> Bool) (body : T -> SLang T) (init : T) (C : ∀ t : T, canCompile (body t)) :
  canCompile (SLang.probWhile cond body init) :=
  ⟨ while_external cond (fun t => (C t).fst) init,
    by
      apply (isComp.while cond body (fun t => (C t).fst) init)
      intro t
      apply (C t).2 ⟩

/--
Default `probUntil` compilation
-/
noncomputable def probUntil_canCompile {T : Type} (body : SLang T) (cond : T -> Bool) (C : canCompile body) : canCompile (SLang.probUntil body cond) := by
  unfold SLang.probUntil
  apply probBind_canCompile
  · apply C
  · intro init
    apply (probWhile_canCompile _ _ init)
    intro _
    apply C



#reduce (compile (SLang.probUntil (SLang.probPure (5 : ℕ)) (fun (_ : ℕ) => true)) (probUntil_canCompile _ _ probPure_canCompile))




-- TODO:
-- - Uniform
-- - Geometric
-- - Bernoulli
-- - BNE
-- - Laplace (non-optimized)
-- - Laplace (optimized)
-- - LaplaceGen (optimized)
-- - LaplaceGen (non-optimized)
-- - Gaussian
-- - Gen

-- Define typeclass for DPS system where noise is compilable
-- Mechanism compilation for compilable DPS systems

-- Abstract Count
-- Abstract BoundedSum
-- Abstract BoundedMean
-- Abstract Histogram
-- Abstract HistogramMean


end SLang
end SComp
