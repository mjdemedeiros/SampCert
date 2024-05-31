/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Extractor.Abstract
import SampCert.Extractor.Export
import SampCert.Extractor.Align
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Bernoulli.Code
import SampCert.Samplers.BernoulliNegativeExponential.Code
import SampCert.Samplers.Laplace.Code
import SampCert.Samplers.Gaussian.Code

import Lean
open Lean Lean.Expr Lean.Meta


noncomputable section

open SLang


-- PROBLEM 1: How to get the extractor to unfold the definitions we want it to

-- #eval Lean.Expr.const ``SLang.probUntil []
-- Reduce doesn't work (I don't expect it to) so I need some other way to rewrite via def. eq's.
-- #reduce SLang.probUntil
-- #eval Lean.Meta.reduce (Lean.Expr.const ``SLang.probUntil [])

-- This helper function will perform elaboration of the Lean-level syntax and then apply whnf.
-- open Lean.Elab.Term in
-- def whnf' (e : TermElabM Syntax) : TermElabM Format := do
--   let e ← elabTermAndSynthesize (← e) none
--   let w <- withTransparency .reducible $ whnf e
--   ppExpr w
--
-- attribute [reducible] List.cons
-- #eval whnf' `(List.cons 1 [])
-- attribute [irreducible] List.cons
-- #eval whnf' `(List.cons 1 [])
--
-- def body' : SLang Nat := pure 4
-- def cond' : Nat -> Bool := fun _ => true
-- -- #check (probUntil body' cond')
-- #eval whnf' `(probUntil body' cond')
-- attribute [reducible] probUntil
-- #eval whnf' `(probUntil body' cond')                      -- Unfolded (up to probWhile)
-- #eval whnf' `(probWhile cond' (fun _ => body'))           -- Not unfolded
-- #eval whnf' `(probUntil body' cond' 5)                    -- Unfolded (up to body')

-- LGTM! So somehow we need to figure out how to manage the attributes at extraction time
-- since we cannot control the attributes that the users put on their DSL terms.



-- Here's the next question... do we use whnf, or do we write our own normalizer?


-- #eval whnf (Lean.Expr.const ``BernoulliSample []) -- works, but not what I want
-- #eval whnf (Lean.Expr.const ``probWhile []) -- works, like expected


section test_reducibility


-- def PNat_1_expr : Expr :=
--  Lean.Expr.app
--    (Lean.Expr.app
--      (Lean.Expr.app
--        (Lean.Expr.app (Lean.Expr.const `Subtype.mk [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
--        (Lean.Expr.lam
--          `n
--          (Lean.Expr.const `Nat [])
--          (Lean.Expr.app
--            (Lean.Expr.app
--              (Lean.Expr.app
--                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
--                (Lean.Expr.const `instLTNat []))
--              (Lean.Expr.app
--                (Lean.Expr.app
--                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
--                  (Lean.Expr.lit (Lean.Literal.natVal 0)))
--                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
--            (Lean.Expr.bvar 0))
--          (Lean.BinderInfo.default)))
--      (Lean.Expr.lit (Lean.Literal.natVal 1)))
--    (Lean.Expr.app
--      (Lean.Expr.app (Lean.Expr.const `instOfNatPNatOfNeZeroNat.proof_1 []) (Lean.Expr.lit (Lean.Literal.natVal 1)))
--      (Lean.Expr.const `testPNat.proof_1 []))
--
-- def US_test : MetaM Expr := do
--   let (e : Expr) <- mkAppM ``UniformSample #[PNat_1_expr]
--   let (e1) <- withTransparency .reducible $ whnf (Lean.mkApp (Lean.Expr.const ``UniformSample []) PNat_1_expr)
--   return e1
--
-- #eval US_test

-- OK so it seems like the test is just not a good test-- doing it this way adds in a bunch of explicit monad
-- instance and universe level junk. I'll just test inside the extractor instead.






-- Can I locally mark a definition as reducible? The issue in reducing the probUntil term is
-- just that it unfolds probWhile too. I wonder if I could put an attribute on probUntil
-- to tell capsid this?

-- What does the unfold tactic do?

end test_reducibility




-- PROBLEM 2: How to get the frontend to infer the Capsid typeclass itself?

-- infers universe cosntants, maybe also typeclasses??
-- #check Lean.Meta.mkAppM


-- The WF normalization thing: What is the notion of a monadic (extractable) program?
-- #check Lean.Meta.forallTelescope


/-! Extraction using Capsid

This file instantiates a Capsid instance for SLang, and marks a list of SLang files for extraction.

The names in this file are protected: the extractor will not work if these names are changed.a

Additionally, the following names are protected:
 - ``UniformPowerOfTwoSample``
-/

-- instance : Capsid SLang where
--   capsWhile := probWhile

instance SLang_Capsid : Capsid SLang where
  capsWhile := probWhile
  capsUntil := probUntil



def testSLang : SLang Nat := (return 5) >>= (fun x => x)

-- Get a Capsid instance from typeclass inference
def encapsulate {T U : Type*} [HC : Capsid M] (f : T -> M U) : (Capsid M × (T -> M U)) := (HC, f)

-- Better design for encapsulate
-- Syntax-level transformation:
-- Given a function
--   - If that function is a wf monadic program (syntactic check on the type)
--   - Get the monad
--   - Get a Capsid instance associated to that monad
--   - Pair the Capsid instance with the function.
--
-- Eliminate the wf type check on the other side>? (it's at the expr level).





-- MARKUSDE: Push encapsulate into the attribute?

-- attribute [reducible] probUntil


def tc_UniformSample := (SLang_Capsid, UniformSample)
def tc_BernoulliSample := (SLang_Capsid, BernoulliSample)
def tc_BernoulliExpNegSampleUnitLoop := (SLang_Capsid, BernoulliExpNegSampleUnitLoop)
def tc_BernoulliExpNegSampleUnitAux := (SLang_Capsid, BernoulliExpNegSampleUnitAux )
def tc_BernoulliExpNegSampleUnit := (SLang_Capsid, BernoulliExpNegSampleUnit )
def tc_BernoulliExpNegSampleGenLoop := (SLang_Capsid, BernoulliExpNegSampleGenLoop )
def tc_BernoulliExpNegSample := (SLang_Capsid, BernoulliExpNegSample )
def tc_DiscreteLaplaceSampleLoopIn1Aux := (SLang_Capsid, DiscreteLaplaceSampleLoopIn1Aux )
def tc_DiscreteLaplaceSampleLoopIn1 := (SLang_Capsid, DiscreteLaplaceSampleLoopIn1)
def tc_DiscreteLaplaceSampleLoopIn2Aux := (SLang_Capsid, DiscreteLaplaceSampleLoopIn2Aux )
def tc_DiscreteLaplaceSampleLoopIn2 := (SLang_Capsid, DiscreteLaplaceSampleLoopIn2)
def tc_DiscreteLaplaceSampleLoop := (SLang_Capsid, DiscreteLaplaceSampleLoop )
def tc_DiscreteLaplaceSample := (SLang_Capsid, DiscreteLaplaceSample )
def tc_DiscreteGaussianSampleLoop := (SLang_Capsid, DiscreteGaussianSampleLoop )
def tc_DiscreteGaussianSample := (SLang_Capsid, DiscreteGaussianSample)


-- Remaining two examples fail to extract becasue they're looking for
-- a name X, but there is only the name tc_X. Fix the frontend.

attribute [export_dafny] tc_UniformSample
attribute [export_dafny] tc_BernoulliSample
attribute [export_dafny] tc_BernoulliExpNegSampleUnitLoop
attribute [export_dafny] tc_BernoulliExpNegSampleUnitAux
attribute [export_dafny] tc_BernoulliExpNegSampleUnit
-- attribute [export_dafny] tc_BernoulliExpNegSampleGenLoop
attribute [export_dafny] tc_BernoulliExpNegSample
attribute [export_dafny] tc_DiscreteLaplaceSampleLoopIn1Aux
attribute [export_dafny] tc_DiscreteLaplaceSampleLoopIn1
attribute [export_dafny] tc_DiscreteLaplaceSampleLoopIn2Aux
attribute [export_dafny] tc_DiscreteLaplaceSampleLoopIn2
-- attribute [export_dafny] tc_DiscreteLaplaceSampleLoop
attribute [export_dafny] tc_DiscreteLaplaceSample
attribute [export_dafny] tc_DiscreteGaussianSampleLoop
attribute [export_dafny] tc_DiscreteGaussianSample
