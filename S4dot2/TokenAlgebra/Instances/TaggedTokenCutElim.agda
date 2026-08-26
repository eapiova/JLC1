{-# OPTIONS --cubical --safe #-}

-- Genuine-parametricity witness: elaborate the full generic S4.2 mix and
-- cut-elimination chain at the non-NAT tagged-token algebra.

module S4dot2.TokenAlgebra.Instances.TaggedTokenCutElim where

open import S4dot2.TokenAlgebra.Instances.TaggedToken
  using (taggedToken)
open import S4dot2.Generic.CutElimination.MixNew taggedToken public
  using (mix)
open import S4dot2.Generic.CutElimination.CutElimination taggedToken public
  using (CutElimination)

-- Named witnesses of the instantiated chain, so that the paper can link to
-- this module through stable anchors (re-exports get none in the HTML).
taggedMix = mix
taggedCutElimination = CutElimination
