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
