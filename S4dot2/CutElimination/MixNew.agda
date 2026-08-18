{-# OPTIONS --cubical --safe #-}

-- Facade (Phase 5 of the token-algebra parameterization): the mix engine
-- is generic (S4dot2.Generic.CutElimination.MixNew); this instantiates
-- it at the NAT-SDL instance.  The theorem statement is pinned verbatim
-- in S4dot2/TokenAlgebra/Test/MixStatementPin.agda.

module S4dot2.CutElimination.MixNew where

open import S4dot2.TokenAlgebra.NatSDL using (natSDL)
open import S4dot2.Generic.CutElimination.MixNew natSDL public
