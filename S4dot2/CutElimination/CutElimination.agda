{-# OPTIONS --cubical --safe #-}

-- Facade (Phase 5 of the token-algebra parameterization): the
-- cut-elimination driver is generic
-- (S4dot2.Generic.CutElimination.CutElimination); this instantiates it
-- at the NAT-SDL instance.  The theorem statement is pinned verbatim in
-- S4dot2/TokenAlgebra/Test/MixStatementPin.agda.

module S4dot2.CutElimination.CutElimination where

open import S4dot2.TokenAlgebra.NatSDL using (natSDL)
open import S4dot2.Generic.CutElimination.CutElimination natSDL public
