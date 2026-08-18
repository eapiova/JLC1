{-# OPTIONS --cubical --safe #-}

-- Facade (Phase 5 of the token-algebra parameterization): the generic
-- Defs layer (degree/height/δ/isCutFree + auxiliaries) applied at the
-- NAT-SDL instance.  This module application is the ONE Defs copy of the
-- NAT chain: Base re-exports THIS module (hiding the generic Base's own
-- Defs re-export), so every downstream spelling of the measure heads
-- shares it.

module S4dot2.CutElimination.Defs where

open import S4dot2.TokenAlgebra.NatSDL using (natSDL)
open import S4dot2.Generic.CutElimination.Defs natSDL public
