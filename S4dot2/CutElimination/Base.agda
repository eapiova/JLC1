{-# OPTIONS --cubical --safe #-}

-- Facade (Phase 5 of the token-algebra parameterization): the generic
-- Base applied at the NAT-SDL instance.  Copy discipline: the generic
-- Base re-exports its own application of Defs and of System's
-- discretePFormula; those copies are HIDDEN here and re-sourced from the
-- Defs/System facades, so the whole NAT chain shares exactly one copy of
-- each measure head (δ/height/degree) and of discretePFormula.

module S4dot2.CutElimination.Base where

open import S4dot2.TokenAlgebra.NatSDL using (natSDL)

-- the single Defs copy of the NAT chain (re-exported downstream)
open import S4dot2.CutElimination.Defs public
open import S4dot2.System using (discretePFormula) public

open import S4dot2.Generic.CutElimination.Base natSDL public
  hiding ( case_of_ ; false-neq-true ; degree ; height ; height-subst
         ; height-subst-Γ ; height-subst-Δ ; δ ; isCutFree
         ; leq-max-1 ; leq-max-2 ; leq-max-2-1 ; leq-max-2-2
         ; ≤-reflexive ; _≢_ ; trans ; ¬m<m ; <→≢ ; z≤ ; s≤s ; inv-s≤s
         ; max-least ; Inspect ; it ; inspect ; mem-++-split
         ; discretePFormula )
