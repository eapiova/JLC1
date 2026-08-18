{-# OPTIONS --cubical --safe #-}

-- Facade (Phase 3 of the token-algebra parameterization): the generic
-- syntax layer applied at the NAT-SDL instance, plus the SDL-specific
-- position toolbox re-exported from SortedPosition under today's exact
-- symbols.  The export surface is unchanged: every name is exported
-- exactly once — where Generic and SortedPosition both provide a
-- position-layer name, the SortedPosition original wins (Generic's copy
-- is hidden; at natSDL the two are definitionally equal), so downstream
-- files that import S4dot2.Syntax and S4dot2.SortedPosition together
-- (e.g. CutElimination/ProofSubst.agda) keep resolving to one symbol.

module S4dot2.Syntax where

open import S4dot2.TokenAlgebra.NatSDL using (natSDL)

-- ListExt re-exported here directly (original symbols — going through
-- the applied Generic module would make them ambiguous downstream)
open import S4dot2.ListExt public hiding (_⊑_)

-- Generic syntax layer at the NAT-SDL instance:
-- Formula, PFormula, Sequent, Axiom, ⊢S4dot2, [_], _∘_, _≢_,
-- IsSingleTokenExt, TokenFresh, _∈Init_/_∉Init_, discreteToken (the
-- interface field), the ListExt re-export, and variables A B C.
open import S4dot2.Generic.Syntax natSDL public
  hiding (Token; Position; singleton-pos; merge; insertToken; _∈Pos_; _∉Pos_; _⊑_)

-- SDL-based positions from SortedPosition (today's symbols, verbatim)
open import S4dot2.SortedPosition public
  renaming ([_] to singleton-pos)  -- [_] creates singleton Position from Token
