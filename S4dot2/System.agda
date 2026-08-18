{-# OPTIONS --cubical --safe #-}

-- Facade (Phase 3 of the token-algebra parameterization): the generic
-- sequent-calculus layer applied at the NAT-SDL instance, plus the
-- relocated Position-discreteness block (fromList / unsort-factor /
-- toList-inj / discretePosition) re-exported from
-- S4dot2.TokenAlgebra.DiscretePosition under today's exact symbols.
-- The export surface is unchanged; discretePosition is exported exactly
-- once (Generic's field copy is hidden — at natSDL it is definitionally
-- the relocated proof).

module S4dot2.System where

open import S4dot2.TokenAlgebra.NatSDL using (natSDL)

open import S4dot2.Generic.System natSDL public
  hiding (discretePosition)

open import S4dot2.TokenAlgebra.DiscretePosition public
