{-# OPTIONS --cubical --safe #-}

-- Facade (Phases 4-5 of the token-algebra parameterization): the generic
-- proof-substitution engine applied at the NAT-SDL instance, plus the
-- SDL-geometry extras (>ᴴ-head< / >-head->-maxTail), kept at the
-- instance because they mention SDL internals.  Since Phase 5 the
-- δ/height measure layer (δ-*/height-* preservation lemmas and
-- substEigenposInProof) lives in the generic engine too (over the
-- generic Defs), so it arrives through the public open below.
-- The export surface is today's, each name exactly once.

module S4dot2.CutElimination.ProofSubst where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List hiding ([_]) renaming (_++_ to _++L_)
open import Cubical.Data.List.Properties renaming (++-assoc to ++L-assoc)
open import Cubical.Data.Nat using (ℕ; zero; suc; max; _+_)
open import Cubical.Data.Nat.Order using (_≤_; _<_; _>_; ≤-refl; zero-≤; suc-≤-suc; pred-≤-pred; ≤-trans; ¬-<-zero; <→≢; <-trans; <-weaken)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit; tt)

open import Cubical.Relation.Nullary renaming (¬_ to Neg)

open import S4dot2.Syntax hiding (_⊢_) renaming (_∧_ to _and_; _∨_ to _or_)
open import S4dot2.System
open import S4dot2.SortedPosition renaming (merge to _++Pos_; [_] to singleton-pos)
open import S4dot2.CutElimination.Base using (δ; degree; height)

open import S4dot2.TokenAlgebra.NatSDL using (natSDL)
open import S4dot2.Generic.CutElimination.ProofSubst natSDL public

-- =============================================================================
-- SDL-geometry extras (instance-level: they mention SDL internals)
-- =============================================================================

-- Helper: extract the < proof from >ᴴ for non-empty lists
>ᴴ-head< : ∀ {y z zs z>zs} → y >ᴴ pos-cons z zs z>zs → z < y
>ᴴ-head< (>ᴴcons y>z) = y>z

-- Helper: if n > y and y is the head of the SDL, then n > maxTokenPos ys
-- (re-proved against the listMax-based maxTokenPos)
>-head->-maxTail : (n y : Token) (ys : Position) (y>ys : y >ᴴ ys) → n > y → n > maxTokenPos ys
>-head->-maxTail n y ∅ _ n>y = >-implies->0 n>y
>-head->-maxTail n y (pos-cons z zs z>zs) y>ys n>y =
  myMax-<-both (<-trans (>ᴴ-head< y>ys) n>y)
               (>-head->-maxTail n z zs z>zs (<-trans (>ᴴ-head< y>ys) n>y))

