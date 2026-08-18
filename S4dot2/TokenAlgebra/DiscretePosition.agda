{-# OPTIONS --cubical --safe #-}

-- The Position discreteness proof, relocated VERBATIM from
-- S4dot2/System.agda (lines 208-228, the unsort-factor/toList-inj block)
-- so the NatSDL instance can bind TokenAlgebra.discretePos without
-- importing S4dot2.System — after the facade flip System.agda
-- instantiates NatSDL, which would be a cycle.  Only needs
-- SortedPosition + LFSet.  (discreteToken in the original text is
-- definitionally discreteℕ, used directly here.)

module S4dot2.TokenAlgebra.DiscretePosition where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.List using (List; _∷_; [])
open import Cubical.Data.List.Properties using (discreteList)
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Relation.Nullary using (Dec; yes; no; Discrete)

-- For proving Position equalities via LFSet
open import Cubical.HITs.ListedFiniteSet as LFSet using (LFSet)

open import S4dot2.SortedPosition

-- Helper: Convert list to LFSet
fromList : List Token → LFSet ℕ
fromList [] = LFSet.[]
fromList (x ∷ xs) = x LFSet.∷ fromList xs

-- Lemma: unsortTokens factors through toList
unsort-factor : ∀ (u : Position) → unsortTokens u ≡ fromList (toList u)
unsort-factor ∅ = refl
unsort-factor (pos-cons x xs _) = cong (x LFSet.∷_) (unsort-factor xs)

-- Injectivity of toList via position-inj
toList-inj : ∀ {u v : Position} → toList u ≡ toList v → u ≡ v
toList-inj {u} {v} p = position-inj u v (
  unsort-factor u ∙
  cong fromList p ∙
  sym (unsort-factor v))

discretePosition : Discrete Position
discretePosition s t with discreteList discreteℕ (toList s) (toList t)
... | yes p = yes (toList-inj p)
... | no p = no (λ eq → p (cong toList eq))
