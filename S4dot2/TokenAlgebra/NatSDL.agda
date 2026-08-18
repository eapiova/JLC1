{-# OPTIONS --cubical --safe #-}

-- The NAT-SDL instance of the token algebra: every operation field is
-- bound to today's SortedPosition/System export VERBATIM, so downstream
-- statements are definitionally unchanged (gate 1 checks this by refl in
-- Test/NatSDLNoOp.agda).  Only the handful of laws whose argument order
-- differs, plus the two listability bridges, carry thin wrappers.

module S4dot2.TokenAlgebra.NatSDL where

open import Cubical.Foundations.Prelude
  using (refl)
open import Cubical.Data.Nat
  using (ℕ; suc)
open import Cubical.Data.Nat.Order
  using (≤-refl)
open import Cubical.Data.Nat.Properties
  using (discreteℕ)
open import Cubical.Data.Sum
  using (inl; inr)

open import S4dot2.SortedPosition
open import S4dot2.TokenAlgebra.DiscretePosition
  using (discretePosition)
open import S4dot2.TokenAlgebra.Interface

-- Bridge between the interface's standalone list membership and the
-- stack's own (identical constructors, distinct datatypes).
private
  ∈List→∈L :
    ∀ {x : ℕ} {xs} → x ∈List xs → x ∈L xs
  ∈List→∈L here = hereL
  ∈List→∈L (there m) = thereL (∈List→∈L m)

  ∈L→∈Pos :
    ∀ (x : ℕ) (s : Position) → x ∈L toList s → x ∈Pos s
  ∈L→∈Pos x (pos-cons y ys _) hereL = inl refl
  ∈L→∈Pos x (pos-cons y ys _) (thereL m) =
    inr (∈L→∈Pos x ys m)

natSDL : TokenAlgebra
TokenAlgebra.Token natSDL = ℕ
TokenAlgebra.Pos natSDL = Position
TokenAlgebra.discreteToken natSDL = discreteℕ
TokenAlgebra.discretePos natSDL = discretePosition
TokenAlgebra.ε natSDL = ∅
TokenAlgebra.sing natSDL = [_]
TokenAlgebra._∪_ natSDL = merge
TokenAlgebra.insert natSDL = insertToken
TokenAlgebra.remove natSDL = remove
TokenAlgebra._∈ᵖ_ natSDL = _∈Pos_
TokenAlgebra._∈ᵖ?_ natSDL = _∈Pos?_
TokenAlgebra.∪-assoc natSDL = merge-assoc
TokenAlgebra.∪-comm natSDL = merge-comm
TokenAlgebra.∪-idr natSDL = merge-∅-r
TokenAlgebra.∪-idem natSDL = merge-idem
TokenAlgebra.∈∪-elim natSDL = ∈Pos-merge
TokenAlgebra.∈∪-introˡ natSDL = merge-∈Pos-l
TokenAlgebra.∈∪-introʳ natSDL = merge-∈Pos-r
TokenAlgebra.∈sing-elim natSDL =
  λ x y → λ { (inl e) → e ; (inr ()) }
TokenAlgebra.∈sing-intro natSDL = λ x → inl refl
TokenAlgebra.¬∈ε natSDL = λ x p → p
TokenAlgebra.insert-∪-sing natSDL = merge-singleton
TokenAlgebra.remove-∈-elim natSDL =
  λ x y s → remove-∈Pos y x s
TokenAlgebra.remove-∈-neq natSDL =
  λ x y s → remove-∈Pos-neq y x s
TokenAlgebra.∈-remove-intro natSDL =
  λ x y s → ∈Pos-remove y x s
TokenAlgebra.remove-∉-id natSDL = remove-∉Pos-id
TokenAlgebra.remove-∪-distr natSDL = remove-merge-distrib
TokenAlgebra.remove-insert-cancel natSDL =
  insertToken-remove-cancel'
TokenAlgebra.posExt natSDL = ⊑-antisym
TokenAlgebra.toList natSDL = toList
TokenAlgebra.∈→toList natSDL =
  λ x s m → ∈List→∈L (toList-∈ x s m)
TokenAlgebra.toList→∈ natSDL = ∈L→∈Pos
TokenAlgebra.tokℕ natSDL = λ x → x
TokenAlgebra.freshAbove natSDL = suc
TokenAlgebra.freshAbove-bound natSDL = λ n → ≤-refl
