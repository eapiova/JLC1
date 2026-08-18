{-# OPTIONS --cubical --safe #-}

-- Position-operation compatibility layer for the generic cut-elimination
-- modules (Phase 4 of the token-algebra parameterization): exports the
-- SortedPosition SPELLINGS and argument orders that the ProofSubst /
-- MixHelpers bodies consume, implemented from the TokenAlgebra fields
-- and the derived layer ALONE.  At the NAT-SDL instance every export is
-- definitionally today's SortedPosition operation/lemma (the wrappers
-- are non-matching definitions, so they unfold on any argument).
--
-- Deliberately NOT exported here (they already flow through
-- S4dot2.Generic.Syntax): Token, Position, insertToken, _∈Pos_, _∉Pos_,
-- _⊑_, singleton-pos.  Consumers hide/rename to avoid double bindings.

open import S4dot2.TokenAlgebra.Interface

module S4dot2.Generic.CutElimination.PositionCompat (TA : TokenAlgebra) where

open import Cubical.Foundations.Prelude using (_≡_; _∙_)
open import Cubical.Relation.Nullary using (¬_)

open import S4dot2.TokenAlgebra.Derived

-- Same-name-and-order derived lemmas: re-export directly.
open DerivedLaws TA public
  using ( ∉Pos-merge ; ∉Pos-remove
        ; ∈Pos-insertToken ; insertToken-∈Pos
        ; remove-insertToken ; remove-insertToken-neq
        ; merge-insertToken-l ; merge-⊑-mono
        ; remove-sing-self )

-- Operation fields under SortedPosition spellings.
open TokenAlgebra TA public
  using (remove; ∈sing-elim)
  renaming (ε to ∅; sing to [_]; _∪_ to merge; _∈ᵖ?_ to _∈Pos?_)

-- Internal (non-exported) access to the remaining fields.
open TokenAlgebra TA
  using ( _∈ᵖ_ ; ∪-assoc ; ∪-comm ; ∪-idr ; ∪-idem ; insert-∪-sing
        ; ∈∪-elim ; ∈∪-introˡ ; ∈∪-introʳ
        ; remove-∈-elim ; remove-∈-neq ; ∈-remove-intro ; remove-∉-id
        ; remove-∪-distr ; remove-insert-cancel )

-- Same-order aliases (SortedPosition names for the law fields).
merge-assoc = ∪-assoc
merge-comm = ∪-comm
merge-∅-r = ∪-idr
merge-idem = ∪-idem
merge-singleton = insert-∪-sing
∈Pos-merge = ∈∪-elim
merge-∈Pos-l = ∈∪-introˡ
merge-∈Pos-r = ∈∪-introʳ
remove-∉Pos-id = remove-∉-id
remove-merge-distrib = remove-∪-distr
insertToken-remove-cancel' = remove-insert-cancel

-- Argument-order wrappers (SortedPosition puts the removed token first).
remove-∈Pos : ∀ x t s → t ∈ᵖ remove x s → t ∈ᵖ s
remove-∈Pos x t s = remove-∈-elim t x s

remove-∈Pos-neq : ∀ x t s → t ∈ᵖ remove x s → ¬ (x ≡ t)
remove-∈Pos-neq x t s = remove-∈-neq t x s

∈Pos-remove : ∀ x t s → t ∈ᵖ s → ¬ (x ≡ t) → t ∈ᵖ remove x s
∈Pos-remove x t s = ∈-remove-intro t x s

-- Mirror of SortedPosition:496-498 (merge-with-singleton phrasing).
insertToken-remove-cancel : ∀ x s → x ∈ᵖ s → merge (remove x s) [ x ] ≡ s
insertToken-remove-cancel x s x∈s =
  merge-singleton (remove x s) x ∙ insertToken-remove-cancel' x s x∈s
