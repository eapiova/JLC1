{-# OPTIONS --cubical --safe #-}

-- The commutative-idempotent token algebra the S4dot2 stack is being
-- parameterized over (CUTELIM-BOUNDARIES "Verdict", the one open door).
--
-- Design rule (from the demand surveys, .claude/block6-work/s42/):
-- any operation that appears in a theorem STATEMENT of System / the
-- ProofSubst API / MixNew is a FIELD, never a derived definition, so the
-- NAT instance can bind it to today's definition verbatim and every
-- downstream statement is definitionally unchanged.  Laws are fields
-- only when ProofSubst consumes them by name.
--
-- Deliberate ANTI-fields (demanded by nothing in the chain): no strict
-- order on Token, no trichotomy, no canonical-form constructor, no
-- prefix relation, no snoc-injectivity (false over idempotent union).

module S4dot2.TokenAlgebra.Interface where

open import Cubical.Foundations.Prelude
  using (Type; _≡_)
open import Cubical.Data.Empty
  using (⊥)
open import Cubical.Data.List
  using (List; []; _∷_)
open import Cubical.Data.Nat
  using (ℕ)
open import Cubical.Data.Nat.Order
  using (_<_)
open import Cubical.Data.Sum
  using (_⊎_)
open import Cubical.Relation.Nullary
  using (Dec; Discrete; ¬_)

-- Standalone list membership (the interface cannot depend on any
-- instance's list machinery).
data _∈L_ {ℓ} {A : Type ℓ} (x : A) : List A → Type ℓ where
  hereL  : ∀ {xs} → x ∈L (x ∷ xs)
  thereL : ∀ {y xs} → x ∈L xs → x ∈L (y ∷ xs)

record TokenAlgebra : Type₁ where
  no-eta-equality
  field
    ---- Carriers ----
    Token : Type₀
    Pos   : Type₀
    discreteToken : Discrete Token
    discretePos   : Discrete Pos

    ---- Operations (statement-visible ⇒ fields) ----
    ε      : Pos
    sing   : Token → Pos
    _∪_    : Pos → Pos → Pos
    insert : Token → Pos → Pos
    remove : Token → Pos → Pos
    _∈ᵖ_   : Token → Pos → Type₀
    _∈ᵖ?_  : ∀ x s → Dec (x ∈ᵖ s)

    ---- Commutative idempotent monoid ----
    ∪-assoc : ∀ s t r → (s ∪ t) ∪ r ≡ s ∪ (t ∪ r)
    ∪-comm  : ∀ s t → s ∪ t ≡ t ∪ s
    ∪-idr   : ∀ s → s ∪ ε ≡ s
    ∪-idem  : ∀ s → s ∪ s ≡ s

    ---- Membership characterizations ----
    ∈∪-elim   : ∀ x s t → x ∈ᵖ (s ∪ t) → (x ∈ᵖ s) ⊎ (x ∈ᵖ t)
    ∈∪-introˡ : ∀ x s t → x ∈ᵖ s → x ∈ᵖ (s ∪ t)
    ∈∪-introʳ : ∀ x s t → x ∈ᵖ t → x ∈ᵖ (s ∪ t)
    ∈sing-elim  : ∀ x y → x ∈ᵖ sing y → x ≡ y
    ∈sing-intro : ∀ x → x ∈ᵖ sing x
    ¬∈ε : ∀ x → ¬ (x ∈ᵖ ε)
    insert-∪-sing : ∀ s x → s ∪ sing x ≡ insert x s

    ---- remove characterization ----
    remove-∈-elim  : ∀ x y s → x ∈ᵖ remove y s → x ∈ᵖ s
    remove-∈-neq   : ∀ x y s → x ∈ᵖ remove y s → ¬ (y ≡ x)
    ∈-remove-intro : ∀ x y s → x ∈ᵖ s → ¬ (y ≡ x) → x ∈ᵖ remove y s
    remove-∉-id    : ∀ x s → ¬ (x ∈ᵖ s) → remove x s ≡ s
    remove-∪-distr :
      ∀ x s t → remove x (s ∪ t) ≡ (remove x s) ∪ (remove x t)
    remove-insert-cancel :
      ∀ x s → x ∈ᵖ s → insert x (remove x s) ≡ s

    ---- Extensionality (the one non-equational axiom) ----
    posExt :
      ∀ s t
      → (∀ x → x ∈ᵖ s → x ∈ᵖ t)
      → (∀ x → x ∈ᵖ t → x ∈ᵖ s)
      → s ≡ t

    ---- Listability (substrate of the fresh-token engine) ----
    toList   : Pos → List Token
    ∈→toList : ∀ x s → x ∈ᵖ s → x ∈L toList s
    toList→∈ : ∀ x s → x ∈L toList s → x ∈ᵖ s

    ---- Token measure + fresh generation ----
    tokℕ : Token → ℕ
    freshAbove : ℕ → Token
    freshAbove-bound : ∀ n → n < tokℕ (freshAbove n)
