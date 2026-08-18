{-# OPTIONS --cubical --safe #-}

-- Generic syntax layer of the S4dot2 stack, parameterized over a token
-- algebra (Phase 3 of the token-algebra parameterization).  Body ported
-- verbatim from S4dot2/Syntax.agda; the only real edits are that names
-- previously sourced from SortedPosition now come from TA's fields /
-- DerivedLaws TA, and discreteToken is the interface field.

open import S4dot2.TokenAlgebra.Interface

module S4dot2.Generic.Syntax (TA : TokenAlgebra) where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; _∙_; cong; transport; subst; J; funExt; _∎)
open import Cubical.Data.List using (List; []; _∷_; _++_; map) renaming ([_] to List-[_])
open import Cubical.Data.List.Properties using (++-assoc; map++)
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma using (∃; _×_; _,_; fst; snd; Σ)
open import Cubical.Data.Empty renaming (rec to emptyRec)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Maybe using (Maybe; just; nothing)

open import S4dot2.TokenAlgebra.Derived

-- NON-public: re-exporting ListExt through this applied parameterized
-- module would mint distinct scope copies of its names, making them
-- ambiguous downstream against direct S4dot2.ListExt imports.  The
-- facade re-exports the ListExt originals itself.
open import S4dot2.ListExt hiding (_⊑_)

-- Positions come from the token algebra TA.
-- (At the NAT-SDL instance every name below is definitionally today's
-- SortedPosition export; the facade re-exports the SortedPosition
-- originals and hides these.)
open TokenAlgebra TA public
  using (Token; discreteToken)
  renaming ( Pos to Position
           ; sing to singleton-pos
           ; _∪_ to merge
           ; insert to insertToken
           ; _∈ᵖ_ to _∈Pos_ )

open DerivedLaws TA public
  using (_⊑_)
  renaming (_∉ᵖ_ to _∉Pos_)

-- List singleton notation for contexts
[_] : ∀ {ℓ} {A : Type ℓ} → A → List A
[ x ] = x ∷ []

-- Reference: Section 2
-- Token is the token algebra's token carrier

-- Position is the token algebra's position carrier
-- Concatenation is now set union (merge)
_∘_ : Position → Position → Position
_∘_ = merge

-- Section 2.1
-- Definition 2.2
data Formula : Type where
  Atom : ℕ → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  _⇒_ : Formula → Formula → Formula
  ¬_ : Formula → Formula
  □ : Formula → Formula
  ♢ : Formula → Formula

infixr 6 _⇒_
infixr 7 _∨_
infixr 8 _∧_
infix  9 ¬_ □ ♢

-- Definition 2.3.1 (Position-Formulas)
record PFormula : Type where
  constructor _^_
  field
    form : Formula
    pos : Position


-- Decidable equality for Tokens: the interface field (re-exported above)

-- Position subset relation _⊑_ and its laws come from DerivedLaws TA
-- s ⊑ t means every token in s is also in t

-- Token inequality
_≢_ : Token → Token → Type
x ≢ y = x ≡ y → ⊥

-- Token not in position (re-exported above as _∉Pos_)

-- t extends s by exactly one token x (set-based version)
-- This means: s ⊆ t, x ∈ t, x ∉ s, and x is the only new token
IsSingleTokenExt : Position → Position → Token → Type
IsSingleTokenExt s t x = (s ⊑ t) × (x ∈Pos t) × (x ∉Pos s) × (∀ y → y ∈Pos t → y ∉Pos s → y ≡ x)

-- Token fresh for a context (doesn't appear in any position in the context)
TokenFresh : Token → List PFormula → Type
TokenFresh x [] = Unit
TokenFresh x (pf ∷ Γ) = (x ∉Pos PFormula.pos pf) × TokenFresh x Γ

-- Definition 2.3.2 (Extended Sequents)
record Sequent : Type where
  constructor _⊢_
  field
    ant : List PFormula
    succedent : List PFormula

infix 4 _⊢_


-- Definition of Init(Γ) (Page 5)
-- t ∈Init Γ means t is a subset of some position in Γ
_∈Init_ : Position → List PFormula → Type
t ∈Init Γ = Σ PFormula λ pf → (pf ∈ Γ) × (t ⊑ PFormula.pos pf)

_∉Init_ : Position → List PFormula → Type
t ∉Init Γ = (t ∈Init Γ) → ⊥

variable
  A B C : Formula

-- Hilbert axiom basis for S4.2 (S4.2 paper, Sec 3.1).
-- Formalization decision 2026-07-24: ∧, ∨, and ♢ are primitive, hence the basis is
-- extended with their axioms and ♢-duality. Previously only D compensated for
-- ♢-primitivity; the old basis made (A ∧ A) ⇒ A underivable. See
-- S4dot2/Algebra/LegacyBasisRefuted.agda.
data Axiom : Formula → Type where
  -- Propositional axioms
  P1  : Axiom (A ⇒ (B ⇒ A))
  P2  : Axiom ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
  P3  : Axiom (((¬ B) ⇒ (¬ A)) ⇒ (((¬ B) ⇒ A) ⇒ B))
  ∧E₁ : Axiom ((A ∧ B) ⇒ A)
  ∧E₂ : Axiom ((A ∧ B) ⇒ B)
  ∧I  : Axiom (A ⇒ (B ⇒ (A ∧ B)))
  ∨I₁ : Axiom (A ⇒ (A ∨ B))
  ∨I₂ : Axiom (B ⇒ (A ∨ B))
  ∨E  : Axiom ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ ((A ∨ B) ⇒ C)))
  ♢def₁ : Axiom ((♢ A) ⇒ (¬ (□ (¬ A))))
  ♢def₂ : Axiom ((¬ (□ (¬ A))) ⇒ (♢ A))
  -- Modal axioms
  K   : Axiom (□ (A ⇒ B) ⇒ (□ A ⇒ □ B))
  D   : Axiom (□ A ⇒ ♢ A)       -- Seriality; redundant given ♢def₁, ♢def₂ and T
  T   : Axiom (□ A ⇒ A)
  Ax4 : Axiom (□ A ⇒ □ (□ A))   -- Paper: 4 (bare digit not valid Agda identifier)
  AxC : Axiom (♢ (□ A) ⇒ □ (♢ A)) -- Paper: G/.2 (bare C conflicts with variable C)

data ⊢S4dot2 : Formula → Type where
  -- Axioms
  ax : Axiom A → ⊢S4dot2 A
  -- Modus Ponens
  MP : ⊢S4dot2 A → ⊢S4dot2 (A ⇒ B) → ⊢S4dot2 B
  -- Necessitation
  NEC : ⊢S4dot2 A → ⊢S4dot2 (□ A)
