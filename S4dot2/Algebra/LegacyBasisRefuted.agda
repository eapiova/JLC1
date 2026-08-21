{-# OPTIONS --cubical --safe #-}

-- Machine-checked witness for the JLC erratum: this module archives the
-- pre-2026-07-24 Hilbert basis. The live ⊢S4dot2 has been fixed.
--
-- The former ModalAlgebraStr soundness refutation is not archived here: it
-- depended on the superseded record without ♢-duality, and its constant-false
-- interpretation of ♢ cannot inhabit the planned ♢-dual record.

module S4dot2.Algebra.LegacyBasisRefuted where

open import Cubical.Foundations.Prelude
  using (Type; _≡_; refl; sym; _∙_)
open import Cubical.Data.Bool
  using (Bool; true; false; not; _or_; _and_; false≢true)
open import Cubical.Data.Nat using (zero)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd)
open import Cubical.Data.Empty as Empty using (⊥)

open import S4dot2.Syntax
  using (Formula; Atom; _∧_; _∨_; _⇒_; ¬_; □; ♢)
open import S4dot2.Equivalence.FiniteModel
  using (FiniteModel; eval)

private
  variable
    A B C : Formula

-- The eight constructors of the old, pre-2026-07-24 basis.
data LegacyAxiom : Formula → Type where
  P1  : LegacyAxiom (A ⇒ (B ⇒ A))
  P2  : LegacyAxiom ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
  P3  : LegacyAxiom (((¬ B) ⇒ (¬ A)) ⇒ (((¬ B) ⇒ A) ⇒ B))
  K   : LegacyAxiom (□ (A ⇒ B) ⇒ (□ A ⇒ □ B))
  D   : LegacyAxiom (□ A ⇒ ♢ A)
  T   : LegacyAxiom (□ A ⇒ A)
  Ax4 : LegacyAxiom (□ A ⇒ □ (□ A))
  AxC : LegacyAxiom (♢ (□ A) ⇒ □ (♢ A))

data ⊢legacy : Formula → Type where
  ax  : LegacyAxiom A → ⊢legacy A
  MP  : ⊢legacy A → ⊢legacy (A ⇒ B) → ⊢legacy B
  NEC : ⊢legacy A → ⊢legacy (□ A)

infixr 6 _⊃ᵇ_

_⊃ᵇ_ : Bool → Bool → Bool
a ⊃ᵇ b = not a or b

counterEval : Formula → Bool
counterEval (Atom _) = false
counterEval (_ ∧ _) = true
counterEval (_ ∨ _) = false
counterEval (A ⇒ B) = counterEval A ⊃ᵇ counterEval B
counterEval (¬ A) = not (counterEval A)
counterEval (□ A) = counterEval A
counterEval (♢ A) = counterEval A

boolImpRefl : (a : Bool) → a ⊃ᵇ a ≡ true
boolImpRefl false = refl
boolImpRefl true = refl

boolP1 : (a b : Bool) → a ⊃ᵇ (b ⊃ᵇ a) ≡ true
boolP1 false b = refl
boolP1 true false = refl
boolP1 true true = refl

boolP2 : (a b c : Bool)
  → (a ⊃ᵇ (b ⊃ᵇ c)) ⊃ᵇ ((a ⊃ᵇ b) ⊃ᵇ (a ⊃ᵇ c)) ≡ true
boolP2 false b c = refl
boolP2 true false c = refl
boolP2 true true false = refl
boolP2 true true true = refl

boolP3 : (a b : Bool)
  → ((not b ⊃ᵇ not a) ⊃ᵇ ((not b ⊃ᵇ a) ⊃ᵇ b)) ≡ true
boolP3 false false = refl
boolP3 false true = refl
boolP3 true false = refl
boolP3 true true = refl

counterSoundAxiom :
  {A : Formula} → LegacyAxiom A → counterEval A ≡ true
counterSoundAxiom {A = A ⇒ (B ⇒ A)} P1 =
  boolP1 (counterEval A) (counterEval B)
counterSoundAxiom
  {A = (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))}
  P2 =
  boolP2 (counterEval A) (counterEval B) (counterEval C)
counterSoundAxiom
  {A = ((¬ B) ⇒ (¬ A)) ⇒ (((¬ B) ⇒ A) ⇒ B)}
  P3 =
  boolP3 (counterEval A) (counterEval B)
counterSoundAxiom {A = □ (A ⇒ B) ⇒ (□ A ⇒ □ B)} K =
  boolImpRefl (counterEval A ⊃ᵇ counterEval B)
counterSoundAxiom {A = □ A ⇒ ♢ A} D =
  boolImpRefl (counterEval A)
counterSoundAxiom {A = □ A ⇒ A} T =
  boolImpRefl (counterEval A)
counterSoundAxiom {A = □ A ⇒ □ (□ A)} Ax4 =
  boolImpRefl (counterEval A)
counterSoundAxiom {A = ♢ (□ A) ⇒ □ (♢ A)} AxC =
  boolImpRefl (counterEval A)

boolMP : {a b : Bool} → a ≡ true → a ⊃ᵇ b ≡ true → b ≡ true
boolMP {true} _ q = q
boolMP {false} p _ = Empty.rec (false≢true p)

counterSound : {A : Formula} → ⊢legacy A → counterEval A ≡ true
counterSound (ax a) = counterSoundAxiom a
counterSound (MP p q) = boolMP (counterSound p) (counterSound q)
counterSound (NEC p) = counterSound p

idempotenceFormula : Formula
idempotenceFormula = (Atom zero ∧ Atom zero) ⇒ Atom zero

idempotenceNotDerivable : ⊢legacy idempotenceFormula → ⊥
idempotenceNotDerivable d = false≢true (counterSound d)

private
  notAndSelfOr : (b : Bool) → not (b and b) or b ≡ true
  notAndSelfOr false = refl
  notAndSelfOr true = refl

-- (A ∧ A) ⇒ A is true at every world of every finite model.
evalIdemTrue : (M : FiniteModel) (w : FiniteModel.World M)
             → eval M w idempotenceFormula ≡ true
evalIdemTrue M w = notAndSelfOr (eval M w (Atom zero))

legacySegerbergFMP-impossible :
  (∀ A → (⊢legacy A → ⊥) →
    Σ FiniteModel
      (λ M → eval M (FiniteModel.m M) A ≡ false)) →
  ⊥
legacySegerbergFMP-impossible fmp =
  false≢true
    (sym (snd M×p) ∙
      evalIdemTrue (fst M×p) (FiniteModel.m (fst M×p)))
  where
  M×p = fmp idempotenceFormula idempotenceNotDerivable
