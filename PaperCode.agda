-- Worked derivations displayed in the JLC paper: the Geach axiom, and the
-- closure of derivability under necessitation and modus ponens.  Formerly a
-- literate .lagda.tex module; converted to a plain module so that the HTML
-- rendering shows code only, and the paper's listings are generated from
-- this source by scripts/gen-agda-snippet.py.

{-# OPTIONS --cubical --safe #-}

module PaperCode where

open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Foundations.Prelude using (_≡_; subst; sym; _∙_)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Order using (≤-refl; suc-≤-suc)
open import Cubical.Data.Unit using (tt)
open import S4dot2.Syntax hiding (_⊢_)
open import S4dot2.System
open import S4dot2.Equivalence.HilbertCompleteness
  using (TokenFresh-singleton; TokenFresh-[]; 1≢0; lift-proof)
open import S4dot2.CutElimination.ProofSubst
  using (NoEigenposInt-singleton-fresh; maxEigenposToken)

-- Imports for HTML documentation generation
import S4dot2.CutElimination.Base
import S4dot2.CutElimination.CutElimination
import S4dot2.CutElimination.MixNew
import S4dot2.CutElimination.SubformulaProperty
import S4dot2.CutElimination.Consistency

private module G (A : Formula) where
  α = ∅
  β = insertToken 0 α
  γ = insertToken 1 α
  δ = insertToken 1 β
  fresh-α-0 : 0 ∉Pos α
  fresh-α-0 = λ ()
  fresh-α-1 : 1 ∉Pos α
  fresh-α-1 = λ ()
  fresh-Δ-♢⊢ = TokenFresh-singleton {x = 0} {A = □ (♢ A)} {s = α} fresh-α-0
  fresh-β-1 = ∉Pos-insertToken 0 1 α fresh-α-1 1≢0
  fresh-Γ-⊢□ = TokenFresh-singleton {x = 1} {A = □ A} {s = β} fresh-β-1
  eq-γ0-δ : γ ∘ singleton-pos 0 ≡ δ
  eq-γ0-δ = merge-singleton γ 0 ∙ insertToken-swap 0 1 α
  eq-β1-δ : β ∘ singleton-pos 1 ≡ δ
  eq-β1-δ = merge-singleton β 1
  ax-subst : [ A ^ δ ] ⊢ [ A ^ (γ ∘ singleton-pos 0) ]
  ax-subst = subst (λ pos → [ A ^ δ ] ⊢ [ A ^ pos ]) (sym eq-γ0-δ) (Ax {A = A} {s = δ})
  ax-subst' : [ A ^ (β ∘ singleton-pos 1) ] ⊢ [ A ^ (γ ∘ singleton-pos 0) ]
  ax-subst' = subst (λ pos → [ A ^ pos ] ⊢ [ A ^ (γ ∘ singleton-pos 0) ]) (sym eq-β1-δ) ax-subst

geachAxiom : [] ⊢ [ (♢ (□ A) ⇒ □ (♢ A)) ^ ∅ ]
geachAxiom {A} = let open G A in
  ⊢⇒ {Γ = []} {s = α} {Δ = []}
    (♢⊢ {x = 0} fresh-α-0 (TokenFresh-[] {x = 0}) fresh-Δ-♢⊢
      (⊢□ {x = 1} fresh-α-1 fresh-Γ-⊢□ (TokenFresh-[] {x = 1})
        (⊢♢ {t = singleton-pos 0}
          (□⊢ {Γ = []} {s = β} {t = singleton-pos 1} ax-subst'))))

private module N (A : Formula) (pA : [] ⊢ [ A ^ ∅ ]) where
  xN = suc (maxEigenposToken pA)
  tN = singleton-pos xN
  ncN = NoEigenposInt-singleton-fresh xN pA (suc-≤-suc ≤-refl)
  liftedN = lift-proof tN pA ncN
  fresh-∅N : xN ∉Pos ∅
  fresh-∅N = λ ()

closureNec : [] ⊢ [ A ^ ∅ ]
           → [] ⊢ [ (□ A) ^ ∅ ]
closureNec {A} pA = let open N A pA in
  ⊢□ {x = xN}
    fresh-∅N
    (TokenFresh-[] {x = xN})
    (TokenFresh-[] {x = xN})
    liftedN

closureMP : [] ⊢ [ A ^ ∅ ]
          → [] ⊢ [ (A ⇒ B) ^ ∅ ]
          → [] ⊢ [ B ^ ∅ ]
closureMP pA pA⇒B =
  Cut pA⇒B (⇒⊢ {Γ₁ = []} Ax pA)
