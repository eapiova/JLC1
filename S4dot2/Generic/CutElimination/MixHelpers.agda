{-# OPTIONS --cubical --safe #-}

-- Generic (token-algebra-parameterized) part of the Mix helper layer
-- (Phase 4 of the token-algebra parameterization).  Bodies ported
-- byte-identically from S4dot2/CutElimination/MixHelpers.agda:60-146
-- (subset-needs-token, mkSingleTokenExt, TokenFresh→IsEigenposition,
-- eigenpos-extend-cross); the only real edits are the imports (facade
-- opens replaced by the Generic/PositionCompat opens) and the private
-- copies of case_of_ / mem-++-split (today sourced from CutElimination
-- Defs via Base, which stays NAT-bound until Phase 5).  The removeAll /
-- context-rearrangement / degree lemmas stay in the facade: they consume
-- the Base/Defs measure layer.

open import S4dot2.TokenAlgebra.Interface

module S4dot2.Generic.CutElimination.MixHelpers (TA : TokenAlgebra) where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; cong; subst; _∙_)
open import Agda.Primitive using (Level)
open import Cubical.Data.Empty renaming (rec to emptyRec) using (⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List using (List; _∷_; []; _++_)
open import Cubical.Data.List.Properties using (++-unit-r)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (Dec; yes; no) renaming (¬_ to Neg)
open import Cubical.Data.Unit using (Unit; tt)

open import S4dot2.Generic.Syntax TA hiding (_⊢_; _≢_)
open import S4dot2.Generic.System TA
open import S4dot2.ListExt hiding (_⊑_)
open import S4dot2.Generic.CutElimination.PositionCompat TA
  using (∅; insertToken-∈Pos; ∈Pos-insertToken; merge-∈Pos-l; merge-∈Pos-r)
open TokenAlgebra TA using (∈sing-intro)

private
  -- today: CutElimination.Defs.case_of_ (via Base)
  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x

  -- today: CutElimination.Defs.mem-++-split (via Base)
  mem-++-split : ∀ {ℓ} {A : Type ℓ} {x : A} {xs ys : List A} → x ∈ xs ++ ys → (x ∈ xs) ⊎ (x ∈ ys)
  mem-++-split {xs = []} p = inr p
  mem-++-split {xs = y ∷ xs} here = inl here
  mem-++-split {xs = y ∷ xs} (there p) with mem-++-split p
  ... | inl p' = inl (there p')
  ... | inr p' = inr p'

-- =============================================================================
-- Token/Position Helper Lemmas
-- =============================================================================

-- Key lemma: If x ∉ t and ((s ∘ singleton-pos x) ∘ r) ⊑ t, contradiction
subset-needs-token : ∀ {x : Token} {s r t : Position}
                   → x ∉Pos t
                   → Neg (((s ∘ singleton-pos x) ∘ r) ⊑ t)
subset-needs-token {x} {s} {r} {t} x∉t sub = x∉t (sub x x∈merged)
  where
    -- x is in singleton-pos x (interface field: sing is a separate field
    -- from insert, so the old insertToken-x-∅ route is not definitional)
    x∈singleton : x ∈Pos (singleton-pos x)
    x∈singleton = ∈sing-intro x
    -- x is in s ∘ singleton-pos x (right component of merge)
    x∈s∘singleton : x ∈Pos (s ∘ singleton-pos x)
    x∈s∘singleton = merge-∈Pos-r x s (singleton-pos x) x∈singleton
    -- x is in (s ∘ singleton-pos x) ∘ r (left component of merge)
    x∈merged : x ∈Pos ((s ∘ singleton-pos x) ∘ r)
    x∈merged = merge-∈Pos-l x (s ∘ singleton-pos x) r x∈s∘singleton

-- Helper: Construct IsSingleTokenExt from x ∉Pos s
mkSingleTokenExt : ∀ (s : Position) (x : Token) → x ∉Pos s → IsSingleTokenExt s (insertToken x s) x
mkSingleTokenExt s x x∉s = (sub , x∈extPos , x∉s , unique)
  where
    extPos = insertToken x s
    -- s ⊑ insertToken x s (inserting x preserves existing elements)
    sub : s ⊑ extPos
    sub t t∈s = insertToken-∈Pos x t s (inr t∈s)
    -- x ∈Pos (insertToken x s)
    x∈extPos : x ∈Pos extPos
    x∈extPos = insertToken-∈Pos x x s (inl refl)
    -- Uniqueness: the only element in extPos but not in s is x
    unique : ∀ t → t ∈Pos extPos → t ∉Pos s → t ≡ x
    unique t t∈extPos t∉s with ∈Pos-insertToken x t s t∈extPos
    ... | inl t≡x = t≡x
    ... | inr t∈s = emptyRec (t∉s t∈s)

-- TokenFresh implies IsEigenposition
TokenFresh→IsEigenposition : ∀ {s : Position} {x : Token} {Γ Δ : Ctx}
  → TokenFresh x (Γ ,, Δ)
  → IsEigenposition s x Γ Δ
TokenFresh→IsEigenposition {s} {x} {Γ} {Δ} fresh (pf , pf∈ , sub) =
  let x∈singleton : x ∈Pos (singleton-pos x)
      x∈singleton = ∈sing-intro x
      x∈merged : x ∈Pos (s ∘ singleton-pos x)
      x∈merged = merge-∈Pos-r x s (singleton-pos x) x∈singleton
      x∈pf : x ∈Pos (PFormula.pos pf)
      x∈pf = sub x x∈merged
      x∉pf : x ∉Pos (PFormula.pos pf)
      x∉pf = helper (Γ ++ Δ) pf∈ fresh
  in x∉pf x∈pf
  where
    helper : (ctx : Ctx) → pf ∈ ctx → TokenFresh x ctx → x ∉Pos (PFormula.pos pf)
    helper (qf ∷ ctx) here (freshQf , freshRest) = freshQf
    helper (qf ∷ ctx) (there mem) (freshQf , freshRest) = helper ctx mem freshRest

-- Combine eigenposition from one derivation with token freshness from another
eigenpos-extend-cross : ∀ {s : Position} {x : Token} {Γ Δ Γ' Δ' : Ctx}
  → IsEigenposition s x Γ Δ
  → TokenFresh x (Γ' ,, Δ')
  → IsEigenposition s x (Γ ,, Γ') (Δ ,, Δ')
eigenpos-extend-cross {s} {x} {Γ} {Δ} {Γ'} {Δ'} eigenOrig freshExt inInit =
  case inInit of λ { (pf , pf∈ , pre) →
    split-mem pf pf∈ pre
  }
  where
    split-mem : (pf : PFormula) → pf ∈ ((Γ ++ Γ') ++ (Δ ++ Δ'))
              → (s ∘ singleton-pos x) ⊑ PFormula.pos pf → ⊥
    split-mem pf mem pre with mem-++-split {xs = Γ ++ Γ'} {ys = Δ ++ Δ'} mem
    ... | inl memL with mem-++-split {xs = Γ} {ys = Γ'} memL
    ...   | inl memΓ = eigenOrig (pf , mem-++-l memΓ , pre)
    ...   | inr memΓ' = TokenFresh→IsEigenposition {s = s} {Γ = Γ'} {Δ = []}
                          (subst (TokenFresh x) (sym (++-unit-r Γ')) (TokenFresh-fst Γ' Δ' freshExt))
                          (pf , subst (pf ∈_) (sym (++-unit-r Γ')) memΓ' , pre)
      where
        TokenFresh-fst : (A B : Ctx) → TokenFresh x (A ,, B) → TokenFresh x A
        TokenFresh-fst [] B _ = tt
        TokenFresh-fst (qf ∷ as) B (freshQf , rest) = freshQf , TokenFresh-fst as B rest
    split-mem pf mem pre | inr memR with mem-++-split {xs = Δ} {ys = Δ'} memR
    ...   | inl memΔ = eigenOrig (pf , mem-++-r Γ memΔ , pre)
    ...   | inr memΔ' = TokenFresh→IsEigenposition {s = s} {Γ = Δ'} {Δ = []}
                          (subst (TokenFresh x) (sym (++-unit-r Δ')) (TokenFresh-snd Γ' Δ' freshExt))
                          (pf , subst (pf ∈_) (sym (++-unit-r Δ')) memΔ' , pre)
      where
        TokenFresh-snd : (A B : Ctx) → TokenFresh x (A ,, B) → TokenFresh x B
        TokenFresh-snd [] B freshB = freshB
        TokenFresh-snd (_ ∷ as) B (_ , rest) = TokenFresh-snd as B rest

-- =============================================================================
-- RemoveAll Helper Lemmas (Phase 5 of the token-algebra parameterization:
-- moved from the facade S4dot2/CutElimination/MixHelpers.agda:31-45 — they
-- consume the Base layer, generic since Phase 5; text verbatim)
-- =============================================================================

open import S4dot2.Generic.CutElimination.Base TA
  using (_-_; _≢_; lemma-removeAll-eq; removeAll-++-r-pf-neq; removeAll-yes; removeAll-no)

-- When A ≡ B, removing A from (Γ ++ [B]) gives (Γ - A)
lemma-removeAll-cons-eq : ∀ {A B : PFormula} {Γ : Ctx} → A ≡ B → (Γ ++ [ B ]) - A ≡ Γ - A
lemma-removeAll-cons-eq {A} {B} {Γ} eq = lemma-removeAll-eq {A} {B} {Γ} eq

-- When A ≢ B, removing A from (Γ ++ [B]) gives (Γ - A) ++ [B]
lemma-removeAll-cons-neq : ∀ {A B : PFormula} {Γ : Ctx} → A ≢ B → (Γ ++ [ B ]) - A ≡ (Γ - A) ++ [ B ]
lemma-removeAll-cons-neq {A} {B} {Γ} neq = removeAll-++-r-pf-neq {A} {B} {Γ} neq

-- When A ≡ B, removing A from (B ∷ Γ) gives (Γ - A)
lemma-removeAll-head-eq : ∀ {A B : PFormula} {Γ : Ctx} → A ≡ B → (B ∷ Γ) - A ≡ Γ - A
lemma-removeAll-head-eq {A} {B} {Γ} eq = removeAll-yes A B Γ eq

-- When A ≢ B, removing A from (B ∷ Γ) gives B ∷ (Γ - A)
lemma-removeAll-head-neq : ∀ {A B : PFormula} {Γ : Ctx} → A ≢ B → (B ∷ Γ) - A ≡ B ∷ (Γ - A)
lemma-removeAll-head-neq {A} {B} {Γ} neq = removeAll-no A B Γ neq
