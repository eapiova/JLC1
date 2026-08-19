{-# OPTIONS --cubical --safe #-}

-- A genuinely non-NAT token algebra.  Tokens carry a Boolean tag, and the
-- injective measure
--
--   (n , b) ↦ 2 · n + bit b
--
-- pulls the strict natural-number order back to the token carrier.  Positions
-- are Cubical's strictly descending lists at that pulled-back order.

module S4dot2.TokenAlgebra.Instances.TaggedToken where

open import Cubical.Foundations.Prelude
  using (Type; _≡_; refl; sym; _∙_; cong; subst; isProp)
open import Cubical.Data.Bool
  using (Bool; false; true; true≢false; false≢true)
open import Cubical.Data.Empty as ⊥
  using (⊥)
open import Cubical.Data.List
  using (List; []; _∷_)
open import Cubical.Data.Nat
  using (ℕ; zero; suc; _+_; _·_; isEven; discreteℕ)
open import Cubical.Data.Nat.IsEven
  using (trueIsEven; falseIsEven)
open import Cubical.Data.Nat.Order
  using (_<_; _>_; Trichotomy; _≟_; <-trans; ¬m<m; <→≢; isProp≤)
open import Cubical.Data.Nat.Properties
  using (+-zero; +-comm; inj-+m; inj-sm·)
open import Cubical.Data.Sigma
  using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum as Sum
  using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary
  using (Dec; yes; no; Discrete)
  renaming (¬_ to Type¬)

open import Cubical.HITs.ListedFiniteSet as LFSet
  using (LFSet; _++_; [])
open import Cubical.HITs.ListedFiniteSet.Properties
  using (comm-++; comm-++-[])

open import S4dot2.TokenAlgebra.Interface

Token : Type₀
Token = ℕ × Bool

bit : Bool → ℕ
bit false = 0
bit true  = 1

tagMeasure : Token → ℕ
tagMeasure x = 2 · fst x + bit (snd x)

private
  even-false : ∀ n → isEven (2 · n + 0) ≡ true
  even-false n =
    trueIsEven (2 · n + 0) (n , +-zero (2 · n))

  even-true : ∀ n → isEven (2 · n + 1) ≡ false
  even-true n =
    falseIsEven (2 · n + 1) (n , +-comm (2 · n) 1)

tagMeasure-injective : ∀ x y → tagMeasure x ≡ tagMeasure y → x ≡ y
tagMeasure-injective (n , false) (m , false) p =
  cong (λ k → k , false)
    (inj-sm· {m = 1}
      (sym (+-zero (2 · n)) ∙ p ∙ +-zero (2 · m)))
tagMeasure-injective (n , true) (m , true) p =
  cong (λ k → k , true)
    (inj-sm· {m = 1} (inj-+m p))
tagMeasure-injective (n , false) (m , true) p =
  ⊥.rec
    (true≢false
      (sym (even-false n) ∙ cong isEven p ∙ even-true m))
tagMeasure-injective (n , true) (m , false) p =
  ⊥.rec
    (false≢true
      (sym (even-true n) ∙ cong isEven p ∙ even-false m))

discreteToken : Discrete Token
discreteToken x y with discreteℕ (tagMeasure x) (tagMeasure y)
... | yes p = yes (tagMeasure-injective x y p)
... | no p = no (λ q → p (cong tagMeasure q))

freshAbove : ℕ → Token
freshAbove m = suc m , false

freshAbove-bound : ∀ m → m < tagMeasure (freshAbove m)
freshAbove-bound m =
  suc m ,
  ( cong (suc m +_) (sym (+-zero (suc m)))
  ∙ sym (+-zero (2 · suc m))
  )

_>tag_ : Token → Token → Type₀
x >tag y = tagMeasure x > tagMeasure y

open import Cubical.Data.DescendingList.Strict Token _>tag_
  renaming (SDL to Position; [] to ∅; cons to pos-cons)

import Cubical.Data.DescendingList.Strict.Properties as SDLPropsModule
module SDLProps = SDLPropsModule Token _>tag_

open SDLProps using (Tri; tri-<; tri-≡; tri->)

>tag-isProp : ∀ {x y} → isProp (x >tag y)
>tag-isProp = isProp≤

>tag-trans : ∀ {x y z} → x >tag y → y >tag z → x >tag z
>tag-trans x>y y>z = <-trans y>z x>y

>tag-irreflexive : ∀ {x} → (x >tag x → ⊥)
>tag-irreflexive x>x = ¬m<m x>x

triTag : ∀ x y → Tri (y >tag x) (x ≡ y) (x >tag y)
triTag x y with tagMeasure x ≟ tagMeasure y
... | Trichotomy.lt x<y =
  tri-< x<y
    (λ x≡y → <→≢ x<y (cong tagMeasure x≡y))
    (λ y<x → ¬m<m (<-trans x<y y<x))
... | Trichotomy.eq mx≡my =
  tri-≡
    (λ x<y → <→≢ x<y mx≡my)
    (tagMeasure-injective x y mx≡my)
    (λ y<x → <→≢ y<x (sym mx≡my))
... | Trichotomy.gt y<x =
  tri->
    (λ x<y → ¬m<m (<-trans y<x x<y))
    (λ x≡y → <→≢ y<x (sym (cong tagMeasure x≡y)))
    y<x

unsortTokens : Position → LFSet Token
unsortTokens = SDLProps.unsort

open SDLProps.IsoToLFSet
  discreteToken
  (λ {x} {y} → >tag-isProp {x} {y})
  triTag
  (λ {x} {y} {z} → >tag-trans {x} {y} {z})
  (λ {x} → >tag-irreflexive {x})
  renaming
    ( insert to insertToken
    ; insert-swap to insertToken-swap
    ; insert-dup to insertToken-dup
    ; unsort-inj to position-inj
    ; SDL-isSet to Position-isSet
    )

-- ---------------------------------------------------------------------------
-- Position operations and direct membership
-- ---------------------------------------------------------------------------

sing : Token → Position
sing x = pos-cons x ∅ >ᴴ[]

_∈Pos_ : Token → Position → Type₀
x ∈Pos ∅ = ⊥.⊥
x ∈Pos (pos-cons y ys _) = (x ≡ y) ⊎ (x ∈Pos ys)

_∉Pos_ : Token → Position → Type₀
x ∉Pos s = Type¬ (x ∈Pos s)

_∈Pos?_ : (x : Token) → (s : Position) → Dec (x ∈Pos s)
x ∈Pos? ∅ = no (λ ())
x ∈Pos? (pos-cons y ys _) with discreteToken x y
... | yes x≡y = yes (inl x≡y)
... | no x≢y with x ∈Pos? ys
...   | yes x∈ys = yes (inr x∈ys)
...   | no x∉ys =
  no λ { (inl x≡y) → x≢y x≡y ; (inr x∈ys) → x∉ys x∈ys }

merge : Position → Position → Position
merge ∅ t = t
merge (pos-cons x xs _) t = insertToken x (merge xs t)

unsort-merge : ∀ s t
  → unsortTokens (merge s t)
    ≡ unsortTokens s LFSet.++ unsortTokens t
unsort-merge ∅ t = refl
unsort-merge (pos-cons x xs x>xs) t =
  insert-correct x (merge xs t)
  ∙ cong (x LFSet.∷_) (unsort-merge xs t)

merge-comm : ∀ s t → merge s t ≡ merge t s
merge-comm s t =
  position-inj (merge s t) (merge t s)
    ( unsort-merge s t
    ∙ comm-++ (unsortTokens s) (unsortTokens t)
    ∙ sym (unsort-merge t s)
    )

remove : Token → Position → Position
remove x ∅ = ∅
remove x (pos-cons y ys _) with discreteToken x y
... | yes _ = ys
... | no _ = insertToken y (remove x ys)

unsort-remove-not-in : ∀ x s → x ∉Pos s
  → unsortTokens (remove x s) ≡ unsortTokens s
unsort-remove-not-in x ∅ x∉s = refl
unsort-remove-not-in x (pos-cons y ys y>ys) x∉s
  with discreteToken x y
... | yes x≡y = ⊥.rec (x∉s (inl x≡y))
... | no x≢y =
  insert-correct y (remove x ys)
  ∙ cong (y LFSet.∷_)
      (unsort-remove-not-in x ys (λ x∈ys → x∉s (inr x∈ys)))

remove-∉Pos-id : ∀ x s → x ∉Pos s → remove x s ≡ s
remove-∉Pos-id x s x∉s =
  position-inj (remove x s) s (unsort-remove-not-in x s x∉s)

-- Membership in insertion is exactly old membership or equality with the
-- inserted token.  The proof follows the three branches of SDL insertion.
∈Pos-insertToken : ∀ x y s → y ∈Pos insertToken x s
  → (y ≡ x) ⊎ (y ∈Pos s)
∈Pos-insertToken x y ∅ mem with triTag x x
... | tri-≡ _ _ _ with mem
...   | inl y≡x = inl y≡x
∈Pos-insertToken x y ∅ mem | tri-< x>x _ _ =
  ⊥.rec (>tag-irreflexive {x = x} x>x)
∈Pos-insertToken x y ∅ mem | tri-> _ _ x>x =
  ⊥.rec (>tag-irreflexive {x = x} x>x)
∈Pos-insertToken x y (pos-cons z zs z>zs) mem with triTag x z
... | tri-< z>x _ _ with mem
...   | inl y≡z = inr (inl y≡z)
...   | inr y∈insert with ∈Pos-insertToken x y zs y∈insert
...     | inl y≡x = inl y≡x
...     | inr y∈zs = inr (inr y∈zs)
∈Pos-insertToken x y (pos-cons z zs z>zs) mem
  | tri-≡ _ x≡z _ with mem
...   | inl y≡z = inl (y≡z ∙ sym x≡z)
...   | inr y∈zs = inr (inr y∈zs)
∈Pos-insertToken x y (pos-cons z zs z>zs) mem
  | tri-> _ _ x>z with mem
...   | inl y≡x = inl y≡x
...   | inr (inl y≡z) = inr (inl y≡z)
...   | inr (inr y∈zs) = inr (inr y∈zs)

insertToken-∈Pos : ∀ x y s → (y ≡ x) ⊎ (y ∈Pos s)
  → y ∈Pos insertToken x s
insertToken-∈Pos x y ∅ (inl y≡x) with triTag x x
... | tri-≡ _ _ _ = inl y≡x
... | tri-< x>x _ _ = ⊥.rec (>tag-irreflexive {x = x} x>x)
... | tri-> _ _ x>x = ⊥.rec (>tag-irreflexive {x = x} x>x)
insertToken-∈Pos x y ∅ (inr ())
insertToken-∈Pos x y (pos-cons z zs z>zs) choice with triTag x z
insertToken-∈Pos x y (pos-cons z zs z>zs) (inl y≡x)
  | tri-< z>x _ _ = inr (insertToken-∈Pos x y zs (inl y≡x))
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inl y≡z))
  | tri-< z>x _ _ = inl y≡z
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inr y∈zs))
  | tri-< z>x _ _ = inr (insertToken-∈Pos x y zs (inr y∈zs))
insertToken-∈Pos x y (pos-cons z zs z>zs) (inl y≡x)
  | tri-≡ _ x≡z _ = inl (y≡x ∙ x≡z)
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inl y≡z))
  | tri-≡ _ x≡z _ = inl y≡z
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inr y∈zs))
  | tri-≡ _ x≡z _ = inr y∈zs
insertToken-∈Pos x y (pos-cons z zs z>zs) (inl y≡x)
  | tri-> _ _ x>z = inl y≡x
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inl y≡z))
  | tri-> _ _ x>z = inr (inl y≡z)
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inr y∈zs))
  | tri-> _ _ x>z = inr (inr y∈zs)

head-∉Pos-tail : ∀ y ys → (y>ys : y >ᴴ ys) → y ∉Pos ys
head-∉Pos-tail y ∅ _ ()
head-∉Pos-tail y (pos-cons z zs z>zs) (>ᴴcons y>z) (inl y≡z) =
  >tag-irreflexive {x = y} (subst (y >tag_) (sym y≡z) y>z)
head-∉Pos-tail y (pos-cons z zs z>zs) (>ᴴcons y>z) (inr y∈zs) =
  head-∉Pos-tail y zs (>ᴴ-trans y z zs y>z z>zs) y∈zs

remove-∈Pos : ∀ x t s → t ∈Pos remove x s → t ∈Pos s
remove-∈Pos x t ∅ ()
remove-∈Pos x t (pos-cons y ys y>ys) t∈rem
  with discreteToken x y
... | yes x≡y = inr t∈rem
... | no x≢y with ∈Pos-insertToken y t (remove x ys) t∈rem
...   | inl t≡y = inl t≡y
...   | inr t∈remys = inr (remove-∈Pos x t ys t∈remys)

remove-∈Pos-neq : ∀ x t s → t ∈Pos remove x s → Type¬ (x ≡ t)
remove-∈Pos-neq x t ∅ () _
remove-∈Pos-neq x t (pos-cons y ys y>ys) t∈rem x≡t
  with discreteToken x y
... | yes x≡y =
  head-∉Pos-tail y ys y>ys
    (subst (_∈Pos ys) (sym x≡t ∙ x≡y) t∈rem)
... | no x≢y with ∈Pos-insertToken y t (remove x ys) t∈rem
...   | inl t≡y = x≢y (x≡t ∙ t≡y)
...   | inr t∈remys = remove-∈Pos-neq x t ys t∈remys x≡t

∈Pos-remove : ∀ x t s → t ∈Pos s → Type¬ (x ≡ t)
  → t ∈Pos remove x s
∈Pos-remove x t ∅ () _
∈Pos-remove x t (pos-cons y ys y>ys) (inl t≡y) x≢t
  with discreteToken x y
... | yes x≡y = ⊥.rec (x≢t (x≡y ∙ sym t≡y))
... | no x≢y = insertToken-∈Pos y t (remove x ys) (inl t≡y)
∈Pos-remove x t (pos-cons y ys y>ys) (inr t∈ys) x≢t
  with discreteToken x y
... | yes x≡y = t∈ys
... | no x≢y =
  insertToken-∈Pos y t (remove x ys)
    (inr (∈Pos-remove x t ys t∈ys x≢t))

∈Pos-merge : ∀ x s t → x ∈Pos merge s t
  → (x ∈Pos s) ⊎ (x ∈Pos t)
∈Pos-merge x ∅ t mem = inr mem
∈Pos-merge x (pos-cons y ys y>ys) t mem
  with ∈Pos-insertToken y x (merge ys t) mem
... | inl x≡y = inl (inl x≡y)
... | inr x∈merge with ∈Pos-merge x ys t x∈merge
...   | inl x∈ys = inl (inr x∈ys)
...   | inr x∈t = inr x∈t

merge-∈Pos-l : ∀ x s t → x ∈Pos s → x ∈Pos merge s t
merge-∈Pos-l x (pos-cons y ys y>ys) t (inl x≡y) =
  insertToken-∈Pos y x (merge ys t) (inl x≡y)
merge-∈Pos-l x (pos-cons y ys y>ys) t (inr x∈ys) =
  insertToken-∈Pos y x (merge ys t)
    (inr (merge-∈Pos-l x ys t x∈ys))

merge-∈Pos-r : ∀ x s t → x ∈Pos t → x ∈Pos merge s t
merge-∈Pos-r x ∅ t mem = mem
merge-∈Pos-r x (pos-cons y ys y>ys) t mem =
  insertToken-∈Pos y x (merge ys t)
    (inr (merge-∈Pos-r x ys t mem))

merge-∅-r : ∀ s → merge s ∅ ≡ s
merge-∅-r ∅ = refl
merge-∅-r s@(pos-cons x xs x>xs) =
  position-inj (merge s ∅) s
    ( unsort-merge s ∅
    ∙ comm-++-[] (unsortTokens s)
    )

merge-assoc : ∀ s t r → merge (merge s t) r ≡ merge s (merge t r)
merge-assoc s t r =
  position-inj (merge (merge s t) r) (merge s (merge t r))
    ( unsort-merge (merge s t) r
    ∙ cong (LFSet._++ unsortTokens r) (unsort-merge s t)
    ∙ sym (LFSet.assoc-++ (unsortTokens s) (unsortTokens t)
                          (unsortTokens r))
    ∙ cong (unsortTokens s LFSet.++_) (sym (unsort-merge t r))
    ∙ sym (unsort-merge s (merge t r))
    )

merge-idem : ∀ s → merge s s ≡ s
merge-idem s =
  position-inj (merge s s) s
    (unsort-merge s s ∙ LFSet.idem-++ (unsortTokens s))

merge-singleton : ∀ s x → merge s (sing x) ≡ insertToken x s
merge-singleton s x =
  position-inj (merge s (sing x)) (insertToken x s)
    ( unsort-merge s (sing x)
    ∙ cong (unsortTokens s LFSet.++_) (insert-correct x ∅)
    ∙ comm-++ (unsortTokens s) (x LFSet.∷ LFSet.[])
    ∙ sym (insert-correct x s)
    )

toList : Position → List Token
toList ∅ = []
toList (pos-cons x xs _) = x ∷ toList xs

∈Pos→∈L : ∀ x s → x ∈Pos s → x ∈L toList s
∈Pos→∈L x (pos-cons y ys _) (inl x≡y) =
  subst (λ z → z ∈L (y ∷ toList ys)) (sym x≡y) hereL
∈Pos→∈L x (pos-cons y ys _) (inr x∈ys) =
  thereL (∈Pos→∈L x ys x∈ys)

∈L→∈Pos : ∀ x s → x ∈L toList s → x ∈Pos s
∈L→∈Pos x (pos-cons y ys _) hereL = inl refl
∈L→∈Pos x (pos-cons y ys _) (thereL m) =
  inr (∈L→∈Pos x ys m)

private
  ∈→dup : ∀ x s → x ∈Pos s
    → x LFSet.∷ unsortTokens s ≡ unsortTokens s
  ∈→dup x ∅ ()
  ∈→dup x (pos-cons y ys y>ys) (inl x≡y) =
    cong (λ z → z LFSet.∷ (y LFSet.∷ unsortTokens ys)) x≡y
    ∙ LFSet.dup y (unsortTokens ys)
  ∈→dup x (pos-cons y ys y>ys) (inr x∈ys) =
    LFSet.comm x y (unsortTokens ys)
    ∙ cong (y LFSet.∷_) (∈→dup x ys x∈ys)

insertToken-∈Pos-id : ∀ x s → x ∈Pos s → insertToken x s ≡ s
insertToken-∈Pos-id x s x∈s =
  position-inj (insertToken x s) s
    (insert-correct x s ∙ ∈→dup x s x∈s)

_⊑_ : Position → Position → Type₀
s ⊑ t = ∀ x → x ∈Pos s → x ∈Pos t

merge-absorb-⊑ : ∀ s t → s ⊑ t → merge s t ≡ t
merge-absorb-⊑ ∅ t s⊑t = refl
merge-absorb-⊑ (pos-cons x xs x>xs) t s⊑t =
  cong (insertToken x)
    (merge-absorb-⊑ xs t (λ y y∈xs → s⊑t y (inr y∈xs)))
  ∙ insertToken-∈Pos-id x t (s⊑t x (inl refl))

posExt : ∀ s t
  → (∀ x → x ∈Pos s → x ∈Pos t)
  → (∀ x → x ∈Pos t → x ∈Pos s)
  → s ≡ t
posExt s t s⊑t t⊑s =
  sym (merge-absorb-⊑ t s t⊑s)
  ∙ merge-comm t s
  ∙ merge-absorb-⊑ s t s⊑t

remove-merge-distrib : ∀ x s t
  → remove x (merge s t) ≡ merge (remove x s) (remove x t)
remove-merge-distrib x s t =
  posExt (remove x (merge s t)) (merge (remove x s) (remove x t))
    fwd bwd
  where
  fwd : ∀ y → y ∈Pos remove x (merge s t)
    → y ∈Pos merge (remove x s) (remove x t)
  fwd y y∈rem =
    Sum.rec
      (λ y∈s → merge-∈Pos-l y (remove x s) (remove x t)
        (∈Pos-remove x y s y∈s
          (remove-∈Pos-neq x y (merge s t) y∈rem)))
      (λ y∈t → merge-∈Pos-r y (remove x s) (remove x t)
        (∈Pos-remove x y t y∈t
          (remove-∈Pos-neq x y (merge s t) y∈rem)))
      (∈Pos-merge y s t (remove-∈Pos x y (merge s t) y∈rem))

  bwd : ∀ y → y ∈Pos merge (remove x s) (remove x t)
    → y ∈Pos remove x (merge s t)
  bwd y y∈merge =
    Sum.rec
      (λ y∈rem-s → ∈Pos-remove x y (merge s t)
        (merge-∈Pos-l y s t (remove-∈Pos x y s y∈rem-s))
        (remove-∈Pos-neq x y s y∈rem-s))
      (λ y∈rem-t → ∈Pos-remove x y (merge s t)
        (merge-∈Pos-r y s t (remove-∈Pos x y t y∈rem-t))
        (remove-∈Pos-neq x y t y∈rem-t))
      (∈Pos-merge y (remove x s) (remove x t) y∈merge)

insertToken-remove-cancel' : ∀ x s → x ∈Pos s
  → insertToken x (remove x s) ≡ s
insertToken-remove-cancel' x s x∈s =
  posExt (insertToken x (remove x s)) s fwd bwd
  where
  fwd : ∀ y → y ∈Pos insertToken x (remove x s) → y ∈Pos s
  fwd y y∈insert =
    Sum.rec
      (λ y≡x → subst (_∈Pos s) (sym y≡x) x∈s)
      (remove-∈Pos x y s)
      (∈Pos-insertToken x y (remove x s) y∈insert)

  bwd : ∀ y → y ∈Pos s → y ∈Pos insertToken x (remove x s)
  bwd y y∈s with discreteToken x y
  ... | yes x≡y =
    insertToken-∈Pos x y (remove x s) (inl (sym x≡y))
  ... | no x≢y =
    insertToken-∈Pos x y (remove x s)
      (inr (∈Pos-remove x y s y∈s x≢y))

import Cubical.Data.DescendingList.Properties as DLPropsModule
module DLProps = DLPropsModule Token _>tag_
module PositionDiscrete = DLProps.isSetDL
  (λ {x} {y} → >tag-isProp {x} {y}) discreteToken

discretePosition : Discrete Position
discretePosition = PositionDiscrete.discreteDL

taggedToken : TokenAlgebra
TokenAlgebra.Token taggedToken = Token
TokenAlgebra.Pos taggedToken = Position
TokenAlgebra.discreteToken taggedToken = discreteToken
TokenAlgebra.discretePos taggedToken = discretePosition
TokenAlgebra.ε taggedToken = ∅
TokenAlgebra.sing taggedToken = sing
TokenAlgebra._∪_ taggedToken = merge
TokenAlgebra.insert taggedToken = insertToken
TokenAlgebra.remove taggedToken = remove
TokenAlgebra._∈ᵖ_ taggedToken = _∈Pos_
TokenAlgebra._∈ᵖ?_ taggedToken = _∈Pos?_
TokenAlgebra.∪-assoc taggedToken = merge-assoc
TokenAlgebra.∪-comm taggedToken = merge-comm
TokenAlgebra.∪-idr taggedToken = merge-∅-r
TokenAlgebra.∪-idem taggedToken = merge-idem
TokenAlgebra.∈∪-elim taggedToken = ∈Pos-merge
TokenAlgebra.∈∪-introˡ taggedToken = merge-∈Pos-l
TokenAlgebra.∈∪-introʳ taggedToken = merge-∈Pos-r
TokenAlgebra.∈sing-elim taggedToken =
  λ x y → λ { (inl e) → e ; (inr ()) }
TokenAlgebra.∈sing-intro taggedToken = λ x → inl refl
TokenAlgebra.¬∈ε taggedToken = λ x p → p
TokenAlgebra.insert-∪-sing taggedToken = merge-singleton
TokenAlgebra.remove-∈-elim taggedToken =
  λ x y s → remove-∈Pos y x s
TokenAlgebra.remove-∈-neq taggedToken =
  λ x y s → remove-∈Pos-neq y x s
TokenAlgebra.∈-remove-intro taggedToken =
  λ x y s → ∈Pos-remove y x s
TokenAlgebra.remove-∉-id taggedToken = remove-∉Pos-id
TokenAlgebra.remove-∪-distr taggedToken = remove-merge-distrib
TokenAlgebra.remove-insert-cancel taggedToken =
  insertToken-remove-cancel'
TokenAlgebra.posExt taggedToken = posExt
TokenAlgebra.toList taggedToken = toList
TokenAlgebra.∈→toList taggedToken = ∈Pos→∈L
TokenAlgebra.toList→∈ taggedToken = ∈L→∈Pos
TokenAlgebra.tokℕ taggedToken = tagMeasure
TokenAlgebra.freshAbove taggedToken = freshAbove
TokenAlgebra.freshAbove-bound taggedToken = freshAbove-bound
