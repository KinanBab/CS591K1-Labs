module Problem1 where

open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

-- Problem 1 : Ordered lists and merge [30 points]

-- Part A [5 points] : Define two polymorphic types in the style of lab 9:
--                     one for list and one for vector (with and without length)
-- Call your definitions 'List' and 'Vector'

data List (A : Set) : Set where
  LNil : List A
  LCons : A → List A → List A

data Vector (A : Set) : Nat → Set where
  VNil : Vector A 0
  VCons : {n : Nat} → A → Vector A n → Vector A (suc n)


-- Part B [10 points] : Define two length functions: one over lists and one over vectors
--                      Make sure the types are accurate for the vector case, you
--                      will need to use subst in the proof.
-- Call your functions 'llength' and 'vlength'
-- Hint: Look at lab 9

llength : {A : Set} → List A → Nat
llength LNil = 0
llength (LCons _ l) = suc (llength l)

vlength : {A : Set} → {n : Nat} → Vector A n → Σ Nat (λ r → r ≡ n)
vlength VNil = 0 , refl
vlength (VCons _ l) = let
    res = vlength l
    ln = proj₁ res
    pf = proj₂ res
  in
      suc ln , subst (λ r → suc (proj₁ (vlength l)) ≡ suc r) pf refl


-- Part C [5 points] : Implement the following function

vmap : {A B : Set} → {n : Nat} → (A → B) → Vector A n → Vector B n
vmap F VNil = VNil
vmap F (VCons x l) = VCons (F x) (vmap F l)


-- Part D [10 points] : Implement the following function and prove the lemma

lmap : {A B : Set} → (A → B) → List A → List B
lmap F LNil = LNil
lmap F (LCons x l) = LCons (F x) (lmap F l)

lemma : {A B : Set} → (f : A → B) → (l : List A) → (llength l ≡ llength (lmap f l))
lemma F LNil = refl
lemma F (LCons x l) rewrite lemma F l = refl


-- Bonus : Part E [10 points] : Sigma type: define and implement an alternative to lmap,
--                      that express the lemma as part of the function signature
--                      using a sigma type.
--                      In other words, define a function that guarantees that the
--                      length is perserved at the type level, without
--                      need for an external lemma
-- Hint: for proving the inductive case, look at cong!
smap : {A B : Set} → (A → B) → (l : List A) → Σ (List B) (λ r → llength r ≡ llength l)
smap F LNil = LNil , refl
smap F (LCons x l) = let
    res = smap F l
    m = proj₁ res
    pf = proj₂ res
  in
    LCons (F x) m , cong (suc) pf
