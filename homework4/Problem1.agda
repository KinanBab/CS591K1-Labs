module Problem1 where

open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

-- Problem 1 : Ordered lists and merge [30 points]

-- Part A [5 points] : Define two polymorphic types in the style of lab 9:
--                     one for list and one for vector (with and without length)
-- Call your definitions 'List' and 'Vector'




-- Part B [10 points] : Define two length functions: one over lists and one over vectors
--                      Make sure the types are accurate for the vector case, you
--                      will need to use subst in the proof.
-- Call your functions 'llength' and 'vlength'
-- Hint: Look at lab 9




-- Part C [5 points] : Implement the following function

-- vmap : {A B : Set} → {n : Nat} → (A → B) → Vector A n → Vector B n



-- Part D [10 points] : Implement the following function and prove the lemma

-- lmap : {A B : Set} → (A → B) → List A → List B

-- lemma : {A B : Set} → (f : A → B) → (l : List A) → (llength l ≡ llength (lmap f l))




-- Bonus : Part E [10 points] : Sigma type: define and implement an alternative to lmap,
--                      that express the lemma as part of the function signature
--                      using a sigma type.
--                      In other words, define a function that guarantees that the
--                      length is perserved at the type level, without
--                      need for an external lemma
-- Hint: for proving the inductive case, look at cong!
