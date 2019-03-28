module Problem2 where

open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

-- Problem 1 [25 points] : Proofs in Agda


-- Part A [5 points] : Define a function that sums all numbers
--                    up to a given n (e.g. 0 + 1 + 2 + ... + n)
-- Call your function 'sumto'





-- Part B [20 points] : Prove the following lemma
-- You will likely need several helper lemmas proving commutativity and associativity of addition and multipliation
-- Look at Agda's standard library to find some of these lemmas out of the box, or prove them yourself!


-- sum_to_lemma : (n : Nat) → 2 * (sumto n) ≡ n * (suc n)


-- Bonus [10 points] : Part C define a variant of sumto that asserts the above lemma using a Sigma type.
