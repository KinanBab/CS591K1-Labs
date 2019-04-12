module Problem2 where

open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

-- Problem 1 [25 points] : Proofs in Agda


-- Part A [5 points] : Define a function that sums all numbers
--                    up to a given n (e.g. 0 + 1 + 2 + ... + n)
-- Call your function 'sumto'
sumto : Nat → Nat
sumto 0 = 0
sumto (suc n) = (suc n) + sumto n


-- Part B [20 points] : Prove the following lemma
-- You will likely need several helper lemmas proving commutativity and associativity of addition and multipliation
-- Look at Agda's standard library to find some of these lemmas out of the box, or prove them yourself!

-- misc
x+0 : (x : Nat) → x + 0 ≡ x
x+0 0 = refl
x+0 (suc x) rewrite x+0 x = refl

suc+1 : (x : Nat) → suc x ≡ x + 1
suc+1 0 = refl
suc+1 (suc x) rewrite suc+1 x = refl

1+suc : (x : Nat) → suc x ≡ 1 + x
1+suc 0 = refl
1+suc (suc x) rewrite 1+suc x = refl

+*2 : (n : Nat) → n + n ≡ 2 * n
+*2 0 = refl
+*2 (suc n) rewrite +*2 n | x+0 n = refl 

-- associativity
+assoc : (x y z : Nat) → x + (y + z) ≡ x + y + z
+assoc 0 y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

assoc+ : (x y z : Nat) → x + y + z ≡ x + (y + z)
assoc+ 0 y z = refl
assoc+ (suc x) y z rewrite +assoc x y z = refl

-- commutativity
commute' : (x y : Nat) → suc (x + y) ≡ (x + suc y)
commute' zero y = refl
commute' (suc x) y rewrite commute' x y = refl

+comm : (x y : Nat) → x + y ≡ y + x
+comm zero y rewrite x+0 y = refl
+comm (suc x) y rewrite +comm x y = commute' y x

-- distributivity
dist1 : (n t : Nat) → n + n * (n + t) ≡ n * (n + t + 1)
dist1 0 t = refl
dist1 (suc n) t rewrite suc+1 n | suc+1 (n + t) | suc+1 (n + t + n * (n + t + 1)) | suc+1 (n + (n + t + n * (n + t + 1) + 1)) |
                        suc+1 (n + t + 1) | suc+1 (n + t + 1 + n * (n + t + 1 + 1)) |
                        +assoc n (n + t + n * (n + t + 1)) 1 | +assoc n (n + t) (n * (n + t + 1)) | +assoc n n t |
                        +comm (n + t) 1 | 1+suc (n + t) | suc+1 (n + t + n * suc (n + t + 1) + 1) |
                        assoc+ n n t | +comm n t | +assoc n t n | +comm t n | suc+1 (n + t + 1) | suc+1 (n + t) |
                        assoc+ (n + t) n (n * (n + t + 1)) | assoc+ n t 1 |
                        dist1 n (t + 1)
                      = refl

-- lemma
helper1 : (n : Nat) → n + sumto n + (n + sumto n + 1) ≡ n + n + (sumto n + sumto n) + 1
helper1 n rewrite  +assoc (n + sumto n) (n + sumto n) 1 | +assoc (n + sumto n) n (sumto n) |
                 assoc+ n (sumto n) n | +comm (sumto n) n | +assoc n n (sumto n) | assoc+ (n + n) (sumto n) (sumto n) = refl


-- main theorem
sum_to_lemma : (n : Nat) → 2 * (sumto n) ≡ n * (suc n)
sum_to_lemma 0 = refl
sum_to_lemma (suc n) rewrite suc+1 (n + sumto n + 0) | x+0 (n + sumto n) |
                             suc+1 (n + sumto n + (n + sumto n + 1)) |
                             suc+1 n | suc+1 (n + 1) | suc+1 (n + n * (n + 1 + 1)) |
                             suc+1 (n + n * (n + 1 + 1) + 1) |
                             helper1 n |
                             +*2 (sumto n) |
                             sum_to_lemma n |
                             suc+1 n | assoc+ n n (n * (n + 1)) |
                             dist1 n 1 = refl

