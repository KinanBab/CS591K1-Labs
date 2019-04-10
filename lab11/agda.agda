module agda where

open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Int
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import Data.Bool.Base using (if_then_else_)

--lemmas
x+0 : (x : Nat) → (x + 0) ≡ x
x+0 0 = refl
x+0 (suc x) rewrite x+0 x = refl

commute' : (x y : Nat) → suc (x + y) ≡ (x + suc y)
commute' zero y = refl
commute' (suc x) y rewrite commute' x y = refl

+comm : (x y : Nat) → x + y ≡ y + x
+comm zero y rewrite x+0 y = refl
+comm (suc x) y rewrite +comm x y = commute' y x

+comm3 : (x y z : Nat) → x + y + z ≡ x + z + y
+comm3 zero y z rewrite +comm y z = refl
+comm3 (suc x) y z rewrite +comm3 x y z = refl

+assoc : (x y z : Nat) → x + (y + z) ≡ x + y + z
+assoc 0 y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

suc+1 : (x : Nat) → suc x ≡ x + 1
suc+1 0 = refl
suc+1 (suc x) rewrite suc+1 x = refl

+assoc2 : (k1 k2 : Nat) → k1 + k1 + (k2 + k2 + 1) ≡ k1 + k2 + (k1 + k2) + 1
+assoc2 k1 k2 rewrite +assoc (k1 + k1) (k2 + k2) 1 | +assoc (k1 + k1) k2 k2 | +assoc (k1 + k2) k1 k2 | +comm3 k1 k1 k2  = refl

-- main theorem: adding two even numbers produce an even number
even_odd : (e o k1 k2 : Nat) → e ≡ 2 * k1 → o ≡ 2 * k2 + 1 → e + o ≡ 2 * (k1 + k2) + 1
even_odd e o k1 k2 pf1 pf2 rewrite pf1 | pf2 | x+0 k1 | x+0 k2 | x+0 (k1 + k2) = +assoc2 k1 k2

