module agda2 where

open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Int
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import Data.Bool.Base using (if_then_else_)

data Even : Nat → Set where
  evenZero : Even 0
  evenSuc : {n : Nat} → Even n → Even (suc (suc n))

data Odd : Nat → Set where
  oddOne : Odd 1
  oddSuc : {n : Nat} → Odd n → Odd (suc (suc n))

evenOdd : {e o : Nat} → Even e → Odd o → Odd (e + o)
evenOdd evenZero oddOne = oddOne
evenOdd evenZero (oddSuc O) = oddSuc O
evenOdd (evenSuc E) O = oddSuc (evenOdd E O)
