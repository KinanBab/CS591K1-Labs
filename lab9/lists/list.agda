module list where

open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Int
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import Data.Bool.Base using (if_then_else_)

-- data definitions
data NatList : Set where
  Nil : NatList
  Cons : Nat → NatList → NatList

data List (A : Set) : Set where  -- polymorphic list
  Nil : List A
  Cons : A → List A → List A

data NatVector : Nat → Set where  -- list with length
  Nil : NatVector 0
  Cons : {n : Nat} → Nat → NatVector n → NatVector (suc n)

infix 5 _::_
data Vector (A : Set) : Nat → Set where  -- polymorphic with length
  [] : Vector A 0
  _::_ : {n : Nat} → A → Vector A n → Vector A (suc n)


-- lemmas: proving that addition is commutative
x+0 : (x : Nat) → (x + 0) ≡ x
x+0 0 = refl
x+0 (suc x) rewrite x+0 x = refl

comm' : (x y : Nat) → (x + suc y) ≡ suc (x + y)
comm' 0 y = refl
comm' (suc x) y rewrite comm' x y = refl

comm : (x y : Nat) → (x + y) ≡ (y + x)
comm 0 y rewrite x+0 y = refl
comm (suc x) y rewrite comm' y x | comm x y = refl


-- function implementation
infix 5 _++_
_++_ : {A : Set} → {n1 n2 : Nat} → Vector A n1 → Vector A n2 → (Vector A (n1 + n2))
_++_ [] l = l
_++_ (x :: l) l2 = x :: (l ++ l2)

rev : {A : Set} → {n : Nat} → Vector A n → Vector A n
rev [] = []
rev (x :: l) =
  let
    result = (rev l) ++ (x :: [])
  in
    subst (Vector _) (comm _ 1) result

-- Sigma types: function return types as Dependent types
-- A new vector definition: keeps track of the maximum element at the type level (as well as the length)
data MaxNatVector : Nat → Nat → Set where
  MNil : MaxNatVector 0 0  -- max of an empty list is zero (the identity)
  MCons :  {n m : Nat} → (a : Nat) → (MaxNatVector n m) → (MaxNatVector (suc n) (if a < m then m else a))  -- length + 1, max(a, old_max)

my_max : {n m : Nat} → (MaxNatVector n m) → Σ (Nat) (λ r → r ≡ m)
my_max MNil = 0 , refl
my_max (MCons a l) = let
    res = my_max l
    pf = proj₂ res
    m = proj₁ res
  in
    (if a < m then m else a) , (subst (λ r → ((if a < m then m else a) ≡ (if a < r then r else a))) pf refl)

-- some testing
open import IO

test_list = MCons 2 (MCons 3 (MCons 0 (MCons 1 MNil)))
-- Type C-c C-d here, then write test_list and ENTER to check the type of test_list

test_max = proj₁ (my_max test_list)

main = run (putStrLn (primShowInteger (pos test_max)))

