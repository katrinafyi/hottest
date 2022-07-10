{-# OPTIONS --without-K --safe #-}

open import general-notation

data Bool : Type where
  true false : Bool

not : Bool → Bool
not true = false
not false = true


id : (X : Type) → X → X
id X x = x

example : {P Q : Type} → P → (Q → P)
example {P} {Q} p = f
  where
    f : Q → P
    f _ = p

open import binary-products

ex : {P Q : Type} → P × Q → Q × P
ex (p , q) = (q , p)

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

three : ℕ
three = suc (suc (suc zero))

{-# BUILTIN NATURAL ℕ #-}

three' : ℕ
three' = 3

D : Bool → Type
D true = ℕ
D false = Bool

if_then_else_ : {X : Type} → Bool → X → X → X
if true then x else y = x
if false then x else y = y

if[_]_then_else_ : (X : Bool → Type)
  → (b : Bool)
  → X true
  → X false
  → X b
if[ X ] true then x else y = x
if[ X ] false then x else y = y

unfamiliar : (b : Bool) → D b
unfamiliar b = if[ D ] b then 3 else false

-- dependent functions like the dependent if correponds to elimination
-- rules from type theory.

data List (A : Type) : Type where
  [] : List A
  _::_ : A → List A → List A

infixr 10 _::_

list₀ : List ℕ
list₀ = 0 :: 1 :: 2 :: []


length : {A : Type} → List A → ℕ
length [] = zero
length (x :: xs) = suc (length xs)

-- induction for ℕ, the only recursive rule allowed in Martin-Lof TT.
ℕ-elim : {A : ℕ → Type}
  → A 0
  → ((k : ℕ) → A k → A (suc k))
  → (n : ℕ) → A n
ℕ-elim {A} a₀ f n = h n
  where
    h : (n : ℕ) → A n
    h zero = a₀
    h (suc n) = f n (h n)


ℕ-elim' : {A : ℕ → Type}
  → A 0
  → ((k : ℕ) → A k → A (suc k))
  → (n : ℕ) → A n
ℕ-elim' {A} a₀ f zero = a₀
ℕ-elim' {A} a₀ f (suc n) = f n (ℕ-elim' a₀ f n)

List-elim : {X : Type} (A : List X → Type)
  → A []
  → ((x : X) (xs : List X) → A xs → A (x :: xs))
  → (xs : List X) → A xs
List-elim {X} A a0 f [] = a0
List-elim {X} A a0 f (x :: xs) = f x xs (List-elim A a0 f xs)


_≣_ : ℕ → ℕ → Type
X ≣ Y = {!!}
