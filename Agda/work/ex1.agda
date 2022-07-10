{-# OPTIONS --without-K --safe #-}

module ex1 where

open import prelude hiding (not-is-involution)

_&&'_ : Bool → Bool → Bool
true &&' true = true
true &&' false = false
false &&' true = false
false &&' false = false


_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

^-example : 3 ^ 4 ≡ 81
^-example = refl 81 -- refl 81 should fill the hole here

_! : ℕ → ℕ
zero ! = 1
suc n ! = (suc n) * (n !)

!-example : 4 ! ≡ 24
!-example = refl 24 -- refl 24 should fill the hole here


max : ℕ → ℕ → ℕ
max zero    m       = m
max (suc n) zero    = suc n
max (suc n) (suc m) = suc (max n m)

min : ℕ → ℕ → ℕ
min zero m = zero
min (suc n) zero = zero
min (suc n) (suc m) = suc (min n m)

min-example : min 5 3 ≡ 3
min-example = refl 3 -- refl 3 should fill the hole here

map : {X Y : Type} → (X → Y) → List X → List Y
map f [] = []
map f (x :: xs) = f x :: map f xs

map-example : map (_+ 3) (1 :: 2 :: 3 :: []) ≡ 4 :: 5 :: 6 :: []
map-example = refl (4 :: 5 :: 6 :: []) -- refl _ should fill the hole here

                   -- We write the underscore, because we don't wish to repeat
                   -- the relatively long "4 :: 5 :: 6 :: []" and Agda can
                   -- figure out what is supposed to go there.

filter : {X : Type} (p : X → Bool) → List X → List X
filter p [] = []
filter p (x :: xs) with p x
... | true = x :: filter p xs
... | false = filter p xs

is-non-zero : ℕ → Bool
is-non-zero zero    = false
is-non-zero (suc _) = true

filter-example : filter is-non-zero (4 :: 3 :: 0 :: 1 :: 0 :: []) ≡ 4 :: 3 :: 1 :: []
filter-example = refl (4 :: 3 :: 1 :: []) -- refl _ should fill the hole here

_≣_ : Bool → Bool → Type
true ≣ true = 𝟙
true ≣ false = 𝟘
false ≣ true = 𝟘
false ≣ false = 𝟙

Bool-refl : (b : Bool) → b ≣ b
Bool-refl true = ⋆
Bool-refl false = ⋆

≡-to-≣ : (a b : Bool) → a ≡ b → a ≣ b
≡-to-≣ true true a≡b = ⋆
≡-to-≣ false false a≡b = ⋆

≣-to-≡ : (a b : Bool) → a ≣ b → a ≡ b
≣-to-≡ true true a≣b = refl true
≣-to-≡ false false a≣b = refl false

not-is-involution : (b : Bool) → not (not b) ≡ b
not-is-involution true  = refl true
not-is-involution false = refl false

||-is-commutative : (a b : Bool) → a || b ≡ b || a
||-is-commutative true true = refl true
||-is-commutative false true = refl true
||-is-commutative true false = refl true
||-is-commutative false false = refl false


&&-is-associative : (a b c : Bool) → a && (b && c) ≡ (a && b) && c
&&-is-associative true b c = refl (b && c)
&&-is-associative false b c = refl false


min-is-commutative : (n m : ℕ) → min n m ≡ min m n
min-is-commutative zero zero = refl zero
min-is-commutative zero (suc m) = refl zero
min-is-commutative (suc n) zero = refl zero
min-is-commutative (suc n) (suc m) = ap suc (min-is-commutative n m)

0-right-neutral : (n : ℕ) → n ≡ n + 0
0-right-neutral zero = refl zero
0-right-neutral (suc n) = ap suc (0-right-neutral n)

map-id : {X : Type} (xs : List X) → map id xs ≡ xs
map-id [] = refl []
map-id (x :: xs) = ap (x ::_) (map-id xs)

map-comp : {X Y Z : Type} (f : X → Y) (g : Y → Z)
           (xs : List X) → map (g ∘ f) xs ≡ map g (map f xs)
map-comp f g [] = refl []
map-comp f g (x :: xs) = ap (g (f x) ::_) (map-comp f g xs)


-- martin escardo proposed we do this.

G : (A B : Type) → ℕ → Type
G A B zero = B
G A B (suc x) = A → G A B x


_ : {A : ℕ → Type} → A 0 → ((k : ℕ) → A k → A (suc k)) → (n : ℕ) → A n
_ = ℕ-elim

h1 : {A B : Type} → B → (n : ℕ) → G A B n
h1 {A} {B} b0 = ℕ-elim {G A B} b0 (λ _ Gk → λ a → Gk)

σ : {A B : Type} {C : A → B → Type}
  → ((x : A) (y : B) → C x y)
  → (y : B) (x : A) → C x y
σ f y x = f x y

--length' : {X : Type} → List X → ℕ
--length' xs = ℕ-elim {!!} {!!} {!!}

data EqList {A : Type} : (l r : A) → Type where
  eq[] : (a : A) → EqList a a
  eq:: : {x l r : A} → (p : x ≡ l) → EqList l r → EqList x r

eqlist-to-eq : {A : Type} {l r : A} → EqList l r → l ≡ r
eqlist-to-eq (eq[] x) = refl x
eqlist-to-eq (eq:: p eq) = trans p (eqlist-to-eq eq)

Step : (A : Type) (n : ℕ) (l x r : A) → Type
Step A zero l x r = x ≡ r → l ≡ r
Step A (suc n) l x r = {x' : A} → (q : x ≡ x') → Step A n l x' r

h : {A : Type} {x x' l r : A} → (n : ℕ) → (x ≡ x') → Step A n l x r → Step A (suc n) l x' r
h zero x≡x' step x'≡x'' x''≡r = step (trans x≡x' (trans x'≡x'' x''≡r))
h (suc n) x≡x' step = λ q q₁ → step (trans x≡x' (trans q q₁))

k : {A : Type} {l x r : A} (n : ℕ) → l ≡ x → Step A n l x r
k zero p q = trans p q
k (suc n) p q = k n (trans p q)

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

eq : {A : Type} {l r : A} → (n : ℕ) → Step A (pred n) l l r
eq zero = λ z → z
eq (suc n) = k n (refl _)

_ : 1 ≡ 1
_ = eq 1 (refl _)

{-
h : {A : Type} {x l r : A} (n : ℕ) → (x ≡ l) → Step A n l r → Step A (suc n) x r
h zero x≡l step = λ q → trans (sym q) (trans x≡l step)
h (suc n) x≡l step = λ q → λ q₁ → step (trans (sym x≡l) (trans q q₁))

t : {A : Type} {l r : A} (n : ℕ) → Step A n l r → l ≡ r
t zero = λ z → z
t (suc n) = λ step → {!!}

e : {A : Type} {l r : A} (n : ℕ) → Step A n r r
e {A} {l} {r} zero = refl r
e {A} {l} {r} (suc n) {x} = {!!}
-}

F : (A B : Type) → ℕ → Type
F A B zero = B
F A B (suc n) = A → F A B n

{-
-- F A B n is a function which takes n arguments of type A and returns a B
Fold : {A B : Type} → (f : A → Type → Type) → (n : ℕ) → Type
Fold {A} {B} f zero = B
Fold {A} {B} f (suc n) = (a : A) → Fold (f a) n
-}



