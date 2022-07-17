{-# OPTIONS --without-K #-}

open import general-notation
open import prelude
open import sums
open import decidability

open import Agda.Primitive

¬¬ : Type → Type
¬¬ x = (x → 𝟘) → 𝟘

lem : _
lem = {A : Type} → A ∔ ¬ A

dne : _
dne = {A : Type} → ¬¬ A → A

peirce : _
peirce = {A B : Type} → ((A → B) → A) → A

contra : _
contra = {A B : Type} → (¬ A → ¬ B) → B → A

lem2 : _
lem2 = {A B : Type} → (A → B) → (¬ A → B) → B

h1 :  lem → lem2
h1 lem {A} {B} f1 f2 = h lem
  where
    h : A ∔ ¬ A → B
    h (inl x) = f1 x
    h (inr x) = f2 x

h1' : lem2 → lem
h1' lem2 = lem2 inl inr

absurd = 𝟘-elim

h2 : lem2 → dne
h2 lem {A} = lem (λ a _ → a) (λ nA nnA → absurd (nnA nA))

h3 : dne → peirce
h3 dne = dne (λ f → f λ x → x λ a → absurd (f λ _ → a))

h4 : peirce → contra
h4 peirce f = peirce (λ g b → absurd (f (λ a → g (λ _ → a)) b))

dn : {A : Type} → A → ¬¬ A
dn a nA = nA a

h7 : contra → dne
h7 contra = contra dn

h5 : dne → lem2
h5 dne f1 f2 = dne λ nB → nB (f2 λ a → nB (f1 a))
