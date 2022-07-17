{-# OPTIONS --without-K --allow-unsolved-metas #-}

module ex2 where

open import prelude
open import decidability
open import sums

¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)


uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry = λ x x₁ → x (pr₁ x₁) (pr₂ x₁)

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry = λ x x₁ x₂ → x (x₁ , x₂)

variable
  A B C : Type


[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (pr₃ , pr₄)) = (inl pr₃) , (inl pr₄)
[i] (inr x) = inr x , inr x

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl x , pr₄) = inl (x , pr₄)
[ii] (inr x , pr₄) = inr (x , pr₄)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] x = (λ z → x (inl z)) , (λ z → x (inr z))

h1 : ¬ (A × ¬ A)
h1 (pr₃ , pr₄) = pr₄ pr₃

lem : Type₁
lem = {A : Type} → A ∔ ¬ A

[iv] : lem → {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
[iv] lem {A} {B} f = h lem
  where
    h : A ∔ ¬ A → ¬ A ∔ ¬ B
    h (inl a) = inr (λ x → f (a , x))
    h (inr x) = inl x

[iv]-irref : ¬¬ (¬ (A × B) → ¬ A ∔ ¬ B)
[iv]-irref f = f (λ _ → inl λ a → f λ nAB → inr λ b → nAB (a , b))

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] x = λ z z₁ → z (x z₁)

[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
[vi] x = λ x₁ → {!!}

postulate
 0-elim : 𝟘 → A

[vi]-irref : ¬¬ ((¬ A → ¬ B) → B → A)
[vi]-irref f = f λ g b → 0-elim (g (λ x → f λ _ _ → x) b)

[vi]-dne : ({A B : Type} → (¬ A → ¬ B) → B → A) → (¬¬ A → ¬¬ B) → A → B
[vi]-dne vi x = vi (vi x)


[vii] : {A B : Type} → ((A → B) → A) → A
[vii] x = {!!}

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] f a Ba = f (a , Ba)

[ix] : {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
[ix] x = {!!} , {!!}

[ix]-dne :
    ({A : Type} {B : A → Type} → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a))
    → {A : Type} → ¬¬ A → A
[ix]-dne ix nnA = pr₁ (ix nnA)


[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] x = (λ z → pr₁ (x z)) , λ a → pr₂ (x a)

tne : {A : Type} → ¬¬¬ A → ¬ A
tne f a = f (λ nA → nA a)

¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor = [v] ∘ [v]

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f = tne ∘ ¬¬-functor f
