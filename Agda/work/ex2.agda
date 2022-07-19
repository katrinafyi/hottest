{-# OPTIONS --without-K --allow-unsolved-metas #-}

module ex2 where

open import prelude
open import decidability

open import classical using (¬¬)

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

[vi]-irref : ¬¬ ((¬ A → ¬ B) → B → A)
[vi]-irref f = f λ g b → 𝟘-elim (g (λ x → f λ _ _ → x) b)

[vi]-dne : ({A B : Type} → (¬ A → ¬ B) → B → A) → (¬¬ A → ¬¬ B) → A → B
[vi]-dne vi x = vi (vi x)


[vii] : {A B : Type} → ((A → B) → A) → A
[vii] x = {!!}

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] f a Ba = f (a , Ba)

absurd = 𝟘-nondep-elim

[ix] : classical.lem2 →
  {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
[ix] lem2 {A} {B} f = lem2 h1 h2
  where
    dne = classical.h2 lem2

    h1 : A →  Σ a ꞉ A , ¬ B a
    h1 x = lem2 id (λ g → x , absurd (f λ a → dne ([viii] g a)))
    h2 : ¬ A → Σ a ꞉ A , ¬ B a
    h2 x = absurd (f λ a → absurd (x a))

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


bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘


bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ _ _ (refl x) = id , id

true≢false : ¬ (true ≡ false)
true≢false ()

bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true f = refl true
bool-≡-char₂ true false f = absurd (pr₁ f ⋆)
bool-≡-char₂ false true f = absurd (pr₂ f ⋆)
bool-≡-char₂ false false f = refl false


has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)

lr : ∀ {A} → has-decidable-equality A → has-bool-dec-fct A
lr {A} f = dec , proof
  where
    dec' : {x y : A} → is-decidable (x ≡ y) → Bool
    dec' (inl _) = true
    dec' (inr _) = false

    dec : A → A → Bool
    dec x y = dec' (f x y)

    f-true : {x y : A} → (p : is-decidable (x ≡ y)) → x ≡ y → dec' p ≡ true
    f-true (inl x) _ = refl true
    f-true (inr neq) p = absurd (neq p)

    f-true' : {x y : A} → (p : is-decidable (x ≡ y)) → dec' p ≡ true → x ≡ y
    f-true' (inl x) _ = x

    proof : (x y : A) → x ≡ y ⇔ dec x y ≡ true
    proof x y = f-true (f x y) , f-true' (f x y)

neg-eq : {x y : Bool} → x ≡ y → ¬(x ≡ not y)
neg-eq (refl true) = λ p → true≢false p
neg-eq (refl false) = λ p → true≢false (sym p)

rl : ∀ {A} → has-bool-dec-fct A → has-decidable-equality A
rl {A} (f , proof) x y = decider (f x y) (refl _)
  where
    eq-f-true : (x ≡ y) → (f x y ≡ true)
    eq-f-true = lr-implication (proof x y)

    decider : (b : Bool) → f x y ≡ b → is-decidable (x ≡ y)
    decider true p = inl (rl-implication (proof x y) p)
    decider false p = inr (λ q → (neg-eq p) (eq-f-true q))

decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char A = lr , rl



