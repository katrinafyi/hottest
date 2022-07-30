module ex3a where

open import new-prelude hiding (Sigma)

open import sums
open import natural-numbers-type
open import natural-numbers-functions
open import binary-sums
open import decidability
open import Fin

sym : {l : Level} {A : Type l} {x y : A} → x ≡ y → y ≡ x
sym (refl _) = refl _

suc-eq-inv : {n m : ℕ} → suc n ≡ suc m [ ℕ ] → n ≡ m
suc-eq-inv (refl .(suc _)) = refl _

suc-le-inv : {n m : ℕ} → suc n ≤ suc m → n ≤ m
suc-le-inv (suc-preserves-≤ le) = le

p : (x y : ℕ) → is-decidable (x ≡ y)
p zero zero = inl (refl zero)
p zero (suc m) = inr (λ ())
p (suc n) zero = inr (λ ())
p (suc n) (suc m) = q (p n m)
  where
  q : ∀ {n m : ℕ} → is-decidable (n ≡ m) → is-decidable (_≡_ {_} {ℕ} (suc n) ( suc m))
  q (inl x) = inl (ap suc x)
  q (inr x) = inr λ x₁ → x (suc-eq-inv x₁)

p2 : (x y : ℕ) → is-decidable (x ≤ y)
p2 zero zero = inl 0-smallest
p2 zero (suc m) = inl 0-smallest
p2 (suc n) zero = inr (λ ())
p2 (suc n) (suc m) = q (p2 n m)
  where
  o : suc n ≤ suc m → n ≤ m
  o (suc-preserves-≤ s) = s

  q : is-decidable (n ≤ m) → is-decidable (suc n ≤ suc m)
  q (inl x) = inl (suc-preserves-≤ x)
  q (inr x) = inr (λ x₁ → x (o x₁))

fin-bound : ∀ n → (f : Fin n) → suc (ι f) ≤ n
fin-bound (suc n) zero = suc-preserves-≤ 0-smallest
fin-bound (suc n) (suc f) = suc-preserves-≤ (fin-bound n f)

bb : ∀ n → Fin n ≅ (Σ m ꞉ ℕ , suc m ≤ n)
bb n = Isomorphism ltr (Inverse rtl rtl-of-ltr ltr-of-rtl)
  where
  ltr : {n : ℕ} → Fin n → (Σ m ꞉ ℕ , suc m ≤ n)
  ltr zero = zero , suc-preserves-≤ 0-smallest
  ltr (suc m) = (suc (pr₁ (ltr m))) , suc-preserves-≤ (pr₂ (ltr m))

  rtl : {n : ℕ} → (Σ m ꞉ ℕ , suc m ≤ n) → Fin n
  rtl (zero , suc-preserves-≤ 0-smallest) = zero
  rtl (suc l , suc-preserves-≤ r) = suc (rtl (l , r))

  rtl-of-ltr : ∀ {n} → (rtl {n} ∘ ltr {n}) ∼ id
  rtl-of-ltr zero = refl zero
  rtl-of-ltr (suc x) = ap suc (rtl-of-ltr x)

  ltr-of-rtl : ∀ {n} → (ltr {n} ∘ rtl {n}) ∼ id
  ltr-of-rtl (zero , suc-preserves-≤ 0-smallest) = refl (zero , suc-preserves-≤ 0-smallest)
  ltr-of-rtl (suc fn , suc-preserves-≤ le) = ap (λ { (m , le') → (suc m) , (suc-preserves-≤ le')}) (ltr-of-rtl (fn , le))


fz : Fin zero → 𝟘
fz = λ ()

g : ∀ n → is-exhaustively-searchable (Fin n)
g zero A x = inr λ y → fz (pr₁ y)
g (suc n) A d = l (d zero) (g n (λ z → A (suc z)) (λ x → d (suc x)))
  where
  l : is-decidable (A zero) → is-decidable (Σ z ꞉ Fin n , A (suc z)) → is-decidable (Σ x ꞉ Fin (suc n) , A x)
  l (inl x) neg = inl (zero , x)
  l (inr x) (inl (pr₃ , pr₄)) = inl (suc pr₃ , pr₄)
  l (inr x) (inr x₁) = inr destroy
    where
    destroy : ¬ (Σ z ꞉ Fin (suc n) , A z)
    destroy (zero , pr₄) = x pr₄
    destroy (suc pr₃ , pr₄) = x₁ (pr₃ , pr₄)

postulate
  ua : {l : Level} {A B : Type l} → (A ≅ B) → (A ≡ B)

g2 : ∀ n → is-exhaustively-searchable (Σ m ꞉ ℕ , suc m ≤ n)
g2 n = transport is-exhaustively-searchable (ua (bb n)) (g n)

_divides_ : ℕ → ℕ → Type
x divides y = Σ z ꞉ ℕ , x * z ≡ y


zero-mul-r : (n : ℕ) → n * zero ≡ zero
zero-mul-r zero = refl zero
zero-mul-r (suc n) = ap (_+ zero) (zero-mul-r n)

add-comm : (n m : ℕ) → n + m ≡ m + n
add-comm zero zero = refl zero
add-comm zero (suc m) = ap suc (add-comm zero m)
add-comm (suc n) m = ap suc (add-comm n m) ∙ qq n m
  where
  qq : (n m : ℕ) → suc (m + n) ≡ m + suc n
  qq n zero = refl (suc n)
  qq n (suc m) = ap suc (qq n m)

suc-ne : {n : ℕ} → ¬(suc n ≡ zero [ ℕ ])
suc-ne {n} = λ ()

dec0 : (n x y : ℕ) → is-decidable-predicate (λ (f : Fin n) → x * ι f ≡ y)
dec0 n zero zero = λ x → inl (refl zero)
dec0 n zero (suc y) = λ x → inr (λ ())
dec0 _ (suc x) zero zero = inl (ap (_+ zero) (zero-mul-r x))
dec0 _ (suc x) zero (suc i) = inr λ x₁ → suc-ne (add-comm (suc (ι i)) (x * suc (ι i)) ∙ x₁)
dec0 .(suc _) (suc x) (suc y) zero = inr λ x₁ → suc-ne (sym (ap (_+ zero) (sym (zero-mul-r x)) ∙ x₁))
dec0 .(suc _) (suc x) (suc y) (suc f) = {!!}

dec1 : {n : ℕ} → (x y : ℕ)  → is-decidable (Σ f ꞉ Fin n , x * ι f ≡ y)
dec1 x y = {!!}

zero-ne-suc : (n : ℕ) → ¬ (0 ≡ suc n)
zero-ne-suc n = λ ()

{-
div-is-decidable : (d n : ℕ) → is-decidable (d divides n)
div-is-decidable d zero = inl (zero , zero-mul-r d)
div-is-decidable zero (suc n) = inr λ x → zero-ne-suc n (pr₂ x)
div-is-decidable (suc d) (suc n) = {!!}
-}
