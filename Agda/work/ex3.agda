{-# OPTIONS --without-K --allow-unsolved-metas #-}

module ex3 where

open import prelude hiding (_∼_)
open import natural-numbers-functions
open import decidability
open import Fin

module _ {A : Type} {B : A → Type} where
  _∼_ : ((x : A) → B x) → ((x : A) → B x) → Type
  f ∼ g = ∀ x → f x ≡ g x

  ∼-refl : (f : (x : A) → B x) → f ∼ f
  ∼-refl f = λ x → refl (f x)

  ∼-inv : (f g : (x : A) → B x) → (f ∼ g) → (g ∼ f)
  ∼-inv f g H x = sym (H x)

  ∼-concat : (f g h : (x : A) → B x) → f ∼ g → g ∼ h → f ∼ h
  ∼-concat f g h H K x = trans (H x) (K x)

  infix 0 _∼_

record is-bijection {A B : Type} (f : A → B) : Type where
 constructor
  Inverse
 field
  inverse : B → A
  η       : inverse ∘ f ∼ id
  ε       : f ∘ inverse ∼ id

record _≅_ (A B : Type) : Type where
 constructor
  Isomorphism
 field
  bijection   : A → B
  bijectivity : is-bijection bijection

infix 0 _≅_


is-bijection' : {A B : Type} → (A → B) → Type
is-bijection' {A} {B} f = Σ inv ꞉ (B → A) , (inv ∘ f ∼ id) × (f ∘ inv ∼ id)

_≅'_ : Type → Type → Type
A ≅' B = Σ f ꞉ (A → B) , is-bijection' f

data 𝟚 : Type where
 𝟎 𝟏 : 𝟚

Bool-𝟚-isomorphism : Bool ≅ 𝟚
Bool-𝟚-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟚
  f false = 𝟎
  f true  = 𝟏

  g : 𝟚 → Bool
  g 𝟎 = false
  g 𝟏 = true

  gf : g ∘ f ∼ id
  gf true  = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg 𝟎 = refl 𝟎
  fg 𝟏 = refl 𝟏

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }



Fin-elim' : (A : {n : ℕ} → Fin n → Type)
         → ({n : ℕ} → A {suc n} zero)
         → ({n : ℕ} (k : Fin n) → A k → A (suc k))
         → {n : ℕ} (k : Fin n) → A k
Fin-elim' A a f = h
 where
  h : {n : ℕ} (k : Fin n) → A k
  h zero    = a
  h (suc k) = f k (h k)


Fin' : ℕ → Type
Fin' 0       = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

zero' : {n : ℕ} → Fin' (suc n)
zero' = inl ⋆

suc'  : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = inr


Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Fin n → Fin' n
  f (suc n) zero    = inl ⋆
  f (suc n) (suc k) = inr (f n k)

  g : (n : ℕ) → Fin' n → Fin n
  g (suc n) (inl ⋆) = zero
  g (suc n) (inr k) = suc (g n k)

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf (suc n) zero    = refl zero
  gf (suc n) (suc k) = γ
   where
    IH : g n (f n k) ≡ k
    IH = gf n k

    γ = g (suc n) (f (suc n) (suc k)) ≡⟨ refl (suc (g n (f n k))) ⟩
        g (suc n) (suc' (f n k))      ≡⟨ refl (suc (g n (f n k))) ⟩
        suc (g n (f n k))             ≡⟨ ap suc IH ⟩
        suc k                         ∎

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg (suc n) (inl ⋆) = refl (inl ⋆)
  fg (suc n) (inr k) = γ
   where
    IH : f n (g n k) ≡ k
    IH = fg n k

    γ = f (suc n) (g (suc n) (suc' k)) ≡⟨ refl (inr (f n (g n k))) ⟩
        f (suc n) (suc (g n k))        ≡⟨ refl (inr (f n (g n k))) ⟩
        suc' (f n (g n k))             ≡⟨ ap suc' IH ⟩
        suc' k                         ∎

  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n}


is-lower-bound : (P : ℕ → Type) (n : ℕ) → Type
is-lower-bound P n = (m : ℕ) → P m → n ≤₁ m

minimal-element : (P : ℕ → Type) → Type
minimal-element P = Σ n ꞉ ℕ , (P n) × (is-lower-bound P n)

leq-zero : (n : ℕ) → 0 ≤₁ n
leq-zero n = ⋆


open import decidability
  using (is-decidable; is-decidable-predicate)

Well-ordering-principle = (P : ℕ → Type) → (d : is-decidable-predicate P) → (n : ℕ) → P n → minimal-element P


-- given a decidable predicate which holds for some number "suc m", and
-- m is a lower bound for the predicate P (suc x), i.e. the predicate
-- on non-zero naturals, and
-- the predicate does not hold at zero, then
-- "suc m" is a lower bound for all of P.
is-minimal-element-suc :
  (P : ℕ → Type) (d : is-decidable-predicate P)
  (m : ℕ) (pm : P (suc m))
  (is-lower-bound-m : is-lower-bound (λ x → P (suc x)) m) →
  ¬ (P 0) → is-lower-bound P (suc m)
is-minimal-element-suc P d _ pm is-lower-bound-m neg-p0 0 p0 = neg-p0 p0
is-minimal-element-suc P d 0 pm is-lower-bound-m neg-p0 (suc n) psuccn = ⋆
is-minimal-element-suc P d (suc m) pm is-lower-bound-m neg-p0 (suc n) psuccn = is-lower-bound-m n psuccn


well-ordering-principle-suc :
  (P : ℕ → Type) (d : is-decidable-predicate P)
  (n : ℕ) (p : P (suc n)) →
  is-decidable (P 0) →
  minimal-element (λ m → P (suc m)) → minimal-element P
well-ordering-principle-suc P d n p (inl p0) _  = zero , p0 , (λ x x₁ → ⋆)
well-ordering-principle-suc P d n p (inr neg-p0) (m , (pm , is-min-m)) =
  suc m , (pm , is-minimal-element-suc P d m pm is-min-m neg-p0)

well-ordering-principle : (P : ℕ → Type) → (d : is-decidable-predicate P) → (n : ℕ) → P n → minimal-element P
well-ordering-principle P d 0 p = zero , p , (λ x x₁ → ⋆)
well-ordering-principle P d (suc n) p = well-ordering-principle-suc P d n p (d 0)
  (well-ordering-principle (λ z → P (suc z)) (λ x → d (suc x)) n p)


is-zero-well-ordering-principle-suc :
  (P : ℕ → Type) (d : is-decidable-predicate P)
  (n : ℕ) (p : P (suc n)) (d0 : is-decidable (P 0)) →
  (x : minimal-element (λ m → P (suc m))) (p0 : P 0) →
  (pr₁ (well-ordering-principle-suc P d n p d0 x)) ≡ 0
is-zero-well-ordering-principle-suc P d n p (inl p0) x q0 = refl zero
is-zero-well-ordering-principle-suc P d n p (inr np0) x q0 = 𝟘-nondep-elim (np0 q0)


is-zero-well-ordering-principle :
  (P : ℕ → Type) (d : is-decidable-predicate P) →
  (n : ℕ) → (pn : P n) →
  P 0 →
  pr₁ (well-ordering-principle P d n pn) ≡ 0
is-zero-well-ordering-principle P d 0 p p0 = refl 0
is-zero-well-ordering-principle P d (suc m) pm = is-zero-well-ordering-principle-suc P d m pm (d 0) (well-ordering-principle (λ z → P (suc z)) (λ x → d (suc x)) m pm)


_divides_ : ℕ → ℕ → Type
x divides y = Σ z ꞉ ℕ , x * z ≡ y

zero-ne-suc : (n : ℕ) → ¬ (0 ≡ suc n)
zero-ne-suc n = λ ()


fz : Fin zero → 𝟘
fz ()

uncurry : {A B : Type} → {C : Type₁} → (A → B → C) → (A × B → C)
uncurry f = λ z → f (pr₁ z) (pr₂ z)

p : (x y : ℕ) → is-decidable (x ≡ y)
p zero zero = inl (refl zero)
p zero (suc m) = inr (λ ())
p (suc n) zero = inr (λ ())
p (suc n) (suc m) = q (p n m)
  where
  q : ∀ {n m : ℕ} → is-decidable (n ≡ m) → is-decidable (_≡_ {ℕ} (suc n) ( suc m))
  q (inl x) = inl (ap suc x)
  q (inr x) = inr λ x₁ → x (suc-is-injective x₁)

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
bb n = Isomorphism ltr (Inverse rtl {!!} {!!})
  where
  ltr : {n : ℕ} → Fin n → (Σ m ꞉ ℕ , suc m ≤ n)
  ltr zero = zero , suc-preserves-≤ 0-smallest
  ltr (suc m) = (suc (pr₁ (ltr m))) , suc-preserves-≤ (pr₂ (ltr m))

  rtl : {n : ℕ} → (Σ m ꞉ ℕ , suc m ≤ n) → Fin n
  rtl (zero , suc-preserves-≤ 0-smallest) = zero
  rtl (suc l , suc-preserves-≤ r) = suc (rtl (l , r))

  rtl-of-ltr : ∀ {n} → (rtl {n} ∘ ltr {n}) ∼ id
  rtl-of-ltr zero = refl zero
  rtl-of-ltr (suc x) = {!!}

  ltr-of-rtl : ∀ {n} → (ltr {n} ∘ rtl {n}) ∼ id
  ltr-of-rtl (zero , suc-preserves-≤ 0-smallest) = refl (zero , suc-preserves-≤ 0-smallest)
  ltr-of-rtl (suc pr₃ , suc-preserves-≤ a) = {!!}



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

g2 : ∀ n → is-exhaustively-searchable (Σ m ꞉ ℕ , m ≤ n)
g2 zero A x = e (x (zero , 0-smallest))
  where
  t : (w : Σ m ꞉ ℕ , (m ≤ zero)) → A w → A (zero , 0-smallest)
  t (zero , 0-smallest) x = x

  e : is-decidable (A (zero , 0-smallest)) → is-decidable (Σ w ꞉ (Σ m ꞉ ℕ , m ≤ zero) , A w)
  e (inl x) = inl ((zero , 0-smallest) , x)
  e (inr x) = inr (λ x₂ → x (t (pr₁ x₂) (pr₂ x₂)))

g2 (suc n) A x = {!!}

div-is-decidable : (d n : ℕ) → is-decidable (d divides n)
div-is-decidable d zero = inl (zero , *-base d)
div-is-decidable zero (suc n) = inr λ x → zero-ne-suc n (pr₂ x)
div-is-decidable (suc d) (suc n) = {!!}

{-
(d + 1) * z = n + 1

d * z + z = n + 1

dz + d + z = n
-}
