module ryan where

open import prelude
open import decidability
open import Fin
open import ws5

_≅_ : Type → Type → Type
A ≅ B = Σ f ꞉ (A → B) , is-equiv f

is-finite : Type → Type
is-finite A = Σ n ꞉ ℕ , A ≅ Fin n

-- the claim that "any subset of a finite set is subset".

{- 
ERRATA: this claim derives a contradiction by setting A = 1 and P = const N,
the resulting Sigma type is obviously not finite.
this can be fixed by ensuring "P a" is a proposition, e.g. by truncating it.
-}
fin-subset : Set1
fin-subset = {A : Type} → {P : A → Type} → is-finite A → is-finite (Σ a ꞉ A , P a)

is-finite-1 : is-finite 𝟙
is-finite-1 = suc zero , f , (g , sec-pf) , g , ret-pf
  where
  f : 𝟙 → Fin 1
  f ⋆ = zero

  g : Fin 1 → 𝟙
  g zero = ⋆

  sec-pf : (f ∘ g) ∼ id
  sec-pf zero = refl zero

  ret-pf : (g ∘ f) ∼ id
  ret-pf ⋆ = refl ⋆

fz : {A : Type} → Fin zero → A
fz ()

f-zero-ne-suc : {n : ℕ} → {f : Fin n} → _≡_ {Fin (suc n)} zero (suc f) → 𝟘
f-zero-ne-suc ()

is-prop : Type → Type
is-prop A = (x y : A) → x ≡ y

g : {P : Type} → is-prop P → is-finite (Σ a ꞉ 𝟙 , P) → is-decidable P
g _ (zero , f , F) = inr (λ P → fz (f (⋆ , P)))
g _ (suc zero , f , ((s , S) , _)) = inl (pr₂ (s zero))
g {P} prop (suc (suc n) , f , ((s , S) , (r , R))) = 𝟘-elim (f-zero-ne-suc cc)
  where
  prop2 : is-prop (Σ a ꞉ 𝟙 , P)
  prop2 (⋆ , p1) (⋆ , p2) = ap (⋆ ,_) (prop p1 p2)

  f-prop : (x y : (Σ a ꞉ 𝟙 , P)) → f x ≡ f y
  f-prop x y = ap f (prop2 x y)

  cc : _≡_ {Fin (suc (suc n))} zero (suc zero)
  cc = sym (S zero) ∙ f-prop (s zero) (s (suc zero)) ∙ S (suc zero)

h : fin-subset → (P : Type) → is-prop P → is-decidable P
h fin-subset P prop = g prop (fin-subset is-finite-1)
