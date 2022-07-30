module ws5 where

open import prelude
open import sums

sec : {A B : Type} → (A → B) → Type
sec {A} {B} f = Σ g ꞉ (B → A) , f ∘ g ∼ id

retr : {A B : Type} → (A → B) → Type
retr {A} {B} f = Σ g ꞉ (B → A) , g ∘ f ∼ id

is-equiv : {A B : Type} → (A → B) → Type
is-equiv f = sec f × retr f


has-inverse : {A B : Type} → (A → B) → Type
has-inverse {A} {B} f = Σ g ꞉ (B → A) , (f ∘ g ∼ id) × (g ∘ f ∼ id)


module _ {A B : Type} {f g : A → B} where
  _∙-_ : {C : Type} → f ∼ g → (f' : C → A) → f ∘ f' ∼ g ∘ f'
  f~g ∙- h = λ x → f~g (h x)

  _-∙_ : {C : Type} → (f' : B → C) → f ∼ g → f' ∘ f ∼ f' ∘ g
  f' -∙ h = λ x → ap f' (h x)

  sym∙ : f ∼ g → g ∼ f
  sym∙ x = λ x₁ → sym (x x₁)

  _∙∙_ : {h : A → B} → f ∼ g → g ∼ h → f ∼ h
  a ∙∙ b = λ x → a x ∙ b x


equiv-has-inverse : {A B : Type} → (f : A → B) → is-equiv f → has-inverse f
equiv-has-inverse f ((s , S) , (r , R)) = s , S , ((K ∙- f) ∙∙ R)
  where
  K : s ∼ r
  K = (sym∙ R ∙- s) ∙∙ (r -∙ S)



q1 : {A B : Type} → (f : A → B) → retr f → (a a' : A) → f a ≡ f a' → a ≡ a'
q1 f (g , g∘f) a a' eq = sym (g∘f a) ∙ (ap g eq) ∙ (g∘f a')

module _ {A B X : Type} (h : A → B) (f : A → X) (g : B → X) (ht : f ∼ g ∘ h) where
  q21a : (s : sec h) → f ∘ pr₁ s ∼ g
  q21a (s , h∘s) x = (ht (s x)) ∙ (ap g (h∘s x))

  q21b : (s : sec h) → sec f ⇔ sec g
  q21b (s , h∘s) = p1 , p2
    where
    p1 : sec f → sec g
    p1 (fs , f∘fs) = (h ∘ fs) , ((sym∙ ht) ∙- fs) ∙∙ f∘fs

    p2 : sec g → sec f
    p2 (gs , g∘gs) = (s ∘ gs) , ((h1 ∙- gs) ∙∙ g∘gs)
      where
      h1 : (f ∘ s) ∼ g
      h1 = (ht ∙- s) ∙∙ (g -∙ h∘s)

Eq-bool : Bool → Bool → Type
Eq-bool true true = 𝟙
Eq-bool true false = 𝟘
Eq-bool false true = 𝟘
Eq-bool false false = 𝟙

phi : {b b' : Bool} → b ≡ b' → Eq-bool b b'
phi (refl true) = ⋆
phi (refl false) = ⋆

phi-equiv : {b b' : Bool} → is-equiv (phi {b} {b'})
phi-equiv = {!!} , {!!}
