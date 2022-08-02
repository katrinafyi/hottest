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

  infixl 10 _∙∙_
  infixl 11 _∙-_
  infixr 12 _-∙_

s~r-equiv : {A B : Type} → {f : A → B} → (eq : is-equiv f) → pr₁ (pr₁ eq) ∼ pr₁ (pr₂ eq)
s~r-equiv ((s , S) , (r , R)) = K
  where
  K : s ∼ r
  K = (sym∙ R ∙- s) ∙∙ (r -∙ S)

equiv-has-inverse : {A B : Type} → (f : A → B) → is-equiv f → has-inverse f
equiv-has-inverse f ((s , S) , (r , R)) = s , S , ((K ∙- f) ∙∙ R)
  where
  K : s ∼ r
  K = s~r-equiv ((s , S) , r , R)



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

q24 : ∀ {A B} {f : A → B} → (eq : is-equiv f) → (pr₁ (pr₁ eq) ∘ f) ∼ id
q24 {_} {_} {f} ((s , S) , (r , R')) = (sym∙ K ∙- f) ∙∙ R'
  where
  K : r ∼ s
  K = (r -∙ sym∙ S) ∙∙ (R' ∙- s)


Eq-bool : Bool → Bool → Type
Eq-bool true true = 𝟙
Eq-bool true false = 𝟘
Eq-bool false true = 𝟘
Eq-bool false false = 𝟙

phi : {b b' : Bool} → b ≡ b' → Eq-bool b b'
phi (refl true) = ⋆
phi (refl false) = ⋆

phi-equiv : {b b' : Bool} → is-equiv (phi {b} {b'})
phi-equiv = (inv , p1) , (inv , p2)
  where
    inv : {b b' : Bool} → Eq-bool b b' → b ≡ b'
    inv {true} {true} _ = refl true
    inv {false} {false} _ = refl false

    p1 : ∀ {b b'} → ((phi {b} {b'}) ∘ inv) ∼ id
    p1 {true} {true} ⋆ = refl ⋆
    p1 {false} {false} ⋆ = refl ⋆

    p2 : ∀ {b b'} → (inv ∘ (phi {b} {b'})) ∼ id
    p2 {true} {true} (refl .true) = refl (refl true)
    p2 {false} {false} (refl .false) = refl (refl false)

const : ∀ {A B : Type} → A → B → A
const x a = x

true-neq-false : ¬ (true ≡ false)
true-neq-false ()

q4 : ∀ {A : Type} {b : Bool} → ¬ is-equiv {A} (const b)
q4 {_} {true} ((pr₃ , p) , y) = true-neq-false (p false)
q4 {_} {false} ((pr₃ , p) , y) = true-neq-false (sym (p true))


q7 : ∀ {A B} → {e e' : A → B} → (eq : is-equiv e) → (eq' : is-equiv e') → e ∼ e'
  → pr₁ (pr₁ eq) ∼ pr₁ (pr₁ eq')
q7 {_} {_} {e} {e'} ((s , S) , r , R) ((s' , S') , r' , R') H = sym∙ (s'-e' ∙- s) ∙∙ (s' -∙ sym∙ H ∙- s) ∙∙ (s' -∙ S)
  where
    equiv = ((s' , S') , r' , R')
    s'-e' : s' ∘ e' ∼ id
    s'-e' = q24 equiv

    r'~s : r' ∼ s
    r'~s = (r' -∙ (sym∙ S ∙∙ (H ∙- s))) ∙∙ (R' ∙- s)

    s'~r' : s' ∼ r'
    s'~r' = s~r-equiv equiv


