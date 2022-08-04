module ws6 where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) renaming (Set to Type) 

open import prelude hiding (Type)
import ws5

is-contr : Type → Type
is-contr A = Σ c ꞉ A , ((x : A) → c ≡ x)

q : {A : Type} {x y : A} → (eq : x ≡ y) → sym eq ∙ eq ≡ refl y
q (refl _) = refl (refl _)

h0 : {A : Type} → is-contr A → (x y : A) → is-contr (x ≡ y)
h0 {A} (pr₃ , contr) x y = (sym (contr x) ∙ contr y) , c
  where
  c : ∀ {x y : A} (x₁ : x ≡ y) → sym (contr x) ∙ contr y ≡ x₁
  c (refl x) = q (contr x)


h1 : is-contr 𝟙
h1 = ⋆ , 𝟙-elim (refl ⋆)

h2 : {A : Type} → (a : A) → is-contr (Σ x ꞉ A , a ≡ x)
h2 a = (a , refl a) , c
  where
  c : (s : Σ (a ≡_)) → (a , refl a) ≡ s
  c (a' , refl .a') = refl (a' , refl a')

const : {A B : Type} → A → B → A
const x _ = x

h3 : {A : Type} → is-contr A ⇔ ws5.is-equiv {A} (const ⋆)
h3 {A} = l , r
  where
  l : is-contr A → ws5.is-equiv {A} (const ⋆)
  l (c , contr) = (f , 𝟙-elim refl ⋆) , (f , λ x → refl c ∙ contr x)
    where
    f : 𝟙 → A
    f ⋆ = c

  r : ws5.is-equiv {A} (const ⋆) → is-contr A
  r ((s , S) , (r , R)) = r ⋆ , R


record Σ' {l1 l2 : Level} {A : Type l1 } (B : A → Type l2) : Type (l1 ⊔ l2)  where
 constructor
  _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ' public
infixr 0 _,_

Sigma' : {l1 l2 : Level} (A : Type l1) (B : A → Type l2) → Type (l1 ⊔ l2)
Sigma' A B = Σ' B

syntax Sigma' A (λ x → b) = Σ' x ꞉ A , b

infix -1 Sigma'


ev-pt : {A : Type} {B : A → Type} → (a : A) → ((x : A) → B x) → B a
ev-pt a f = f a

singleton-ind : {A : Type} → A → Set1
singleton-ind {A} a = (B : A → Type) → ws5.sec (ev-pt {A} {B} a)

h4 : {A : Type} → is-contr A → (Σ' a ꞉ A , singleton-ind a)
h4 {A} (c , C) = c , ind
  where
  ind : (B : A → Type) → ws5.sec (ev-pt {A} {B} c)
  ind B = sec , ff
    where
    C' : (x : A) → c ≡ x
    C' x = sym (C c) ∙ C x

    C'-refl : C' c ≡ refl c
    C'-refl = q (C c)

    sec : B c → (x : A) → B x
    sec Bc x = transport B (C' x) Bc

    ff : (b : B c) → sec b c ≡ b
    ff b = ap (λ H → transport B H b) C'-refl

h4' : {A : Type} → (Σ' a ꞉ A , singleton-ind a) → is-contr A
h4' {A} (a , ind) = a , xx
  where
  xx : (x : A) → (a ≡ x)
  xx = pr₁ (ind (a ≡_)) (refl a)

