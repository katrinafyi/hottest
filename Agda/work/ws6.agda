module ws6 where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) renaming (Set to Type) 

open import prelude hiding (Type)
open import new-prelude using (Path)
open import ws5
open import ex3 using (_≅_)

is-contr : Type → Type
is-contr A = Σ c ꞉ A , ((x : A) → c ≡ x)

q : {A : Type} {x y : A} → (eq : x ≡ y) → sym eq ∙ eq ≡ refl y
q (refl _) = refl (refl _)

q' : {A : Type} {x y : A} → (eq : x ≡ y) → eq ∙ sym eq ≡ refl x
q' (refl _) = refl (refl _)

h0 : {A : Type} → is-contr A → (x y : A) → is-contr (x ≡ y)
h0 {A} (pr₃ , contr) x y = (sym (contr x) ∙ contr y) , c
  where
  c : ∀ {x y : A} (x₁ : x ≡ y) → sym (contr x) ∙ contr y ≡ x₁
  c (refl x) = q (contr x)

hx : {A : Type} → is-contr A → (x y : A) → (x ≡ y)
hx (_ , contr) x y = sym (contr x) ∙ contr y


h1 : is-contr 𝟙
h1 = ⋆ , 𝟙-elim (refl ⋆)

h2 : {A : Type} → (a : A) → is-contr (Σ x ꞉ A , a ≡ x)
h2 a = (a , refl a) , c
  where
  c : (s : Σ (a ≡_)) → (a , refl a) ≡ s
  c (a' , refl .a') = refl (a' , refl a')

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
  ind B = g , ff
    where
    C' : (x : A) → c ≡ x
    C' x = sym (C c) ∙ C x

    C'-refl : C' c ≡ refl c
    C'-refl = q (C c)

    g : B c → (x : A) → B x
    g Bc x = transport B (C' x) Bc

    ff : (b : B c) → g b c ≡ b
    ff b = ap (λ H → transport B H b) C'-refl

h4' : {A : Type} → (Σ' a ꞉ A , singleton-ind a) → is-contr A
h4' {A} (a , ind) = a , xx
  where
  xx : (x : A) → (a ≡ x)
  xx = pr₁ (ind (a ≡_)) (refl a)


refl-trans-l : {A : Type} {x y : A} (l : x ≡ y) → l ≡ refl x ∙ l
refl-trans-l (refl _) = refl (refl _)

module _ {A B : Type} (f : A → B) where
  fib : B → Type
  fib b = Σ x ꞉ A , f x ≡ b

  Sigma-eq : {a a' : A} {b : B}
    (p : a ≡ a') → (q : f a ≡ b)
    → transport (λ x → f x ≡ b) p q ≡ sym (ap f p) ∙ q
  Sigma-eq (refl _) (refl _) = refl (refl _)

  cor1 : {b : B} (x x' : fib b)
    → (x ≡ x') ≅ (Σ p ꞉ (pr₁ x ≡ pr₁ x') , pr₂ x ≡ ap f p ∙ pr₂ x')
  cor1 x x' = ex3.Isomorphism left (ex3.Inverse right rol lor)
    where
    left : {b : B} {x x' : fib b}
      → (x ≡ x') → (Σ p ꞉ (pr₁ x ≡ pr₁ x') , pr₂ x ≡ ap f p ∙ pr₂ x')
    left (refl (pr₃ , pr₄)) = refl _ , refl-trans-l pr₄

    right : {b : B} {x x' : fib b}
      → (Σ p ꞉ (pr₁ x ≡ pr₁ x') , pr₂ x ≡ ap f p ∙ pr₂ x') → (x ≡ x')
    right {b} {a , pf} {.a , pf'} (refl .a , eq) =
      ap (a ,_) (eq ∙ sym (refl-trans-l pf'))

    lor : {b : B} {x x' : fib b}
      → left {b} {x} {x'} ∘ right ∼ id
    lor {.(f a)} {a , _} {.a , refl _} (refl .a , refl _) = refl _

    rol : {b : B} {x x' : fib b}
      → right {b} {x} {x'} ∘ left {b} {x} {x'} ∼ id
    rol {.(f a)} {a , refl .(f a)} {_} (refl _) = refl _


is-contr-map : {A B : Type} (f : A → B) → Set
is-contr-map {A} {B} f = (b : B) → is-contr (fib f b)

thm1 : {A B : Type} {f : A → B} → is-contr-map f → ws5.is-equiv f
thm1 {A} {B} {f} contr-map = (g , G) , (g , G')
  where
  centres : (y : B) → fib f y
  centres y = pr₁ (contr-map y)

  g : B → A
  g y = pr₁ (centres y)

  G : f ∘ g ∼ id
  G y = pr₂ (centres y)

  p : ((f ∘ g) ∘ f) ∼ f
  p = G ∙- f

  G' : g ∘ f ∼ id
  G' x = contr-x gfx
    where
    gfx : fib f (f x)
    gfx = (g (f x) , p x)

    contr-x : (l : fib f (f x)) → pr₁ l ≡ x
    contr-x l = ap pr₁ (pr₁ (h0 (contr-map (f x)) l (x , refl _)))

record has-inv {A B : Set} (f : A → B) : Set where
  constructor
    Has-Inv
  field
    g : B → A
    G : f ∘ g ∼ id
    H : g ∘ f ∼ id

record has-coh-inv {A B : Set} (f : A → B) : Set where
  constructor
    Has-Coh-Inv
  field
    g : B → A
    G : f ∘ g ∼ id
    H : g ∘ f ∼ id
    K : G ∙- f ∼ f -∙ H

is-contr-has-coh-inv : {A B : Set} {f : A → B}
  → (has-coh-inv f) → is-contr-map f
is-contr-has-coh-inv {A} {B} {f} record { g = g ; G = G ; H = H ; K = K } y = centre y , C y
  where
  centre : (y : B) → fib f y
  centre y = (g y , G y)

  C : (y : B) → (x : fib f y) → centre y ≡ x
  C .(f x) (x , refl .(f x)) = equiv-to-eq (cor1 f (centre (f x)) (x , (refl _))) sig
    where
    equiv-to-eq : {A B : Type} → A ≅ B → B → A
    equiv-to-eq (ex3.Isomorphism bijection (ex3.Inverse inverse η ε)) = inverse

    --cor1 : {b : B} (x x' : fib b)
    --→ (x ≡ x') ≅ (Σ p ꞉ (pr₁ x ≡ pr₁ x') , pr₂ x ≡ ap f p ∙ pr₂ x')
    sig : Σ p ꞉ (g (f x) ≡ x) , (G (f x) ≡ ap f p ∙ refl (f x))
    sig = H x , K x

is-equiv-has-inverse : {A B : Set} {f : A → B}
  → has-inverse f → is-equiv f
is-equiv-has-inverse (pr₃ , pr₄) = (pr₃ , pr₁ pr₄) , (pr₃ , pr₂ pr₄)

nat-htpy : {A B : Set} {f g : A → B} {x y : A} (H : f ∼ g) (p : x ≡ y)
  → ap f p ∙ H y ≡ H x ∙ ap g p
nat-htpy H (refl x) = sym (refl-trans-l (H x))

ap-id : {A : Set} {x y : A} → (eq : x ≡ y) → ap id eq ≡ eq
ap-id (refl _) = refl (refl _)

ap-merge : {A B C : Set} {x y : A} {eq : x ≡ y}
   (g : B → C) (f : A → B)
  → ap g (ap f eq) ≡ ap (g ∘ f) eq
ap-merge {A} {B} {C} {_} {_} {refl _} f g = refl (refl _)

trans-assoc : {A : Type} {x y z w : A}
  → (xy : x ≡ y) (yz : y ≡ z) (zw : z ≡ w)
  → xy ∙ (yz ∙ zw) ≡ (xy ∙ yz) ∙ zw
trans-assoc xy yz (refl _) = refl (trans xy yz)

nat-htpy-case : {A : Set} {h : A → A} (H : h ∼ id)
  → h -∙ H ∼ H ∙- h
nat-htpy-case {A} {h} H x =
    ap h (H x)
  ≡⟨ ap (λ X → ap h (H x) ∙ X) (sym (q' (H x))) ⟩
    ap h (H x) ∙ ((H x) ∙ sym (H x))
  ≡⟨ trans-assoc _ (H x) (sym (H x)) ⟩
    ap h (H x) ∙ (H x) ∙ sym (H x)
  ≡⟨ ap (_∙ sym (H x)) (nat-htpy H (H x)) ⟩
    H (h x) ∙ ap id (H x) ∙ sym (H x)
  ≡⟨ ap (λ X → H (h x) ∙ X ∙ sym (H x)) (ap-id (H x)) ⟩
    H (h x) ∙ H x ∙ sym (H x)
  ≡⟨ sym (trans-assoc (H (h x)) (H x) (sym (H x))) ⟩
    H (h x) ∙ (H x ∙ sym (H x))
  ≡⟨ ap (H (h x) ∙_) (q' (H x)) ⟩
    H (h x)
  ∎

has-coh-inv-has-inv : {A B : Set} → {f : A → B}
  → has-inv f → has-coh-inv f
has-coh-inv-has-inv {A} {B} {f} (Has-Inv g G H) = Has-Coh-Inv g G' H K
  where
  G' : f ∘ g ∼ id
  G' y = sym (G (f (g y))) ∙ (ap f (H (g y)) ∙ G y)

  K : G' ∙- f ∼ f -∙ H
  K x = goal
    where
    -- replace top edge using special case.
    top : ap f (H (g (f x))) ≡ ap (f ∘ (g ∘ f)) (H x)
    top =
        ap f (H (g (f x)))
      ≡⟨ ap (ap f) (sym (nat-htpy-case H x)) ⟩
        ap f (ap (g ∘ f) (H x))
      ≡⟨ ap-merge f (g ∘ f) ⟩
        ap (f ∘ (g ∘ f)) (H x)
      ∎

    -- second half of proof with ap fgf (H x) on top edge.
    second : ap (f ∘ (g ∘ f)) (H x) ∙ (G ∙- f) x ≡ (G ∙- f) (g (f x)) ∙ ap f (H x)
    second = nat-htpy (G ∙- f) (H x)

    -- first half of proof (that is, the real goal) which is exactly
    -- G' ∙- f ∼ f -∙ H with the left edge reversed.
    first : ap f (H (g (f x))) ∙ (G ∙- f) x ≡ (G ∙- f) (g (f x)) ∙ ap f (H x)
    first =
      transport
      (λ top → top ∙ (G ∙- f) x ≡ (G ∙- f) (g (f x)) ∙ ap f (H x))
      (sym top) second

    -- first but with added reverse path on left edge.
    first' :
      sym ((G ∙- f) (g (f x)))
      ∙ (ap f (H (g (f x))) ∙ (G ∙- f) x)
      ≡ sym ((G ∙- f) (g (f x)))
      ∙ ((G ∙- f) (g (f x)) ∙ ap f (H x))
    first' = ap (sym ((G ∙- f) (g (f x))) ∙_) first

    -- cancellation of reverse path to get f -∙ H on RHS.
    simp : sym ((G ∙- f) (g (f x))) ∙ ((G ∙- f) (g (f x)) ∙ ap f (H x)) ≡ ap f (H x)
    simp =
        sym ((G ∙- f) (g (f x))) ∙ ((G ∙- f) (g (f x)) ∙ ap f (H x))
      ≡⟨ trans-assoc _ ((G ∙- f) (g (f x))) (ap f (H x)) ⟩
        sym ((G ∙- f) (g (f x))) ∙ (G ∙- f) (g (f x)) ∙ ap f (H x)
      ≡⟨ ap (_∙ ap f (H x)) (q ((G ∙- f) (g (f x)))) ⟩
        refl _ ∙ ap f (H x)
      ≡⟨ sym (refl-trans-l _) ⟩
        ap f (H x)
      ∎

    goal : (G' ∙- f) x ≡ (f -∙ H) x
    goal = first' ∙ simp


not-contr-0 : ¬ is-contr 𝟘
not-contr-0 (() , _)


Eq-N : ℕ → ℕ → Type
Eq-N 0 0 = 𝟙
Eq-N (suc _) 0 = 𝟘
Eq-N 0 (suc _) = 𝟘
Eq-N (suc n) (suc m) = Eq-N n m
 
not-contr-N : ¬ (is-contr ℕ)
not-contr-N (pr₃ , contr) = x 1=0
  where
  x : 1 ≡ 0 → 𝟘
  x ()

  1=0 : 1 ≡ 0
  1=0 = sym (contr 1) ∙ contr 0

ws6-4 : {A : Type} {B : A → Type}
  → is-equiv {Σ x ꞉ A , B x} {A} pr₁
  ⇔ ((a : A) → is-contr (B a))
ws6-4 {A} {B} = left , {!!}
  where
  left : is-equiv {Σ x ꞉ A , B x} {A} pr₁ → (a : A) → is-contr (B a)
  left ((s , S) , (r , R)) a = transport B (S a) (pr₂ (s a)) , {!!}
    where
    c4 : is-contr-map {Σ x ꞉ A , B x} {A} pr₁ → (a : A) → is-contr (B a)
    c4 contr-map a = b , λ x → f3 {b} {x}
      where
      b : B a
      b = transport B (S a) (pr₂ (s a))

      ff : {A : Type} {B : A → Type} {x y : Σ a ꞉ A , B a}
        → x ≡ y → pr₁ x ≡ pr₁ y
      ff (refl _) = refl _

      ff' : {A : Type} {B : A → Type}
        → (a : A) (b b' : B a) → (a , b) ≡ (a , b') [ (Σ a ꞉ A , B a) ] → b ≡ b'
      ff' a b .b (new-prelude.refl .(a , b)) = refl b

      f2 : {x y : Σ a ꞉ A , B a} → pr₁ x ≡ pr₁ y → x ≡ y
      f2 {x} {.(pr₁ x) , pr₃} (refl .(pr₁ x)) =
        ff (hx (contr-map (pr₁ x)) (x , refl _) (((pr₁ x) , pr₃) , refl _))

      eq-conv : {A : Type} {x y : A} → x ≡ y → x ≡ y [ A ]
      eq-conv (refl _) = new-prelude.refl _

      f3 : {x y : B a} → x ≡ y
      f3 {x} {y} = ff' a x y (eq-conv (f2 (refl a)))


    contr : (x : B a) → transport B (S a) (pr₂ (s a)) ≡ x
    contr b = {!!}
    


