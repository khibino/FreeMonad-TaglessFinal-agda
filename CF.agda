open import Agda.Builtin.Equality using (_≡_; refl)

data _×_  (A : Set) (B : Set) : Set where
  _,_ : A → B → A × B

infixr 6 _×_
infixr 6 _,_

data _⊎_ (A : Set) (B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 5 _⊎_

_∘_ : ∀{a b c} {A : Set a} {B : Set b} {C : Set c} → (B → C) → (A → B) → A → C
(f ∘ g) = λ x → f (g x)

infixr 9 _∘_

sym : ∀{a} {A : Set a} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{a} {A : Set a} → {x y z : A} → x ≡ y → y ≡ z  → x ≡ z
trans refl yz = yz

cong : ∀{a b} {A : Set a} {B : Set b} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

--------------------------------------------------------------------------------

record Functor (F : Set → Set) : Set1 where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} → ∀(x : F A) → fmap (λ z → z) x ≡ x
    fmap-compose
        :  {A B C : Set} (f : B → C) → (g : A → B) → (x : F A)
        → fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x

open Functor ⦃...⦄

--------------------------------------------------------------------------------

{-
"Containers: Constructing strictly positive types"
https://doi.org/10.1016/j.tcs.2005.06.002
https://www.sciencedirect.com/science/article/pii/S0304397505003373
 -}

-- Container Functor definition
data CF (S : Set) (P : S → Set) (X : Set) : Set where
  cf : (s : S) → (k : P s → X) → CF S P X

fmap-CF : {S : Set} {P : S → Set} {A B : Set} → (A → B) → CF S P A → CF S P B
fmap-CF f (cf s k) = cf s (f ∘ k)

fmap-id-CF : {S : Set} {P : S → Set} {A : Set} → ∀ (x : CF S P A) → fmap-CF (λ z → z) x ≡ x
fmap-id-CF (cf s k) = refl

fmap-compose-CF
  : {S : Set} {P : S → Set} {A B C : Set}
  → (f : B → C) → (g : A → B) → (x : CF S P A)
  → fmap-CF (f ∘ g) x ≡ (fmap-CF f ∘ fmap-CF g) x
fmap-compose-CF f g (cf s k) = refl

instance
  functor-CF : {S : Set} {P : S → Set}  → Functor (CF S P)
  fmap ⦃ functor-CF ⦄ = fmap-CF
  fmap-id ⦃ functor-CF ⦄ = fmap-id-CF
  fmap-compose ⦃ functor-CF ⦄ = fmap-compose-CF

--------------------------------------------------------------------------------

postulate
  funext :
    ∀{a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g
  implicit-funext :
    ∀{a b} {A : Set a} {B : A → Set b} {f g : {x : A} → B x}
    → (∀ {x : A} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
