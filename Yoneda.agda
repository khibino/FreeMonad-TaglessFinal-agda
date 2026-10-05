open import Agda.Builtin.Equality using (_≡_; refl)

open import CF
open import CFree

open Functor ⦃...⦄
open Monad ⦃...⦄

infixr 5 _≡⟨_⟩_ _≡˘⟨_⟩_
infix 6 _∎

_≡⟨_⟩_
  : ∀ {a} {A : Set a}
  → (x : A)
  → {y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
x ≡⟨ refl ⟩ q = q

_≡˘⟨_⟩_
  : ∀ {a} {A : Set a}
  → (x : A)
  → {y z : A}
  → y ≡ x
  → y ≡ z
  → x ≡ z
x ≡˘⟨ refl ⟩ q = q

_∎
  : ∀ {a} {A : Set a}
  → (x : A)
  → x ≡ x
x ∎ = refl

------------------------------------------------------------

record Category (_hom-⇒_ : Set → Set → Set) : Set₁ where
  field
    c-id : {A : Set} → A hom-⇒ A
    _∘ᶜ_ : {A B C : Set} → (B hom-⇒ C) → (A hom-⇒ B) → (A hom-⇒ C)
    --
    c-left-id  : {A B : Set} → (f : A hom-⇒ B) → c-id ∘ᶜ f ≡ f
    c-right-id : {A B : Set} → (f : A hom-⇒ B) →  f ∘ᶜ c-id ≡ f
    c-assoc
      :  {A B C D : Set}
      → (f : C hom-⇒ D) → (g : B hom-⇒ C) → (h : A hom-⇒ B)
      → (f ∘ᶜ g) ∘ᶜ h ≡ f ∘ᶜ (g ∘ᶜ h)

open Category ⦃...⦄

_→ₛ_ : Set → Set → Set
A →ₛ B = A → B

instance
  set-Cat : Category (_→ₛ_)
  --
  c-id ⦃ set-Cat ⦄ = λ z → z
  _∘ᶜ_ ⦃ set-Cat ⦄ f g = f ∘ g
  --
  c-left-id  ⦃ set-Cat ⦄ f = refl
  c-right-id ⦃ set-Cat ⦄ f = refl
  c-assoc ⦃ set-Cat ⦄ f g h = refl

homₖ : {Set → Set} → Set → Set → Set
homₖ {M} A B = A → M B

_→ₖ_ = homₖ

idₖ :  {M : Set → Set} ⦃ _ : Monad M ⦄
    → {A : Set} → homₖ {M} A A
idₖ = pure

_∘ₖ_
  : {M : Set → Set} ⦃ _ : Monad M ⦄ {A B C : Set}
  → (homₖ {M} B C) → (homₖ {M} A B) → (homₖ {M} A C)
f ∘ₖ g = λ x → g x ≫= f

postulate
  pure-natural
    :  {M : Set → Set} ⦃ _ : Monad M ⦄
    → {A B : Set}
    → (g : A → B) → (a : A)
    → (pure ∘ g) a ≡ (fmap {M} g ∘ pure) a
  join-natural
    :  {M : Set → Set} ⦃ _ : Monad M ⦄
    → {A B : Set}
    → (g : A → B) → (a : M (M A))
    → (join ∘ fmap (fmap g)) a ≡ (fmap g ∘ join) a

kl-left-id
  :  {M : Set → Set} ⦃ _ : Monad M ⦄ {A B : Set}
  → (f : homₖ {M} A B) → idₖ {M} ∘ₖ f ≡ f
kl-left-id f = funext λ a → join-right-id (f a)

kl-right-id
  :  {M : Set → Set} ⦃ _ : Monad M ⦄ {A B : Set}
  → (f : homₖ {M} A B) → f ∘ₖ idₖ {M} ≡ f
kl-right-id {_} {A} f = funext h
  where
    h :  (a : A) → (f ∘ₖ idₖ) a ≡ f a
    h a = join ((fmap f ∘ pure) a)
          ≡˘⟨ cong join (pure-natural f a) ⟩
          join ((pure ∘ f) a)
          ≡⟨ join-left-id (f a) ⟩
          f a
          ∎

bind-assoc
  :  {M : Set → Set} ⦃ _ : Monad M ⦄
  → {A B C : Set}
  → (f : B → M C) (g : A → M B)
  → (a : M A)
  → join (fmap (λ x → join (fmap f (g x))) a) ≡
     join (fmap f (join (fmap g a)))
bind-assoc f g a =
  join (fmap (λ x → join (fmap f (g x))) a)
  ≡⟨ cong join (fmap-compose join (λ x → fmap f (g x)) a) ⟩
  join ((fmap join ∘ fmap (λ x → fmap f (g x))) a)
  ≡⟨ cong (join ∘ fmap join) (fmap-compose (fmap f) g a) ⟩
  join ((fmap join ∘ fmap (fmap f) ∘ fmap g) a)
  ≡˘⟨ join-assoc ((fmap (fmap f) ∘ fmap g) a) ⟩
  join ((join ∘ fmap (fmap f) ∘ fmap g) a)
  ≡⟨ cong join (join-natural f (fmap g a)) ⟩
  join (fmap f (join (fmap g a)))
  ∎

kl-assoc
  :  {M : Set → Set} ⦃ _ : Monad M ⦄
  → {A B C D : Set}
  → (f : homₖ {M} C D) → (g : homₖ {M} B C) → (h : homₖ {M} A B)
  → (f ∘ₖ g) ∘ₖ h ≡ f ∘ₖ (g ∘ₖ h)
kl-assoc {M} {A} f g h = funext eqh
  where
    eqh : (a : A)
      → join (fmap (λ x → join (fmap f (g x))) (h a)) ≡
         join (fmap f (join (fmap g (h a))))
    eqh a = bind-assoc f g (h a)

instance
  kleisli-Cat
    :  {M : Set → Set} ⦃ _ : Monad M ⦄
    → Category (homₖ {M})
  c-id ⦃ kleisli-Cat ⦄ = idₖ
  _∘ᶜ_ ⦃ kleisli-Cat ⦄ = _∘ₖ_
  --
  c-left-id  ⦃ kleisli-Cat ⦄ = kl-left-id
  c-right-id ⦃ kleisli-Cat ⦄ {A} = kl-right-id
  c-assoc ⦃ kleisli-Cat ⦄ = kl-assoc

------------------------------------------------------------

record
  CatFunctor
    (F : Set → Set)
    {_⇒₁_ : Set → Set → Set}
    (dom : Category _⇒₁_)
    {_⇒₂_ : Set → Set → Set}
    (cod : Category _⇒₂_)
    : Set₁ where

  c-id₁ = c-id ⦃ dom ⦄
  _∘₁_ = _∘ᶜ_ ⦃ dom ⦄
  c-id₂ = c-id ⦃ cod ⦄
  _∘₂_ = _∘ᶜ_ ⦃ cod ⦄

  field
    c-fmap : {A B : Set} → (A ⇒₁ B) → (F A ⇒₂ F B)
    --
    c-fmap-id : {X : Set} → c-fmap {X} {X} c-id₁ ≡ c-id₂
    c-fmap-compose
      :  {A B C : Set} (f : B ⇒₁ C) (g : A ⇒₁ B)
      → c-fmap (f ∘₁ g) ≡ c-fmap f ∘₂ c-fmap g

open CatFunctor ⦃...⦄

c-fmap-rep
  :  {hom : Set → Set → Set} ⦃ _ : Category hom ⦄
  → {R : Set}
  → {A B : Set} → (hom A B)
  → hom R A → hom R B
c-fmap-rep {hom} {R} {A} g fa = g ∘ᶜ fa

c-fmap-id-rep
  :  {hom : Set → Set → Set} ⦃ _ : Category hom ⦄
  → {R : Set}
  → {X : Set} → c-fmap-rep {hom} {R} {X} {X} c-id ≡ λ z → z
c-fmap-id-rep {hom} {R} {X} = funext λ rx → c-left-id rx

c-fmap-compose-rep
      :  {hom : Set → Set → Set} ⦃ _ : Category hom ⦄
      → {R : Set}
      → {A B C : Set} (f : hom B C) (g : hom A B)
      → c-fmap-rep {hom} {R} (f ∘ᶜ g) ≡ c-fmap-rep f ∘ c-fmap-rep g
c-fmap-compose-rep {hom} {R} f g = funext λ ra → c-assoc f g ra

instance
  rep-Functor
    :  {hom : Set → Set → Set} ⦃ cat : Category hom ⦄
    → {R : Set}
    → CatFunctor (hom R) cat set-Cat
  c-fmap ⦃ rep-Functor ⦄ = c-fmap-rep
  c-fmap-id ⦃ rep-Functor ⦄ = c-fmap-id-rep
  c-fmap-compose ⦃ rep-Functor ⦄ = c-fmap-compose-rep

fmap-kl-rep
  :  {M : Set → Set} ⦃ _ : Monad M ⦄ {R : Set}
  → {A B : Set} → homₖ {M} A B
  → homₖ {M} R A →ₛ homₖ {M} R B
fmap-kl-rep {M} = c-fmap-rep {homₖ {M}}
-- fmap-kl-rep {M} f ra = -- f ∘ₖ ra

fmap-id-kl-rep
  :  {M : Set → Set} ⦃ _ : Monad M ⦄ {R : Set}
  → {X : Set} → fmap-kl-rep {M} {R} {X} {X} c-id ≡ (λ z → z)
fmap-id-kl-rep {M} = c-fmap-id-rep {homₖ {M}}
  -- funext λ rx → funext λ r → join-right-id (rx r)

fmap-compose-kl-rep
  :  {M : Set → Set} ⦃ _ : Monad M ⦄ {R : Set}
  → {A B C : Set} (f : homₖ {M} B C) (g : homₖ {M} A B)
  → fmap-kl-rep {M} {R} (f ∘ₖ g) ≡
     fmap-kl-rep {M} {R} f ∘ fmap-kl-rep {M} {R} g
fmap-compose-kl-rep {M} = c-fmap-compose-rep {homₖ {M}}

{-
instance
  kl-rep-Functor
    :  {M : Set → Set} ⦃ _ : Monad M ⦄ {R : Set}
    → CatFunctor (F-kl-rep {M} {R}) (kleisli-Cat {M}) set-Cat
  c-fmap ⦃ kl-rep-Functor ⦄ = fmap-kl-rep
  c-fmap-id  ⦃ kl-rep-Functor ⦄ = fmap-id-kl-rep
  c-fmap-compose ⦃ kl-rep-Functor ⦄ = fmap-compose-kl-rep
 -}

c-fmap-kl-monad
  :  {M : Set → Set} ⦃ _ : Monad M ⦄
  → {A B : Set} → homₖ {M} A B
  → M A →ₛ M B
c-fmap-kl-monad f ma = ma ≫= f

c-fmap-id-kl-monad
  :  {M : Set → Set} ⦃ _ : Monad M ⦄
  → {X : Set} → c-fmap-kl-monad {M} {X} {X} c-id ≡ (λ z → z)
c-fmap-id-kl-monad {M} = funext join-right-id

c-fmap-compose-kl-monad
  :  {M : Set → Set} ⦃ _ : Monad M ⦄
  → {A B C : Set} (f : homₖ {M} B C) (g : homₖ {M} A B)
  → c-fmap-kl-monad {M} (f ∘ₖ g) ≡
     c-fmap-kl-monad {M} f ∘ c-fmap-kl-monad {M} g
c-fmap-compose-kl-monad f g =
  funext λ a → bind-assoc f g a

instance
  kl-monad-Functor
    :  {M : Set → Set} ⦃ _ : Monad M ⦄
    → CatFunctor M (kleisli-Cat {M}) set-Cat
  c-fmap ⦃ kl-monad-Functor ⦄ = c-fmap-kl-monad
  c-fmap-id ⦃ kl-monad-Functor ⦄ = c-fmap-id-kl-monad
  c-fmap-compose ⦃ kl-monad-Functor ⦄ = c-fmap-compose-kl-monad

------------------------------------------------------------

yoneda-⌊_⌋
  :  {R : Set}
  → { _⇒_ : Set → Set → Set} ⦃ _ : Category _⇒_ ⦄
  → {F : Set → Set}
  → ({X : Set} → (R ⇒ X) → F X)
  → F R
yoneda-⌊ α ⌋ = α c-id

yoneda-lower = yoneda-⌊_⌋

yoneda-lower-M
  :  {R : Set}
  → {M : Set → Set} ⦃ _ : Monad M ⦄
  → ({X : Set} → (homₖ {M} R X) → M X)
  → M R
yoneda-lower-M = yoneda-lower

yoneda-⟦_⟧
  :  {R : Set}
  → { _⇒_ : Set → Set → Set} ⦃ c : Category _⇒_ ⦄
  → {F : Set → Set} ⦃ functor : CatFunctor F c set-Cat ⦄
  → F R
  → ({X : Set} → (R ⇒ X) → F X)
yoneda-⟦_⟧ ⦃ _ ⦄ ⦃ functor ⦄ fr rx = c-fmap ⦃ functor ⦄ rx fr

yoneda-lift = yoneda-⟦_⟧

yoneda-lift-M
  :  {R : Set}
  → {M : Set → Set} ⦃ _ : Monad M ⦄
  → M R
  → ({X : Set} → (homₖ {M} R X) → M X)
yoneda-lift-M = yoneda-lift

yoneda-lower-∘-lift-≡-Id
  :  {R : Set}
  → {hom : Set → Set → Set} ⦃ c : Category hom ⦄
  → {F : Set → Set} ⦃ functor : CatFunctor F c set-Cat ⦄
  → (fr : F R)
  → yoneda-lower ⦃ c ⦄ (yoneda-lift ⦃ c ⦄ ⦃ functor ⦄ fr) ≡ fr
yoneda-lower-∘-lift-≡-Id {R} {_} ⦃ c ⦄ {F} ⦃ functor ⦄ fr =
  yoneda-lower ⦃ c ⦄ (yoneda-lift ⦃ c ⦄ ⦃ functor ⦄ fr)
  ≡⟨ refl ⟩
  c-fmap ⦃ functor ⦄ (c-id ⦃ c ⦄) fr
  ≡⟨ cong (λ g → g fr) (c-fmap-id  ⦃ functor ⦄ {R}) ⟩
  fr
  ∎

yoneda-lower-∘-lift-M-≡-Id
  :  {R : Set}
  → {M : Set → Set} ⦃ monad : Monad M ⦄
  → (mr : M R)
  → yoneda-lower-M (yoneda-lift-M ⦃ monad ⦄ mr) ≡ mr
yoneda-lower-∘-lift-M-≡-Id {_} {M} mr = yoneda-lower-∘-lift-≡-Id {_} {homₖ {M}} mr

yoneda-lift-∘-lower-≡-Id
  :  {R : Set}
  → {hom : Set → Set → Set} ⦃ c : Category hom ⦄
  → {F : Set → Set} ⦃ functor : CatFunctor F c set-Cat ⦄
  → (α : {X : Set} → hom R X → F X)
  → (α-natural
        :  {A B : Set}
        → (f : hom A B)
        → (a : hom R A)
        → (α ∘ c-fmap ⦃ rep-Functor {hom} {R} ⦄ f) a ≡ (c-fmap ⦃ functor ⦄ f ∘ α) a
      )
  → {Y : Set}
  → (k : hom R Y)
  → yoneda-lift (yoneda-lower α) k ≡ α k
yoneda-lift-∘-lower-≡-Id {R} {hom} ⦃ c ⦄ ⦃ functor ⦄ α α-natural k =
  yoneda-lift (yoneda-lower α) k
  ≡⟨ refl ⟩
  c-fmap ⦃ functor ⦄ k (α c-id)
  ≡˘⟨ α-natural k c-id ⟩
  α (c-fmap ⦃ rep-Functor {hom} {R} ⦄ k c-id)
  ≡⟨ refl ⟩
  α (k ∘ᶜ c-id)
  ≡⟨ cong α (c-right-id k) ⟩
  α k
  ∎

yoneda-lift-∘-lower-M-≡-Id
  :  {R : Set}
  → {M : Set → Set} ⦃ monad : Monad M ⦄
  → (α : {X : Set} → homₖ {M} R X → M X)
  → (α-natural
        :  {A B : Set}
        → (f : homₖ {M} A B)
        → (a : homₖ {M} R A)
        → (α ∘ c-fmap ⦃ rep-Functor {homₖ {M}} {R} ⦄ f) a ≡ (c-fmap ⦃ kl-monad-Functor ⦄ f ∘ α) a
      )
  → {Y : Set}
  → (k : homₖ {M} R Y)
  → yoneda-lift-M (yoneda-lower-M α) k ≡ α k
yoneda-lift-∘-lower-M-≡-Id = yoneda-lift-∘-lower-≡-Id

eh-→-tf
  :  {A R : Set}
  → {M : Set → Set} ⦃ _ : Monad M ⦄
  → ({X : Set} → A → (R → M X) → M X)
  → (A → M R)
eh-→-tf {_} {R} β a = yoneda-lower-M {R} (β a)

tf-→-eh
  :  {A R : Set}
  → {M : Set → Set} ⦃ _ : Monad M ⦄
  → (A → M R)
  → ({X : Set} → A → (R → M X) → M X)
tf-→-eh dict a = yoneda-lift-M (dict a)

tf-→-eh-→-tf-≡-Id
  :  {A R : Set}
  → {M : Set → Set} ⦃ _ : Monad M ⦄
  → (dict : A → M R)
  → (a : A)
  → eh-→-tf (tf-→-eh dict) a ≡ dict a
tf-→-eh-→-tf-≡-Id dict a = yoneda-lower-∘-lift-M-≡-Id (dict a)

eh-→-tf-→-eh-≡-Id
  :  {A R : Set}
  → {M : Set → Set} ⦃ _ : Monad M ⦄
  → (β : {X : Set} → A → (R → M X) → M X)
  → (a : A)
  → (β-natural
      :  {S T : Set}
      → (f : S → M T)
      → (g : R → M S)
      → (β a ∘ (f ∘ₖ_)) g ≡ ((_≫= f) ∘ β a) g  -- kleisli 合成の自然性を仮定
      )
  → {Y : Set} → (k : R → M Y)
  → tf-→-eh (eh-→-tf β) a k ≡ β a k
eh-→-tf-→-eh-≡-Id β a β-natural k = yoneda-lift-∘-lower-M-≡-Id (β a) β-natural k
