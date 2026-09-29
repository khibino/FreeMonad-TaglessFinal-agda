open import Agda.Builtin.Equality using (_≡_; refl)

open import CF
open import CFree


open Functor ⦃...⦄

------------------------------------------------------------

{- {X : Set} → (R → X) → M X ≅ M R  -}

yoneda-⌊_⌋
  :  {R : Set} {M : Set → Set}
  → ({X : Set} → (R → X) → M X)
  → M R
yoneda-⌊ α ⌋  = α λ r → r

yoneda-lower = yoneda-⌊_⌋

yoneda-⟦_⟧
  :  {R : Set} {M : Set → Set} ⦃ _ : Functor M ⦄
  → M R
  → ({X : Set} → (R → X) → M X)
yoneda-⟦ mr ⟧ = λ k → fmap k mr

yoneda-lift = yoneda-⟦_⟧

yoneda-⌊⌋-∘-⟦⟧-≡-Id
  : {R : Set} {M : Set → Set} ⦃ _ : Functor M ⦄
  → (mr : M R)
  → yoneda-⌊_⌋ yoneda-⟦ mr ⟧ ≡ mr
yoneda-⌊⌋-∘-⟦⟧-≡-Id = fmap-id

yoneda-⟦⟧-∘-⌊⌋-≡-Id
  : {R : Set} {M : Set → Set} ⦃ _ : Functor M ⦄
  → (α : {X : Set} → (R → X) → M X)
  → (α-natural
        :  {A B : Set}
        → (f : A → B)
        → (a : R → A)
        → (α ∘ (λ k → f ∘ k)) a ≡ (fmap f ∘ α) a)
  → {Y : Set}
  → (k : R → Y)
  → yoneda-⟦_⟧ yoneda-⌊ α ⌋ k ≡ α k
yoneda-⟦⟧-∘-⌊⌋-≡-Id α α-natural k = sym (α-natural k (λ r → r))

------------------------------------------------------------

⟦_⟧₁
  :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Functor M ⦄
  → ((s : S) → M (P s))
  → ({X : Set} → CF S P X → M X)
⟦ dict ⟧₁ (cf s k) = yoneda-⟦ dict s ⟧ k

interpret₁ = ⟦_⟧₁

⌊_⌋₁
  :  {S : Set} {P : S → Set} {M : Set → Set}
  → ({X : Set} → CF S P X → M X)
  → ((s : S) → M (P s))
⌊ σ ⌋₁ s = yoneda-⌊ σ ∘ cf s ⌋

extract₁ = ⌊_⌋₁

⌊⌋₁-∘-⟦⟧₁-≡-Id
  :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Functor M ⦄
  → (dict : (s : S) → M (P s))
  → ((s : S) → ⌊_⌋₁ ⟦ dict ⟧₁ s ≡ dict s)
⌊⌋₁-∘-⟦⟧₁-≡-Id dict s = yoneda-⌊⌋-∘-⟦⟧-≡-Id (dict s)

⟦⟧₁-∘-⌊⌋₁-≡-Id
  :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Functor M ⦄
  → (σ : {X : Set} → CF S P X → M X)
  → {Z : Set} → (cfz : CF S P Z)
  → ⟦_⟧₁ ⌊ σ ⌋₁ cfz  ≡ σ cfz
⟦⟧₁-∘-⌊⌋₁-≡-Id {_} {P} {M} σ (cf s k) =
    yoneda-⟦⟧-∘-⌊⌋-≡-Id α α-natural k
  where
    α : {X : Set} → (P s → X) → M X
    α = σ ∘ cf s
    α-natural
      : {A B : Set}
      → (f : A → B)
      → (a : P s → A)
      → (α ∘ (λ k → f ∘ k)) a ≡ (fmap f ∘ α) a
    α-natural f a = σ-natural f σ (cf s a)

------------------------------------------------------------

open Monad ⦃...⦄

⟦_⟧
  :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → ((s : S) → M (P s))
  → ({X : Set} → CFree S P X → M X)
⟦ dict ⟧ = foldFree ⟦ dict ⟧₁

interpret = ⟦_⟧

⌊_⌋
  : {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → ({X : Set} → CFree S P X → M X)
  → ((s : S) → M (P s))
⌊ interp ⌋ = ⌊ interp ∘ liftF ⌋₁

extract = ⌊_⌋

⌊⌋-∘-⟦⟧-≡-Id
  : {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → (dict : (s : S) → M (P s))
  → (s : S)
  → ⌊_⌋ ⟦ dict ⟧ s ≡ dict s
⌊⌋-∘-⟦⟧-≡-Id {S} {P} dict s
  = trans
    (Ψ-∘-Φ≡id ⟦ dict ⟧₁ (cf s (λ z → z)))
    (⌊⌋₁-∘-⟦⟧₁-≡-Id dict s)

⟦⟧-∘-⌊⌋-≡-Id
  : {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → (h : {X : Set} → CFree S P X → M X)
  → (morph-pure : {X : Set} → (x : X) → (h ∘ pure) x ≡ pure x)
  → (morph-join
        :  {X : Set}
        → (ff : CFree S P (CFree S P X))
        → (h {X} ∘ join {CFree S P}) ff ≡ (join {M} ∘ h ∘ fmap h) ff)
  → {Z : Set}
  → (f : CFree S P Z)
  → ⟦_⟧ ⌊ h ⌋ f ≡ h f
⟦⟧-∘-⌊⌋-≡-Id {S} {P} {M} h morph-pure morph-join f
  = trans
    (cong
       (λ (σ : {X : Set} → CF S P X → M X) → foldFree σ f)
       (implicit-funext λ {Z} → funext λ cfz →
         ⟦⟧₁-∘-⌊⌋₁-≡-Id (h ∘ liftF) cfz))
    (Φ-∘-Ψ≡id h morph-pure morph-join f)

------------------------------------------------------------

record MonadTFC (S : Set) (P : S → Set) (M : Set → Set) : Set1 where
  field
    overlap ⦃ tf-monad ⦄ : Monad M
    --
    tf-dict : (s : S) → M (P s)

open MonadTFC ⦃...⦄

from-TF
  :  {S : Set} {P : S → Set} {M : Set → Set}
  → MonadTFC S P M
  → ({X : Set} → CF S P X → M X)
from-TF record { tf-monad = tf-monad₁ ; tf-dict = dict } = ⟦ dict ⟧₁

to-TF
  :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → ({X : Set} → CF S P X → M X)
  → MonadTFC S P M
to-TF {S} {P} {M} ⦃ monad ⦄ σ =
    record
    { tf-monad   = monad
    ; tf-dict  = ⌊ σ ⌋₁
    }

to-∘-from-TF
  :  {S : Set} {P : S → Set} {M : Set → Set}
  → (tf : MonadTFC S P M)
  → to-TF (from-TF tf) ≡ tf
to-∘-from-TF {S} {P} {M} tf@(record { tf-monad = monad ; tf-dict = dict })
  = cong mk-tf (funext (⌊⌋₁-∘-⟦⟧₁-≡-Id dict))
  where
    mk-tf : ((s : S) → M (P s)) → MonadTFC S P M
    mk-tf = λ a → record { tf-monad = monad ; tf-dict = a}

from-∘-to-TF
  :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → (σ : {X : Set} → CF S P X → M X)
  → {Z : Set} → (cfz : CF S P Z)
  → from-TF (to-TF σ) cfz  ≡ σ cfz
from-∘-to-TF σ cfz = ⟦⟧₁-∘-⌊⌋₁-≡-Id σ cfz
