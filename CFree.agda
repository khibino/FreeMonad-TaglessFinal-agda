open import Agda.Builtin.Equality using (_≡_; refl)

open import CF

open Functor ⦃...⦄

record Monad (M : Set → Set) : Set1 where
  field
    overlap ⦃ monad-functor ⦄ : Functor M
    --
    pure : {A : Set} → A → M A
    join : {A : Set} → M (M A) → M A
    --
    join-left-id
      :  {X : Set} → (mx : M X)
      → join (pure mx) ≡ mx
    join-right-id
      :  {X : Set} → (mx : M X)
      → join (fmap pure mx) ≡ mx
    join-assoc
      :  {X : Set} → (mmmx : M (M (M X)))
      → join (join mmmx) ≡ join (fmap join mmmx)

open Monad ⦃...⦄

infixl 2 _≫=_

_≫=_
  : {X Y : Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → M X → (X → M Y) → M Y
mx ≫= k = join (fmap k mx)

------------------------------------------------------------

data CFree (S : Set) (P : S → Set) (X : Set) : Set where
  Pure : X → CFree S P X
  Impure : CF S P (CFree S P X) → CFree S P X

-- functor
fmap-CFree
  :  {X Y : Set} {S : Set} {P : S → Set}
  → (X → Y) → CFree S P X → CFree S P Y
fmap-CFree f (Pure x)           = Pure (f x)
fmap-CFree f (Impure (cf s k))  = Impure (cf s λ p → fmap-CFree f (k p))

fmap-id-CFree
  :  {X : Set} {S : Set} {P : S → Set}
  → (fx : CFree S P X) → fmap-CFree (λ x → x) fx ≡ fx
fmap-id-CFree (Pure x)           = refl
fmap-id-CFree (Impure (cf s k))  =
  cong (Impure ∘ cf s) (funext λ p → fmap-id-CFree (k p))

fmap-compose-CFree
  :  {S : Set} {P : S → Set} {A B C : Set}
  → (f : B → C) → (g : A → B) → (x : CFree S P A)
  → fmap-CFree (f ∘ g) x ≡ (fmap-CFree f ∘ fmap-CFree g) x
fmap-compose-CFree f g (Pure x)           = refl
fmap-compose-CFree f g (Impure (cf s k))  =
  cong (Impure ∘ cf s) (funext λ p → fmap-compose-CFree f g (k p))

instance
  functor-CFree : {S : Set} {P : S → Set} → Functor (CFree S P)
  fmap          ⦃ functor-CFree ⦄ = fmap-CFree
  fmap-id       ⦃ functor-CFree ⦄ = fmap-id-CFree
  fmap-compose  ⦃ functor-CFree ⦄ = fmap-compose-CFree

-- monad
join-CFree
  : {X : Set} {S : Set} {P : S → Set}
  → CFree S P (CFree S P X) → CFree S P X
join-CFree (Pure x)           = x
join-CFree (Impure (cf s k))  = Impure (cf s λ p → join-CFree (k p))

join-left-id-CFree
  : {X : Set} {S : Set} {P : S → Set} → (mx : CFree S P X)
  → join-CFree (Pure mx) ≡ mx
join-left-id-CFree mx = refl

join-right-id-CFree
  : {X : Set} {S : Set} {P : S → Set} → (mx : CFree S P X)
  → join-CFree (fmap Pure mx) ≡ mx
join-right-id-CFree (Pure x)           = refl
join-right-id-CFree (Impure (cf s k))  =
  cong (Impure ∘ cf s) (funext λ p → join-right-id-CFree (k p))

join-assoc-CFree
  :  {X : Set} {S : Set} {P : S → Set}
  → (mmmx : CFree S P (CFree S P (CFree S P X)))
  → join-CFree (join-CFree mmmx) ≡ join-CFree (fmap-CFree join-CFree mmmx)
join-assoc-CFree (Pure mmx)         = refl
join-assoc-CFree (Impure (cf s k))  =
  cong (Impure ∘ cf s) (funext λ p → join-assoc-CFree (k p))

instance
  monad-CFree : {S : Set} {P : S → Set} → Monad (CFree S P)
  --
  monad-functor ⦃ monad-CFree ⦄ = functor-CFree
  --
  pure          ⦃ monad-CFree ⦄ = Pure
  join          ⦃ monad-CFree ⦄ = join-CFree
  join-left-id  ⦃ monad-CFree ⦄ = join-left-id-CFree
  join-right-id ⦃ monad-CFree ⦄ = join-right-id-CFree
  join-assoc    ⦃ monad-CFree ⦄ = join-assoc-CFree

liftF : {S : Set} {P : S → Set} {X : Set} → CF S P X → CFree S P X
liftF (cf s k) = Impure (cf s (Pure ∘ k))

foldFree
  :  {S : Set} {P : S → Set} {M : Set → Set}
  → ({X : Set} → CF S P X → M X)
  → (⦃ _ : Monad M ⦄ {A : Set} → CFree S P A → M A)
foldFree σ (Pure x)           = pure x
foldFree σ (Impure (cf s k))  = join (σ (cf s (λ p → foldFree σ (k p))))

postulate
  σ-natural
    :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Functor M ⦄ {A B : Set}
    → (g : A → B)
    → (σ : {X : Set} → CF S P X → M X)
    → (a : CF S P A)
    → (σ ∘ fmap g) a ≡ (fmap g ∘ σ) a

{-
** foldFree の停止性チェックを通らない再帰を書き換える **
** 書き換えの正当性の証明 **

  (fmap_m (foldFree σ) ∘ σ) op
  {- σ の自然性 -}
≡ (σ ∘ fmap_f (foldFree σ)) op
  {- CF の定義, ∘ の定義 -}
≡ σ (fmap_f (foldFree σ) (cf s k))
  {- fmap-CF の定義 -}
≡ σ (cf s (λ p → foldFree σ (k p)))
 -}
foldFree-Impure-case-equiv
  :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → (σ : {X : Set} → CF S P X → M X)
  → {A : Set}
  → (op : CF S P (CFree S P A))
  → foldFree σ {A} (Impure op) ≡ join ((fmap (foldFree σ) ∘ σ) op)
foldFree-Impure-case-equiv {S} {P} {M} σ op@(cf s k)
  {-    foldFree σ (Impure (cf s k))
        -- foldFree の定義 Impure の場合
     =  join (σ (cf s (λ p → foldFree σ (k p))))
        -- fmap {CF S P} の定義
     =  join ((σ ∘ fmap {CF S P} (foldFree σ)) (cf s k))  -}
  with  (σ ∘ fmap {CF S P} (foldFree σ)) op
            | σ-natural (foldFree σ) σ op
... | .((fmap {M} (foldFree σ) ∘ σ) op)
            | refl
 = refl

------------------------------------------------------------

Φ :  {S : Set} {P : S → Set} {M : Set → Set}
  → ({X : Set} → CF S P X → M X)
  → ( ⦃ _ : Monad M ⦄ {A : Set} → CFree S P A → M A)
Φ = foldFree

Ψ :  {S : Set} {P : S → Set} {M : Set → Set}
  → ({A : Set} → CFree S P A → M A)
  → ({X : Set} → CF S P X → M X)
Ψ h x = h (liftF x)

------------------------------------------------------------

{- (∘ liftF) ∘ foldFree ≡ id -}
Ψ-∘-Φ≡id
  :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → {Z : Set}
  → (σ : {X : Set} → CF S P X → M X)
  → (z : CF S P Z)
  → Ψ (Φ σ) z ≡ σ z
Ψ-∘-Φ≡id {S} {P} {M} σ z@(cf s k)
  {-    Ψ (Φ σ) z
        -- Ψ と Φ の定義
     =  foldFree σ (liftF (cf s k))
        -- liftF の定義
     =  foldFree σ (Impure (cf s (Pure ∘ k)))
        -- foldFree の定義. Impure の場合
     =  join (σ (cf s (λ p → foldFree σ ((Pure ∘ k) p))))
        -- foldFree の定義. Pure の場合
     =  join (σ (cf s (λ p → pure (k p))))
        -- fmap {CF S P} の定義
     =  join ((σ ∘ fmap (pure {M})) (cf s k))  -}
  with  (σ ∘ fmap (pure {M})) (cf s k)
            | σ-natural (pure {M}) σ z
... | .((fmap (pure {M}) ∘ σ) z)
            | refl
  {-    join (fmap {M} (pure {M}) (σ z))     -}
  = join-right-id (σ z)
  {- =  σ z                                  -}

------------------------------------------------------------

{- foldFree ∘ (∘ liftF) ≡ id -}
Φ-∘-Ψ≡id
  :  {S : Set} {P : S → Set} {M : Set → Set} ⦃ _ : Monad M ⦄
  → {Z : Set}
  → (h : {X : Set} → CFree S P X → M X)
  → (morph-pure : {X : Set} → (x : X) → (h ∘ pure) x ≡ pure x)
  → (morph-join
        :  {X : Set}
        → (ff : CFree S P (CFree S P X))
        → (h {X} ∘ join {CFree S P}) ff ≡ (join {M} ∘ h ∘ fmap h) ff)
  → (z : CFree S P Z)
  → Φ (Ψ h) z ≡ h z
Φ-∘-Ψ≡id             h morph-pure morph-join    (Pure x)
  rewrite morph-pure x
  = refl
Φ-∘-Ψ≡id {S} {P} {M} h morph-pure morph-join z@(Impure (cf s k))
  = proof
  where
    ih-k
      :  (p : P s)
      →  Pure {S} {P} (foldFree (h ∘ liftF) (k p)) ≡ Pure (h (k p))
    ih-k p = cong Pure (Φ-∘-Ψ≡id h morph-pure morph-join (k p))

    proof : Φ (Ψ h) z ≡ h z
    proof
      {-    Φ (Ψ h) z
            -- Φ と Ψ の定義
         =  foldFree (h ∘ liftF) (Impure (cf s k))
            -- foldFree の定義. Impure の場合
         =  join (h (Impure (cf s
              (λ p → Pure (foldFree (h ∘ liftF) (k p))))))  -}
      with  (λ p → Pure (foldFree (h ∘ liftF) (k p)))
                | funext ih-k
    ... | .( λ p → Pure (h (k p)) )
                | refl
      {-    join {M} (h (Impure (cf s
              (λ p → Pure (h (k p))))))
            -- fmap の定義. Pure の場合
         =  join {M} (h (Impure (cf s
              (λ p → fmap h (Pure (k p))))))
            -- fmap の定義. Impre の場合
         =  (join {M} ∘ h ∘ fmap h)
              (Impure (cf s (Pure ∘ k)))                     -}
      with  (join {M} ∘ h ∘ fmap {CFree S P} h) (Impure (cf s (Pure ∘ k)))
                | morph-join (Impure (cf s (Pure ∘ k)))
    ... | .((h ∘ join {CFree S P}) (Impure (cf s (Pure ∘ k))))
                | refl
      {-    (h ∘ join {CFree S P}) (Impure (cf s (Pure ∘ k)))
            -- join の定義. Impure の場合
            h (Impure (cf s (λ p → join ((Pure ∘ k) p))))
            -- join の定義. Pure の場合
            h (Impure (cf s k))                              -}
      = refl

------------------------------------------------------------

foldFree-monad-morph-pure
  :  {S : Set} {P : S → Set} {M : Set → Set}
  → (σ : {X : Set} → CF S P X → M X)
  → {Z : Set}
  → (z : Z)
  → ⦃ _ : Monad M ⦄
  → foldFree σ (pure z) ≡ pure z
foldFree-monad-morph-pure σ z = refl

foldFree-monad-morph-join
  :  {S : Set} {P : S → Set} {M : Set → Set}
  → (σ : {X : Set} → CF S P X → M X)
  → {Z : Set}
  → (z : CFree S P (CFree S P Z))
  → ⦃ monadM : Monad M ⦄
  → (foldFree σ ∘ join {CFree S P}) z ≡ (join {M} ∘ foldFree σ ∘ fmap (foldFree σ)) z
foldFree-monad-morph-join σ (Pure x)
  rewrite join-left-id (foldFree σ x)
  = refl
foldFree-monad-morph-join {S} {P} {M} σ {Z} z@(Impure (cf s k))
  = proof
  where
    ih-k
      :  (p : P s)
      → (foldFree σ ∘ join {CFree S P}) (k p) ≡
         (join {M} ∘ foldFree σ ∘ fmap (foldFree σ)) (k p)
    ih-k p = foldFree-monad-morph-join σ (k p)
    --
    fmm : CF S P (M (M Z))
    fmm = cf s λ p → foldFree σ (fmap {CFree S P} (foldFree σ) (k p))
    --
    proof
      :  (foldFree σ ∘ join {CFree S P}) z ≡
         (join {M} ∘ foldFree σ ∘ fmap (foldFree σ)) z
    proof
      {-    (foldFree σ ∘ join {CFree S P}) (Impure (cf s k))
            -- join の定義. Impure の場合
         =  foldFree σ (Impure (cf s λ p → join (k p)))
            -- foldFree の定義. Impure の場合
         =  join (σ (cf s (λ p → foldFree σ (join (k p)))))  -}
      with (λ p → (foldFree σ ∘ join) (k p))
                | funext ih-k
    ... | .(λ p → (join {M} ∘ foldFree σ ∘ fmap (foldFree σ)) (k p))
                | refl
      with  (σ ∘ fmap {CF S P} join) fmm
                | σ-natural (join {M}) σ fmm
    ... |  .((fmap {M} join ∘ σ) fmm)
                | refl
      with  join {M} (fmap join (σ fmm))
                | join-assoc (σ fmm)
    ... | .(join {M} (join {M} (σ fmm)))
                | refl
      {-    join {M} (join {M} (σ (cf s (λ p →
              foldFree σ (fmap {CFree S P} (foldFree σ) (k p))))))
            -- foldFree の定義. Impure の場合
            (join {M} ∘ foldFree σ)
              (Impure (cf s (λ p → fmap (foldFree σ) (k p))))
            -- fmap の定義. Impure の場合
            (join {M} ∘ foldFree σ ∘ fmap (foldFree σ))
              (Impure (cf s k))                               -}
      = refl

postulate
  foldFree-σ-natural
    :  {S : Set} {P : S → Set} {M : Set → Set} {A B : Set}
    → (g : A → B)
    → (σ : {X : Set} → CF S P X → M X)
    → (a : CFree S P A)
    → ⦃ _ : Monad M ⦄
    → (foldFree σ ∘ fmap g) a ≡ (fmap g ∘ foldFree σ) a

foldFree-monad-morph-≫=
  :  {S : Set} {P : S → Set} {M : Set → Set}
  → (σ : {X : Set} → CF S P X → M X)
  → {Y Z : Set}
  → (fy : CFree S P Y) → (k : Y → CFree S P Z)
  → ⦃ monadM : Monad M ⦄
  → foldFree σ (fy ≫= k) ≡ (foldFree σ fy ≫= foldFree σ ∘ k)
foldFree-monad-morph-≫= σ fy k
  {-    foldFree σ (fy ≫= k)
        -- (≫= k) = join ∘ fmap k
        foldFree σ (join (fmap k fy))     -}
  with  foldFree σ (join (fmap k fy))
            | foldFree-monad-morph-join σ (fmap k fy)
... | .(join (foldFree σ (fmap (foldFree σ) (fmap k fy))))
            | refl
  with  (fmap (foldFree σ) ∘ fmap k) fy
            | fmap-compose (foldFree σ) k fy
... | .( fmap (foldFree σ ∘ k) fy )
            | refl
  with  foldFree σ (fmap (foldFree σ ∘ k) fy)
            | foldFree-σ-natural (foldFree σ ∘ k) σ fy
... | .(fmap (foldFree σ ∘ k) (foldFree σ fy))
            | refl
  {-    join {M} (fmap {M} (foldFree σ ∘ k) (foldFree σ fy))
        --  (≫= g) = join ∘ fmap g
        foldFree σ fy ≫= foldFree σ ∘ k  -}
  = refl

------------------------------------------------------------

{-
プログラムの対応関係

**次の 2つが等しい**

* Free Monad のプログラム全体を解釈した結果
    * foldFree σ (liftF cfy ≫= λ y → liftF (cfk y))
* それぞれの部品を解釈して連結した結果
    * σ cfy ≫= λ y →  σ (cfk y)
 -}
foldFree-correspondence-≫=
  :  {S : Set} {P : S → Set} {M : Set → Set}
  → (σ : {X : Set} → CF S P X → M X)
  → {Y Z : Set}
  → (cfy : CF S P Y) → (cfk : Y → CF S P Z)
  → ⦃ _ : Monad M ⦄
  → foldFree σ (liftF cfy ≫= λ y → liftF (cfk y))
     ≡
     ( σ cfy ≫= λ y →  σ (cfk y) )
foldFree-correspondence-≫= σ cfy cfk
  with  foldFree σ (liftF cfy ≫= λ y → liftF (cfk y))
            | foldFree-monad-morph-≫= σ (liftF cfy) (λ y → liftF (cfk y))
... | .(foldFree σ (liftF cfy) ≫= λ y → foldFree σ (liftF (cfk y)))
            | refl
  with  foldFree σ (liftF cfy)
            | Ψ-∘-Φ≡id σ cfy
... | .(σ cfy)
            | refl
  with (λ y → foldFree σ (liftF (cfk y)))
            | funext (λ y → Ψ-∘-Φ≡id σ (cfk y))
... | .(λ y → σ (cfk y))
            | refl
  = refl
