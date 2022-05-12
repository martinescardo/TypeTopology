Martin Escardo, 2012-

Expanded on demand whenever a general equivalence is needed.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import Two-Properties
open import Plus-Properties
open import UF-Base
open import UF-Equiv
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-PropIndexedPiSigma

module UF-EquivalenceExamples where

curry-uncurry' : funext 𝓤 (𝓥 ⊔ 𝓦)
               → funext (𝓤 ⊔ 𝓥) 𝓦
               → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : (Σ x ꞉ X , Y x) → 𝓦 ̇ }
               → Π Z ≃ (Π x ꞉ X , Π y ꞉ Y x , Z (x , y))
curry-uncurry' {𝓤} {𝓥} {𝓦} fe fe' {X} {Y} {Z} = qinveq c (u , uc , cu)
 where
  c : (w : Π Z) → ((x : X) (y : Y x) → Z (x , y))
  c f x y = f (x , y)

  u : ((x : X) (y : Y x) → Z (x , y)) → Π Z
  u g (x , y) = g x y

  cu : ∀ g → c (u g) ≡ g
  cu g = dfunext fe (λ x → dfunext (lower-funext 𝓤 𝓦 fe') (λ y → refl))
  uc : ∀ f → u (c f) ≡ f
  uc f = dfunext fe' (λ w → refl)

curry-uncurry : (fe : FunExt)
              → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : (Σ x ꞉ X , Y x) → 𝓦 ̇ }
              → Π Z ≃ (Π x ꞉ X , Π y ꞉ Y x , Z (x , y))
curry-uncurry {𝓤} {𝓥} {𝓦} fe = curry-uncurry' (fe 𝓤 (𝓥 ⊔ 𝓦)) (fe (𝓤 ⊔ 𝓥) 𝓦)

Σ-≡-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
      → (σ ≡ τ) ≃ (Σ p ꞉ pr₁ σ ≡ pr₁ τ , transport A p (pr₂ σ) ≡ pr₂ τ)
Σ-≡-≃ {𝓤} {𝓥} {X} {A} {x , a} {y , b} = qinveq from-Σ-≡ (to-Σ-≡ , ε , η)
 where
  η : (σ : Σ p ꞉ x ≡ y , transport A p a ≡ b) → from-Σ-≡ (to-Σ-≡ σ) ≡ σ
  η (refl , refl) = refl
  ε : (q : x , a ≡ y , b) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  ε refl = refl

×-≡-≃ : {X : 𝓤 ̇ } {A : 𝓥 ̇ } {σ τ : X × A}
      → (σ ≡ τ) ≃ (pr₁ σ ≡ pr₁ τ) × (pr₂ σ ≡ pr₂ τ)
×-≡-≃ {𝓤} {𝓥} {X} {A} {x , a} {y , b} = qinveq from-×-≡' (to-×-≡' , (ε , η))
 where
  η : (t : (x ≡ y) × (a ≡ b)) → from-×-≡' (to-×-≡' t) ≡ t
  η (refl , refl) = refl

  ε : (u : x , a ≡ y , b) → to-×-≡' (from-×-≡' u) ≡ u
  ε refl = refl

Σ-assoc : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : Σ Y → 𝓦 ̇ }
        → Σ Z ≃ (Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y))
Σ-assoc {𝓤} {𝓥} {𝓦} {X} {Y} {Z} = qinveq c (u , (λ τ → refl) , (λ σ → refl))
 where
  c : Σ Z → Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y)
  c ((x , y) , z) = (x , (y , z))

  u : (Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y)) → Σ Z
  u (x , (y , z)) = ((x , y) , z)

Σ-flip : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → Y → 𝓦 ̇ }
       → (Σ x ꞉ X , Σ y ꞉ Y , A x y) ≃ (Σ y ꞉ Y , Σ x ꞉ X , A x y)
Σ-flip {𝓤} {𝓥} {𝓦} {X} {Y} {A} = qinveq f (g , ε , η)
 where
  f : (Σ x ꞉ X , Σ y ꞉ Y , A x y) → (Σ y ꞉ Y , Σ x ꞉ X , A x y)
  f (x , y , p) = y , x , p

  g : (Σ y ꞉ Y , Σ x ꞉ X , A x y) → (Σ x ꞉ X , Σ y ꞉ Y , A x y)
  g (y , x , p) = x , y , p

  ε : ∀ σ → g (f σ) ≡ σ
  ε (x , y , p) = refl

  η : ∀ τ → f (g τ) ≡ τ
  η (y , x , p) = refl

Σ-cong : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Y' : X → 𝓦 ̇ }
       → ((x : X) → Y x ≃ Y' x) → Σ Y ≃ Σ Y'
Σ-cong {𝓤} {𝓥} {𝓦} {X} {Y} {Y'} φ = (F , (G , FG) , (H , HF))
 where
  f : (x : X) → Y x → Y' x
  f x = pr₁ (φ x)

  g : (x : X) → Y' x → Y x
  g x = pr₁ (pr₁ (pr₂ (φ x)))

  fg : (x : X) (y' : Y' x) → f x (g x y') ≡ y'
  fg x = pr₂ (pr₁ (pr₂ (φ x)))

  h : (x : X) → Y' x → Y x
  h x = pr₁ (pr₂ (pr₂ (φ x)))

  hf : (x : X) (y : Y x) → h x (f x y) ≡ y
  hf x = pr₂ (pr₂ (pr₂ (φ x)))

  F : Σ Y → Σ Y'
  F (x , y) = x , f x y

  G : Σ Y' → Σ Y
  G (x , y') = x , g x y'

  H : Σ Y' → Σ Y
  H (x , y') = x , h x y'

  FG : (w' : Σ Y') → F (G w') ≡ w'
  FG (x , y') = to-Σ-≡' (fg x y')

  HF : (w : Σ Y) → H (F w) ≡ w
  HF (x , y) = to-Σ-≡' (hf x y)

ΠΣ-distr-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Π x ꞉ X , Σ a ꞉ A x , P x a) ≃ (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))
ΠΣ-distr-≃ {𝓤} {𝓥} {𝓦} {X} {A} {P} = qinveq ΠΣ-distr (ΠΣ-distr-back , ε , η)
 where
  η :  ΠΣ-distr {𝓤} {𝓥} {𝓦} {X} {A} {P} ∘ ΠΣ-distr-back ∼ id
  η _ = refl

  ε : ΠΣ-distr-back ∘ ΠΣ-distr ∼ id
  ε _ = refl

Σ+ : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
   → (Σ x ꞉ X , A x + B x)
   ≃ ((Σ x ꞉ X , A x) + (Σ x ꞉ X , B x))
Σ+ X A B = qinveq f (g , η , ε)
 where
  f : (Σ x ꞉ X , A x + B x) → (Σ x ꞉ X , A x) + (Σ x ꞉ X , B x)
  f (x , inl a) = inl (x , a)
  f (x , inr b) = inr (x , b)

  g : ((Σ x ꞉ X , A x) + (Σ x ꞉ X , B x)) → (Σ x ꞉ X , A x + B x)
  g (inl (x , a)) = x , inl a
  g (inr (x , b)) = x , inr b

  η : g ∘ f ∼ id
  η (x , inl a) = refl
  η (x , inr b) = refl

  ε : f ∘ g ∼ id
  ε (inl (x , a)) = refl
  ε (inr (x , b)) = refl

\end{code}

The following name is badly chosen, and probably should have been used
for the above:

\begin{code}

Σ+distr : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (A : X + Y → 𝓦 ̇ )
        → (Σ x ꞉ X , A (inl x)) + (Σ y ꞉ Y , A (inr y))
        ≃ (Σ z ꞉ X + Y , A z)
Σ+distr X Y A = qinveq f (g , η , ε)
 where
  f : (Σ x ꞉ X , A (inl x)) + (Σ y ꞉ Y , A (inr y)) → (Σ z ꞉ X + Y , A z)
  f (inl (x , a)) = inl x , a
  f (inr (y , a)) = inr y , a

  g : (Σ z ꞉ X + Y , A z) → (Σ x ꞉ X , A (inl x)) + (Σ y ꞉ Y , A (inr y))
  g (inl x , a) = inl (x , a)
  g (inr y , a) = inr (y , a)

  η : g ∘ f ∼ id
  η (inl _) = refl
  η (inr _) = refl

  ε : f ∘ g ∼ id
  ε (inl _ , _) = refl
  ε (inr _ , _) = refl

Π-cong : funext 𝓤 𝓥
       → funext 𝓤 𝓦
       → (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) (Y' : X → 𝓦 ̇ )
       → ((x : X) → Y x ≃ Y' x) → Π Y ≃ Π Y'
Π-cong fe fe' X Y Y' φ = (F , (G , FG) , (H , HF))
 where
  f : (x : X) → Y x → Y' x
  f x = pr₁ (φ x)

  g : (x : X) → Y' x → Y x
  g x =  pr₁ (pr₁ (pr₂ (φ x)))

  fg : (x : X) (y' : Y' x) → f x (g x y') ≡ y'
  fg x = pr₂ (pr₁ (pr₂ (φ x)))

  h : (x : X) → Y' x → Y x
  h x = pr₁ (pr₂ (pr₂ (φ x)))

  hf : (x : X) (y : Y x) → h x (f x y) ≡ y
  hf x = pr₂ (pr₂ (pr₂ (φ x)))

  F : ((x : X) → Y x) → ((x : X) → Y' x)
  F = λ z x → pr₁ (φ x) (z x)

  G : ((x : X) → Y' x) → (x : X) → Y x
  G u x = g x (u x)

  H : ((x : X) → Y' x) → (x : X) → Y x
  H u' x = h x (u' x)

  FG :  (w' : ((x : X) → Y' x)) → F (G w') ≡ w'
  FG w' = dfunext fe' FG'
   where
    FG' : (x : X) → F (G w') x ≡ w' x
    FG' x = fg x (w' x)

  HF : (w : ((x : X) → Y x)) → H (F w) ≡ w
  HF w = dfunext fe GF'
   where
    GF' : (x : X) → H (F w) x ≡ w x
    GF' x = hf x (w x)

\end{code}

An application of Π-cong is the following:

\begin{code}

≃-funext₂ : funext 𝓤 (𝓥 ⊔ 𝓦)
          → funext 𝓥 𝓦
          → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : (x : X) → Y x → 𝓦 ̇ }
            (f g : (x : X) (y : Y x) → A x y) → (f ≡ g) ≃ (∀ x y → f x y ≡ g x y)
≃-funext₂ fe fe' {X} f g =
 (f ≡ g)            ≃⟨ ≃-funext fe f g ⟩
 (f ∼ g)            ≃⟨ Π-cong fe fe X
                        (λ x → f x ≡ g x)
                        (λ x → f x ∼ g x)
                        (λ x → ≃-funext fe' (f x) (g x))⟩
 (∀ x → f x ∼ g x)  ■

𝟙-lneutral : {Y : 𝓤 ̇ } → 𝟙 {𝓥} × Y ≃ Y
𝟙-lneutral {𝓤} {𝓥} {Y} = qinveq f (g , ε , η)
 where
   f : 𝟙 × Y → Y
   f (o , y) = y

   g : Y → 𝟙 × Y
   g y = (⋆ , y)

   η : ∀ x → f (g x) ≡ x
   η y = refl

   ε : ∀ z → g (f z) ≡ z
   ε (o , y) = ap (_, y) (𝟙-is-prop ⋆ o)

×-comm : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × Y ≃ Y × X
×-comm {𝓤} {𝓥} {X} {Y} = qinveq f (g , ε , η)
 where
  f : X × Y → Y × X
  f (x , y) = (y , x)

  g : Y × X → X × Y
  g (y , x) = (x , y)

  η : ∀ z → f (g z) ≡ z
  η z = refl

  ε : ∀ t → g (f t) ≡ t
  ε t = refl

𝟙-rneutral : {Y : 𝓤 ̇ } → Y × 𝟙 {𝓥} ≃ Y
𝟙-rneutral {𝓤} {𝓥} {Y} = Y × 𝟙 ≃⟨ ×-comm ⟩
                          𝟙 × Y ≃⟨ 𝟙-lneutral {𝓤} {𝓥} ⟩
                          Y     ■

+comm : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X + Y ≃ Y + X
+comm {𝓤} {𝓥} {X} {Y} = qinveq f (g , η , ε)
 where
   f : X + Y → Y + X
   f (inl x) = inr x
   f (inr y) = inl y

   g : Y + X → X + Y
   g (inl y) = inr y
   g (inr x) = inl x

   ε : (t : Y + X) → (f ∘ g) t ≡ t
   ε (inl y) = refl
   ε (inr x) = refl

   η : (u : X + Y) → (g ∘ f) u ≡ u
   η (inl x) = refl
   η (inr y) = refl

𝟘-rneutral : {X : 𝓤 ̇ } → X ≃ X + 𝟘 {𝓥}
𝟘-rneutral {𝓤} {𝓥} {X} = qinveq f (g , η , ε)
 where
   f : X → X + 𝟘
   f = inl

   g : X + 𝟘 → X
   g (inl x) = x
   g (inr y) = 𝟘-elim y

   ε : (y : X + 𝟘) → (f ∘ g) y ≡ y
   ε (inl x) = refl
   ε (inr y) = 𝟘-elim y

   η : (x : X) → (g ∘ f) x ≡ x
   η x = refl

𝟘-rneutral' : {X : 𝓤 ̇ } → X + 𝟘 {𝓥} ≃ X
𝟘-rneutral' {𝓤} {𝓥} = ≃-sym (𝟘-rneutral {𝓤} {𝓥})

𝟘-lneutral : {X : 𝓤 ̇ } → 𝟘 {𝓥} + X ≃ X
𝟘-lneutral {𝓤} {𝓥} {X} = (𝟘 + X) ≃⟨ +comm ⟩
                         (X + 𝟘) ≃⟨ 𝟘-rneutral' {𝓤} {𝓥} ⟩
                         X       ■

one-𝟘-only : 𝟘 {𝓤} ≃ 𝟘 {𝓥}
one-𝟘-only = qinveq 𝟘-elim (𝟘-elim , 𝟘-induction , 𝟘-induction)

one-𝟙-only : (𝓤 𝓥 : Universe) → 𝟙 {𝓤} ≃ 𝟙 {𝓥}
one-𝟙-only _ _ = unique-to-𝟙 , (unique-to-𝟙 , (λ {⋆ → refl})) , (unique-to-𝟙 , (λ {⋆ → refl}))

+assoc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → (X + Y) + Z ≃ X + (Y + Z)
+assoc {𝓤} {𝓥} {𝓦} {X} {Y} {Z} = qinveq f (g , η , ε)
 where
   f : (X + Y) + Z → X + (Y + Z)
   f (inl (inl x)) = inl x
   f (inl (inr y)) = inr (inl y)
   f (inr z)       = inr (inr z)

   g : X + (Y + Z) → (X + Y) + Z
   g (inl x)       = inl (inl x)
   g (inr (inl y)) = inl (inr y)
   g (inr (inr z)) = inr z

   ε : (t : X + (Y + Z)) → (f ∘ g) t ≡ t
   ε (inl x)       = refl
   ε (inr (inl y)) = refl
   ε (inr (inr z)) = refl

   η : (u : (X + Y) + Z) → (g ∘ f) u ≡ u
   η (inl (inl x)) = refl
   η (inl (inr x)) = refl
   η (inr x)       = refl

+cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
      → X ≃ A → Y ≃ B → X + Y ≃ A + B
+cong {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} (f , (g , e) , (g' , d)) (φ , (γ , ε) , (γ' , δ)) =
 +functor f φ , (+functor g γ , E) , (+functor g' γ' , D)
 where
  E : (c : A + B) → +functor f φ (+functor g γ c) ≡ c
  E (inl a) = ap inl (e a)
  E (inr b) = ap inr (ε b)

  D : (z : X + Y) → +functor g' γ' (+functor f φ z) ≡ z
  D (inl x) = ap inl (d x)
  D (inr y) = ap inr (δ y)

×𝟘 : {X : 𝓤 ̇ } → 𝟘 {𝓥} ≃ X × 𝟘 {𝓦}
×𝟘 {𝓤} {𝓥} {𝓦} {X} = qinveq f (g , η , ε)
 where
   f : 𝟘 → X × 𝟘
   f = unique-from-𝟘

   g : X × 𝟘 → 𝟘
   g (x , y) = 𝟘-elim y

   ε : (t : X × 𝟘) → (f ∘ g) t ≡ t
   ε (x , y) = 𝟘-elim y

   η : (u : 𝟘) → (g ∘ f) u ≡ u
   η = 𝟘-induction

𝟙distr : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × Y + X ≃ X × (Y + 𝟙 {𝓦})
𝟙distr {𝓤} {𝓥} {𝓦} {X} {Y} = f , (g , ε) , (g , η)
 where
   f : X × Y + X → X × (Y + 𝟙)
   f (inl (x , y)) = x , inl y
   f (inr x)       = x , inr ⋆

   g : X × (Y + 𝟙) → X × Y + X
   g (x , inl y) = inl (x , y)
   g (x , inr O) = inr x

   ε : (t : X × (Y + 𝟙)) → (f ∘ g) t ≡ t
   ε (x , inl y) = refl
   ε (x , inr ⋆) = refl

   η : (u : X × Y + X) → (g ∘ f) u ≡ u
   η (inl (x , y)) = refl
   η (inr x)       = refl

Ap+ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (Z : 𝓦 ̇ ) → X ≃ Y → X + Z ≃ Y + Z
Ap+ {𝓤} {𝓥} {𝓦} {X} {Y} Z (f , (g , ε) , (h , η)) = f' , (g' , ε') , (h' , η')
 where
   f' : X + Z → Y + Z
   f' (inl x) = inl (f x)
   f' (inr z) = inr z

   g' : Y + Z → X + Z
   g' (inl y) = inl (g y)
   g' (inr z) = inr z

   h' : Y + Z → X + Z
   h' (inl y) = inl (h y)
   h' (inr z) = inr z

   ε' : (t : Y + Z) → (f' ∘ g') t ≡ t
   ε' (inl y) = ap inl (ε y)
   ε' (inr z) = refl

   η' : (u : X + Z) → (h' ∘ f') u ≡ u
   η' (inl x) = ap inl (η x)
   η' (inr z) = refl

×comm : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × Y ≃ Y × X
×comm {𝓤} {𝓥} {X} {Y} = f , (g , ε) , (g , η)
 where
   f : X × Y → Y × X
   f (x , y) = (y , x)

   g : Y × X → X × Y
   g (y , x) = (x , y)

   ε : (t : Y × X) → (f ∘ g) t ≡ t
   ε (y , x) = refl

   η : (u : X × Y) → (g ∘ f) u ≡ u
   η (x , y) = refl

×functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
         → (X → A) → (Y → B) → X × Y → A × B
×functor f g (x , y) = f x , g y

×-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
      → X ≃ A → Y ≃ B → X × Y ≃ A × B
×-cong {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} (f , (g , e) , (g' , d)) (φ , (γ , ε) , (γ' , δ)) =
 ×functor f φ , (×functor g γ , E) , (×functor g' γ' , D)
 where
  E : (c : A × B) → ×functor f φ (×functor g γ c) ≡ c
  E (a , b) = to-×-≡ (e a) (ε b)

  D : (z : X × Y) → ×functor g' γ' (×functor f φ z) ≡ z
  D (x , y) = to-×-≡ (d x) (δ y)

𝟘→ : {X : 𝓤 ̇ }
   → funext 𝓦 𝓤
   → 𝟙 {𝓥} ≃ (𝟘 {𝓦} → X)
𝟘→ {𝓤} {𝓥} {𝓦} {X} fe = qinveq f (g , ε , η)
 where
  f : 𝟙 → 𝟘 → X
  f ⋆ y = 𝟘-elim y

  g : (𝟘 → X) → 𝟙
  g h = ⋆

  η : (h : 𝟘 → X) → f (g h) ≡ h
  η h = dfunext fe (λ z → 𝟘-elim z)

  ε : (y : 𝟙) → g (f y) ≡ y
  ε ⋆ = refl

𝟙→ : {X : 𝓤 ̇ }
   → funext 𝓥 𝓤
   → X ≃ (𝟙 {𝓥} → X)
𝟙→ {𝓤} {𝓥} {X} fe = qinveq f (g , ε , η)
 where
  f : X → 𝟙 → X
  f x ⋆ = x

  g : (𝟙 → X) → X
  g h = h ⋆

  η : (h : 𝟙 → X) → f (g h) ≡ h
  η h = dfunext fe γ
   where
    γ : (t : 𝟙) → f (g h) t ≡ h t
    γ ⋆ = refl

  ε : (x : X) → g (f x) ≡ x
  ε x = refl

→𝟙 : {X : 𝓤 ̇ } → funext 𝓤 𝓥
   → (X → 𝟙 {𝓥}) ≃ 𝟙 {𝓥}
→𝟙 {𝓤} {𝓥} {X} fe = qinveq f (g , ε , η)
 where
  f : (X → 𝟙) → 𝟙
  f = unique-to-𝟙

  g : (t : 𝟙) → X → 𝟙
  g t = unique-to-𝟙

  ε : (α : X → 𝟙) → g ⋆ ≡ α
  ε α = dfunext fe λ (x : X) → 𝟙-is-prop (g ⋆ x) (α x)

  η : (t : 𝟙) → ⋆ ≡ t
  η = 𝟙-is-prop ⋆


Π×+ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X + Y → 𝓦 ̇ } → funext (𝓤 ⊔ 𝓥) 𝓦
    → (Π x ꞉ X , A (inl x)) × (Π y ꞉ Y , A (inr y))
    ≃ (Π z ꞉ X + Y , A z)

Π×+ {𝓤} {𝓥} {𝓦} {X} {Y} {A} fe = qinveq f (g , ε , η)
 where
  f : (Π x ꞉ X , A (inl x)) × (Π y ꞉ Y , A (inr y)) → (Π z ꞉ X + Y , A z)
  f (l , r) (inl x) = l x
  f (l , r) (inr y) = r y

  g : (Π z ꞉ X + Y , A z) → (Π x ꞉ X , A (inl x)) × (Π y ꞉ Y , A (inr y))
  g h = h ∘ inl , h ∘ inr

  η : f ∘ g ∼ id
  η h = dfunext fe γ
   where
    γ : (z : X + Y) → (f ∘ g) h z ≡ h z
    γ (inl x) = refl
    γ (inr y) = refl

  ε : g ∘ f ∼ id
  ε (l , r) = refl


+→ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
   → funext (𝓤 ⊔ 𝓥) 𝓦
   → ((X + Y) → Z) ≃ (X → Z) × (Y → Z)
+→ fe = ≃-sym (Π×+ fe)

→× : {A : 𝓤 ̇ } {X : A → 𝓥 ̇ } {Y : A → 𝓦 ̇ }
   → ((a : A) → X a × Y a)  ≃ Π X × Π Y
→× {𝓤} {𝓥} {𝓦} {A} {X} {Y} = qinveq f (g , ε , η)
 where
  f : ((a : A) → X a × Y a) → Π X × Π Y
  f φ = (λ a → pr₁ (φ a)) , (λ a → pr₂ (φ a))

  g : Π X × Π Y → (a : A) → X a × Y a
  g (γ , δ) a = γ a , δ a

  ε : (φ : (a : A) → X a × Y a) → g (f φ) ≡ φ
  ε φ = refl

  η : (α : Π X × Π Y) → f (g α) ≡ α
  η (γ , δ) = refl

→cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
      → funext 𝓦 𝓣
      → funext 𝓤 𝓥
      → X ≃ A → Y ≃ B → (X → Y) ≃ (A → B)
→cong {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} fe fe' (f , i) (φ , j) =
 H (equivs-are-qinvs f i) (equivs-are-qinvs φ j)
 where
  H : qinv f → qinv φ → (X → Y) ≃ (A → B)
  H (g , e , d) (γ , ε , δ) =  F , (G , E) , (G , D)
   where
    F : (X → Y) → (A → B)
    F h = φ ∘ h ∘ g

    G : (A → B) → (X → Y)
    G k = γ ∘ k ∘ f

    E : (k : A → B) → F (G k) ≡ k
    E k = dfunext fe (λ a → δ (k (f (g a))) ∙ ap k (d a))

    D : (h : X → Y) → G (F h) ≡ h
    D h = dfunext fe' (λ x → ε (h (g (f x))) ∙ ap h (e x))

→cong' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {B : 𝓣 ̇ }
       → funext 𝓤 𝓣
       → funext 𝓤 𝓥
       → Y ≃ B → (X → Y) ≃ (X → B)
→cong' {𝓤} {𝓥} {𝓣} {X} {Y} {B} fe fe' = →cong fe fe' (≃-refl X)

→cong'' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
        → funext 𝓦 𝓥
        → funext 𝓤 𝓥
        → X ≃ A → (X → Y) ≃ (A → Y)
→cong'' {𝓤} {𝓥} {𝓣} {X} {Y} {B} fe fe' e = →cong fe fe' e (≃-refl Y)

pr₁-equivalence : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                → ((x : X) → is-singleton (A x))
                → is-equiv (pr₁ {𝓤} {𝓥} {X} {A})
pr₁-equivalence {𝓤} {𝓥} X A iss = qinvs-are-equivs pr₁ (g , ε , η)
 where
  g : X → Σ A
  g x = x , pr₁ (iss x)

  η : (x : X) → pr₁ (g x) ≡ x
  η x = refl

  ε : (σ : Σ A) → g (pr₁ σ) ≡ σ
  ε (x , a) = to-Σ-≡ (η x , singletons-are-props (iss x) _ _)

NatΣ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                 → (x : X) (b : B x) → fiber (ζ x) b ≃ fiber (NatΣ ζ) (x , b)
NatΣ-fiber-equiv A B ζ x b = qinveq (f b) (g b , ε b , η b)
 where
  f : (b : B x) → fiber (ζ x) b → fiber (NatΣ ζ) (x , b)
  f . (ζ x a) (a , refl) = (x , a) , refl

  g : (b : B x) → fiber (NatΣ ζ) (x , b) → fiber (ζ x) b
  g . (ζ x a) ((.x , a) , refl) = a , refl

  ε : (b : B x) (w : fiber (ζ x) b) → g b (f b w) ≡ w
  ε . (ζ x a) (a , refl) = refl

  η : (b : B x) (t : fiber (NatΣ ζ) (x , b)) → f b (g b t) ≡ t
  η b (a , refl) = refl

NatΣ-vv-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
              → ((x : X) → is-vv-equiv (ζ x))
              → is-vv-equiv (NatΣ ζ)
NatΣ-vv-equiv A B ζ i (x , b) = equiv-to-singleton
                                   (≃-sym (NatΣ-fiber-equiv A B ζ x b))
                                   (i x b)

NatΣ-vv-equiv-converse : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                       → is-vv-equiv (NatΣ ζ)
                       → ((x : X) → is-vv-equiv (ζ x))
NatΣ-vv-equiv-converse A B ζ e x b = equiv-to-singleton
                                      (NatΣ-fiber-equiv A B ζ x b)
                                      (e (x , b))

NatΣ-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
           → ((x : X) → is-equiv (ζ x))
           → is-equiv (NatΣ ζ)
NatΣ-equiv A B ζ i = vv-equivs-are-equivs
                         (NatΣ ζ)
                         (NatΣ-vv-equiv A B ζ
                           (λ x → equivs-are-vv-equivs (ζ x) (i x)))

NatΣ-equiv-converse : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                    → is-equiv (NatΣ ζ)
                    → ((x : X) → is-equiv (ζ x))
NatΣ-equiv-converse A B ζ e x = vv-equivs-are-equivs (ζ x)
                                 (NatΣ-vv-equiv-converse A B ζ
                                   (equivs-are-vv-equivs (NatΣ ζ) e) x)

NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                                   (φ : Nat A B)
                                 → is-equiv (NatΣ φ)
                                 → is-fiberwise-equiv φ
NatΣ-equiv-gives-fiberwise-equiv = NatΣ-equiv-converse _ _

Σ-cong' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
        → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B
Σ-cong' A B e = NatΣ (λ x → pr₁ (e x)) , NatΣ-equiv A B (λ x → pr₁ (e x)) (λ x → pr₂ (e x))

NatΣ-equiv' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
            → ((x : X) → is-equiv (ζ x))
            → is-equiv (NatΣ ζ)
NatΣ-equiv' A B ζ i = ((s , ζs), (r , rζ))
 where
  s : Σ B → Σ A
  s (x , b) = x , pr₁ (pr₁ (i x)) b

  ζs : (β : Σ B) → (NatΣ ζ ∘ s) β ≡ β
  ζs (x , b) = ap (λ - → (x , -)) (pr₂ (pr₁ (i x)) b)

  r : Σ B → Σ A
  r (x , b) = x , (pr₁ (pr₂ (i x)) b)

  rζ : (α : Σ A) → (r ∘ NatΣ ζ) α ≡ α
  rζ (x , a) = ap (λ - → (x , -)) (pr₂ (pr₂ (i x)) a)

Σ-change-of-variable' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X → 𝓦 ̇ ) (g : Y → X)
                       → is-hae g
                       → Σ γ ꞉ ((Σ y ꞉ Y , A (g y)) → Σ A) , qinv γ
Σ-change-of-variable' {𝓤} {𝓥} {𝓦} {X} {Y} A g (f , η , ε , α) = γ , φ , φγ , γφ
 where
  γ : (Σ y ꞉ Y , A (g y)) → Σ A
  γ (y , a) = (g y , a)

  φ : Σ A → Σ y ꞉ Y , A (g y)
  φ (x , a) = (f x , transport⁻¹ A (ε x) a)

  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = to-Σ-≡ (ε x , p)
   where
    p : transport A (ε x) (transport⁻¹ A (ε x) a) ≡ a
    p = back-and-forth-transport (ε x)

  φγ : (τ : (Σ y ꞉ Y , A (g y))) → φ (γ τ) ≡ τ
  φγ (y , a) = to-Σ-≡ (η y , q)
   where
    q = transport (λ - → A (g -)) (η y) (transport⁻¹ A (ε (g y)) a) ≡⟨ i ⟩
        transport A (ap g (η y)) (transport⁻¹ A (ε (g y)) a)        ≡⟨ ii ⟩
        transport A (ε (g y)) (transport⁻¹ A (ε (g y)) a)           ≡⟨ iii ⟩
        a                                                           ∎
     where
      i   = transport-ap A g (η y)
      ii  = ap (λ - → transport A - (transport⁻¹ A (ε (g y)) a)) (α y)
      iii = back-and-forth-transport (ε (g y))

Σ-change-of-variable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X → 𝓦 ̇ ) (g : Y → X)
                     → is-equiv g → (Σ y ꞉ Y , A (g y)) ≃ Σ A
Σ-change-of-variable {𝓤} {𝓥} {𝓦} {X} {Y} A g e = γ , qinvs-are-equivs γ q
 where
  γ :  (Σ y ꞉ Y , A (g y)) → Σ A
  γ = pr₁ (Σ-change-of-variable' A g (equivs-are-haes g e))

  q :  qinv γ
  q = pr₂ (Σ-change-of-variable' A g (equivs-are-haes g e))

NatΠ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                 → funext 𝓤 𝓦
                 → (g : Π B) → (Π x ꞉ X , fiber (ζ x) (g x)) ≃ fiber (NatΠ ζ) g
NatΠ-fiber-equiv {𝓤} {𝓥} {𝓦} {X} A B ζ fe g =
  (Π x ꞉ X , fiber (ζ x) (g x))           ≃⟨ i ⟩
  (Π x ꞉ X , Σ a ꞉ A x , ζ x a ≡ g x)     ≃⟨ ii ⟩
  (Σ f ꞉ Π A , Π x ꞉ X , ζ x (f x) ≡ g x) ≃⟨ iii ⟩
  (Σ f ꞉ Π A , (λ x → ζ x (f x)) ≡ g)     ≃⟨ iv ⟩
  fiber (NatΠ ζ) g                        ■
   where
    i   = ≃-refl _
    ii  = ΠΣ-distr-≃
    iii = Σ-cong (λ f → ≃-sym (≃-funext fe (λ x → ζ x (f x)) g))
    iv  =  ≃-refl _

NatΠ-vv-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
              → funext 𝓤 (𝓥 ⊔ 𝓦)
              → ((x : X) → is-vv-equiv (ζ x))
              → is-vv-equiv (NatΠ ζ)
NatΠ-vv-equiv {𝓤} {𝓥} {𝓦} A B ζ fe i g = equiv-to-singleton
                                           (≃-sym (NatΠ-fiber-equiv A B ζ
                                                    (lower-funext 𝓤 𝓥 fe) g))
                                           (Π-is-singleton fe (λ x → i x (g x)))

NatΠ-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
           → funext 𝓤 (𝓥 ⊔ 𝓦)
           → ((x : X) → is-equiv (ζ x))
           → is-equiv (NatΠ ζ)
NatΠ-equiv A B ζ fe i = vv-equivs-are-equivs
                             (NatΠ ζ)
                             (NatΠ-vv-equiv A B ζ fe
                               (λ x → equivs-are-vv-equivs (ζ x) (i x)))

Π-cong' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
        → funext 𝓤 (𝓥 ⊔ 𝓦)
        → ((x : X) → A x ≃ B x)
        → Π A ≃ Π B
Π-cong' A B fe e = NatΠ (λ x → pr₁ (e x)) ,
                   NatΠ-equiv A B (λ x → pr₁ (e x)) fe (λ x → pr₂ (e x))

≡-cong : {X : 𝓤 ̇ } (x y : X) {x' y' : X} → x ≡ x' → y ≡ y' → (x ≡ y) ≃ (x' ≡ y')
≡-cong x y refl refl = ≃-refl (x ≡ y)

≡-cong-l : {X : 𝓤 ̇ } (x y : X) {x' : X} → x ≡ x' → (x ≡ y) ≃ (x' ≡ y)
≡-cong-l x y refl = ≃-refl (x ≡ y)

≡-cong-r : {X : 𝓤 ̇ } (x y : X) {y' : X} → y ≡ y' → (x ≡ y) ≃ (x ≡ y')
≡-cong-r x y refl = ≃-refl (x ≡ y)

≡-flip : {X : 𝓤 ̇ } {x y : X} → (x ≡ y) ≃ (y ≡ x)
≡-flip = _⁻¹ , (_⁻¹ , ⁻¹-involutive) , (_⁻¹ , ⁻¹-involutive)

singleton-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → is-singleton X → is-singleton Y → X ≃ Y
singleton-≃ {𝓤} {𝓥} (c , φ) (d , γ) = (λ _ → d) , ((λ _ → c) , γ) , ((λ _ → c) , φ)

singleton-≃-𝟙 : {X : 𝓤 ̇ } → is-singleton X → X ≃ 𝟙 {𝓥}
singleton-≃-𝟙 i = singleton-≃ i 𝟙-is-singleton

singleton-≃-𝟙' : {X : 𝓤 ̇ } → is-singleton X → 𝟙 {𝓥} ≃ X
singleton-≃-𝟙' = singleton-≃ 𝟙-is-singleton

𝟙-≡-≃ : (P : 𝓤 ̇ )
      → funext 𝓤 𝓤
      → propext 𝓤
      → is-prop P
      → (𝟙 ≡ P) ≃ P
𝟙-≡-≃ P fe pe i = qinveq (λ q → Idtofun q ⋆) (f , ε , η)
 where
  f : P → 𝟙 ≡ P
  f p = pe 𝟙-is-prop i (λ _ → p) unique-to-𝟙

  η : (p : P) → Idtofun (f p) ⋆ ≡ p
  η p = i (Idtofun (f p) ⋆) p

  ε : (q : 𝟙 ≡ P) → f (Idtofun q ⋆) ≡ q
  ε q = identifications-of-props-are-props pe fe P i 𝟙 (f (Idtofun q ⋆)) q

empty-≃-𝟘 : {X : 𝓤 ̇ } → (X → 𝟘 {𝓥}) → X ≃ 𝟘 {𝓦}
empty-≃-𝟘 i = qinveq (𝟘-elim ∘ i) (𝟘-elim , (λ x → 𝟘-elim (i x)) , (λ x → 𝟘-elim x))

complement-is-equiv : is-equiv complement
complement-is-equiv = qinvs-are-equivs complement
                       (complement , complement-involutive , complement-involutive)

complement-≃ : 𝟚 ≃ 𝟚
complement-≃ = (complement , complement-is-equiv)

domain-is-total-fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → X ≃ Σ (fiber f)
domain-is-total-fiber {𝓤} {𝓥} {X} {Y} f =
  X                             ≃⟨ ≃-sym (𝟙-rneutral {𝓤} {𝓤}) ⟩
  X × 𝟙                         ≃⟨ Σ-cong (λ x → singleton-≃ 𝟙-is-singleton
                                          (singleton-types-are-singletons (f x))) ⟩
  (Σ x ꞉ X , Σ y ꞉ Y , f x ≡ y) ≃⟨ Σ-flip ⟩
  (Σ y ꞉ Y , Σ x ꞉ X , f x ≡ y) ■

total-fiber-is-domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → (Σ y ꞉ Y , Σ x ꞉ X , f x ≡ y) ≃ X
total-fiber-is-domain {𝓤} {𝓥} {X} {Y} f = ≃-sym (domain-is-total-fiber f)

left-Id-equiv : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (x : X)
              → (Σ x' ꞉ X , (x' ≡ x) × Y x') ≃ Y x
left-Id-equiv {𝓤} {𝓥} {X} {Y} x =
   (Σ x' ꞉ X , (x' ≡ x) × Y x')            ≃⟨ ≃-sym Σ-assoc ⟩
   (Σ (x' , _) ꞉ singleton-type' x , Y x') ≃⟨ a ⟩
   Y x                                     ■
  where
   a = prop-indexed-sum (singleton-types'-are-props x) (singleton'-center x)

right-Id-equiv : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (x : X)
               → (Σ x' ꞉ X , Y x' × (x' ≡ x)) ≃ Y x
right-Id-equiv {𝓤} {𝓥} {X} {Y} x =
   (Σ x' ꞉ X , Y x' × (x' ≡ x))  ≃⟨ Σ-cong (λ x' → ×-comm) ⟩
   (Σ x' ꞉ X , (x' ≡ x) × Y x')  ≃⟨ left-Id-equiv x ⟩
   Y x                           ■


pr₁-fiber-equiv : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (x : X)
                → fiber (pr₁ {𝓤} {𝓥} {X} {Y}) x ≃ Y x
pr₁-fiber-equiv {𝓤} {𝓥} {X} {Y} x =
  fiber pr₁ x                   ≃⟨ Σ-assoc ⟩
  (Σ x' ꞉ X , Y x' × (x' ≡ x))  ≃⟨ right-Id-equiv x ⟩
  Y x                           ■

\end{code}

Tom de Jong, September 2019 (two lemmas used in UF-Classifiers-Old)

A nice application of Σ-change-of-variable is that the fiber of a map doesn't
change (up to equivalence, at least) when precomposing with an equivalence.

These two lemmas are used in UF-Classifiers-Old, but are sufficiently general to
warrant their place here.

\begin{code}

precomposition-with-equiv-does-not-change-fibers : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                                                   (e : Z ≃ X) (f : X → Y) (y : Y)
                                                 → fiber (f ∘ ⌜ e ⌝) y ≃ fiber f y
precomposition-with-equiv-does-not-change-fibers (g , i) f y =
 Σ-change-of-variable (λ x → f x ≡ y) g i

retract-pointed-fibers : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {r : Y → X}
                       → (Σ s ꞉ (X → Y) , r ∘ s ∼ id) ≃ (Π x ꞉ X , fiber r x)
retract-pointed-fibers {𝓤} {𝓥} {X} {Y} {r} = qinveq f (g , (p , q))
 where
  f : (Σ s ꞉ (X → Y) , r ∘ s ∼ id) → Π (fiber r)
  f (s , rs) x = (s x) , (rs x)

  g : ((x : X) → fiber r x) → Σ s ꞉ (X → Y) , r ∘ s ∼ id
  g α = (λ (x : X) → pr₁ (α x)) , (λ (x : X) → pr₂ (α x))

  p : (srs : Σ s ꞉ (X → Y) , r ∘ s ∼ id) → g (f srs) ≡ srs
  p (s , rs) = refl

  q : (α : Π x ꞉ X , fiber r x) → f (g α) ≡ α
  q α = refl

\end{code}

Added 10 February 2020 by Tom de Jong.

\begin{code}

fiber-of-composite : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
                   → (z : Z)
                   → fiber (g ∘ f) z
                   ≃ (Σ (y , _) ꞉ fiber g z , fiber f y)
fiber-of-composite {𝓤} {𝓥} {𝓦} {X} {Y} {Z} f g z =
 qinveq ϕ (ψ , (ψϕ , ϕψ))
  where
   ϕ : fiber (g ∘ f) z
     → (Σ w ꞉ (fiber g z) , fiber f (fiber-point w))
   ϕ (x , p) = ((f x) , p) , (x , refl)

   ψ : (Σ w ꞉ (fiber g z) , fiber f (fiber-point w))
     → fiber (g ∘ f) z
   ψ ((y , q) , (x , p)) = x , ((ap g p) ∙ q)

   ψϕ : (w : fiber (g ∘ f) z) → ψ (ϕ w) ≡ w
   ψϕ (x , refl) = refl

   ϕψ : (w : Σ w ꞉ (fiber g z) , fiber f (fiber-point w))
      → ϕ (ψ w) ≡ w
   ϕψ ((.(f x) , refl) , (x , refl)) = refl

fiber-of-unique-to-𝟙 : {𝓥 : Universe} {X : 𝓤 ̇ }
                     → (u : 𝟙) → fiber (unique-to-𝟙 {_} {𝓥} {X}) u ≃ X
fiber-of-unique-to-𝟙 {𝓤} {𝓥} {X} ⋆ =
 (Σ x ꞉ X , unique-to-𝟙 x ≡ ⋆) ≃⟨ Σ-cong ψ ⟩
 X × 𝟙{𝓥}                      ≃⟨ 𝟙-rneutral ⟩
 X                             ■
  where
   ψ : (x : X) → (⋆ ≡ ⋆) ≃ 𝟙
   ψ x = singleton-≃-𝟙
         (pointed-props-are-singletons refl (props-are-sets 𝟙-is-prop))

∼-fiber-identifications-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : X → Y}
                          → f ∼ g
                          → (y : Y) (x : X) → (f x ≡ y) ≃ (g x ≡ y)
∼-fiber-identifications-≃ {𝓤} {𝓥} {X} {Y} {f} {g} H y x = qinveq α (β , (βα , αβ))
 where
  α : f x ≡ y → g x ≡ y
  α p = (H x) ⁻¹ ∙ p

  β : g x ≡ y → f x ≡ y
  β q = (H x) ∙ q

  βα : (p : f x ≡ y) → β (α p) ≡ p
  βα p = β (α p)                ≡⟨ refl ⟩
         (H x) ∙ ((H x) ⁻¹ ∙ p) ≡⟨ (∙assoc (H x) ((H x) ⁻¹) p) ⁻¹ ⟩
         (H x) ∙ (H x) ⁻¹ ∙ p   ≡⟨ ap (λ - → - ∙ p) ((right-inverse (H x)) ⁻¹) ⟩
         refl ∙ p               ≡⟨ refl-left-neutral ⟩
         p                      ∎

  αβ : (q : g x ≡ y) → α (β q) ≡ q
  αβ q = α (β q)                ≡⟨ refl ⟩
         (H x) ⁻¹ ∙ ((H x) ∙ q) ≡⟨ (∙assoc ((H x) ⁻¹) (H x) q) ⁻¹ ⟩
         (H x) ⁻¹ ∙ (H x) ∙ q   ≡⟨ ap (λ - → - ∙ q) (left-inverse (H x)) ⟩
         refl ∙ q               ≡⟨ refl-left-neutral ⟩
         q                      ∎

∼-fiber-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : X → Y}
          → f ∼ g
          → (y : Y) → fiber f y ≃ fiber g y
∼-fiber-≃ H y = Σ-cong (∼-fiber-identifications-≃ H y)

∙-is-equiv-left : {X : 𝓤 ̇ } {x y z : X} (p : z ≡ x)
                → is-equiv (λ (q : x ≡ y) → p ∙ q)
∙-is-equiv-left {𝓤} {X} {x} {y} refl =
 equiv-closed-under-∼ id (refl ∙_) (id-is-equiv (x ≡ y))
  (λ _ → refl-left-neutral)

∙-is-equiv-right : {X : 𝓤 ̇ } {x y z : X} (q : x ≡ y)
                 → is-equiv (λ (p : z ≡ x) → p ∙ q)
∙-is-equiv-right {𝓤} {X} {x} {y} {z} refl = id-is-equiv (z ≡ y)

\end{code}

Added by Tom de Jong, November 2021.

\begin{code}

≃-2-out-of-3-right : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                   → {f : X → Y} {g : Y → Z}
                   → is-equiv f → is-equiv (g ∘ f) → is-equiv g
≃-2-out-of-3-right {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} i j =
 equiv-closed-under-∼ (g ∘ f ∘ f⁻¹) g k h
  where
   𝕗 : X ≃ Y
   𝕗 = (f , i)
   f⁻¹ : Y → X
   f⁻¹ = ⌜ 𝕗 ⌝⁻¹
   k : is-equiv (g ∘ f ∘ f⁻¹)
   k = ∘-is-equiv (⌜⌝⁻¹-is-equiv 𝕗) j
   h : g ∼ g ∘ f ∘ f⁻¹
   h y = ap g ((≃-sym-is-rinv 𝕗 y) ⁻¹)

≃-2-out-of-3-left : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                  → {f : X → Y} {g : Y → Z}
                  → is-equiv g → is-equiv (g ∘ f) → is-equiv f
≃-2-out-of-3-left {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} i j =
 equiv-closed-under-∼ (g⁻¹ ∘ g ∘ f) f k h
  where
   𝕘 : Y ≃ Z
   𝕘 = (g , i)
   g⁻¹ : Z → Y
   g⁻¹ = ⌜ 𝕘 ⌝⁻¹
   k : is-equiv (g⁻¹ ∘ g ∘ f)
   k = ∘-is-equiv j (⌜⌝⁻¹-is-equiv 𝕘)
   h : f ∼ g⁻¹ ∘ g ∘ f
   h x = (≃-sym-is-linv 𝕘 (f x)) ⁻¹

\end{code}

Completely unrelated to the above, but still useful.

\begin{code}

open import UF-PropTrunc

module _
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 ∥∥-cong : {X : 𝓤 ̇  } {Y : 𝓥 ̇  } → X ≃ Y → ∥ X ∥ ≃ ∥ Y ∥
 ∥∥-cong f = logically-equivalent-props-are-equivalent ∥∥-is-prop ∥∥-is-prop
              (∥∥-functor ⌜ f ⌝) (∥∥-functor ⌜ f ⌝⁻¹)

 ∃-cong : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {Y' : X → 𝓦 ̇  }
        → ((x : X) → Y x ≃ Y' x)
        → ∃ Y ≃ ∃ Y'
 ∃-cong e = ∥∥-cong (Σ-cong e)

 outer-∃-inner-Σ : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {A : (x : X) → Y x → 𝓦 ̇  }
                 → (∃ x ꞉ X , ∃ y ꞉ Y x , A x y)
                 ≃ (∃ x ꞉ X , Σ y ꞉ Y x , A x y)
 outer-∃-inner-Σ {𝓤} {𝓥} {𝓦} {X} {Y} {A} =
  logically-equivalent-props-are-equivalent ∥∥-is-prop ∥∥-is-prop f g
   where
    g : (∃ x ꞉ X , Σ y ꞉ Y x , A x y)
      → (∃ x ꞉ X , ∃ y ꞉ Y x , A x y)
    g = ∥∥-functor (λ (x , y , a) → x , ∣ y , a ∣)
    f : (∃ x ꞉ X , ∃ y ꞉ Y x , A x y)
      → (∃ x ꞉ X , Σ y ꞉ Y x , A x y)
    f = ∥∥-rec ∥∥-is-prop ϕ
     where
      ϕ : (Σ x ꞉ X , ∃ y ꞉ Y x , A x y)
        → (∃ x ꞉ X , Σ y ꞉ Y x , A x y)
      ϕ (x , p) = ∥∥-functor (λ (y , a) → x , y , a) p

\end{code}
