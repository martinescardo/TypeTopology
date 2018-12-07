Martin Escardo, 2012-

Expanded on demand whenever a general equivalence is needed.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module UF-EquivalenceExamples where

curry-uncurry : (fe : ∀ 𝓤 𝓥 → funext 𝓤 𝓥)
              → {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {Z : (Σ \(x : X) → Y x) → 𝓦 ̇}
              → Π Z ≃ Π \(x : X) → Π \(y : Y x) → Z(x , y)
curry-uncurry {𝓤} {𝓥} {𝓦} fe {X} {Y} {Z} = qinveq c (u , uc , cu)
 where
  c : (w : Π Z) → ((x : X) (y : Y x) → Z(x , y))
  c f x y = f (x , y)
  u : ((x : X) (y : Y x) → Z(x , y)) → Π Z
  u g (x , y) = g x y
  cu : ∀ g → c (u g) ≡ g
  cu g = dfunext (fe 𝓤 (𝓥 ⊔ 𝓦)) (λ x → dfunext (fe 𝓥 𝓦) (λ y → refl))
  uc : ∀ f → u (c f) ≡ f
  uc f = dfunext (fe (𝓤 ⊔ 𝓥) 𝓦) (λ w → refl)

Σ-≡-≃ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {σ τ : Σ A}
      → (σ ≡ τ) ≃ (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
Σ-≡-≃ {𝓤} {𝓥} {X} {A} {x , a} {y , b} = qinveq from-Σ-≡ (to-Σ-≡ , ε , η)
 where
  η : (σ : Σ \(p : x ≡ y) → transport A p a ≡ b) → from-Σ-≡ (to-Σ-≡ σ) ≡ σ
  η (refl , refl) = refl
  ε : (q : x , a ≡ y , b) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  ε refl = refl

×-≡-≃ : {X : 𝓤 ̇} {A : 𝓥 ̇} {σ τ : X × A}
      → (σ ≡ τ) ≃ (pr₁ σ ≡ pr₁ τ) × (pr₂ σ ≡ pr₂ τ)
×-≡-≃ {𝓤} {𝓥} {X} {A} {x , a} {y , b} = qinveq from-×-≡' (to-×-≡' , (ε , η))
 where
  η : (t : (x ≡ y) × (a ≡ b)) → from-×-≡' (to-×-≡' t) ≡ t
  η (refl , refl) = refl
  ε : (u : x , a ≡ y , b) → to-×-≡' (from-×-≡' u) ≡ u
  ε refl = refl

Σ-assoc : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {Z : Σ Y → 𝓦 ̇}
        → Σ Z ≃ (Σ \(x : X) → Σ \(y : Y x) → Z(x , y))
Σ-assoc {𝓤} {𝓥} {𝓦} {X} {Y} {Z} = qinveq c (u , (λ τ → refl) , (λ σ → refl))
 where
  c : Σ Z → Σ \x → Σ \y → Z (x , y)
  c ((x , y) , z) = (x , (y , z))
  u : (Σ \x → Σ \y → Z (x , y)) → Σ Z
  u (x , (y , z)) = ((x , y) , z)

Σ-flip : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : X → Y → 𝓦 ̇}
       → (Σ \(x : X) → Σ \(y : Y) → A x y) ≃ (Σ \(y : Y) → Σ \(x : X) → A x y)
Σ-flip {𝓤} {𝓥} {𝓦} {X} {Y} {A} = qinveq f (g , ε , η)
 where
  f : (Σ \(x : X) → Σ \(y : Y) → A x y) → (Σ \(y : Y) → Σ \(x : X) → A x y)
  f (x , y , p) = y , x , p
  g : (Σ \(y : Y) → Σ \(x : X) → A x y) → (Σ \(x : X) → Σ \(y : Y) → A x y)
  g (y , x , p) = x , y , p
  ε : ∀ σ → g (f σ) ≡ σ
  ε (x , y , p) = refl
  η : ∀ τ → f (g τ) ≡ τ
  η (y , x , p) = refl

Σ-cong : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {Y' : X → 𝓦 ̇}
       → ((x : X) → Y x ≃ Y' x) → Σ Y ≃ Σ Y'
Σ-cong {𝓤} {𝓥} {𝓦} {X} {Y} {Y'} φ = (F , (G , FG) , (H , HF))
 where
  f : (x : X) → Y x → Y' x
  f x = pr₁(φ x)
  g : (x : X) → Y' x → Y x
  g x = pr₁(pr₁(pr₂(φ x)))
  fg : (x : X) (y' : Y' x) → f x (g x y') ≡ y'
  fg x = pr₂(pr₁(pr₂(φ x)))
  h : (x : X) → Y' x → Y x
  h x = pr₁(pr₂(pr₂(φ x)))
  hf : (x : X) (y : Y x) → h x (f x y) ≡ y
  hf x = pr₂(pr₂(pr₂(φ x)))

  F : Σ Y → Σ Y'
  F (x , y) = x , f x y
  G : Σ Y' → Σ Y
  G (x , y') = x , (g x y')
  H : Σ Y' → Σ Y
  H (x , y') = x , h x y'
  FG : (w' : Σ Y') → F(G w') ≡ w'
  FG (x , y') = to-Σ-≡' (fg x y')
  HF : (w : Σ Y) → H(F w) ≡ w
  HF (x , y) = to-Σ-≡' (hf x y)

ΠΣ-distr-≃ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {P : (x : X) → A x → 𝓦 ̇}
           → (Π \(x : X) → Σ \(a : A x) → P x a) ≃ (Σ \(f : Π A) → Π \(x : X) → P x (f x))
ΠΣ-distr-≃ {𝓤} {𝓥} {𝓦} {X} {A} {P} = qinveq ΠΣ-distr (ΠΣ-distr-back , ε , η)
 where
  η :  ΠΣ-distr {𝓤} {𝓥} {𝓦} {X} {A} {P} ∘ ΠΣ-distr-back ∼ id
  η _ = refl
  ε : ΠΣ-distr-back ∘ ΠΣ-distr ∼ id
  ε _ = refl

Π-cong : funext 𝓤 𝓥 → funext 𝓤 𝓦
       → (X : 𝓤 ̇) (Y : X → 𝓥 ̇) (Y' : X → 𝓦 ̇)
       → ((x : X) → Y x ≃ Y' x) → Π Y ≃ Π Y'
Π-cong fe fe' X Y Y' φ = (F , (G , FG) , (H , HF))
 where
  f : (x : X) → Y x → Y' x
  f x = pr₁(φ x)
  g : (x : X) → Y' x → Y x
  g x =  pr₁(pr₁(pr₂(φ x)))
  fg : (x : X) (y' : Y' x) → f x (g x y') ≡ y'
  fg x = pr₂(pr₁(pr₂(φ x)))
  h : (x : X) → Y' x → Y x
  h x = pr₁(pr₂(pr₂(φ x)))
  hf : (x : X) (y : Y x) → h x (f x y) ≡ y
  hf x = pr₂(pr₂(pr₂(φ x)))

  F : ((x : X) → Y x) → ((x : X) → Y' x)
  F = λ z x → pr₁ (φ x) (z x)
  G : ((x : X) → Y' x) → (x : X) → Y x
  G u x = g x (u x)
  H : ((x : X) → Y' x) → (x : X) → Y x
  H u' x = h x (u' x)

  FG :  (w' : ((x : X) → Y' x)) → F(G w') ≡ w'
  FG w' = dfunext fe' FG'
   where
    FG' : (x : X) → F(G w') x ≡ w' x
    FG' x = fg x (w' x)

  HF : (w : ((x : X) → Y x)) → H(F w) ≡ w
  HF w = dfunext fe GF'
   where
    GF' : (x : X) → H(F w) x ≡ w x
    GF' x = hf x (w x)

\end{code}

An application of Π-cong is the following:

\begin{code}

≃-funext₂ : funext 𝓤 (𝓥 ⊔ 𝓦) → funext 𝓥 𝓦
          → {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : (x : X) → Y x → 𝓦 ̇}
            (f g : (x : X) (y : Y x) → A x y) → (f ≡ g) ≃ (∀ x y → f x y ≡ g x y)
≃-funext₂ fe fe' {X} f g =
 (f ≡ g)            ≃⟨ ≃-funext fe f g ⟩
 (f ∼ g)            ≃⟨ Π-cong fe fe X
                          (λ x → f x ≡ g x)
                          (λ x → f x ∼ g x)
                          (λ x → ≃-funext fe' (f x) (g x))⟩
 (∀ x → f x ∼ g x) ■

𝟙-lneutral : {Y : 𝓤 ̇} → 𝟙 {𝓥} × Y ≃ Y
𝟙-lneutral {𝓤} {𝓥} {Y} = qinveq f (g , ε , η)
 where
   f : 𝟙 × Y → Y
   f (o , y) = y
   g : Y → 𝟙 × Y
   g y = (* , y)
   η : ∀ x → f (g x) ≡ x
   η y = refl
   ε : ∀ z → g (f z) ≡ z
   ε (o , y) = ap (_, y) (𝟙-is-prop * o)

×-comm : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X × Y ≃ Y × X
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

𝟙-rneutral : {Y : 𝓤 ̇} → Y × 𝟙 {𝓥} ≃ Y
𝟙-rneutral {𝓤} {𝓥} {Y} = Y × 𝟙 ≃⟨ ×-comm ⟩
                          𝟙 × Y ≃⟨ 𝟙-lneutral {𝓤} {𝓥} ⟩
                          Y     ■

+comm : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X + Y ≃ Y + X
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

𝟘-rneutral : {X : 𝓤 ̇} → X ≃ X + 𝟘 {𝓥}
𝟘-rneutral {𝓤} {𝓥} {X} = qinveq f (g , η , ε)
 where
   f : X → X + 𝟘
   f = inl
   g : X + 𝟘 → X
   g (inl x) = x
   g (inr ())
   ε : (y : X + 𝟘) → (f ∘ g) y ≡ y
   ε (inl x) = refl
   ε (inr ())
   η : (x : X) → (g ∘ f) x ≡ x
   η x = refl

𝟘-rneutral' : {X : 𝓤 ̇} → X + 𝟘 {𝓥} ≃ X
𝟘-rneutral' {𝓤} {𝓥} = ≃-sym (𝟘-rneutral {𝓤} {𝓥})

𝟘-lneutral : {X : 𝓤 ̇} → 𝟘 {𝓥} + X ≃ X
𝟘-lneutral {𝓤} {𝓥} {X} = (𝟘 + X) ≃⟨ +comm ⟩
                         (X + 𝟘) ≃⟨ 𝟘-rneutral' {𝓤} {𝓥} ⟩
                          X      ■

+assoc : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} → (X + Y) + Z ≃ X + (Y + Z)
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

+-cong : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} {B : 𝓣 ̇}
       → X ≃ A → Y ≃ B → X + Y ≃ A + B
+-cong {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} (f , (g , e) , (g' , d)) (φ , (γ , ε) , (γ' , δ)) =
 F , (G , E) , (G' , D)
 where
  F : X + Y → A + B
  F (inl x) = inl (f x)
  F (inr y) = inr (φ y)
  G : A + B → X + Y
  G (inl a) = inl (g a)
  G (inr b) = inr (γ b)
  G' : A + B → X + Y
  G' (inl a) = inl (g' a)
  G' (inr b) = inr (γ' b)
  E : (c : A + B) → F (G c) ≡ c
  E (inl a) = ap inl (e a)
  E (inr b) = ap inr (ε b)
  D : (z : X + Y) → G' (F z) ≡ z
  D (inl x) = ap inl (d x)
  D (inr y) = ap inr (δ y)

×𝟘 : {X : 𝓤 ̇} → 𝟘 {𝓥} ≃ X × 𝟘 {𝓦}
×𝟘 {𝓤} {𝓥} {𝓦} {X} = qinveq f (g , η , ε)
 where
   f : 𝟘 → X × 𝟘
   f ()
   g : X × 𝟘 → 𝟘
   g (x , ())
   ε : (t : X × 𝟘) → (f ∘ g) t ≡ t
   ε (x , ())
   η : (u : 𝟘) → (g ∘ f) u ≡ u
   η ()

𝟙distr : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X × Y + X ≃ X × (Y + 𝟙 {𝓦})
𝟙distr {𝓤} {𝓥} {𝓦} {X} {Y} = f , (g , ε) , (g , η)
 where
   f : X × Y + X → X × (Y + 𝟙)
   f (inl (x , y)) = x , inl y
   f (inr x)       = x , inr *
   g : X × (Y + 𝟙) → X × Y + X
   g (x , inl y) = inl (x , y)
   g (x , inr O) = inr x
   ε : (t : X × (Y + 𝟙)) → (f ∘ g) t ≡ t
   ε (x , inl y) = refl
   ε (x , inr *) = refl
   η : (u : X × Y + X) → (g ∘ f) u ≡ u
   η (inl (x , y)) = refl
   η (inr x)       = refl

Ap+ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (Z : 𝓦 ̇) → X ≃ Y → X + Z ≃ Y + Z
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

×comm : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X × Y ≃ Y × X
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

×-cong : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} {B : 𝓣 ̇}
      → X ≃ A → Y ≃ B → X × Y ≃ A × B
×-cong {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} (f , (g , e) , (g' , d)) (φ , (γ , ε) , (γ' , δ)) =
 F , (G , E) , (G' , D)
 where
  F : X × Y → A × B
  F (x , y) = f x , φ y
  G : A × B → X × Y
  G (a , b) = g a , γ b
  G' : A × B → X × Y
  G' (a , b) = g' a , γ' b
  E : (c : A × B) → F (G c) ≡ c
  E (a , b) = to-×-≡ (e a) (ε b)
  D : (z : X × Y) → G' (F z) ≡ z
  D (x , y) = to-×-≡ (d x) (δ y)

𝟘→ : {X : 𝓤 ̇} → funext 𝓦 𝓤
   → 𝟙 {𝓥} ≃ (𝟘 {𝓦} → X)
𝟘→ {𝓤} {𝓥} {𝓦} {X} fe = qinveq f (g , ε , η)
 where
  f : 𝟙 → 𝟘 → X
  f * ()
  g : (𝟘 → X) → 𝟙
  g h = *
  η : (h : 𝟘 → X) → f (g h) ≡ h
  η h = dfunext fe (λ z → 𝟘-elim z)
  ε : (y : 𝟙) → g (f y) ≡ y
  ε * = refl

𝟙→ : {X : 𝓤 ̇} → funext 𝓥 𝓤
   → X ≃ (𝟙 {𝓥} → X)
𝟙→ {𝓤} {𝓥} {X} fe = qinveq f (g , ε , η)
 where
  f : X → 𝟙 → X
  f x * = x
  g : (𝟙 → X) → X
  g h = h *
  η : (h : 𝟙 → X) → f (g h) ≡ h
  η h = dfunext fe γ
   where
    γ : (t : 𝟙) → f (g h) t ≡ h t
    γ * = refl
  ε : (x : X) → g (f x) ≡ x
  ε x = refl

+→ : ∀ {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} → funext (𝓤 ⊔ 𝓥) 𝓦
   → ((X + Y) → Z) ≃ (X → Z) × (Y → Z)
+→ {𝓤} {𝓥} {𝓦} {X} {Y} {Z} fe = qinveq f (g , ε , η)
 where
  f : (X + Y → Z) → (X → Z) × (Y → Z)
  f h = h ∘ inl , h ∘ inr
  g : (X → Z) × (Y → Z) → X + Y → Z
  g (l , r) (inl x) = l x
  g (l , r) (inr y) = r y
  η : (w : (X → Z) × (Y → Z)) → f (g w) ≡ w
  η (l , r) = refl
  ε : (h : X + Y → Z) → g (f h) ≡ h
  ε h = dfunext fe γ
   where
    γ : (t : X + Y) → g (f h) t ≡ h t
    γ (inl x) = refl
    γ (inr y) = refl

→-cong : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} {B : 𝓣 ̇}
       → funext 𝓦 𝓣 → funext 𝓤 𝓥
       → X ≃ A → Y ≃ B → (X → Y) ≃ (A → B)
→-cong {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} fe fe' (f , i) (φ , j) =
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

pr₁-equivalence : (X : 𝓤 ̇) (A : X → 𝓥 ̇)
                → ((x : X) → is-singleton (A x))
                → is-equiv (pr₁ {𝓤} {𝓥} {X} {A})
pr₁-equivalence {𝓤} {𝓥} X A iss = qinvs-are-equivs pr₁ (g , ε , η)
 where
  g : X → Σ A
  g x = x , pr₁(iss x)
  η : (x : X) → pr₁ (g x) ≡ x
  η x = refl
  ε : (σ : Σ A) → g(pr₁ σ) ≡ σ
  ε (x , a) = to-Σ-≡ (η x , singletons-are-props (iss x) _ _)

NatΣ-fiber-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) (ζ : Nat A B)
                 → (x : X) (b : B x) → fiber (ζ x) b ≃ fiber (NatΣ ζ) (x , b)
NatΣ-fiber-equiv A B ζ x b = qinveq (f b) (g b , ε b , η b)
 where
  f : (b : B x) → fiber (ζ x) b → fiber (NatΣ ζ) (x , b)
  f .(ζ x a) (a , refl) = (x , a) , refl
  g : (b : B x) → fiber (NatΣ ζ) (x , b) → fiber (ζ x) b
  g .(ζ x a) ((.x , a) , refl) = a , refl
  ε : (b : B x) (w : fiber (ζ x) b) → g b (f b w) ≡ w
  ε .(ζ x a) (a , refl) = refl
  η : (b : B x) (t : fiber (NatΣ ζ) (x , b)) → f b (g b t) ≡ t
  η b (a , refl) = refl

NatΣ-vv-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) (ζ : Nat A B)
              → ((x : X) → is-vv-equiv(ζ x)) → is-vv-equiv(NatΣ ζ)
NatΣ-vv-equiv A B ζ i (x , b) = equiv-to-singleton
                                   (≃-sym (NatΣ-fiber-equiv A B ζ x b))
                                   (i x b)

NatΣ-vv-equiv-converse : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) (ζ : Nat A B)
                       → is-vv-equiv(NatΣ ζ) → ((x : X) → is-vv-equiv(ζ x))
NatΣ-vv-equiv-converse A B ζ e x b = equiv-to-singleton
                                      (NatΣ-fiber-equiv A B ζ x b)
                                      (e (x , b))

NatΣ-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) (ζ : Nat A B)
           → ((x : X) → is-equiv(ζ x)) → is-equiv(NatΣ ζ)
NatΣ-equiv A B ζ i = vv-equivs-are-equivs
                         (NatΣ ζ)
                         (NatΣ-vv-equiv A B ζ
                           (λ x → equivs-are-vv-equivs (ζ x) (i x)))

NatΣ-equiv-converse : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) (ζ : Nat A B)
                    → is-equiv(NatΣ ζ) → ((x : X) → is-equiv(ζ x))
NatΣ-equiv-converse A B ζ e x = vv-equivs-are-equivs (ζ x)
                                 (NatΣ-vv-equiv-converse A B ζ
                                   (equivs-are-vv-equivs (NatΣ ζ) e) x)

Σ-cong' : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇)
        → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B
Σ-cong' A B e = NatΣ (λ x → pr₁(e x)) , NatΣ-equiv A B (λ x → pr₁(e x)) (λ x → pr₂(e x))

NatΣ-equiv' : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) (ζ : Nat A B)
            → ((x : X) → is-equiv(ζ x)) → is-equiv(NatΣ ζ)
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

Σ-change-of-variables' : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X → 𝓦 ̇) (g : Y → X)
                       → is-hae g → Σ \(γ : (Σ \(y : Y) → A (g y)) → Σ A) → qinv γ
Σ-change-of-variables' {𝓤} {𝓥} {𝓦} {X} {Y} A g (f , η , ε , α) = γ , φ , φγ , γφ
 where
  γ : (Σ \(y : Y) → A (g y)) → Σ A
  γ (y , a) = (g y , a)
  φ : Σ A → Σ \(y : Y) → A (g y)
  φ (x , a) = (f x , back-transport A (ε x) a)
  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = to-Σ-≡ (ε x , p)
   where
    p : transport A (ε x) (back-transport A (ε x) a) ≡ a
    p = back-and-forth-transport (ε x)
  φγ : (τ : (Σ \(y : Y) → A (g y))) → φ (γ τ) ≡ τ
  φγ (y , a) = to-Σ-≡ (η y , q)
   where
    q : transport (λ - → A (g -)) (η y) (back-transport A (ε (g y)) a) ≡ a
    q = transport (λ - → A (g -)) (η y) (back-transport A (ε (g y)) a) ≡⟨ transport-ap A g (η y) ⟩
        transport A (ap g (η y)) (back-transport A (ε (g y)) a)        ≡⟨ ap (λ - → transport A - (back-transport A (ε (g y)) a)) (α y) ⟩
        transport A (ε (g y)) (back-transport A (ε (g y)) a)           ≡⟨ back-and-forth-transport (ε (g y)) ⟩
        a                                                              ∎

Σ-change-of-variables : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X → 𝓦 ̇) (g : Y → X)
                      → is-equiv g → (Σ \(y : Y) → A (g y)) ≃ Σ A
Σ-change-of-variables {𝓤} {𝓥} {𝓦} {X} {Y} A g e = γ , qinvs-are-equivs γ q
 where
  γ :  (Σ \(y : Y) → A (g y)) → Σ A
  γ = pr₁(Σ-change-of-variables' A g (equivs-are-haes g e))
  q :  qinv γ
  q = pr₂(Σ-change-of-variables' A g (equivs-are-haes g e))

NatΠ-fiber-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) (ζ : Nat A B)
                 → funext 𝓤 𝓦
                 → (g : Π B) → (Π \(x : X) → fiber (ζ x) (g x)) ≃ fiber (NatΠ ζ) g
NatΠ-fiber-equiv {𝓤} {𝓥} {𝓦} {X} A B ζ fe g =
  (Π \(x : X) → fiber (ζ x) (g x))              ≃⟨ ≃-refl _ ⟩
  (Π \(x : X) → Σ \(a : A x) → ζ x a ≡ g x)     ≃⟨ ΠΣ-distr-≃ ⟩
  (Σ \(f : Π A) → Π \(x : X) → ζ x (f x) ≡ g x) ≃⟨ Σ-cong (λ f → ≃-sym (≃-funext fe (λ x → ζ x (f x)) g)) ⟩
  (Σ \(f : Π A) → (λ x → ζ x (f x)) ≡ g)        ≃⟨ ≃-refl _ ⟩
  fiber (NatΠ ζ) g                              ■

NatΠ-vv-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) (ζ : Nat A B)
              → funext 𝓤 𝓦  → funext 𝓤 (𝓥 ⊔ 𝓦)
              → ((x : X) → is-vv-equiv(ζ x)) → is-vv-equiv(NatΠ ζ)
NatΠ-vv-equiv A B ζ fe fe' i g = equiv-to-singleton
                                    (≃-sym (NatΠ-fiber-equiv A B ζ fe g))
                                    (Π-is-singleton fe' (λ x → i x (g x)))

NatΠ-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) (ζ : Nat A B)
           → funext 𝓤 𝓦  → funext 𝓤 (𝓥 ⊔ 𝓦)
           → ((x : X) → is-equiv(ζ x)) → is-equiv(NatΠ ζ)
NatΠ-equiv A B ζ fe fe' i = vv-equivs-are-equivs
                             (NatΠ ζ)
                             (NatΠ-vv-equiv A B ζ fe fe'
                               (λ x → equivs-are-vv-equivs (ζ x) (i x)))

Π-cong' : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇)
        → funext 𝓤 𝓦  → funext 𝓤 (𝓥 ⊔ 𝓦)
        → ((x : X) → A x ≃ B x) → Π A ≃ Π B
Π-cong' A B fe fe' e = NatΠ (λ x → pr₁(e x)) , NatΠ-equiv A B (λ x → pr₁(e x)) fe fe' (λ x → pr₂(e x))

≡-cong : {X : 𝓤 ̇} (x y : X) {x' y' : X} → x ≡ x' → y ≡ y' → (x ≡ y) ≃ (x' ≡ y')
≡-cong x y refl refl = ≃-refl (x ≡ y)

≡-cong-l : {X : 𝓤 ̇} (x y : X) {x' : X} → x ≡ x' → (x ≡ y) ≃ (x' ≡ y)
≡-cong-l x y refl = ≃-refl (x ≡ y)

≡-cong-r : {X : 𝓤 ̇} (x y : X) {y' : X} → y ≡ y' → (x ≡ y) ≃ (x ≡ y')
≡-cong-r x y refl = ≃-refl (x ≡ y)

≡-flip : {X : 𝓤 ̇} {x y : X} → (x ≡ y) ≃ (y ≡ x)
≡-flip = _⁻¹ , (_⁻¹ , ⁻¹-involutive) , (_⁻¹ , ⁻¹-involutive)

singleton-≃ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → is-singleton X → is-singleton Y → X ≃ Y
singleton-≃ {𝓤} {𝓥} (c , φ) (d , γ) = (λ _ → d) , ((λ _ → c) , γ) , ((λ _ → c) , φ)

{- TODO: probably remove this.
singleton-𝟙 : {X : 𝓤 ̇} → is-singleton X → X ≃ 𝟙 {𝓥}
singleton-𝟙 i = singleton-≃ i 𝟙-is-singleton

singleton-𝟙' : {X : 𝓤 ̇} → is-singleton X → 𝟙 {𝓥} ≃ X
singleton-𝟙' = singleton-≃ 𝟙-is-singleton
-}

𝟙-≡-≃ : (P : 𝓤 ̇) → funext 𝓤 𝓤 → propext 𝓤
      → is-prop P → (𝟙 ≡ P) ≃ P
𝟙-≡-≃ P fe pe i = qinveq (λ q → Idtofun q *) (f , ε , η)
 where
  f : P → 𝟙 ≡ P
  f p = pe 𝟙-is-prop i (λ _ → p) unique-to-𝟙
  η : (p : P) → Idtofun (f p) * ≡ p
  η p = i (Idtofun (f p) *) p
  ε : (q : 𝟙 ≡ P) → f (Idtofun q *) ≡ q
  ε q = identifications-of-props-are-props pe fe P i 𝟙 (f (Idtofun q *)) q

sum-of-fibers : (X : 𝓤 ̇) (Y : 𝓥 ̇) (f : X → Y) → X ≃ Σ (fiber f)
sum-of-fibers {𝓤} {𝓥} X Y f =
  X                                   ≃⟨ ≃-sym (𝟙-rneutral {𝓤} {𝓤}) ⟩
  X × 𝟙                               ≃⟨ Σ-cong (λ x → singleton-≃ 𝟙-is-singleton
                                                (singleton-types-are-singletons (f x))) ⟩
  (Σ \(x : X) → Σ \(y : Y) → f x ≡ y) ≃⟨ Σ-flip ⟩
  (Σ \(y : Y) → Σ \(x : X) → f x ≡ y) ■

\end{code}

Alternatively, where we should change the name of this function:

\begin{code}

graph-domain-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                   → (Σ \(y : Y) → Σ \(x : X) → f x ≡ y) ≃ X
graph-domain-equiv {𝓤} {𝓥} {X} {Y} f = qinveq h (g , ε , η)
 where
  g : X → Σ \(y : Y) → Σ \(x : X) → f x ≡ y
  g x = f x , x , refl
  h : (Σ \(y : Y) → Σ \(x : X) → f x ≡ y) → X
  h (.(f x) , x , refl) = x
  ε : (σ : Σ \(y : Y) → Σ \(x : X) → f x ≡ y) → g (h σ )≡ σ
  ε (.(f x) , x , refl) = refl
  η : (x : X) → h (g x) ≡ x
  η x = refl

\end{code}
