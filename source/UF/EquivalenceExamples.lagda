Martin Escardo, 2012-

Expanded on demand whenever a general equivalence is needed.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

module UF.EquivalenceExamples where

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

  cu : ∀ g → c (u g) ＝ g
  cu g = dfunext fe (λ x → dfunext (lower-funext 𝓤 𝓦 fe') (λ y → refl))

  uc : ∀ f → u (c f) ＝ f
  uc f = dfunext fe' (λ w → refl)

curry-uncurry : (fe : FunExt)
              → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : (Σ x ꞉ X , Y x) → 𝓦 ̇ }
              → Π Z ≃ (Π x ꞉ X , Π y ꞉ Y x , Z (x , y))
curry-uncurry {𝓤} {𝓥} {𝓦} fe = curry-uncurry' (fe 𝓤 (𝓥 ⊔ 𝓦)) (fe (𝓤 ⊔ 𝓥) 𝓦)

Σ-＝-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
      → (σ ＝ τ) ≃ (Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
Σ-＝-≃ {𝓤} {𝓥} {X} {A} {x , a} {y , b} = qinveq from-Σ-＝ (to-Σ-＝ , ε , η)
 where
  η : (σ : Σ p ꞉ x ＝ y , transport A p a ＝ b) → from-Σ-＝ (to-Σ-＝ σ) ＝ σ
  η (refl , refl) = refl

  ε : (q : x , a ＝ y , b) → to-Σ-＝ (from-Σ-＝ q) ＝ q
  ε refl = refl

×-＝-≃ : {X : 𝓤 ̇ } {A : 𝓥 ̇ } {σ τ : X × A}
      → (σ ＝ τ) ≃ (pr₁ σ ＝ pr₁ τ) × (pr₂ σ ＝ pr₂ τ)
×-＝-≃ {𝓤} {𝓥} {X} {A} {x , a} {y , b} = qinveq from-×-＝' (to-×-＝' , (ε , η))
 where
  η : (t : (x ＝ y) × (a ＝ b)) → from-×-＝' (to-×-＝' t) ＝ t
  η (refl , refl) = refl

  ε : (u : x , a ＝ y , b) → to-×-＝' (from-×-＝' u) ＝ u
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

  ε : ∀ σ → g (f σ) ＝ σ
  ε (x , y , p) = refl

  η : ∀ τ → f (g τ) ＝ τ
  η (y , x , p) = refl

Σ-interchange : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → 𝓦 ̇ } {B : Y → 𝓣 ̇ }
              → (Σ x ꞉ X , Σ y ꞉ Y , A x × B y)
              ≃ ((Σ x ꞉ X , A x) × (Σ y ꞉ Y , B y))
Σ-interchange {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} = qinveq f (g , ε , η)
 where
  f : (Σ x ꞉ X , Σ y ꞉ Y , A x × B y)
    → ((Σ x ꞉ X , A x) × (Σ y ꞉ Y , B y))
  f (x , y , a , b) = ((x , a) , (y , b))

  g : codomain f → domain f
  g ((x , a) , (y , b)) = (x , y , a , b)

  ε : ∀ σ → g (f σ) ＝ σ
  ε (x , y , a , b) = refl

  η : ∀ τ → f (g τ) ＝ τ
  η ((x , a) , (y , b)) = refl

Σ-cong : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Y' : X → 𝓦 ̇ }
       → ((x : X) → Y x ≃ Y' x)
       → Σ Y ≃ Σ Y'
Σ-cong {𝓤} {𝓥} {𝓦} {X} {Y} {Y'} φ = qinveq f (g , gf , fg)
 where
  f : Σ Y → Σ Y'
  f (x , y) = x , ⌜ φ x ⌝ y

  g : Σ Y' → Σ Y
  g (x , y') = x , ⌜ φ x ⌝⁻¹ y'

  fg : (w' : Σ Y') → f (g w') ＝ w'
  fg (x , y') = to-Σ-＝' (inverses-are-sections ⌜ φ x ⌝ ⌜ φ x ⌝-is-equiv y')

  gf : (w : Σ Y) → g (f w) ＝ w
  gf (x , y) = to-Σ-＝' (inverses-are-retractions ⌜ φ x ⌝ ⌜ φ x ⌝-is-equiv y)

ΠΣ-distr-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Π x ꞉ X , Σ a ꞉ A x , P x a) ≃ (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))
ΠΣ-distr-≃ = qinveq ΠΣ-distr (ΠΣ-distr⁻¹ , (λ _ → refl) , (λ _ → refl))

Π×-distr : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
         → (Π x ꞉ X , A x × B x)
         ≃ ((Π x ꞉ X , A x) × (Π x ꞉ X , B x))
Π×-distr = ΠΣ-distr-≃

Π×-distr₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            {A : X → Y → 𝓦 ̇ } {B : X → Y → 𝓣 ̇ }
          → (Π x ꞉ X , Π y ꞉ Y , A x y × B x y)
          ≃ ((Π x ꞉ X , Π y ꞉ Y , A x y) × (Π x ꞉ X , Π y ꞉ Y , B x y))
Π×-distr₂ = qinveq
             (λ f → (λ x y → pr₁ (f x y)) , (λ x y → pr₂ (f x y)))
             ((λ (g , h) x y → g x y , h x y) ,
              (λ _ → refl) ,
              (λ _ → refl))

Σ+-distr : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
         → (Σ x ꞉ X , A x + B x)
         ≃ ((Σ x ꞉ X , A x) + (Σ x ꞉ X , B x))
Σ+-distr X A B = qinveq f (g , η , ε)
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

Σ+-split : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (A : X + Y → 𝓦 ̇ )
         → (Σ x ꞉ X , A (inl x)) + (Σ y ꞉ Y , A (inr y))
         ≃ (Σ z ꞉ X + Y , A z)
Σ+-split X Y A = qinveq f (g , η , ε)
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

Π-flip : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → Y → 𝓦 ̇ }
       → ((x : X) (y : Y) → A x y) ≃ ((y : Y) (x : X) → A x y)
Π-flip {_} {_} {_} {X} {Y} {A} = qinveq f (g , H , G)
 where
  f : ((x : X) (y : Y) → A x y) → ((y : Y) (x : X) → A x y)
  f h y x = h x y
  g : ((y : Y) (x : X) → A x y) → ((x : X) (y : Y) → A x y)
  g h x y = h y x
  H : (h : ((x : X) (y : Y) → A x y)) → g (f h) ＝ h
  H h = refl
  G : (h : ((y : Y) (x : X) → A x y)) → f (g h) ＝ h
  G h = refl

Π-flip' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → Y → 𝓦 ̇ }
        → ((y : Y) (x : X) → A x y) ≃ ((x : X) (y : Y) → A x y)
Π-flip' = ≃-sym Π-flip

Π-cong : funext 𝓤 𝓥
       → funext 𝓤 𝓦
       → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Y' : X → 𝓦 ̇ }
       → ((x : X) → Y x ≃ Y' x)
       → Π Y ≃ Π Y'
Π-cong fe fe' {X} {Y} {Y'} φ = qinveq f (g , gf , fg)
 where
  f : ((x : X) → Y x) → ((x : X) → Y' x)
  f h x = ⌜ φ x ⌝ (h x)

  g : ((x : X) → Y' x) → (x : X) → Y x
  g k x = ⌜ φ x ⌝⁻¹ (k x)

  fg : (k : ((x : X) → Y' x)) → f (g k) ＝ k
  fg k = dfunext fe'
          (λ x → inverses-are-sections ⌜ φ x ⌝ ⌜ φ x ⌝-is-equiv (k x))

  gf : (h : ((x : X) → Y x)) → g (f h) ＝ h
  gf h = dfunext fe
          (λ x → inverses-are-retractions ⌜ φ x ⌝ ⌜ φ x ⌝-is-equiv (h x))

\end{code}

An application of Π-cong is the following:

\begin{code}

≃-funext₂ : funext 𝓤 (𝓥 ⊔ 𝓦)
          → funext 𝓥 𝓦
          → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : (x : X) → Y x → 𝓦 ̇ }
            (f g : (x : X) (y : Y x) → A x y)
          → (f ＝ g) ≃ (∀ x y → f x y ＝ g x y)
≃-funext₂ fe fe' {X} f g =
 (f ＝ g)           ≃⟨ ≃-funext fe f g ⟩
 (f ∼ g)            ≃⟨ Π-cong fe fe (λ x → ≃-funext fe' (f x) (g x)) ⟩
 (∀ x → f x ∼ g x)  ■

𝟙-lneutral : {Y : 𝓤 ̇ } → 𝟙 {𝓥} × Y ≃ Y
𝟙-lneutral {𝓤} {𝓥} {Y} = qinveq f (g , ε , η)
 where
  f : 𝟙 × Y → Y
  f (o , y) = y

  g : Y → 𝟙 × Y
  g y = (⋆ , y)

  η : ∀ x → f (g x) ＝ x
  η y = refl

  ε : ∀ z → g (f z) ＝ z
  ε (o , y) = ap (_, y) (𝟙-is-prop ⋆ o)

×-comm : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × Y ≃ Y × X
×-comm {𝓤} {𝓥} {X} {Y} = qinveq f (g , ε , η)
 where
  f : X × Y → Y × X
  f (x , y) = (y , x)

  g : Y × X → X × Y
  g (y , x) = (x , y)

  η : ∀ z → f (g z) ＝ z
  η z = refl

  ε : ∀ t → g (f t) ＝ t
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

  ε : (t : Y + X) → (f ∘ g) t ＝ t
  ε (inl y) = refl
  ε (inr x) = refl

  η : (u : X + Y) → (g ∘ f) u ＝ u
  η (inl x) = refl
  η (inr y) = refl

one-𝟘-only : 𝟘 {𝓤} ≃ 𝟘 {𝓥}
one-𝟘-only = qinveq 𝟘-elim (𝟘-elim , 𝟘-induction , 𝟘-induction)

one-𝟙-only : {𝓤 𝓥 : Universe} → 𝟙 {𝓤} ≃ 𝟙 {𝓥}
one-𝟙-only = qinveq unique-to-𝟙 (unique-to-𝟙 , (λ ⋆ → refl) , (λ ⋆ → refl))

𝟘-rneutral : {X : 𝓤 ̇ } → X ≃ X + 𝟘 {𝓥}
𝟘-rneutral {𝓤} {𝓥} {X} = qinveq f (g , η , ε)
 where
  f : X → X + 𝟘
  f = inl

  g : X + 𝟘 → X
  g (inl x) = x
  g (inr y) = 𝟘-elim y

  ε : (y : X + 𝟘) → (f ∘ g) y ＝ y
  ε (inl x) = refl
  ε (inr y) = 𝟘-elim y

  η : (x : X) → (g ∘ f) x ＝ x
  η x = refl

𝟘-rneutral' : {X : 𝓤 ̇ } → X + 𝟘 {𝓥} ≃ X
𝟘-rneutral' = ≃-sym 𝟘-rneutral

𝟘-lneutral : {X : 𝓤 ̇ } → 𝟘 {𝓥} + X ≃ X
𝟘-lneutral {𝓤} {𝓥} {X} = (𝟘 + X) ≃⟨ +comm ⟩
                         (X + 𝟘) ≃⟨ 𝟘-rneutral' {𝓤} {𝓥} ⟩
                         X       ■

𝟘-lneutral' : {X : 𝓤 ̇ } → X ≃ 𝟘 {𝓥} + X
𝟘-lneutral' = ≃-sym 𝟘-lneutral

𝟘-lneutral'' : 𝟙 {𝓤} ≃ 𝟘 {𝓥} + 𝟙 {𝓦}
𝟘-lneutral'' {𝓤} {𝓥} {𝓦} =
 𝟙 {𝓤}           ≃⟨ one-𝟙-only ⟩
 𝟙 {𝓦}           ≃⟨ 𝟘-lneutral' ⟩
 (𝟘 {𝓥} + 𝟙 {𝓦}) ■

+assoc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
       → (X + Y) + Z ≃ X + (Y + Z)
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

  ε : (t : X + (Y + Z)) → (f ∘ g) t ＝ t
  ε (inl x)       = refl
  ε (inr (inl y)) = refl
  ε (inr (inr z)) = refl

  η : (u : (X + Y) + Z) → (g ∘ f) u ＝ u
  η (inl (inl x)) = refl
  η (inl (inr x)) = refl
  η (inr x)       = refl

+-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
       → X ≃ A → Y ≃ B → X + Y ≃ A + B
+-cong f g = qinveq (+functor ⌜ f ⌝ ⌜ g ⌝) (+functor ⌜ f ⌝⁻¹ ⌜ g ⌝⁻¹ , ε , η)
 where
  ε : +functor ⌜ f ⌝⁻¹ ⌜ g ⌝⁻¹ ∘ +functor ⌜ f ⌝ ⌜ g ⌝ ∼ id
  ε (inl x) = ap inl (inverses-are-retractions ⌜ f ⌝ ⌜ f ⌝-is-equiv x)
  ε (inr y) = ap inr (inverses-are-retractions ⌜ g ⌝ ⌜ g ⌝-is-equiv y)

  η : +functor ⌜ f ⌝ ⌜ g ⌝ ∘ +functor ⌜ f ⌝⁻¹ ⌜ g ⌝⁻¹ ∼ id
  η (inl a) = ap inl (inverses-are-sections ⌜ f ⌝ ⌜ f ⌝-is-equiv a)
  η (inr b) = ap inr (inverses-are-sections ⌜ g ⌝ ⌜ g ⌝-is-equiv b)

×𝟘 : {X : 𝓤 ̇ } → 𝟘 {𝓥} ≃ X × 𝟘 {𝓦}
×𝟘 {𝓤} {𝓥} {𝓦} {X} = qinveq
                       unique-from-𝟘
                       ((λ (x , y) → 𝟘-elim y) ,
                        𝟘-induction ,
                        (λ (x , y) → 𝟘-elim y))

𝟙distr : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × Y + X ≃ X × (Y + 𝟙 {𝓦})
𝟙distr {𝓤} {𝓥} {𝓦} {X} {Y} = qinveq f (g , η , ε)
 where
  f : X × Y + X → X × (Y + 𝟙)
  f (inl (x , y)) = x , inl y
  f (inr x)       = x , inr ⋆

  g : X × (Y + 𝟙) → X × Y + X
  g (x , inl y) = inl (x , y)
  g (x , inr O) = inr x

  ε : f ∘ g ∼ id
  ε (x , inl y) = refl
  ε (x , inr ⋆) = refl

  η : g ∘ f ∼ id
  η (inl (x , y)) = refl
  η (inr x)       = refl

Ap+ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (Z : 𝓦 ̇ ) → X ≃ Y → X + Z ≃ Y + Z
Ap+ {𝓤} {𝓥} {𝓦} {X} {Y} Z f =
 qinveq (+functor ⌜ f ⌝ id) (+functor ⌜ f ⌝⁻¹ id , η , ε)
  where
   η : +functor ⌜ f ⌝⁻¹ id ∘ +functor ⌜ f ⌝ id ∼ id
   η (inl x) = ap inl (inverses-are-retractions ⌜ f ⌝ ⌜ f ⌝-is-equiv x)
   η (inr z) = ap inr refl

   ε : +functor ⌜ f ⌝ id ∘ +functor ⌜ f ⌝⁻¹ id ∼ id
   ε (inl x) = ap inl (inverses-are-sections ⌜ f ⌝ ⌜ f ⌝-is-equiv x)
   ε (inr z) = ap inr refl

×comm : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × Y ≃ Y × X
×comm {𝓤} {𝓥} {X} {Y} = qinveq
                         (λ (x , y) → (y , x))
                         ((λ (y , x) → (x , y)) ,
                          (λ _ → refl) ,
                          (λ _ → refl))

×-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
       → X ≃ A → Y ≃ B → X × Y ≃ A × B
×-cong f g = qinveq (×functor ⌜ f ⌝ ⌜ g ⌝) (×functor ⌜ f ⌝⁻¹ ⌜ g ⌝⁻¹ , ε , η)
 where
  ε : ×functor ⌜ f ⌝⁻¹ ⌜ g ⌝⁻¹ ∘ ×functor ⌜ f ⌝ ⌜ g ⌝ ∼ id
  ε (x , y) = to-×-＝
               (inverses-are-retractions ⌜ f ⌝ ⌜ f ⌝-is-equiv x)
               (inverses-are-retractions ⌜ g ⌝ ⌜ g ⌝-is-equiv y)

  η : ×functor ⌜ f ⌝ ⌜ g ⌝ ∘ ×functor ⌜ f ⌝⁻¹ ⌜ g ⌝⁻¹ ∼ id
  η (a , b) = to-×-＝
               (inverses-are-sections ⌜ f ⌝ ⌜ f ⌝-is-equiv a)
               (inverses-are-sections ⌜ g ⌝ ⌜ g ⌝-is-equiv b)

𝟘→ : {X : 𝓤 ̇ }
   → funext 𝓦 𝓤
   → 𝟙 {𝓥} ≃ (𝟘 {𝓦} → X)
𝟘→ {𝓤} {𝓥} {𝓦} {X} fe = qinveq f (g , η , ε)
 where
  f : 𝟙 → (𝟘 → X)
  f ⋆ y = 𝟘-elim y

  g : (𝟘 → X) → 𝟙
  g h = ⋆

  ε : f ∘ g ∼ id
  ε h = dfunext fe (λ z → 𝟘-elim z)

  η : g ∘ f ∼ id
  η ⋆ = refl

𝟙→ : {X : 𝓤 ̇ }
   → funext 𝓥 𝓤
   → X ≃ (𝟙 {𝓥} → X)
𝟙→ {𝓤} {𝓥} {X} fe = qinveq f (g , η , ε)
 where
  f : X → 𝟙 → X
  f x ⋆ = x

  g : (𝟙 → X) → X
  g h = h ⋆

  ε : (h : 𝟙 → X) → f (g h) ＝ h
  ε h = dfunext fe γ
   where
    γ : (t : 𝟙) → f (g h) t ＝ h t
    γ ⋆ = refl

  η : (x : X) → g (f x) ＝ x
  η x = refl

→𝟙 : {X : 𝓤 ̇ } → funext 𝓤 𝓥
   → (X → 𝟙 {𝓥}) ≃ 𝟙 {𝓥}
→𝟙 {𝓤} {𝓥} {X} fe = qinveq f (g , ε , η)
 where
  f : (X → 𝟙) → 𝟙
  f = unique-to-𝟙

  g : (t : 𝟙) → X → 𝟙
  g t = unique-to-𝟙

  ε : (α : X → 𝟙) → g ⋆ ＝ α
  ε α = dfunext fe λ (x : X) → 𝟙-is-prop (g ⋆ x) (α x)

  η : (t : 𝟙) → ⋆ ＝ t
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
    γ : (z : X + Y) → (f ∘ g) h z ＝ h z
    γ (inl x) = refl
    γ (inr y) = refl

  ε : g ∘ f ∼ id
  ε (l , r) = refl


+→ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
   → funext (𝓤 ⊔ 𝓥) 𝓦
   → (X + Y → Z) ≃ (X → Z) × (Y → Z)
+→ fe = ≃-sym (Π×+ fe)

→× : {A : 𝓤 ̇ } {X : A → 𝓥 ̇ } {Y : A → 𝓦 ̇ }
   → ((a : A) → X a × Y a)  ≃ Π X × Π Y
→× {𝓤} {𝓥} {𝓦} {A} {X} {Y} = qinveq f (g , ε , η)
 where
  f : ((a : A) → X a × Y a) → Π X × Π Y
  f φ = (λ a → pr₁ (φ a)) , (λ a → pr₂ (φ a))

  g : Π X × Π Y → (a : A) → X a × Y a
  g (γ , δ) a = γ a , δ a

  ε : (φ : (a : A) → X a × Y a) → g (f φ) ＝ φ
  ε φ = refl

  η : (α : Π X × Π Y) → f (g α) ＝ α
  η (γ , δ) = refl

→cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
      → funext 𝓦 𝓣
      → funext 𝓤 𝓥
      → X ≃ A → Y ≃ B → (X → Y) ≃ (A → B)
→cong {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} fe fe' f g =
 qinveq ϕ (γ , ((λ h → dfunext fe' (η h)) , (λ k → dfunext fe (ε k))))
   where
    ϕ : (X → Y) → (A → B)
    ϕ h = ⌜ g ⌝ ∘ h ∘ ⌜ f ⌝⁻¹

    γ : (A → B) → (X → Y)
    γ k = ⌜ g ⌝⁻¹ ∘ k ∘ ⌜ f ⌝

    ε : (k : A → B) → ϕ (γ k) ∼ k
    ε k a = ⌜ g ⌝ (⌜ g ⌝⁻¹ (k (⌜ f ⌝ (⌜ f ⌝⁻¹ a)))) ＝⟨ I ⟩
            k (⌜ f ⌝ (⌜ f ⌝⁻¹ a))                   ＝⟨ II ⟩
            k a                                     ∎
             where
              I  = inverses-are-sections ⌜ g ⌝ ⌜ g ⌝-is-equiv _
              II = ap k (inverses-are-sections ⌜ f ⌝ ⌜ f ⌝-is-equiv a)

    η : (h : X → Y) → γ (ϕ h) ∼ h
    η h x = ⌜ g ⌝⁻¹ (⌜ g ⌝ (h (⌜ f ⌝⁻¹ (⌜ f ⌝ x)))) ＝⟨ I ⟩
            h (⌜ f ⌝⁻¹ (⌜ f ⌝ x))                   ＝⟨ II ⟩
            h x                                     ∎
             where
              I  = inverses-are-retractions ⌜ g ⌝ ⌜ g ⌝-is-equiv _
              II = ap h (inverses-are-retractions ⌜ f ⌝ ⌜ f ⌝-is-equiv x)

→cong' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {B : 𝓣 ̇ }
       → funext 𝓤 𝓣
       → funext 𝓤 𝓥
       → Y ≃ B → (X → Y) ≃ (X → B)
→cong' fe fe' = →cong fe fe' (≃-refl _)

→cong'' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
        → funext 𝓦 𝓥
        → funext 𝓤 𝓥
        → X ≃ A → (X → Y) ≃ (A → Y)
→cong'' fe fe' e = →cong fe fe' e (≃-refl _)

pr₁-≃ : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
      → ((x : X) → is-singleton (A x))
      → (Σ x ꞉ X , A x) ≃ X
pr₁-≃ X A f = pr₁ , pr₁-is-equiv X A f

NatΣ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                 → (x : X) (b : B x) → fiber (ζ x) b ≃ fiber (NatΣ ζ) (x , b)
NatΣ-fiber-equiv A B ζ x b = qinveq (f b) (g b , ε b , η b)
 where
  f : (b : B x) → fiber (ζ x) b → fiber (NatΣ ζ) (x , b)
  f _ (a , refl) = (x , a) , refl

  g : (b : B x) → fiber (NatΣ ζ) (x , b) → fiber (ζ x) b
  g _ ((x , a) , refl) = a , refl

  ε : (b : B x) (w : fiber (ζ x) b) → g b (f b w) ＝ w
  ε _ (a , refl) = refl

  η : (b : B x) (t : fiber (NatΣ ζ) (x , b)) → f b (g b t) ＝ t
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

NatΣ-is-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
              → ((x : X) → is-equiv (ζ x))
              → is-equiv (NatΣ ζ)
NatΣ-is-equiv A B ζ i = vv-equivs-are-equivs
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
Σ-cong' A B f = NatΣ (λ x → ⌜ f x ⌝) ,
                NatΣ-is-equiv A B (λ x → ⌜ f x ⌝) (λ x → ⌜ f x ⌝-is-equiv)

Σ-change-of-variable' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X → 𝓦 ̇ ) (g : Y → X)
                      → is-hae g
                      → Σ γ ꞉ ((Σ y ꞉ Y , A (g y)) → Σ A) , qinv γ
Σ-change-of-variable' {𝓤} {𝓥} {𝓦} {X} {Y} A g (f , η , ε , α) = γ , φ , φγ , γφ
 where
  γ : (Σ y ꞉ Y , A (g y)) → Σ A
  γ (y , a) = (g y , a)

  φ : Σ A → Σ y ꞉ Y , A (g y)
  φ (x , a) = (f x , transport⁻¹ A (ε x) a)

  γφ : (σ : Σ A) → γ (φ σ) ＝ σ
  γφ (x , a) = to-Σ-＝ (ε x , p)
   where
    p : transport A (ε x) (transport⁻¹ A (ε x) a) ＝ a
    p = back-and-forth-transport (ε x)

  φγ : (τ : (Σ y ꞉ Y , A (g y))) → φ (γ τ) ＝ τ
  φγ (y , a) = to-Σ-＝ (η y , q)
   where
    q = transport (λ - → A (g -)) (η y) (transport⁻¹ A (ε (g y)) a) ＝⟨ i ⟩
        transport A (ap g (η y)) (transport⁻¹ A (ε (g y)) a)        ＝⟨ ii ⟩
        transport A (ε (g y)) (transport⁻¹ A (ε (g y)) a)           ＝⟨ iii ⟩
        a                                                           ∎
     where
      i   = transport-ap A g (η y)
      ii  = ap (λ - → transport A - (transport⁻¹ A (ε (g y)) a)) (α y)
      iii = back-and-forth-transport (ε (g y))

Σ-change-of-variable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X → 𝓦 ̇ ) (g : Y → X)
                     → is-equiv g
                     → (Σ y ꞉ Y , A (g y)) ≃ (Σ x ꞉ X , A x)
Σ-change-of-variable {𝓤} {𝓥} {𝓦} {X} {Y} A g e = γ , qinvs-are-equivs γ q
 where
  γ :  (Σ y ꞉ Y , A (g y)) → Σ A
  γ = pr₁ (Σ-change-of-variable' A g (equivs-are-haes g e))

  q :  qinv γ
  q = pr₂ (Σ-change-of-variable' A g (equivs-are-haes g e))

Σ-change-of-variable-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X → 𝓦 ̇ ) (e : Y ≃ X)
                       → (Σ y ꞉ Y , A (⌜ e ⌝ y)) ≃ (Σ x ꞉ X , A x)
Σ-change-of-variable-≃ A (g , i) = Σ-change-of-variable A g i

Σ-bicong : {X  : 𝓤 ̇ } (Y  : X  → 𝓥 ̇ )
           {X' : 𝓤' ̇ } (Y' : X' → 𝓥' ̇ )
           (𝕗 : X ≃ X')
         → ((x : X) → Y x ≃ Y' (⌜ 𝕗 ⌝ x))
         → Σ Y ≃ Σ Y'
Σ-bicong {𝓤} {𝓥} {𝓤'} {𝓥'} {X} Y {X'} Y' 𝕗 φ =
 Σ Y                      ≃⟨ Σ-cong φ ⟩
 (Σ x ꞉ X , Y' (⌜ 𝕗 ⌝ x)) ≃⟨ Σ-change-of-variable-≃ Y' 𝕗 ⟩
 Σ Y'                     ■

dprecomp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
         → Π A → Π (A ∘ f)

dprecomp A f = _∘ f

dprecomp-is-equiv : funext 𝓤 𝓦
                  → funext 𝓥 𝓦
                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                  → is-equiv f
                  → is-equiv (dprecomp A f)

dprecomp-is-equiv fe fe' {X} {Y} A f i = qinvs-are-equivs φ ((ψ , ψφ , φψ))
 where
  g = inverse f i
  η = inverses-are-retractions f i
  ε = inverses-are-sections f i

  τ : (x : X) → ap f (η x) ＝ ε (f x)
  τ = half-adjoint-condition f i

  φ : Π A → Π (A ∘ f)
  φ = dprecomp A f

  ψ : Π (A ∘ f) → Π A
  ψ k y = transport A (ε y) (k (g y))

  φψ₀ : (k : Π (A ∘ f)) (x : X) → transport A (ε (f x)) (k (g (f x))) ＝ k x
  φψ₀ k x = transport A (ε (f x))   (k (g (f x))) ＝⟨ a ⟩
            transport A (ap f (η x))(k (g (f x))) ＝⟨ b ⟩
            transport (A ∘ f) (η x) (k (g (f x))) ＝⟨ c ⟩
            k x                                   ∎
    where
     a = ap (λ - → transport A - (k (g (f x)))) ((τ x)⁻¹)
     b = (transport-ap A f (η x)) ⁻¹
     c = apd k (η x)

  φψ : φ ∘ ψ ∼ id
  φψ k = dfunext fe (φψ₀ k)

  ψφ₀ : (h : Π A) (y : Y) → transport A (ε y) (h (f (g y))) ＝ h y
  ψφ₀ h y = apd h (ε y)

  ψφ : ψ ∘ φ ∼ id
  ψφ h = dfunext fe' (ψφ₀ h)

Π-change-of-variable : funext 𝓤 𝓦
                     → funext 𝓥 𝓦
                     → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                     → is-equiv f
                     → (Π y ꞉ Y , A y) ≃ (Π x ꞉ X , A (f x))
Π-change-of-variable fe fe' A f i = dprecomp A f , dprecomp-is-equiv fe fe' A f i

Π-change-of-variable-≃ : FunExt
                       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (𝕗 : X ≃ Y)
                       → (Π x ꞉ X , A (⌜ 𝕗 ⌝ x)) ≃ (Π y ꞉ Y , A y)
Π-change-of-variable-≃ fe A (f , i) =
 ≃-sym (Π-change-of-variable (fe _ _) (fe _ _) A f i)

Π-bicong : FunExt
         → {X  : 𝓤 ̇ } (Y  : X  → 𝓥 ̇ )
           {X' : 𝓤' ̇ } (Y' : X' → 𝓥' ̇ )
           (𝕗 : X ≃ X')
         → ((x : X) → Y x ≃ Y' (⌜ 𝕗 ⌝ x))
         → Π Y ≃ Π Y'
Π-bicong {𝓤} {𝓥} {𝓤'} {𝓥'} fe {X} Y {X'} Y' 𝕗 φ =
 Π Y                      ≃⟨ Π-cong (fe 𝓤 𝓥) (fe 𝓤 𝓥') φ ⟩
 (Π x ꞉ X , Y' (⌜ 𝕗 ⌝ x)) ≃⟨ Π-change-of-variable-≃ fe Y' 𝕗 ⟩
 Π Y'                     ■

NatΠ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                 → funext 𝓤 𝓦
                 → (g : Π B)
                 → (Π x ꞉ X , fiber (ζ x) (g x)) ≃ fiber (NatΠ ζ) g
NatΠ-fiber-equiv {𝓤} {𝓥} {𝓦} {X} A B ζ fe g =
  (Π x ꞉ X , fiber (ζ x) (g x))            ≃⟨ i ⟩
  (Π x ꞉ X , Σ a ꞉ A x , ζ x a ＝ g x)     ≃⟨ ii ⟩
  (Σ f ꞉ Π A , Π x ꞉ X , ζ x (f x) ＝ g x) ≃⟨ iii ⟩
  (Σ f ꞉ Π A , (λ x → ζ x (f x)) ＝ g)     ≃⟨ iv ⟩
  fiber (NatΠ ζ) g                         ■
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

Π-cong' : {X : 𝓤 ̇ }
        → funext 𝓤 (𝓥 ⊔ 𝓦)
        → {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
        → ((x : X) → A x ≃ B x)
        → Π A ≃ Π B
Π-cong' fe {A} {B} e = NatΠ (λ x → pr₁ (e x)) ,
                       NatΠ-equiv A B (λ x → pr₁ (e x)) fe (λ x → pr₂ (e x))

＝-cong : {X : 𝓤 ̇ } (x y : X) {x' y' : X}
        → x ＝ x'
        → y ＝ y'
        → (x ＝ y) ≃ (x' ＝ y')
＝-cong x y refl refl = ≃-refl (x ＝ y)

＝-cong-l : {X : 𝓤 ̇ } (x y : X) {x' : X}
          → x ＝ x'
          → (x ＝ y) ≃ (x' ＝ y)
＝-cong-l x y refl = ≃-refl (x ＝ y)

＝-cong-r : {X : 𝓤 ̇ } (x y : X) {y' : X}
          → y ＝ y'
          → (x ＝ y) ≃ (x ＝ y')
＝-cong-r x y refl = ≃-refl (x ＝ y)

＝-flip : {X : 𝓤 ̇ } {x y : X}
        → (x ＝ y) ≃ (y ＝ x)
＝-flip = _⁻¹ , (_⁻¹ , ⁻¹-involutive) , (_⁻¹ , ⁻¹-involutive)

singleton-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → is-singleton X
            → is-singleton Y
            → X ≃ Y
singleton-≃ i j = (λ _ → center j) , maps-of-singletons-are-equivs _ i j

singleton-≃-𝟙 : {X : 𝓤 ̇ } → is-singleton X → X ≃ 𝟙 {𝓥}
singleton-≃-𝟙 i = singleton-≃ i 𝟙-is-singleton

𝟙-≃-singleton : {X : 𝓤 ̇ } → is-singleton X → 𝟙 {𝓥} ≃ X
𝟙-≃-singleton = singleton-≃ 𝟙-is-singleton

𝟙-＝-≃ : (P : 𝓤 ̇ )
      → funext 𝓤 𝓤
      → propext 𝓤
      → is-prop P
      → (𝟙 ＝ P) ≃ P
𝟙-＝-≃ P fe pe i = qinveq (λ q → Idtofun q ⋆) (f , ε , η)
 where
  f : P → 𝟙 ＝ P
  f p = pe 𝟙-is-prop i (λ _ → p) unique-to-𝟙

  η : (p : P) → Idtofun (f p) ⋆ ＝ p
  η p = i (Idtofun (f p) ⋆) p

  ε : (q : 𝟙 ＝ P) → f (Idtofun q ⋆) ＝ q
  ε q = identifications-with-props-are-props pe fe P i 𝟙 (f (Idtofun q ⋆)) q

empty-≃-𝟘 : {X : 𝓤 ̇ } → (X → 𝟘 {𝓥}) → X ≃ 𝟘 {𝓦}
empty-≃-𝟘 i = qinveq
               (𝟘-elim ∘ i)
               (𝟘-elim ,
                (λ x → 𝟘-elim (i x)) ,
                (λ x → 𝟘-elim x))

complement-is-equiv : is-equiv complement
complement-is-equiv = qinvs-are-equivs
                       complement
                       (complement ,
                        complement-involutive ,
                        complement-involutive)

complement-≃ : 𝟚 ≃ 𝟚
complement-≃ = (complement , complement-is-equiv)

𝟚-≃-𝟙+𝟙 : 𝟚 ≃ 𝟙{𝓤} + 𝟙{𝓤}
𝟚-≃-𝟙+𝟙 = f , qinvs-are-equivs f (g , gf , fg)
 where
  f : 𝟚 → 𝟙 + 𝟙
  f = 𝟚-cases (inl ⋆) (inr ⋆)

  g : 𝟙 + 𝟙 → 𝟚
  g = cases (λ x → ₀) (λ x → ₁)

  fg : (x : 𝟙 + 𝟙) → f (g x) ＝ x
  fg (inl ⋆) = refl
  fg (inr ⋆) = refl

  gf : (x : 𝟚) → g (f x) ＝ x
  gf ₀ = refl
  gf ₁ = refl

alternative-× : funext 𝓤₀ 𝓤
              → {A : 𝟚 → 𝓤 ̇ }
              → (Π n ꞉ 𝟚 , A n) ≃ (A ₀ × A ₁)
alternative-× fe {A} = qinveq ϕ (ψ , η , ε)
 where
  ϕ : (Π n ꞉ 𝟚 , A n) → A ₀ × A ₁
  ϕ f = (f ₀ , f ₁)

  ψ : A ₀ × A ₁ → Π n ꞉ 𝟚 , A n
  ψ (a₀ , a₁) ₀ = a₀
  ψ (a₀ , a₁) ₁ = a₁

  η : ψ ∘ ϕ ∼ id
  η f = dfunext fe (λ {₀ → refl ; ₁ → refl})

  ε : ϕ ∘ ψ ∼ id
  ε (a₀ , a₁) = refl

alternative-+ : {A : 𝟚 → 𝓤 ̇ }
              → (Σ n ꞉ 𝟚 , A n) ≃ (A ₀ + A ₁)
alternative-+ {𝓤} {A} = qinveq ϕ (ψ , η , ε)
 where
  ϕ : (Σ n ꞉ 𝟚 , A n) → A ₀ + A ₁
  ϕ (₀ , a) = inl a
  ϕ (₁ , a) = inr a

  ψ : A ₀ + A ₁ → Σ n ꞉ 𝟚 , A n
  ψ (inl a) = ₀ , a
  ψ (inr a) = ₁ , a

  η : ψ ∘ ϕ ∼ id
  η (₀ , a) = refl
  η (₁ , a) = refl

  ε : ϕ ∘ ψ ∼ id
  ε (inl a) = refl
  ε (inr a) = refl

domain-is-total-fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → X ≃ Σ (fiber f)
domain-is-total-fiber {𝓤} {𝓥} {X} {Y} f =
 X                             ≃⟨ ≃-sym (𝟙-rneutral {𝓤} {𝓤}) ⟩
 X × 𝟙                         ≃⟨ I ⟩
 (Σ x ꞉ X , Σ y ꞉ Y , f x ＝ y) ≃⟨ Σ-flip ⟩
 (Σ y ꞉ Y , Σ x ꞉ X , f x ＝ y) ■
  where
   I =  Σ-cong
         (λ x → singleton-≃ 𝟙-is-singleton
                 (singleton-types-are-singletons (f x)))

total-fiber-is-domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → (Σ y ꞉ Y , Σ x ꞉ X , f x ＝ y) ≃ X
total-fiber-is-domain {𝓤} {𝓥} {X} {Y} f = ≃-sym (domain-is-total-fiber f)

left-Id-equiv : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (x : X)
              → (Σ x' ꞉ X , (x' ＝ x) × Y x') ≃ Y x
left-Id-equiv {𝓤} {𝓥} {X} {Y} x =
   (Σ x' ꞉ X , (x' ＝ x) × Y x')            ≃⟨ ≃-sym Σ-assoc ⟩
   (Σ (x' , _) ꞉ singleton-type' x , Y x') ≃⟨ a ⟩
   Y x                                     ■
  where
   a = prop-indexed-sum (singleton'-center x) (singleton-types'-are-props x)

right-Id-equiv : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (x : X)
               → (Σ x' ꞉ X , Y x' × (x' ＝ x)) ≃ Y x
right-Id-equiv {𝓤} {𝓥} {X} {Y} x =
   (Σ x' ꞉ X , Y x' × (x' ＝ x))  ≃⟨ Σ-cong (λ x' → ×-comm) ⟩
   (Σ x' ꞉ X , (x' ＝ x) × Y x')  ≃⟨ left-Id-equiv x ⟩
   Y x                           ■

pr₁-fiber-equiv : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (x : X)
                → fiber (pr₁ {𝓤} {𝓥} {X} {Y}) x ≃ Y x
pr₁-fiber-equiv {𝓤} {𝓥} {X} {Y} x =
  fiber pr₁ x                   ≃⟨ Σ-assoc ⟩
  (Σ x' ꞉ X , Y x' × (x' ＝ x))  ≃⟨ right-Id-equiv x ⟩
  Y x                           ■

\end{code}

Tom de Jong, September 2019 (two lemmas used in UF.Classifiers-Old)

A nice application of Σ-change-of-variable is that the fiber of a map doesn't
change (up to equivalence, at least) when precomposing with an equivalence.

These two lemmas are used in UF.Classifiers-Old, but are sufficiently general to
warrant their place here.

\begin{code}

precomposition-with-equiv-does-not-change-fibers
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
   (e : Z ≃ X) (f : X → Y) (y : Y)
 → fiber (f ∘ ⌜ e ⌝) y ≃ fiber f y
precomposition-with-equiv-does-not-change-fibers (g , i) f y =
 Σ-change-of-variable (λ - → f - ＝ y) g i

retract-pointed-fibers : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {r : Y → X}
                       → has-section r ≃ (Π x ꞉ X , fiber r x)
retract-pointed-fibers {𝓤} {𝓥} {X} {Y} {r} = qinveq f (g , (p , q))
 where
  f : (Σ s ꞉ (X → Y) , r ∘ s ∼ id) → Π (fiber r)
  f (s , rs) x = (s x) , (rs x)

  g : ((x : X) → fiber r x) → Σ s ꞉ (X → Y) , r ∘ s ∼ id
  g α = (λ (x : X) → pr₁ (α x)) , (λ (x : X) → pr₂ (α x))

  p : (srs : Σ s ꞉ (X → Y) , r ∘ s ∼ id) → g (f srs) ＝ srs
  p (s , rs) = refl

  q : (α : Π x ꞉ X , fiber r x) → f (g α) ＝ α
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

   ψϕ : (w : fiber (g ∘ f) z) → ψ (ϕ w) ＝ w
   ψϕ (x , refl) = refl

   ϕψ : (w : Σ w ꞉ (fiber g z) , fiber f (fiber-point w))
      → ϕ (ψ w) ＝ w
   ϕψ ((.(f x) , refl) , (x , refl)) = refl

fiber-of-unique-to-𝟙 : {𝓥 : Universe} {X : 𝓤 ̇ }
                     → (u : 𝟙)
                     → fiber (unique-to-𝟙 {_} {𝓥} {X}) u ≃ X
fiber-of-unique-to-𝟙 {𝓤} {𝓥} {X} ⋆ =
 (Σ x ꞉ X , unique-to-𝟙 x ＝ ⋆) ≃⟨ Σ-cong ψ ⟩
 X × 𝟙{𝓥}                      ≃⟨ 𝟙-rneutral ⟩
 X                             ■
  where
   ψ : (x : X) → (⋆ ＝ ⋆) ≃ 𝟙
   ψ x = singleton-≃-𝟙
         (pointed-props-are-singletons refl (props-are-sets 𝟙-is-prop))

∼-fiber-identifications-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : X → Y}
                          → f ∼ g
                          → (y : Y) (x : X)
                          → (f x ＝ y) ≃ (g x ＝ y)
∼-fiber-identifications-≃ {𝓤} {𝓥} {X} {Y} {f} {g} H y x = qinveq α (β , (βα , αβ))
 where
  α : f x ＝ y → g x ＝ y
  α p = (H x) ⁻¹ ∙ p

  β : g x ＝ y → f x ＝ y
  β q = (H x) ∙ q

  βα : (p : f x ＝ y) → β (α p) ＝ p
  βα p = β (α p)                ＝⟨refl⟩
         (H x) ∙ ((H x) ⁻¹ ∙ p) ＝⟨ (∙assoc (H x) ((H x) ⁻¹) p) ⁻¹ ⟩
         (H x) ∙ (H x) ⁻¹ ∙ p   ＝⟨ ap (λ - → - ∙ p) ((right-inverse (H x)) ⁻¹) ⟩
         refl ∙ p               ＝⟨ refl-left-neutral ⟩
         p                      ∎

  αβ : (q : g x ＝ y) → α (β q) ＝ q
  αβ q = α (β q)                ＝⟨refl⟩
         (H x) ⁻¹ ∙ ((H x) ∙ q) ＝⟨ (∙assoc ((H x) ⁻¹) (H x) q) ⁻¹ ⟩
         (H x) ⁻¹ ∙ (H x) ∙ q   ＝⟨ ap (λ - → - ∙ q) (left-inverse (H x)) ⟩
         refl ∙ q               ＝⟨ refl-left-neutral ⟩
         q                      ∎

∼-fiber-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : X → Y}
          → f ∼ g
          → (y : Y) → fiber f y ≃ fiber g y
∼-fiber-≃ H y = Σ-cong (∼-fiber-identifications-≃ H y)

\end{code}

Added 9 July 2024 by Tom de Jong.

\begin{code}

fiber-of-ap-≃' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B)
                 {x y : A} (p : f x ＝ f y)
               → fiber (ap f) p ≃ ((x , refl) ＝[ fiber' f (f x) ] (y , p))
fiber-of-ap-≃' f {x} {y} p =
 fiber (ap f) p                                              ≃⟨by-definition⟩
 (Σ e ꞉ x ＝ y , transport (λ - → (f x ＝ f -)) e refl ＝ p) ≃⟨ ≃-sym Σ-＝-≃ ⟩
 ((x , refl) ＝ (y , p))                                     ■

fiber-of-ap-≃ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B)
                {x y : A} (p : f x ＝ f y)
              → fiber (ap f) p ≃ ((x , p) ＝[ fiber f (f y) ] (y , refl))
fiber-of-ap-≃ f {x} {y} p =
 fiber (ap f) p                                              ≃⟨ Σ-cong I ⟩
 (Σ e ꞉ x ＝ y , transport (λ - → f - ＝ f y) e p ＝ refl)   ≃⟨ ≃-sym Σ-＝-≃ ⟩
 ((x , p) ＝ (y , refl))                                     ■
  where
   I : (e : x ＝ y)
     → (ap f e ＝ p) ≃ (transport (λ - → f - ＝ f y) e p ＝ refl)
   I refl = (refl ＝ p)                                   ≃⟨ ＝-flip ⟩
            (p ＝ refl)                                   ≃⟨by-definition⟩
            (transport (λ - → f - ＝ f x) refl p ＝ refl) ■

∙-is-equiv-left : {X : 𝓤 ̇ } {x y z : X} (p : z ＝ x)
                → is-equiv (λ (q : x ＝ y) → p ∙ q)
∙-is-equiv-left {𝓤} {X} {x} {y} refl =
 equiv-closed-under-∼ id (refl ∙_) (id-is-equiv (x ＝ y))
  (λ _ → refl-left-neutral)

∙-is-equiv-right : {X : 𝓤 ̇ } {x y z : X} (q : x ＝ y)
                 → is-equiv (λ (p : z ＝ x) → p ∙ q)
∙-is-equiv-right {𝓤} {X} {x} {y} {z} refl = id-is-equiv (z ＝ y)

\end{code}

Added by Tom de Jong, November 2021.

\begin{code}

open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 ∥∥-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → ∥ X ∥ ≃ ∥ Y ∥
 ∥∥-cong f = logically-equivalent-props-are-equivalent ∥∥-is-prop ∥∥-is-prop
              (∥∥-functor ⌜ f ⌝) (∥∥-functor ⌜ f ⌝⁻¹)

 ∃-cong : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Y' : X → 𝓦 ̇ }
        → ((x : X) → Y x ≃ Y' x)
        → ∃ Y ≃ ∃ Y'
 ∃-cong e = ∥∥-cong (Σ-cong e)

 outer-∃-inner-Σ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : (x : X) → Y x → 𝓦 ̇ }
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

Added by Anna Williams 26 February

We show that for subtypes, equality on subtypes is equivalent
to equality on the base type.

\begin{code}

subtype-＝-≃-pr₁-＝ : {X : 𝓤 ̇ }
                     (P : X → 𝓥 ̇ )
                   → ((x : X) → is-prop (P x))
                   → (x y : Σ P)
                   → (x ＝ y) ≃ (pr₁ x ＝ pr₁ y)
subtype-＝-≃-pr₁-＝ {_} {_} {X} P p (x , Px) (y , Py)
 = qinveq f (f⁻¹ , (f-is-section , f-has-section))
 where
  f : (x , Px) ＝ (y , Py) → x ＝ y
  f refl = refl

  f⁻¹ : x ＝ y → (x , Px) ＝ (y , Py)
  f⁻¹ refl = to-Σ-＝' (p x Px Py)

  f-has-section : f ∘ f⁻¹ ∼ id
  f-has-section refl = t (p x Px Py)
   where
    t : Px ＝ Py → (f ∘ f⁻¹) refl ＝ refl
    t refl = ap (f ∘ to-Σ-＝') (props-are-sets (p x) (p x Px Px) refl)

  f-is-section : f⁻¹ ∘ f ∼ id
  f-is-section refl = ap to-Σ-＝' (props-are-sets (p x) (p x Px Px) refl)

\end{code}
