Martin Escardo, 2012

Expanded on demand whenever a general equivalence is needed.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-FunExt

module UF-EquivalenceExamples where

curry-uncurry : (fe : ∀ U V → funext U V)
             → ∀ {U V W} {X : U ̇} {Y : X → V ̇} {Z : (Σ \(x : X) → Y x) → W ̇}
             → Π Z ≃ Π \(x : X) → Π \(y : Y x) → Z(x , y)
curry-uncurry fe {U} {V} {W} {X} {Y} {Z} = c , (u , cu) , (u , uc)
   where
    c : (w : Π Z) → ((x : X) (y : Y x) → Z(x , y))
    c f x y = f (x , y)
    u : ((x : X) (y : Y x) → Z(x , y)) → Π Z
    u g (x , y) = g x y
    cu : ∀ g → c (u g) ≡ g
    cu g = dfunext (fe U (V ⊔ W)) (λ x → dfunext (fe V W) (λ y → refl))
    uc : ∀ f → u (c f) ≡ f
    uc f = dfunext (fe (U ⊔ V) W) (λ w → refl)

Σ-assoc : ∀ {U V W} → {X : U ̇} {Y : X → V ̇} {Z : (Σ \(x : X) → Y x) → W ̇}
        → Σ Z ≃ (Σ \(x : X) → Σ \(y : Y x) → Z(x , y))
Σ-assoc {U} {V} {W} {X} {Y} {Z} = c , (u , λ τ → refl) , (u , λ σ → refl)
   where
    c : Σ Z → Σ \x → Σ \y → Z (x , y)
    c ((x , y) , z) = (x , (y , z))
    u : (Σ \x → Σ \y → Z (x , y)) → Σ Z
    u (x , (y , z)) = ((x , y) , z)

Σ-≃-congruence : ∀ {U V} (X : U ̇) (Y Y' : X → V ̇)
               → ((x : X) → Y x ≃ Y' x) → Σ Y ≃ Σ Y'
Σ-≃-congruence X Y Y' φ = (F , (G , FG) , (H , HF))
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

Π-congruence : (fe : ∀ {U V} → funext U V)
              → ∀ {U V} (X : U ̇) (Y Y' : X → V ̇)
              → ((x : X) → Y x ≃ Y' x) → Π Y ≃ Π Y'
Π-congruence fe X Y Y' φ = (F , (G , FG) , (H , HF))
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
    FG w' = dfunext fe FG'
     where
      FG' : (x : X) → F(G w') x ≡ w' x
      FG' x = fg x (w' x)

    HF : (w : ((x : X) → Y x)) → H(F w) ≡ w
    HF w = dfunext fe GF'
     where
      GF' : (x : X) → H(F w) x ≡ w x
      GF' x = hf x (w x)

𝟙-lneutral : ∀ {U V} {Y : U ̇} → 𝟙 × Y ≃ Y
𝟙-lneutral {U} {V} {Y} = (f , (g , fg) , (g , gf))
  where
    f : 𝟙 {V} × Y → Y
    f (* , y) = y
    g : Y → 𝟙 × Y
    g y = (* , y)
    fg : ∀ x → f (g x) ≡ x
    fg y = refl
    gf : ∀ z → g (f z) ≡ z
    gf (* , y) = refl

×-comm : ∀ {U V} {X : U ̇} {Y : V ̇} → X × Y ≃ Y × X
×-comm {U} {V} {X} {Y} = (f , (g , fg) , (g , gf))
   where
    f : X × Y → Y × X
    f (x , y) = (y , x)
    g : Y × X → X × Y
    g (y , x) = (x , y)
    fg : ∀ z → f (g z) ≡ z
    fg z = refl
    gf : ∀ t → g (f t) ≡ t
    gf t = refl

𝟙-rneutral : ∀ {U V} {Y : U ̇} → Y × 𝟙 ≃ Y
𝟙-rneutral {U} {V} {Y} =
              Y × 𝟙 ≃⟨ ×-comm ⟩
              𝟙 × Y ≃⟨ 𝟙-lneutral {U} {V} ⟩
              Y ■

+comm : ∀ {U V} {X : U ̇} {Y : V ̇} → X + Y ≃ Y + X
+comm {U} {V} {X} {Y} = f , (g , ε) , (g , η)
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

𝟘-rneutral : ∀ {U V} {X : U ̇} → X ≃ X + 𝟘
𝟘-rneutral {U} {V} {X} = f , (g , ε) , (g , η)
  where
    f : X → X + 𝟘 {V}
    f = inl
    g : X + 𝟘 → X
    g (inl x) = x
    g (inr ())
    ε : (y : X + 𝟘) → (f ∘ g) y ≡ y
    ε (inl x) = refl
    ε (inr ())
    η : (x : X) → (g ∘ f) x ≡ x
    η x = refl

𝟘-rneutral' : ∀ {U V} {X : U ̇} → X + 𝟘 ≃ X
𝟘-rneutral' {U} {V} = ≃-sym (𝟘-rneutral {U} {V})

𝟘-lneutral : ∀ {U V} {X : U ̇} → 𝟘 + X ≃ X
𝟘-lneutral {U} {V} {X} = (𝟘 + X) ≃⟨ +comm ⟩
                         (X + 𝟘) ≃⟨ 𝟘-rneutral' {U} {V} ⟩
                         X ■

+assoc : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} → (X + Y) + Z ≃ X + (Y + Z)
+assoc {U} {V} {W} {X} {Y} {Z} = f , (g , ε) , (g , η)
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

+-cong : ∀ {U V W T} {X : U ̇} {Y : W ̇} {A : V ̇} {B : T ̇}
      → X ≃ A → Y ≃ B → X + Y ≃ A + B
+-cong {U} {V} {W} {T} {X} {Y} {A} {B} (f , (g , e) , (g' , d)) (φ , (γ , ε) , (γ' , δ)) =
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

×𝟘 : ∀ {U V W} {X : U ̇} → 𝟘 ≃ X × 𝟘
×𝟘 {U} {V} {W} {X} = f , (g , ε) , (g , η)
  where
    f : 𝟘 {V} → X × 𝟘 {W}
    f ()
    g : X × 𝟘 → 𝟘
    g (x , ())
    ε : (t : X × 𝟘) → (f ∘ g) t ≡ t
    ε (x , ())
    η : (u : 𝟘) → (g ∘ f) u ≡ u
    η ()

𝟙distr : ∀ {U V W} {X : U ̇} {Y : V ̇} → X × Y + X ≃ X × (Y + 𝟙)
𝟙distr {U} {V} {W} {X} {Y} = f , (g , ε) , (g , η)
  where
    f : X × Y + X → X × (Y + 𝟙 {W})
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

Ap+ : ∀ {U V W} {X : U ̇} {Y : V ̇} (Z : W ̇) → X ≃ Y → X + Z ≃ Y + Z
Ap+ {U} {V} {W} {X} {Y} Z (f , (g , ε) , (h , η)) = f' , (g' , ε') , (h' , η')
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

×comm :  ∀ {U V} {X : U ̇} {Y : V ̇} → X × Y ≃ Y × X
×comm {U} {V} {X} {Y} = f , (g , ε) , (g , η)
  where
    f : X × Y → Y × X
    f (x , y) = (y , x)
    g : Y × X → X × Y
    g (y , x) = (x , y)
    ε : (t : Y × X) → (f ∘ g) t ≡ t
    ε (y , x) = refl
    η : (u : X × Y) → (g ∘ f) u ≡ u
    η (x , y) = refl

×-cong : ∀ {U V W T} {X : U ̇} {Y : W ̇} {A : V ̇} {B : T ̇}
      → X ≃ A → Y ≃ B → X × Y ≃ A × B
×-cong {U} {V} {W} {T} {X} {Y} {A} {B} (f , (g , e) , (g' , d)) (φ , (γ , ε) , (γ' , δ)) =
 F , (G , E) , (G' , D)
 where
  F : X × Y → A × B
  F (x , y) = f x , φ y
  G : A × B → X × Y
  G (a , b) = g a , γ b
  G' : A × B → X × Y
  G' (a , b) = g' a , γ' b
  E : (c : A × B) → F (G c) ≡ c
  E (a , b) = ×-≡ (e a) (ε b)
  D : (z : X × Y) → G' (F z) ≡ z
  D (x , y) = ×-≡ (d x) (δ y)

𝟘→ : ∀ {U V W} {X : U ̇} → funext W U
   → 𝟙 ≃ (𝟘 → X)
𝟘→ {U} {V} {W} {X} fe = f , (g , ε) , (g , η)
 where
  f : 𝟙 {V} → 𝟘 {W} → X
  f * ()
  g : (𝟘 → X) → 𝟙
  g h = *
  ε : (h : 𝟘 → X) → f (g h) ≡ h
  ε h = dfunext fe (λ z → 𝟘-elim z)
  η : (y : 𝟙) → g (f y) ≡ y
  η * = refl

𝟙→ : ∀ {U V} {X : U ̇} → funext V U
   → X ≃ (𝟙 → X)
𝟙→ {U} {V} {X} fe = f , (g , ε) , (g , η)
 where
  f : X → 𝟙 {V} → X
  f x * = x
  g : (𝟙 → X) → X
  g h = h *
  ε : (h : 𝟙 → X) → f (g h) ≡ h
  ε h = dfunext fe γ
   where
    γ : (t : 𝟙) → f (g h) t ≡ h t
    γ * = refl
  η : (x : X) → g (f x) ≡ x
  η x = refl

+→ : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} → funext (U ⊔ V) W
   → ((X + Y) → Z) ≃ (X → Z) × (Y → Z)
+→ {U} {V} {W} {X} {Y} {Z} fe = f , (g , ε) , (g , η)
 where
  f : (X + Y → Z) → (X → Z) × (Y → Z)
  f h = h ∘ inl , h ∘ inr
  g : (X → Z) × (Y → Z) → X + Y → Z
  g (l , r) (inl x) = l x
  g (l , r) (inr y) = r y
  ε : (w : (X → Z) × (Y → Z)) → f (g w) ≡ w
  ε (l , r) = refl
  η : (h : X + Y → Z) → g (f h) ≡ h
  η h = dfunext fe γ
   where
    γ : (t : X + Y) → g (f h) t ≡ h t
    γ (inl x) = refl
    γ (inr y) = refl

→-cong : ∀ {U V W T} {X : U ̇} {Y : W ̇} {A : V ̇} {B : T ̇}
       → funext V T
       → funext U W
       → X ≃ A → Y ≃ B → (X → Y) ≃ (A → B)
→-cong {U} {V} {W} {T} {X} {Y} {A} {B} fe fe' (f , i) (φ , j) =
 H (is-equiv-qinv f i) (is-equiv-qinv φ j)
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

\end{code}
