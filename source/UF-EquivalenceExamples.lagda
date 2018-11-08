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

private
 variable T : Universe

curry-uncurry : (fe : ∀ U V → funext U V)
              → {X : U ̇} {Y : X → V ̇} {Z : (Σ \(x : X) → Y x) → W ̇}
              → Π Z ≃ Π \(x : X) → Π \(y : Y x) → Z(x , y)
curry-uncurry {U} {V} {W} fe {X} {Y} {Z} = c , (u , cu) , (u , uc)
 where
  c : (w : Π Z) → ((x : X) (y : Y x) → Z(x , y))
  c f x y = f (x , y)
  u : ((x : X) (y : Y x) → Z(x , y)) → Π Z
  u g (x , y) = g x y
  cu : ∀ g → c (u g) ≡ g
  cu g = dfunext (fe U (V ⊔ W)) (λ x → dfunext (fe V W) (λ y → refl))
  uc : ∀ f → u (c f) ≡ f
  uc f = dfunext (fe (U ⊔ V) W) (λ w → refl)

Σ-≡-≃ : {X : U ̇} {A : X → V ̇} {σ τ : Σ A}
      → (σ ≡ τ) ≃ (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
Σ-≡-≃ {U} {V} {X} {A} {x , a} {y , b} = from-Σ-≡ , (to-Σ-≡ , η) , (to-Σ-≡ , ε)
 where
  η : (σ : Σ \(p : x ≡ y) → transport A p a ≡ b) → from-Σ-≡ (to-Σ-≡ σ) ≡ σ
  η (refl , refl) = refl
  ε : (q : x , a ≡ y , b) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  ε refl = refl

×-≡-≃ : {X : U ̇} {A : V ̇} {σ τ : X × A}
      → (σ ≡ τ) ≃ (pr₁ σ ≡ pr₁ τ) × (pr₂ σ ≡ pr₂ τ)
×-≡-≃ {U} {V} {X} {A} {x , a} {y , b} = from-×-≡' , (to-×-≡' , η) , (to-×-≡' , ε)
 where
  η : (t : (x ≡ y) × (a ≡ b)) → from-×-≡' (to-×-≡' t) ≡ t
  η (refl , refl) = refl
  ε : (u : x , a ≡ y , b) → to-×-≡' (from-×-≡' u) ≡ u
  ε refl = refl

Σ-assoc : {X : U ̇} {Y : X → V ̇} {Z : Σ Y → W ̇}
        → Σ Z ≃ (Σ \(x : X) → Σ \(y : Y x) → Z(x , y))
Σ-assoc {U} {V} {W} {X} {Y} {Z} = c , (u , λ τ → refl) , (u , λ σ → refl)
 where
  c : Σ Z → Σ \x → Σ \y → Z (x , y)
  c ((x , y) , z) = (x , (y , z))
  u : (Σ \x → Σ \y → Z (x , y)) → Σ Z
  u (x , (y , z)) = ((x , y) , z)

Σ-flip : {X : U ̇} {Y : V ̇} {A : X → Y → W ̇}
       → (Σ \(x : X) → Σ \(y : Y) → A x y) ≃ (Σ \(y : Y) → Σ \(x : X) → A x y)
Σ-flip {U} {V} {W} {X} {Y} {A} = f , (g , η) , (g , ε)
 where
  f : (Σ \(x : X) → Σ \(y : Y) → A x y) → (Σ \(y : Y) → Σ \(x : X) → A x y)
  f (x , y , p) = y , x , p
  g : (Σ \(y : Y) → Σ \(x : X) → A x y) → (Σ \(x : X) → Σ \(y : Y) → A x y)
  g (y , x , p) = x , y , p
  ε : ∀ σ → g (f σ) ≡ σ
  ε (x , y , p) = refl
  η : ∀ τ → f (g τ) ≡ τ
  η (y , x , p) = refl

Σ-cong : {X : U ̇} {Y : X → V ̇} {Y' : X → W ̇}
       → ((x : X) → Y x ≃ Y' x) → Σ Y ≃ Σ Y'
Σ-cong {U} {V} {W} {X} {Y} {Y'} φ = (F , (G , FG) , (H , HF))
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

ΠΣ-distr-≃ : {X : U ̇} {A : X → V ̇} {P : (x : X) → A x → W ̇}
           → (Π \(x : X) → Σ \(a : A x) → P x a) ≃ (Σ \(f : Π A) → Π \(x : X) → P x (f x))
ΠΣ-distr-≃ {U} {V} {W} {X} {A} {P} = ΠΣ-distr , (ΠΣ-distr-back , η) , (ΠΣ-distr-back , ε)
 where
  η :  ΠΣ-distr {U} {V} {W} {X} {A} {P} ∘ ΠΣ-distr-back ∼ id
  η _ = refl
  ε : ΠΣ-distr-back ∘ ΠΣ-distr ∼ id
  ε _ = refl

Π-cong : funext U V → funext U W
       → (X : U ̇) (Y : X → V ̇) (Y' : X → W ̇)
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

≃-funext₂ : funext U (V ⊔ W) → funext V W
          → {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
            (f g : (x : X) (y : Y x) → A x y) → (f ≡ g) ≃ (∀ x y → f x y ≡ g x y)
≃-funext₂ fe fe' {X} f g =
 (f ≡ g)            ≃⟨ ≃-funext fe f g ⟩
 (f ∼ g)            ≃⟨ Π-cong fe fe X
                          (λ x → f x ≡ g x)
                          (λ x → f x ∼ g x)
                          (λ x → ≃-funext fe' (f x) (g x))⟩
 (∀ x → f x ∼ g x) ■

𝟙-lneutral : {Y : U ̇} → 𝟙 {V} × Y ≃ Y
𝟙-lneutral {U} {V} {Y} = (f , (g , fg) , (g , gf))
 where
   f : 𝟙 × Y → Y
   f (* , y) = y
   g : Y → 𝟙 × Y
   g y = (* , y)
   fg : ∀ x → f (g x) ≡ x
   fg y = refl
   gf : ∀ z → g (f z) ≡ z
   gf (* , y) = refl

×-comm : {X : U ̇} {Y : V ̇} → X × Y ≃ Y × X
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

𝟙-rneutral : {Y : U ̇} → Y × 𝟙 {V} ≃ Y
𝟙-rneutral {U} {V} {Y} = Y × 𝟙 ≃⟨ ×-comm ⟩
                         𝟙 × Y ≃⟨ 𝟙-lneutral {U} {V} ⟩
                         Y     ■

+comm : {X : U ̇} {Y : V ̇} → X + Y ≃ Y + X
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

𝟘-rneutral : {X : U ̇} → X ≃ X + 𝟘 {V}
𝟘-rneutral {U} {V} {X} = f , (g , ε) , (g , η)
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

𝟘-rneutral' : {X : U ̇} → X + 𝟘 {V} ≃ X
𝟘-rneutral' {U} {V} = ≃-sym (𝟘-rneutral {U} {V})

𝟘-lneutral : {X : U ̇} → 𝟘 {V} + X ≃ X
𝟘-lneutral {U} {V} {X} = (𝟘 + X) ≃⟨ +comm ⟩
                         (X + 𝟘) ≃⟨ 𝟘-rneutral' {U} {V} ⟩
                          X      ■

+assoc : {X : U ̇} {Y : V ̇} {Z : W ̇} → (X + Y) + Z ≃ X + (Y + Z)
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

+-cong : {X : U ̇} {Y : V ̇} {A : W ̇} {B : T ̇}
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

×𝟘 : {X : U ̇} → 𝟘 {V} ≃ X × 𝟘 {W}
×𝟘 {U} {V} {W} {X} = f , (g , ε) , (g , η)
 where
   f : 𝟘 → X × 𝟘
   f ()
   g : X × 𝟘 → 𝟘
   g (x , ())
   ε : (t : X × 𝟘) → (f ∘ g) t ≡ t
   ε (x , ())
   η : (u : 𝟘) → (g ∘ f) u ≡ u
   η ()

𝟙distr : {X : U ̇} {Y : V ̇} → X × Y + X ≃ X × (Y + 𝟙 {W})
𝟙distr {U} {V} {W} {X} {Y} = f , (g , ε) , (g , η)
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

Ap+ : {X : U ̇} {Y : V ̇} (Z : W ̇) → X ≃ Y → X + Z ≃ Y + Z
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

×comm : {X : U ̇} {Y : V ̇} → X × Y ≃ Y × X
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

×-cong : {X : U ̇} {Y : V ̇} {A : W ̇} {B : T ̇}
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
  E (a , b) = to-×-≡ (e a) (ε b)
  D : (z : X × Y) → G' (F z) ≡ z
  D (x , y) = to-×-≡ (d x) (δ y)

𝟘→ : {X : U ̇} → funext W U
   → 𝟙 {V} ≃ (𝟘 {W} → X)
𝟘→ {U} {V} {W} {X} fe = f , (g , ε) , (g , η)
 where
  f : 𝟙 → 𝟘 → X
  f * ()
  g : (𝟘 → X) → 𝟙
  g h = *
  ε : (h : 𝟘 → X) → f (g h) ≡ h
  ε h = dfunext fe (λ z → 𝟘-elim z)
  η : (y : 𝟙) → g (f y) ≡ y
  η * = refl

𝟙→ : {X : U ̇} → funext V U
   → X ≃ (𝟙 {V} → X)
𝟙→ {U} {V} {X} fe = f , (g , ε) , (g , η)
 where
  f : X → 𝟙 → X
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

+→ : ∀ {X : U ̇} {Y : V ̇} {Z : W ̇} → funext (U ⊔ V) W
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

→-cong : {X : U ̇} {Y : V ̇} {A : W ̇} {B : T ̇}
       → funext W T → funext U V
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

pr₁-equivalence : (X : U ̇) (A : X → V ̇)
                → ((x : X) → is-singleton (A x))
                → is-equiv (pr₁ {U} {V} {X} {A})
pr₁-equivalence {U} {V} X A iss = (g , prg) , (g , gpr)
 where
  g : X → Σ A
  g x = x , pr₁(iss x)
  prg : (x : X) → pr₁ (g x) ≡ x
  prg x = refl
  gpr : (σ : Σ A) → g(pr₁ σ) ≡ σ
  gpr (x , a) = to-Σ-≡ (prg x , is-singleton-is-prop (iss x) _ _)

NatΣ-fiber-equiv : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
                 → (x : X) (b : B x) → fiber (ζ x) b ≃ fiber (NatΣ ζ) (x , b)
NatΣ-fiber-equiv A B ζ x b = f b , (g b , fg b) , (g b , gf b)
 where
  f : (b : B x) → fiber (ζ x) b → fiber (NatΣ ζ) (x , b)
  f .(ζ x a) (a , refl) = (x , a) , refl
  g : (b : B x) → fiber (NatΣ ζ) (x , b) → fiber (ζ x) b
  g .(ζ x a) ((.x , a) , refl) = a , refl
  gf : (b : B x) (w : fiber (ζ x) b) → g b (f b w) ≡ w
  gf .(ζ x a) (a , refl) = refl
  fg : (b : B x) (t : fiber (NatΣ ζ) (x , b)) → f b (g b t) ≡ t
  fg b (a , refl) = refl

NatΣ-vv-equiv : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
              → ((x : X) → is-vv-equiv(ζ x)) → is-vv-equiv(NatΣ ζ)
NatΣ-vv-equiv A B ζ i (x , b) = equiv-to-singleton
                                   (≃-sym (NatΣ-fiber-equiv A B ζ x b))
                                   (i x b)

NatΣ-vv-equiv-converse : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
                       → is-vv-equiv(NatΣ ζ) → ((x : X) → is-vv-equiv(ζ x))
NatΣ-vv-equiv-converse A B ζ e x b = equiv-to-singleton
                                      (NatΣ-fiber-equiv A B ζ x b)
                                      (e (x , b))

NatΣ-equiv : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
           → ((x : X) → is-equiv(ζ x)) → is-equiv(NatΣ ζ)
NatΣ-equiv A B ζ i = is-vv-equiv-is-equiv
                         (NatΣ ζ)
                         (NatΣ-vv-equiv A B ζ
                           (λ x → is-equiv-is-vv-equiv (ζ x) (i x)))

NatΣ-equiv-converse : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
                    → is-equiv(NatΣ ζ) → ((x : X) → is-equiv(ζ x))
NatΣ-equiv-converse A B ζ e x = is-vv-equiv-is-equiv (ζ x)
                                 (NatΣ-vv-equiv-converse A B ζ
                                   (is-equiv-is-vv-equiv (NatΣ ζ) e) x)

Σ-cong' : {X : U ̇} (A : X → V ̇) (B : X → W ̇)
        → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B
Σ-cong' A B e = NatΣ (λ x → pr₁(e x)) , NatΣ-equiv A B (λ x → pr₁(e x)) (λ x → pr₂(e x))

NatΣ-equiv' : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
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

Σ-change-of-variables' : {X : U ̇} {Y : V ̇} (A : X → W ̇) (g : Y → X)
                       → is-hae g → Σ \(γ : (Σ \(y : Y) → A (g y)) → Σ A) → qinv γ
Σ-change-of-variables' {U} {V} {W} {X} {Y} A g (f , fg , gf , α) = γ , φ , φγ , γφ
 where
  γ : (Σ \(y : Y) → A (g y)) → Σ A
  γ (y , a) = (g y , a)
  φ : Σ A → Σ \(y : Y) → A (g y)
  φ (x , a) = (f x , back-transport A (gf x) a)
  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = to-Σ-≡ (gf x , p)
   where
    p : transport A (gf x) (back-transport A (gf x) a) ≡ a
    p = back-and-forth-transport (gf x)
  φγ : (τ : (Σ \(y : Y) → A (g y))) → φ (γ τ) ≡ τ
  φγ (y , a) = to-Σ-≡ (fg y , q)
   where
    q : transport (λ - → A (g -)) (fg y) (back-transport A (gf (g y)) a) ≡ a
    q = transport (λ - → A (g -)) (fg y) (back-transport A (gf (g y)) a) ≡⟨ transport-ap A g (fg y) ⟩
        transport A (ap g (fg y)) (back-transport A (gf (g y)) a)        ≡⟨ ap (λ - → transport A - (back-transport A (gf (g y)) a)) (α y) ⟩
        transport A (gf (g y)) (back-transport A (gf (g y)) a)           ≡⟨ back-and-forth-transport (gf (g y)) ⟩
        a                                                                ∎

Σ-change-of-variables : {X : U ̇} {Y : V ̇} (A : X → W ̇) (g : Y → X)
                      → is-equiv g → (Σ \(y : Y) → A (g y)) ≃ Σ A
Σ-change-of-variables {U} {V} {W} {X} {Y} A g e = γ , qinv-is-equiv γ q
 where
  γ :  (Σ \(y : Y) → A (g y)) → Σ A
  γ = pr₁(Σ-change-of-variables' A g (is-equiv-is-hae g e))
  q :  qinv γ
  q = pr₂(Σ-change-of-variables' A g (is-equiv-is-hae g e))

NatΠ-fiber-equiv : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
                 → funext U W
                 → (g : Π B) → (Π \(x : X) → fiber (ζ x) (g x)) ≃ fiber (NatΠ ζ) g
NatΠ-fiber-equiv {U} {V} {W} {X} A B ζ fe g =
  (Π \(x : X) → fiber (ζ x) (g x))              ≃⟨ ≃-refl _ ⟩
  (Π \(x : X) → Σ \(a : A x) → ζ x a ≡ g x)     ≃⟨ ΠΣ-distr-≃ ⟩
  (Σ \(f : Π A) → Π \(x : X) → ζ x (f x) ≡ g x) ≃⟨ Σ-cong (λ f → ≃-sym (≃-funext fe (λ x → ζ x (f x)) g)) ⟩
  (Σ \(f : Π A) → (λ x → ζ x (f x)) ≡ g)        ≃⟨ ≃-refl _ ⟩
  fiber (NatΠ ζ) g                              ■

NatΠ-vv-equiv : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
              → funext U W → funext U (V ⊔ W)
              → ((x : X) → is-vv-equiv(ζ x)) → is-vv-equiv(NatΠ ζ)
NatΠ-vv-equiv A B ζ fe fe' i g = equiv-to-singleton
                                    (≃-sym (NatΠ-fiber-equiv A B ζ fe g))
                                    (Π-is-singleton fe' (λ x → i x (g x)))

NatΠ-equiv : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
           → funext U W → funext U (V ⊔ W)
           → ((x : X) → is-equiv(ζ x)) → is-equiv(NatΠ ζ)
NatΠ-equiv A B ζ fe fe' i = is-vv-equiv-is-equiv
                             (NatΠ ζ)
                             (NatΠ-vv-equiv A B ζ fe fe'
                               (λ x → is-equiv-is-vv-equiv (ζ x) (i x)))

Π-cong' : {X : U ̇} (A : X → V ̇) (B : X → W ̇)
        → funext U W → funext U (V ⊔ W)
        → ((x : X) → A x ≃ B x) → Π A ≃ Π B
Π-cong' A B fe fe' e = NatΠ (λ x → pr₁(e x)) , NatΠ-equiv A B (λ x → pr₁(e x)) fe fe' (λ x → pr₂(e x))

≡-cong : {X : U ̇} (x y : X) {x' y' : X} → x ≡ x' → y ≡ y' → (x ≡ y) ≃ (x' ≡ y')
≡-cong x y refl refl = ≃-refl (x ≡ y)

≡-cong-l : {X : U ̇} (x y : X) {x' : X} → x ≡ x' → (x ≡ y) ≃ (x' ≡ y)
≡-cong-l x y refl = ≃-refl (x ≡ y)

≡-cong-r : {X : U ̇} (x y : X) {y' : X} → y ≡ y' → (x ≡ y) ≃ (x ≡ y')
≡-cong-r x y refl = ≃-refl (x ≡ y)

≡-flip : {X : U ̇} {x y : X} → (x ≡ y) ≃ (y ≡ x)
≡-flip = _⁻¹ , (_⁻¹ , ⁻¹-involutive) , (_⁻¹ , ⁻¹-involutive)

singleton-≃ : {X : U ̇} {Y : V ̇} → is-singleton X → is-singleton Y → X ≃ Y
singleton-≃ {U} {V} (c , φ) (d , γ) = (λ _ → d) , ((λ _ → c) , γ) , ((λ _ → c) , φ)

{- TODO: probably remove this.
singleton-𝟙 : {X : U ̇} → is-singleton X → X ≃ 𝟙 {V}
singleton-𝟙 i = singleton-≃ i 𝟙-is-singleton

singleton-𝟙' : {X : U ̇} → is-singleton X → 𝟙 {V} ≃ X
singleton-𝟙' = singleton-≃ 𝟙-is-singleton
-}

𝟙-≡-≃ : (P : U ̇) → funext U U → propext U
      → is-prop P → (𝟙 ≡ P) ≃ P
𝟙-≡-≃ P fe pe i = (λ q → Idtofun q *) , (f , η) , (f , ε)
 where
  f : P → 𝟙 ≡ P
  f p = pe 𝟙-is-prop i (λ _ → p) unique-to-𝟙
  η : (p : P) → Idtofun (f p) * ≡ p
  η p = i (Idtofun (f p) *) p
  ε : (q : 𝟙 ≡ P) → f (Idtofun q *) ≡ q
  ε q = equal-to-prop-is-prop pe fe P i 𝟙 (f (Idtofun q *)) q

sum-of-fibers : (X : U ̇) (Y : V ̇) (f : X → Y) → X ≃ Σ (fiber f)
sum-of-fibers {U} {V} X Y f =
  X                                   ≃⟨ ≃-sym (𝟙-rneutral {U} {U}) ⟩
  X × 𝟙                               ≃⟨ Σ-cong (λ x → singleton-≃ 𝟙-is-singleton
                                                (identifications-from-singleton (f x))) ⟩
  (Σ \(x : X) → Σ \(y : Y) → f x ≡ y) ≃⟨ Σ-flip ⟩
  (Σ \(y : Y) → Σ \(x : X) → f x ≡ y) ■

\end{code}

Alternatively, where we should change the name of this function:

\begin{code}

graph-domain-equiv : {X : U ̇} {Y : V ̇} (f : X → Y)
                   → (Σ \(y : Y) → Σ \(x : X) → f x ≡ y) ≃ X
graph-domain-equiv {U} {V} {X} {Y} f = h , ((g , hg) , (g , gh))
 where
  g : X → Σ \(y : Y) → Σ \(x : X) → f x ≡ y
  g x = f x , x , refl
  h : (Σ \(y : Y) → Σ \(x : X) → f x ≡ y) → X
  h (.(f x) , x , refl) = x
  gh : (σ : Σ \(y : Y) → Σ \(x : X) → f x ≡ y) → g (h σ )≡ σ
  gh (.(f x) , x , refl) = refl
  hg : (x : X) → h (g x) ≡ x
  hg x = refl

\end{code}
