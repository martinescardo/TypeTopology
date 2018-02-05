Martin Escardo, 2012

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import UF

module EquivalenceExamples where

Curry-Uncurry : (fe : ∀ {U V} → FunExt U V)
             → ∀ {U V W} {X : U ̇} {Y : X → V ̇} {Z : (Σ \(x : X) → Y x) → W ̇}
             → Π Z ≃ Π \(x : X) → Π \(y : Y x) → Z(x , y)
Curry-Uncurry fe {U} {V} {W} {X} {Y} {Z} = c , (u , cu) , (u , uc)
   where
    c : (w : Π Z) → ((x : X) (y : Y x) → Z(x , y))
    c f x y = f (x , y)
    u : ((x : X) (y : Y x) → Z(x , y)) → Π Z
    u g (x , y) = g x y
    cu : ∀ g → c (u g) ≡ g
    cu g = funext fe (λ x → funext fe (λ y → refl))
    uc : ∀ f → u (c f) ≡ f
    uc f = funext fe (λ w → refl)

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
    FG (x , y') = Σ-≡' x _ y' (fg x y')
    HF : (w : Σ Y) → H(F w) ≡ w
    HF (x , y) = Σ-≡' x _ y (hf x y)
  
Π-congruence : (fe : ∀ {U V} → FunExt U V)
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
    FG w' = funext fe FG' 
     where
      FG' : (x : X) → F(G w') x ≡ w' x
      FG' x = fg x (w' x)
  
    HF : (w : ((x : X) → Y x)) → H(F w) ≡ w
    HF w = funext fe GF' 
     where
      GF' : (x : X) → H(F w) x ≡ w x
      GF' x = hf x (w x)
  
lemma[𝟙×Y≃Y] : ∀ {U} {Y : U ̇} → 𝟙 × Y ≃ Y
lemma[𝟙×Y≃Y] {U} {Y} = (f , (g , fg) , (g , gf))
  where 
    f : 𝟙 × Y → Y
    f (* , y) = y
    g : Y → 𝟙 × Y 
    g y = (* , y)
    fg : ∀ x → f (g x) ≡ x 
    fg y = refl 
    gf : ∀ z → g (f z) ≡ z
    gf (* , y) = refl
  
  
lemma[X×Y≃Y×X] : ∀ {U V} {X : U ̇} {Y : V ̇} → X × Y ≃ Y × X
lemma[X×Y≃Y×X] {U} {V} {X} {Y} = (f , (g , fg) , (g , gf))
   where 
    f : X × Y → Y × X
    f (x , y) = (y , x)
    g : Y × X → X × Y
    g (y , x) = (x , y)
    fg : ∀ z → f (g z) ≡ z 
    fg z = refl 
    gf : ∀ t → g (f t) ≡ t
    gf t = refl
  
lemma[Y×𝟙≃Y] : ∀ {U} {Y : U ̇} → Y × 𝟙 ≃ Y
lemma[Y×𝟙≃Y] {U} {Y} = ≃-trans {U} {U} {U} lemma[X×Y≃Y×X] lemma[𝟙×Y≃Y] 

lemma[X≃X'→Y≃Y'→[X×Y]≃[X'×Y']] : ∀ {U V W T} {X : U ̇} {X' : V ̇} {Y : W ̇} {Y' : T ̇}
                                  → X ≃ X' → Y ≃ Y' → X × Y ≃ X' × Y'
lemma[X≃X'→Y≃Y'→[X×Y]≃[X'×Y']] {U} {V} {W} {T} {X} {X'} {Y} {Y'} (f , (g , fg) , (h , hf)) (f' , (g' , fg') , (h' , hf'))
   = (f'' , (g'' , fg'') , (h'' , hf''))
   where 
    f'' : X × Y → X' × Y'
    f'' (x , y) = (f x , f' y)
    g'' : X' × Y' → X × Y
    g'' (x' , y') = (g x' , g' y')
    h'' : X' × Y' → X × Y
    h'' (x' , y') = (h x' , h' y')
    fg'' : ∀ z' → f'' (g'' z') ≡ z' 
    fg''(x' , y') = ap₂ _,_ lemma₀ lemma₁ 
     where 
      lemma₀ : f(g x') ≡ x'
      lemma₀ = fg x' 
      lemma₁ : f'(g' y') ≡ y'
      lemma₁ = fg' y' 
    hf'' : ∀ z → h'' (f'' z) ≡ z
    hf''(x' , y') = ap₂ _,_ lemma₀ lemma₁ 
      where  
       lemma₀ : h(f x') ≡ x'
       lemma₀ = hf x'
       lemma₁ : h'(f' y') ≡ y'
       lemma₁ = hf' y'
       
\end{code}
  
