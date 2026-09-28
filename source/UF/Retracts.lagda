\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Retracts where

open import MLTT.AlternativePlus
open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons

has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section r = Σ s ꞉ (codomain r → domain r), r ∘ s ∼ id

section-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (r : X → Y)
           → has-section r
           → (Y → X)
section-map r (s , rs) = s

section-equation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (r : X → Y)
                 → (h : has-section r)
                 → r ∘ section-map r h ∼ id
section-equation r (s , rs) = rs

is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-section s = Σ r ꞉ (codomain s → domain s), r ∘ s ∼ id

has-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-retraction = is-section

retraction-of : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (r : X → Y)
              → has-retraction r
              → (Y → X)
retraction-of s (r , rs) = r

retraction-equation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (s : X → Y)
                    → (h : has-retraction s)
                    → retraction-of s h ∘ s ∼ id
retraction-equation s (r , rs) = rs

sections-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (s : X → Y)
                → is-section s
                → left-cancellable s
sections-are-lc s (r , rs) {x} {x'} p = (rs x)⁻¹ ∙ ap r p ∙ rs x'

retract_of_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
retract Y of X = Σ r ꞉ (X → Y) , has-section r

\end{code}

Below we introduce the synonym "Y ◁ X" for "retract Y of X" and
convenient notation for working with chains of compositions of
retractions.

\begin{code}

retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → retract X of Y → (Y → X)
retraction (r , s , rs) = r

section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → retract X of Y → (X → Y)
section (r , s , rs) = s

retraction-idempotency : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                       → (ρ : retract Y of X)
                       → idempotent-map (section ρ ∘ retraction ρ)
retraction-idempotency (r , s , rs) x =
 s (r (s (r x))) ＝⟨ ap s (rs (r x)) ⟩
 s (r x)         ∎

section-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → (ρ : retract X of Y)
                   → is-section (section ρ)
section-is-section (r , s , rs) = r , rs

retract-condition : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : retract X of Y)
                  → retraction ρ ∘ section ρ ∼ id
retract-condition (r , s , rs) = rs

retraction-has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : retract X of Y)
                       → has-section (retraction ρ)
retraction-has-section (r , h) = h

retract-of-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → retract Y of X
                     → is-singleton X
                     → is-singleton Y
retract-of-singleton (r , s , rs) (c , φ) = r c , (λ y → ap r (φ (s y)) ∙ rs y)

retract-of-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → retract Y of X
                → is-prop X
                → is-prop Y
retract-of-prop (r , s , rs) = subtypes-of-props-are-props' s
                                (sections-are-lc s (r , rs))

identity-retraction : {X : 𝓤 ̇ } → retract X of X
identity-retraction = id , id , λ x → refl

has-section-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                           → has-section f
                           → g ∼ f
                           → has-section g
has-section-closed-under-∼ {𝓤} {𝓥} {X} {Y} f g (s , fs) h =
 (s , λ y → g (s y) ＝⟨ h (s y) ⟩ f (s y) ＝⟨ fs y ⟩
  y                 ∎)

has-section-closed-under-∼' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y}
                            → has-section f
                            → f ∼ g
                            → has-section g
has-section-closed-under-∼' ise h =
 has-section-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)

is-section-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                          → is-section f
                          →  g ∼ f
                          → is-section g
is-section-closed-under-∼ {𝓤} {𝓥} {X} {Y} f g (r , rf) h =
  (r , λ x → r (g x) ＝⟨ ap r (h x) ⟩
             r (f x) ＝⟨ rf x ⟩
             x       ∎)

is-section-closed-under-∼' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y}
                           → is-section f
                           → f ∼ g
                           → is-section g
is-section-closed-under-∼' ise h =
 is-section-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)

\end{code}

Surjection expressed in Curry-Howard logic amounts to retraction.

\begin{code}

has-section' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section' f = (y : codomain f) → fiber f y

retract_Of_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
retract Y Of X = Σ f ꞉ (X → Y) , has-section' f

retract-of-gives-retract-Of : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → retract Y of X
                            → retract Y Of X
retract-of-gives-retract-Of {𝓤} {𝓥} {X} {Y} ρ = (retraction ρ , h)
 where
  h : (y : Y) → Σ x ꞉ X , retraction ρ x ＝ y
  h y = section ρ y , retract-condition ρ y

retract-Of-gives-retract-of : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → retract Y Of X
                            → retract Y of X
retract-Of-gives-retract-of {𝓤} {𝓥} {X} {Y} (f , hass) = (f , φ)
 where
  φ : Σ s ꞉ (Y → X) , f ∘ s ∼ id
  φ = (λ y → pr₁ (hass y)) , (λ y → pr₂ (hass y))

retracts-compose : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                 → retract Y of X
                 → retract Z of Y
                 → retract Z of X
retracts-compose (r , s , rs) (r' , s' , rs') =
  r' ∘ r , s ∘ s' , λ z → r' (r (s (s' z))) ＝⟨ ap r' (rs (s' z)) ⟩
                          r' (s' z)         ＝⟨ rs' z ⟩
                          z                 ∎

×-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
          → retract X of A
          → retract Y of B
          → retract (X × Y) of (A × B)
×-retract {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} (r , s , rs) (t , u , tu) =
 f , g , fg
 where
  f : A × B → X × Y
  f (a , b) = (r a , t b)

  g : X × Y → A × B
  g (x , y) = s x , u y

  fg : (z : X × Y) → f (g z) ＝ z
  fg (x , y) = to-×-＝ (rs x) (tu y)

+-retract : {X : 𝓤 ̇ } {Y : 𝓦 ̇ } {A : 𝓥 ̇ } {B : 𝓣 ̇ }
          → retract X of A
          → retract Y of B
          → retract (X + Y) of (A + B)
+-retract {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} (r , s , rs) (t , u , tu) = f , g , fg
 where
  f : A + B → X + Y
  f (inl a) = inl (r a)
  f (inr b) = inr (t b)

  g : X + Y → A + B
  g (inl x) = inl (s x)
  g (inr y) = inr (u y)

  fg : (p : X + Y) → f (g p) ＝ p
  fg (inl x) = ap inl (rs x)
  fg (inr y) = ap inr (tu y)

+'-retract-of-+ : {X Y : 𝓤 ̇ }
                → retract (X +' Y) of (X + Y)
+'-retract-of-+ {𝓤} {X} {Y} = f , g , fg
 where
  f : X + Y → X +' Y
  f (inl x) = ₀ , x
  f (inr y) = ₁ , y

  g : X +' Y → X + Y
  g (₀ , x) = inl x
  g (₁ , y) = inr y

  fg : (z : X +' Y) → f (g z) ＝ z
  fg (₀ , x) = refl
  fg (₁ , y) = refl

+-retract-of-+' : {X Y : 𝓤 ̇ }
                → retract (X + Y) of (X +' Y)
+-retract-of-+' {𝓤} {X} {Y} = g , f , gf
 where
  f : X + Y → X +' Y
  f (inl x) = ₀ , x
  f (inr y) = ₁ , y

  g : X +' Y → X + Y
  g (₀ , x) = inl x
  g (₁ , y) = inr y

  gf : (z : X + Y) → g (f z) ＝ z
  gf (inl x) = refl
  gf (inr y) = refl

+'-retract : {X Y : 𝓤 ̇ } {A B : 𝓥 ̇ }
           → retract X of A
           → retract Y of B
           → retract (X +' Y) of (A +' B)
+'-retract {𝓤} {𝓥} {X} {Y} {A} {B} (r , s , rs) (t , u , tu) = f , g , fg
 where
  f : A +' B → X +' Y
  f (₀ , a) = ₀ , r a
  f (₁ , b) = ₁ , t b

  g : X +' Y → A +' B
  g (₀ , x) = ₀ , s x
  g (₁ , y) = ₁ , u y

  fg : (p : X +' Y) → f (g p) ＝ p
  fg (₀ , x) = ap (λ - → (₀ , -)) (rs x)
  fg (₁ , y) = ap (λ - → (₁ , -)) (tu y)

Σ-reindex-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → 𝓦 ̇ } (r : Y → X)
                  → has-section r
                  → retract (Σ A) of (Σ (A ∘ r))
Σ-reindex-retract {𝓤} {𝓥} {𝓦} {X} {Y} {A} r (s , rs) = γ , φ , γφ
 where
  γ : (Σ y ꞉ Y , A (r y)) → Σ A
  γ (y , a) = (r y , a)

  φ : Σ A → Σ y ꞉ Y , A (r y)
  φ (x , a) = (s x , transport⁻¹ A (rs x) a)

  γφ : (σ : Σ A) → γ (φ σ) ＝ σ
  γφ (x , a) = to-Σ-＝ (rs x , p)
   where
    p : transport A (rs x) (transport⁻¹ A (rs x) a) ＝ a
    p = back-and-forth-transport (rs x)

Σ-reindex-retract' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → 𝓦 ̇ }
                   → (ρ : retract X of Y)
                   → retract (Σ x ꞉ X , A x) of (Σ y ꞉ Y , A (retraction ρ y))
Σ-reindex-retract' (r , s , rs) = Σ-reindex-retract r (s , rs)

Σ-retract : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
          → ((x : X) → retract (A x) of (B x))
          → retract (Σ A) of (Σ B)
Σ-retract {𝓤} {𝓥} {𝓦} {X} A B ρ = NatΣ R , NatΣ S , rs
 where
  R : (x : X) → B x → A x
  R x = retraction (ρ x)

  S : (x : X) → A x → B x
  S x = section (ρ x)

  RS : (x : X) (a : A x) → R x (S x a) ＝ a
  RS x = retract-condition (ρ x)

  rs : (σ : Σ A) → NatΣ R (NatΣ S σ) ＝ σ
  rs (x , a) = to-Σ-＝' (RS x a)

retract-𝟙+𝟙-of-𝟚 : retract 𝟙 + 𝟙 of 𝟚
retract-𝟙+𝟙-of-𝟚 = f , (g , fg)
 where
  f : 𝟚 → 𝟙 {𝓤₀} + 𝟙 {𝓤₀}
  f = 𝟚-cases (inl ⋆) (inr ⋆)

  g : 𝟙 + 𝟙 → 𝟚
  g = cases (λ x → ₀) (λ x → ₁)

  fg : (x : 𝟙 + 𝟙) → f (g x) ＝ x
  fg (inl ⋆) = refl
  fg (inr ⋆) = refl

\end{code}

TODO. Several retractions here are actually equivalences. So some code
should be generalized and moved to an equivalences module. Similarly,
some retracts proved here are also shown as equivalences in other
modules, and hence there is some amount of repetition that should be
removed. This is the result of (1) merging initially independent
developments, and (2) work over many years with uncontrolled growth.

\begin{code}

Σ-retract₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
           → retract X of A
           → ((x : X) → retract  (Y x) of B)
           → retract (Σ Y) of (A × B)
Σ-retract₂ {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} (r , s , rs) R = f , g , gf
 where
  φ : (x : X) → B → Y x
  φ x = retraction (R x)

  γ : (x : X) → Y x → B
  γ x = section (R x)

  φγ : (x : X) → (y : Y x) → φ x (γ x y) ＝ y
  φγ x = retract-condition (R x)

  f : A × B → Σ Y
  f (a , b) = r a , φ (r a) b

  g : Σ Y → A × B
  g (x , y) = s x , γ x y

  gf : (z : Σ Y) → f (g z) ＝ z
  gf (x , y) = to-Σ-＝ (rs x , l (rs x))
   where
    l : {x' : X} (p : x' ＝ x) → transport Y p (φ x' (γ x y)) ＝ y
    l refl = φγ x y

retract-𝟙+𝟙-of-ℕ : retract 𝟙 + 𝟙 of ℕ
retract-𝟙+𝟙-of-ℕ = r , s , rs
 where
  r : ℕ → 𝟙 + 𝟙
  r zero = inl ⋆
  r (succ _) = inr ⋆

  s : 𝟙 + 𝟙 → ℕ
  s (inl ⋆) = zero
  s (inr ⋆) = succ zero

  rs : (z : 𝟙 {𝓤₀} + 𝟙 {𝓤₀}) → r (s z) ＝ z
  rs (inl ⋆) = refl
  rs (inr ⋆) = refl

𝟙-retract-of-ℕ : retract (𝟙 {𝓤₀}) of ℕ
𝟙-retract-of-ℕ = (λ _ → ⋆) , (λ _ → 0) , 𝟙-is-prop ⋆

𝟙-retract-of-Cantor : retract (𝟙 {𝓤₀}) of (ℕ → 𝟚)
𝟙-retract-of-Cantor = (λ _ → ⋆) , (λ _ → λ n → ₀) , 𝟙-is-prop ⋆

\end{code}

Added 5th March 2019. Notation for composing retracts. I should have
added this ages ago to make the above proofs more readable.

\begin{code}

_◁_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
Y ◁ X = retract Y of X

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
_ ◁⟨ d ⟩ e = retracts-compose e d

◁-refl : (X : 𝓤 ̇ ) → X ◁ X
◁-refl {𝓤} X = identity-retraction {𝓤} {X}


_◀ : (X : 𝓤 ̇ ) → X ◁ X
_◀ = ◁-refl

\end{code}

Added 20 February 2020 by Tom de Jong.

\begin{code}

ap-of-section-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (s : X → Y)
                         → is-section s
                         → (x x' : X) → is-section (ap s {x} {x'})
ap-of-section-is-section {𝓤} {𝓥} {X} {Y} s (r , rs) x x' = ρ , ρap
 where
  ρ : s x ＝ s x' → x ＝ x'
  ρ q = x        ＝⟨ (rs x) ⁻¹ ⟩
        r (s x)  ＝⟨ ap r q ⟩
        r (s x') ＝⟨ rs x' ⟩
        x'       ∎

  ρap : (p : x ＝ x') → ρ (ap s p) ＝ p
  ρap p = ρ (ap s p)                          ＝⟨by-definition⟩
          (rs x) ⁻¹ ∙ (ap r (ap s p) ∙ rs x') ＝⟨ i ⟩
          (rs x) ⁻¹ ∙ ap r (ap s p) ∙ rs x'   ＝⟨ ii ⟩
          (rs x) ⁻¹ ∙ ap (r ∘ s) p ∙  rs x'   ＝⟨ iii ⟩
          ap id p                             ＝⟨ (ap-id-is-id' p)⁻¹ ⟩
          p                                   ∎
   where
    i   = ∙assoc ((rs x) ⁻¹) (ap r (ap s p)) (rs x') ⁻¹
    ii  = ap (λ - → (rs x) ⁻¹ ∙ - ∙ rs x') (ap-ap s r p)
    iii = homotopies-are-natural'' (r ∘ s) id rs {x} {x'} {p}

Σ-section-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (ρ : Y ◁ Z) (g : X → Y)
                  → (y : Y)
                  → fiber g y
                  ◁ fiber (section ρ ∘ g) (section ρ y)
Σ-section-retract {𝓤} {𝓥} {𝓦} {X} {Y} {Z} (r , s , rs) g y =
 Σ-retract (λ x → g x ＝ y) (λ x → s (g x) ＝ s y) γ
  where
   γ : (x : X) → (g x ＝ y) ◁ (s (g x) ＝ s y)
   γ x = ρ , (σ , ρσ)
    where
     σ : g x ＝ y → s (g x) ＝ s y
     σ = ap s

     ρ : s (g x) ＝ s y → g x ＝ y
     ρ = pr₁ (ap-of-section-is-section s (r , rs) (g x) y)

     ρσ : (p : g x ＝ y) → ρ (σ p) ＝ p
     ρσ = pr₂ (ap-of-section-is-section s ((r , rs)) (g x) y)

\end{code}

Added 8 August 2024 by Tom de Jong.

\begin{code}

＝-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (s : X → Y)
           → is-section s
           → (x x' : X) → (x ＝ x') ◁ (s x ＝ s x')
＝-retract s s-sect x x' = ρ , ap s , η
 where
  ρ : s x ＝ s x' → x ＝ x'
  ρ = retraction-of (ap s) (ap-of-section-is-section s s-sect x x')
  η : ρ ∘ ap s ∼ id
  η = retraction-equation (ap s) (ap-of-section-is-section s s-sect x x')

\end{code}

Fixities:

\begin{code}

infix  0 _◁_
infix  1 _◀
infixr 0 _◁⟨_⟩_

\end{code}
