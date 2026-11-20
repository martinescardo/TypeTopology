Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.FunExt-from-Univalence where

open import MGS.Equivalence-Induction public

funext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ＝ g

precomp-is-equiv : is-univalent 𝓤
                 → (X Y : 𝓤 ̇ ) (f : X → Y)
                 → is-equiv f
                 → (Z : 𝓤 ̇ ) → is-equiv (λ (g : Y → Z) → g ∘ f)

precomp-is-equiv {𝓤} ua =
   𝕁-equiv ua
     (λ X Y (f : X → Y) → (Z : 𝓤 ̇ ) → is-equiv (λ g → g ∘ f))
     (λ X Z → id-is-equiv (X → Z))

univalence-gives-funext : is-univalent 𝓤 → funext 𝓥 𝓤
univalence-gives-funext {𝓤} {𝓥} ua {X} {Y} {f₀} {f₁} = γ
 where
  Δ : 𝓤 ̇
  Δ = Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ＝ y₁

  δ : Y → Δ
  δ y = (y , y , refl y)

  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁

  δ-is-equiv : is-equiv δ
  δ-is-equiv = invertibles-are-equivs δ (π₀ , η , ε)
   where
    η : (y : Y) → π₀ (δ y) ＝ y
    η y = refl y

    ε : (d : Δ) → δ (π₀ d) ＝ d
    ε (y , y , refl y) = refl (y , y , refl y)

  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ

  φ-is-equiv : is-equiv φ
  φ-is-equiv = precomp-is-equiv ua Y Δ δ δ-is-equiv Y

  p : φ π₀ ＝ φ π₁
  p = refl (𝑖𝑑 Y)

  q : π₀ ＝ π₁
  q = equivs-are-lc φ φ-is-equiv p

  γ : f₀ ∼ f₁ → f₀ ＝ f₁
  γ h = ap (λ π x → π (f₀ x , f₁ x , h x)) q

  γ' : f₀ ∼ f₁ → f₀ ＝ f₁
  γ' h = f₀                             ＝⟨ refl _ ⟩
         (λ x → f₀ x)                   ＝⟨ refl _ ⟩
         (λ x → π₀ (f₀ x , f₁ x , h x)) ＝⟨ ap (λ - x → - (f₀ x , f₁ x , h x)) q ⟩
         (λ x → π₁ (f₀ x , f₁ x , h x)) ＝⟨ refl _ ⟩
         (λ x → f₁ x)                   ＝⟨ refl _ ⟩
         f₁                             ∎

dfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
dfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ＝ g

happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → f ＝ g → f ∼ g
happly f g p x = ap (λ - → - x) p

hfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
hfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → is-equiv (happly f g)

hfunext-gives-dfunext : hfunext 𝓤 𝓥 → dfunext 𝓤 𝓥
hfunext-gives-dfunext hfe {X} {A} {f} {g} = inverse (happly f g) (hfe f g)

vvfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
vvfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
             → ((x : X) → is-singleton (A x))
             → is-singleton (Π A)

dfunext-gives-vvfunext : dfunext 𝓤 𝓥 → vvfunext 𝓤 𝓥
dfunext-gives-vvfunext fe {X} {A} i = γ
 where
  f : Π A
  f x = center (A x) (i x)

  c : (g : Π A) → f ＝ g
  c g = fe (λ (x : X) → centrality (A x) (i x) (g x))

  γ : is-singleton (Π A)
  γ = f , c

postcomp-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                    → funext 𝓦 𝓤
                    → funext 𝓦 𝓥
                    → (f : X → Y)
                    → invertible f
                    → invertible (λ (h : A → X) → f ∘ h)

postcomp-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {A} nfe nfe' f (g , η , ε) = γ
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h

  g' : (A → Y) → (A → X)
  g' k = g ∘ k

  η' : (h : A → X) → g' (f' h) ＝ h
  η' h = nfe (η ∘ h)

  ε' : (k : A → Y) → f' (g' k) ＝ k
  ε' k = nfe' (ε ∘ k)

  γ : invertible f'
  γ = (g' , η' , ε')

postcomp-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                  → funext 𝓦 𝓤
                  → funext 𝓦 𝓥
                  → (f : X → Y)
                  → is-equiv f
                  → is-equiv (λ (h : A → X) → f ∘ h)

postcomp-is-equiv fe fe' f e =
 invertibles-are-equivs
  (λ h → f ∘ h)
  (postcomp-invertible fe fe' f (equivs-are-invertible f e))

vvfunext-gives-hfunext : vvfunext 𝓤 𝓥 → hfunext 𝓤 𝓥
vvfunext-gives-hfunext vfe {X} {Y} f = γ
 where
  a : (x : X) → is-singleton (Σ y ꞉ Y x , f x ＝ y)
  a x = singleton-types'-are-singletons (Y x) (f x)

  c : is-singleton (Π x ꞉ X , Σ y ꞉ Y x , f x ＝ y)
  c = vfe a

  ρ : (Σ g ꞉ Π Y , f ∼ g) ◁ (Π x ꞉ X , Σ y ꞉ Y x , f x ＝ y)
  ρ = ≃-gives-▷ ΠΣ-distr-≃

  d : is-singleton (Σ g ꞉ Π Y , f ∼ g)
  d = retract-of-singleton ρ c

  e : (Σ g ꞉ Π Y , f ＝ g) → (Σ g ꞉ Π Y , f ∼ g)
  e = NatΣ (happly f)

  i : is-equiv e
  i = maps-of-singletons-are-equivs e (singleton-types'-are-singletons (Π Y) f) d

  γ : (g : Π Y) → is-equiv (happly f g)
  γ = NatΣ-equiv-gives-fiberwise-equiv (happly f) i

funext-gives-vvfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → vvfunext 𝓤 𝓥
funext-gives-vvfunext {𝓤} {𝓥} fe fe' {X} {A} φ = γ
 where
  f : Σ A → X
  f = pr₁

  f-is-equiv : is-equiv f
  f-is-equiv = pr₁-equiv φ

  g : (X → Σ A) → (X → X)
  g h = f ∘ h

  e : is-equiv g
  e = postcomp-is-equiv fe fe' f f-is-equiv

  i : is-singleton (Σ h ꞉ (X → Σ A), f ∘ h ＝ 𝑖𝑑 X)
  i = e (𝑖𝑑 X)

  r : (Σ h ꞉ (X → Σ A), f ∘ h ＝ 𝑖𝑑 X) → Π A
  r (h , p) x = transport A (happly (f ∘ h) (𝑖𝑑 X) p x) (pr₂ (h x))

  s : Π A → (Σ h ꞉ (X → Σ A), f ∘ h ＝ 𝑖𝑑 X)
  s φ = (λ x → x , φ x) , refl (𝑖𝑑 X)

  η : ∀ φ → r (s φ) ＝ φ
  η φ = refl (r (s φ))

  γ : is-singleton (Π A)
  γ = retract-of-singleton (r , s , η) i

abstract
 funext-gives-hfunext       : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → hfunext 𝓤 𝓥
 dfunext-gives-hfunext      : dfunext 𝓤 𝓥 → hfunext 𝓤 𝓥
 funext-gives-dfunext       : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → dfunext 𝓤 𝓥
 univalence-gives-dfunext'  : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
 univalence-gives-hfunext'  : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → hfunext 𝓤 𝓥
 univalence-gives-vvfunext' : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → vvfunext 𝓤 𝓥
 univalence-gives-hfunext   : is-univalent 𝓤 → hfunext 𝓤 𝓤
 univalence-gives-dfunext   : is-univalent 𝓤 → dfunext 𝓤 𝓤
 univalence-gives-vvfunext  : is-univalent 𝓤 → vvfunext 𝓤 𝓤

 funext-gives-hfunext fe fe' = vvfunext-gives-hfunext (funext-gives-vvfunext fe fe')

 funext-gives-dfunext fe fe' = hfunext-gives-dfunext (funext-gives-hfunext fe fe')

 dfunext-gives-hfunext fe = vvfunext-gives-hfunext (dfunext-gives-vvfunext fe)

 univalence-gives-dfunext' ua ua' = funext-gives-dfunext
                                     (univalence-gives-funext ua')
                                     (univalence-gives-funext ua)

 univalence-gives-hfunext' ua ua' = funext-gives-hfunext
                                      (univalence-gives-funext ua')
                                      (univalence-gives-funext ua)

 univalence-gives-vvfunext' ua ua' = funext-gives-vvfunext
                                      (univalence-gives-funext ua')
                                      (univalence-gives-funext ua)

 univalence-gives-hfunext ua = univalence-gives-hfunext' ua ua

 univalence-gives-dfunext ua = univalence-gives-dfunext' ua ua

 univalence-gives-vvfunext ua = univalence-gives-vvfunext' ua ua

\end{code}
