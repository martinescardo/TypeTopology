Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.More-FunExt-Consequences where

open import MGS.HAE public
open import MGS.Subsingleton-Theorems public

being-subsingleton-is-subsingleton : dfunext 𝓤 𝓤
                                   →  {X : 𝓤 ̇ }
                                   → is-subsingleton (is-subsingleton X)

being-subsingleton-is-subsingleton fe {X} i j = c
 where
  l : is-set X
  l = subsingletons-are-sets X i

  a : (x y : X) → i x y ＝ j x y
  a x y = l x y (i x y) (j x y)

  b : (x : X) → i x ＝ j x
  b x = fe (a x)

  c : i ＝ j
  c = fe b

being-center-is-subsingleton : dfunext 𝓤 𝓤
                             → {X : 𝓤 ̇ } (c : X)
                             → is-subsingleton (is-center X c)

being-center-is-subsingleton fe {X} c φ γ = k
 where
  i : is-singleton X
  i = c , φ

  j : (x : X) → is-subsingleton (c ＝ x)
  j x = singletons-are-sets X i c x

  k : φ ＝ γ
  k = fe (λ x → j x (φ x) (γ x))

Π-is-set : hfunext 𝓤 𝓥
         → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → ((x : X) → is-set (A x)) → is-set (Π A)

Π-is-set hfe s f g = b
 where
  a : is-subsingleton (f ∼ g)
  a p q = γ
   where
    h : ∀ x →  p x ＝ q x
    h x = s x (f x) (g x) (p x) (q x)
    γ : p ＝  q
    γ = hfunext-gives-dfunext hfe h

  e : (f ＝ g) ≃ (f ∼ g)
  e = (happly f g , hfe f g)

  b : is-subsingleton (f ＝ g)
  b = equiv-to-subsingleton e a

being-set-is-subsingleton : dfunext 𝓤 𝓤
                          → {X : 𝓤 ̇ }
                          → is-subsingleton (is-set X)

being-set-is-subsingleton fe = Π-is-subsingleton fe
                                (λ x → Π-is-subsingleton fe
                                (λ y → being-subsingleton-is-subsingleton fe))

hlevel-relation-is-subsingleton : dfunext 𝓤 𝓤
                                → (n : ℕ) (X : 𝓤 ̇ )
                                → is-subsingleton (X is-of-hlevel n)

hlevel-relation-is-subsingleton {𝓤} fe zero X =
 being-singleton-is-subsingleton fe

hlevel-relation-is-subsingleton fe (succ n) X =
 Π-is-subsingleton fe
  (λ x → Π-is-subsingleton fe
  (λ x' → hlevel-relation-is-subsingleton fe n (x ＝ x')))

●-assoc : dfunext 𝓣 (𝓤 ⊔ 𝓣) → dfunext (𝓤 ⊔ 𝓣) (𝓤 ⊔ 𝓣)
        → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {T : 𝓣 ̇ }
          (α : X ≃ Y) (β : Y ≃ Z) (γ : Z ≃ T)
        → α ● (β ● γ) ＝ (α ● β) ● γ

●-assoc fe fe' (f , a) (g , b) (h , c) = ap (h ∘ g ∘ f ,_) q
 where
  d e : is-equiv (h ∘ g ∘ f)
  d = ∘-is-equiv (∘-is-equiv c b) a
  e = ∘-is-equiv c (∘-is-equiv b a)

  q : d ＝ e
  q = being-equiv-is-subsingleton fe fe' (h ∘ g ∘ f) _ _

≃-sym-involutive : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) →
                   {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                 → ≃-sym (≃-sym α) ＝ α

≃-sym-involutive fe fe' (f , a) = to-subtype-＝
                                   (being-equiv-is-subsingleton fe fe')
                                   (inversion-involutive f a)

≃-sym-is-equiv : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
               → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → is-equiv (≃-sym {𝓤} {𝓥} {X} {Y})

≃-sym-is-equiv fe₀ fe₁ fe₂ = invertibles-are-equivs ≃-sym
                              (≃-sym ,
                               ≃-sym-involutive fe₀ fe₂ ,
                               ≃-sym-involutive fe₁ fe₂)

≃-sym-≃ : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
        → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
        → (X ≃ Y) ≃ (Y ≃ X)

≃-sym-≃ fe₀ fe₁ fe₂ X Y = ≃-sym , ≃-sym-is-equiv fe₀ fe₁ fe₂

Π-cong : dfunext 𝓤 𝓥 → dfunext 𝓤 𝓦
       → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Y' : X → 𝓦 ̇ }
       → ((x : X) → Y x ≃ Y' x) → Π Y ≃ Π Y'

Π-cong fe fe' {X} {Y} {Y'} φ = invertibility-gives-≃ F (G , GF , FG)
 where
  f : (x : X) → Y x → Y' x
  f x = ⌜ φ x ⌝

  e : (x : X) → is-equiv (f x)
  e x = ⌜⌝-is-equiv (φ x)

  g : (x : X) → Y' x → Y x
  g x = inverse (f x) (e x)

  fg : (x : X) (y' : Y' x) → f x (g x y') ＝ y'
  fg x = inverses-are-sections (f x) (e x)

  gf : (x : X) (y : Y x) → g x (f x y) ＝ y
  gf x = inverses-are-retractions (f x) (e x)

  F : ((x : X) → Y x) → ((x : X) → Y' x)
  F φ x = f x (φ x)

  G : ((x : X) → Y' x) → (x : X) → Y x
  G γ x = g x (γ x)

  FG : (γ : ((x : X) → Y' x)) → F (G γ) ＝ γ
  FG γ = fe' (λ x → fg x (γ x))

  GF : (φ : ((x : X) → Y x)) → G (F φ) ＝ φ
  GF φ = fe (λ x → gf x (φ x))

hfunext-≃ : hfunext 𝓤 𝓥
          → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A)
          → (f ＝ g) ≃ (f ∼ g)

hfunext-≃ hfe f g = (happly f g , hfe f g)

hfunext₂-≃ : hfunext 𝓤 (𝓥 ⊔ 𝓦) → hfunext 𝓥 𝓦
           → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : (x : X) → Y x → 𝓦 ̇ }
             (f g : (x : X) (y : Y x) → A x y)
           → (f ＝ g) ≃ (∀ x y → f x y ＝ g x y)

hfunext₂-≃ fe fe' {X} f g =

 (f ＝ g)                  ≃⟨ i ⟩
 (∀ x → f x ＝ g x)        ≃⟨ ii ⟩
 (∀ x y → f x y ＝ g x y)  ■

 where
  i  = hfunext-≃ fe f g
  ii = Π-cong
        (hfunext-gives-dfunext fe)
        (hfunext-gives-dfunext fe)
        (λ x → hfunext-≃ fe' (f x) (g x))

precomp-invertible : dfunext 𝓥 𝓦 → dfunext 𝓤 𝓦
                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y)
                   → invertible f
                   → invertible (λ (h : Y → Z) → h ∘ f)

precomp-invertible fe fe' {X} {Y} {Z} f (g , η , ε) = (g' , η' , ε')
 where
  f' : (Y → Z) → (X → Z)
  f' h = h ∘ f

  g' : (X → Z) → (Y → Z)
  g' k = k ∘ g

  η' : (h : Y → Z) → g' (f' h) ＝ h
  η' h = fe (λ y → ap h (ε y))

  ε' : (k : X → Z) → f' (g' k) ＝ k
  ε' k = fe' (λ x → ap k (η x))

dprecomp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
         → Π A → Π (A ∘ f)

dprecomp A f = _∘ f

dprecomp-is-equiv : dfunext 𝓤 𝓦
                  → dfunext 𝓥 𝓦
                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                  → is-equiv f
                  → is-equiv (dprecomp A f)

dprecomp-is-equiv fe fe' {X} {Y} A f i = invertibles-are-equivs φ (ψ , ψφ , φψ)
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
     b = (transport-ap A f (η x) (k (g (f x))))⁻¹
     c = apd k (η x)

  φψ : φ ∘ ψ ∼ id
  φψ k = fe (φψ₀ k)

  ψφ₀ : (h : Π A) (y : Y) → transport A (ε y) (h (f (g y))) ＝ h y
  ψφ₀ h y = apd h (ε y)

  ψφ : ψ ∘ φ ∼ id
  ψφ h = fe' (ψφ₀ h)

Π-change-of-variable : dfunext 𝓤 𝓦
                     → dfunext 𝓥 𝓦
                     → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                     → is-equiv f
                     → (Π y ꞉ Y , A y) ≃ (Π x ꞉ X , A (f x))

Π-change-of-variable fe fe' A f i = dprecomp A f , dprecomp-is-equiv fe fe' A f i

at-most-one-section : dfunext 𝓥 𝓤 → hfunext 𝓥 𝓥
                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → has-retraction f
                    → is-subsingleton (has-section f)

at-most-one-section {𝓥} {𝓤} fe hfe {X} {Y} f (g , gf) (h , fh) = d
 where
  fe' : dfunext 𝓥 𝓥
  fe' = hfunext-gives-dfunext hfe

  a : invertible f
  a = joyal-equivs-are-invertible f ((h , fh) , (g , gf))

  b : is-singleton (fiber (λ h →  f ∘ h) id)
  b = invertibles-are-equivs (λ h → f ∘ h) (postcomp-invertible fe fe' f a) id

  r : fiber (λ h →  f ∘ h) id → has-section f
  r (h , p) = (h , happly (f ∘ h) id p)

  s : has-section f → fiber (λ h → f ∘ h) id
  s (h , η) = (h , fe' η)

  rs : (σ : has-section f) → r (s σ) ＝ σ
  rs (h , η) = to-Σ-＝' q
   where
    q : happly (f ∘ h) id (inverse (happly (f ∘ h) id) (hfe (f ∘ h) id) η) ＝ η
    q = inverses-are-sections (happly (f ∘ h) id) (hfe (f ∘ h) id) η

  c : is-singleton (has-section f)
  c = retract-of-singleton (r , s , rs) b

  d : (σ : has-section f) → h , fh ＝ σ
  d = singletons-are-subsingletons (has-section f) c (h , fh)

at-most-one-retraction : hfunext 𝓤 𝓤 → dfunext 𝓥 𝓤
                       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → has-section f
                       → is-subsingleton (has-retraction f)

at-most-one-retraction {𝓤} {𝓥} hfe fe' {X} {Y} f (g , fg) (h , hf) = d
 where
  fe : dfunext 𝓤 𝓤
  fe = hfunext-gives-dfunext hfe

  a : invertible f
  a = joyal-equivs-are-invertible f ((g , fg) , (h , hf))

  b : is-singleton (fiber (λ h →  h ∘ f) id)
  b = invertibles-are-equivs (λ h → h ∘ f) (precomp-invertible fe' fe f a) id

  r : fiber (λ h →  h ∘ f) id → has-retraction f
  r (h , p) = (h , happly (h ∘ f) id p)

  s : has-retraction f → fiber (λ h →  h ∘ f) id
  s (h , η) = (h , fe η)

  rs : (σ : has-retraction f) → r (s σ) ＝ σ
  rs (h , η) = to-Σ-＝' q
   where
    q : happly (h ∘ f) id (inverse (happly (h ∘ f) id) (hfe (h ∘ f) id) η) ＝ η
    q = inverses-are-sections (happly (h ∘ f) id) (hfe (h ∘ f) id) η

  c : is-singleton (has-retraction f)
  c = retract-of-singleton (r , s , rs) b

  d : (ρ : has-retraction f) → h , hf ＝ ρ
  d = singletons-are-subsingletons (has-retraction f) c (h , hf)

being-joyal-equiv-is-subsingleton : hfunext 𝓤 𝓤 → hfunext 𝓥 𝓥 → dfunext 𝓥 𝓤
                                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                  → (f : X → Y)
                                  → is-subsingleton (is-joyal-equiv f)

being-joyal-equiv-is-subsingleton fe₀ fe₁ fe₂ f = ×-is-subsingleton'
                                                   (at-most-one-section    fe₂ fe₁ f ,
                                                    at-most-one-retraction fe₀ fe₂ f)

being-hae-is-subsingleton : dfunext 𝓥 𝓤 → hfunext 𝓥 𝓥 → dfunext 𝓤 (𝓥 ⊔ 𝓤)
                          → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                          → is-subsingleton (is-hae f)

being-hae-is-subsingleton fe₀ fe₁ fe₂ {X} {Y} f = subsingleton-criterion' γ
 where
  a : (g : Y → X) (ε : (x : Y) → f (g x) ＝ x) (x : X)
    → (g (f x) , ε (f x) ＝ (x , refl (f x)))
    ≃ (Σ p ꞉ g (f x) ＝ x , ap f p ＝ ε (f x))
  a g ε x =
   ((g (f x) , ε (f x)) ＝ (x , refl (f x)))                                   ≃⟨ i ⟩
   (Σ p ꞉ g (f x) ＝ x , transport (λ - → f - ＝ f x) p (ε (f x)) ＝ refl (f x)) ≃⟨ ii ⟩
   (Σ p ꞉ g (f x) ＝ x , ap f p ＝ ε (f x))                                     ■
    where
     i  = Σ-＝-≃ (g (f x) , ε (f x)) (x , refl (f x))
     ii = Σ-cong (λ p → transport-ap-≃ f p (ε (f x)))

  b : (Σ (g , ε) ꞉ has-section f , ∀ x → (g (f x) , ε (f x)) ＝ (x , refl (f x)))
    ≃ is-hae f
  b = (Σ (g , ε) ꞉ has-section f , ∀ x → (g (f x) , ε (f x)) ＝ (x , refl (f x)))         ≃⟨ i ⟩
      (Σ (g , ε) ꞉ has-section f , ∀ x → Σ  p ꞉ g (f x) ＝ x , ap f p ＝ ε (f x))          ≃⟨ ii ⟩
      (Σ g ꞉ (Y → X) , Σ ε ꞉ f ∘ g ∼ id , ∀ x → Σ  p ꞉ g (f x) ＝ x , ap f p ＝ ε (f x))   ≃⟨ iii ⟩
      (Σ g ꞉ (Y → X) , Σ ε ꞉ f ∘ g ∼ id , Σ η ꞉ g ∘ f ∼ id , ∀ x → ap f (η x) ＝ ε (f x)) ≃⟨ iv ⟩
      is-hae f                                                                           ■
   where
    i   = Σ-cong (λ (g , ε) → Π-cong fe₂ fe₂ (a g ε))
    ii  = Σ-assoc
    iii = Σ-cong (λ g → Σ-cong (λ ε → ΠΣ-distr-≃))
    iv  = Σ-cong (λ g → Σ-flip)

  γ : is-hae f → is-subsingleton (is-hae f)
  γ (g₀ , ε₀ , η₀ , τ₀) = i
   where
    c : (x : X) → is-set (fiber f (f x))
    c x = singletons-are-sets (fiber f (f x)) (haes-are-equivs f (g₀ , ε₀ , η₀ , τ₀) (f x))

    d : ((g , ε) : has-section f) → is-subsingleton (∀ x → (g (f x) , ε (f x)) ＝ (x , refl (f x)))
    d (g , ε) = Π-is-subsingleton fe₂ (λ x → c x (g (f x) , ε (f x)) (x , refl (f x)))

    e : is-subsingleton (Σ (g , ε) ꞉ has-section f , ∀ x → (g (f x) , ε (f x)) ＝ (x , refl (f x)))
    e = Σ-is-subsingleton (at-most-one-section fe₀ fe₁ f (g₀ , ε₀)) d

    i : is-subsingleton (is-hae f)
    i = equiv-to-subsingleton (≃-sym b) e

emptiness-is-subsingleton : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇ )
                          → is-subsingleton (is-empty X)

emptiness-is-subsingleton fe X f g = fe (λ x → !𝟘 (f x ＝ g x) (f x))

+-is-subsingleton : {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
                  → is-subsingleton P
                  → is-subsingleton Q
                  → (P → Q → 𝟘) → is-subsingleton (P + Q)

+-is-subsingleton {𝓤} {𝓥} {P} {Q} i j f = γ
 where
  γ : (x y : P + Q) → x ＝ y
  γ (inl p) (inl p') = ap inl (i p p')
  γ (inl p) (inr q)  = !𝟘 (inl p ＝ inr q) (f p q)
  γ (inr q) (inl p)  = !𝟘 (inr q ＝ inl p) (f p q)
  γ (inr q) (inr q') = ap inr (j q q')

+-is-subsingleton' : dfunext 𝓤 𝓤₀
                   → {P : 𝓤 ̇ } → is-subsingleton P → is-subsingleton (P + ¬ P)

+-is-subsingleton' fe {P} i = +-is-subsingleton i
                               (emptiness-is-subsingleton fe P)
                               (λ p n → n p)

EM-is-subsingleton : dfunext (𝓤 ⁺) 𝓤 → dfunext 𝓤 𝓤 → dfunext 𝓤 𝓤₀
                   → is-subsingleton (EM 𝓤)

EM-is-subsingleton fe⁺ fe fe₀ = Π-is-subsingleton fe⁺
                                 (λ P → Π-is-subsingleton fe
                                         (λ i → +-is-subsingleton' fe₀ i))
\end{code}
