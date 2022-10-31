Tom de Jong, 28 October 2022 - ...

TO DO: Put reference to HoTT Book

In collaboration with Nicolai Kraus, Fredrik Norvall Forsberg and Chuangjie Xu.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

module UF.CumulativeHierarchy
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.Base hiding (_≈_)
open import UF.Subsingletons-FunExt

_≲_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓣 ̇ } → (A → X) → (B → X) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
_≲_ {𝓤} {𝓥} {𝓣} {A} {B} f g = (a : A) → ∃ b ꞉ B , g b ＝ f a

-- Note that _≈_ says that f and g have equal images
_≈_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓣 ̇ } → (A → X) → (B → X) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
f ≈ g = f ≲ g × g ≲ f

module _ (𝓤 : Universe) where

 record cumulative-hierarchy-exists : 𝓤ω where
  field
   𝕍 : 𝓤 ⁺ ̇
   𝕍-is-set : is-set 𝕍
   𝕍-set : {A : 𝓤 ̇ } → (A → 𝕍) → 𝕍
   𝕍-set-ext : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍) → f ≈ g → 𝕍-set f ＝ 𝕍-set g
   𝕍-induction : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
               → ((x : 𝕍) → is-set (P x))
               → (ρ : {A : 𝓤 ̇ } (f : A → 𝕍 ) → ((a : A) → P (f a)) → P (𝕍-set f))
               → ({A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍) (e : f ≈ g)
                   → (IH₁ : (a : A) → P (f a))
                   → (IH₂ : (b : B) → P (g b))
                   → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b ,
                                    transport P p (IH₁ a) ＝ IH₂ b ∥)
                   → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a ,
                                    transport P p (IH₂ b) ＝ IH₁ a ∥)
                   → transport P (𝕍-set-ext f g e) (ρ f IH₁) ＝ ρ g IH₂)
               → (x : 𝕍) → P x
   𝕍-induction-computes : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
                        → (σ : (x : 𝕍) → is-set (P x))
                        → (ρ : {A : 𝓤 ̇ } (f : A → 𝕍 ) → ((a : A) → P (f a))
                                                        → P (𝕍-set f))
                        → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍) (e : f ≈ g)
                             → (IH₁ : (a : A) → P (f a))
                             → (IH₂ : (b : B) → P (g b))
                             → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b ,
                                              transport P p (IH₁ a) ＝ IH₂ b ∥)
                             → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a ,
                                              transport P p (IH₂ b) ＝ IH₁ a ∥)
                             → transport P (𝕍-set-ext f g e) (ρ f IH₁) ＝ ρ g IH₂)
                        → {A : 𝓤 ̇ } (f : A → 𝕍) (IH : (a : A) → P (f a))
                           → 𝕍-induction P σ ρ τ (𝕍-set f) ＝ ρ f IH


  𝕍-prop-induction : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
                   → ((x : 𝕍) → is-prop (P x))
                   → ({A : 𝓤 ̇ } (f : A → 𝕍) → ((a : A) → P (f a)) → P (𝕍-set f))
                   → (x : 𝕍) → P x
  𝕍-prop-induction {𝓣} P P-is-prop-valued ρ =
   𝕍-induction P (λ x → props-are-sets (P-is-prop-valued x)) ρ
                 (λ f g e IH₁ IH₂ _ _ → P-is-prop-valued _ _ _)


  𝕍-prop-simple-induction : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
                          → ((x : 𝕍) → is-prop (P x))
                          → ({A : 𝓤 ̇ } (f : A → 𝕍) → P (𝕍-set f))
                          → (x : 𝕍) → P x
  𝕍-prop-simple-induction P σ ρ = 𝕍-prop-induction P σ (λ f _ → ρ f)

  private
   𝕍-recursion-with-computation :
      {𝓣 : Universe} {X : 𝓣 ̇ }
    → (σ : is-set X)
    → (ρ : {A : 𝓤 ̇ } (f : A → 𝕍) → (A → X) → X)
    → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → (IH₁ : A → X)
         → (IH₂ : B → X)
         → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b ,
                          IH₁ a ＝ IH₂ b ∥)
         → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a ,
                          IH₂ b ＝ IH₁ a ∥)
         → f ≈ g → ρ f IH₁ ＝ ρ g IH₂)
    → Σ ϕ ꞉ (𝕍 → X) , ({A : 𝓤 ̇ } (f : A → 𝕍)
                       (IH : A → X) → ϕ (𝕍-set f) ＝ ρ f IH)
   𝕍-recursion-with-computation {𝓣} {X} σ ρ τ =
    ( 𝕍-induction (λ _ → X) (λ _ → σ) ρ τ'
    , 𝕍-induction-computes (λ _ → X) (λ _ → σ) ρ τ')
       where
        τ' : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
           → (e : f ≈ g) (IH₁ : A → X) (IH₂ : B → X)
           → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b ,
                            transport (λ _ → X) p (IH₁ a) ＝ IH₂ b ∥)
           → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a ,
                            transport (λ _ → X) p (IH₂ b) ＝ IH₁ a ∥)
           → transport (λ _ → X) (𝕍-set-ext f g e) (ρ f IH₁) ＝ ρ g IH₂
        τ' {A} {B} f g e IH₁ IH₂ hIH₁ hIH₂ =
         transport (λ _ → X) e' (ρ f IH₁) ＝⟨ transport-const e'          ⟩
         ρ f IH₁                          ＝⟨ τ f g IH₁ IH₂ hIH₁' hIH₂' e ⟩
         ρ g IH₂                          ∎
          where
           e' = 𝕍-set-ext f g e
           hIH₁' : (a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥
           hIH₁' a = ∥∥-functor
                      (λ (b , p , q) → (b , p , ((transport-const p) ⁻¹ ∙ q)))
                      (hIH₁ a)
           hIH₂' : (b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , IH₂ b ＝ IH₁ a ∥
           hIH₂' b = ∥∥-functor
                      (λ (a , p , q) → (a , p , ((transport-const p) ⁻¹ ∙ q)))
                      (hIH₂ b)

  𝕍-recursion : {𝓣 : Universe} {X : 𝓣 ̇ }
              → is-set X
              → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → (A → X) → X))
              → ({A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                  → (IH₁ : A → X) (IH₂ : B → X)
                  → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
                  → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , IH₂ b ＝ IH₁ a ∥)
                  → f ≈ g → ρ f IH₁ ＝ ρ g IH₂)
              → 𝕍 → X
  𝕍-recursion σ ρ τ = pr₁ (𝕍-recursion-with-computation σ ρ τ)

  𝕍-recursion-computes :
      {𝓣 : Universe} {X : 𝓣 ̇ }
    → (σ : is-set X)
    → (ρ : {A : 𝓤 ̇ } (f : A → 𝕍) → (A → X) → X)
    → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → (IH₁ : A → X) (IH₂ : B → X)
         → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
         → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , IH₂ b ＝ IH₁ a ∥)
         → f ≈ g → ρ f IH₁ ＝ ρ g IH₂)
    → ({A : 𝓤 ̇ } (f : A → 𝕍) (IH : A → X)
        → 𝕍-recursion σ ρ τ (𝕍-set f) ＝ ρ f IH)
  𝕍-recursion-computes σ ρ τ f = pr₂ (𝕍-recursion-with-computation σ ρ τ) f

  private
   𝕍-prop-recursion-with-computation :
      {𝓣 : Universe}
    → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → (A → Ω 𝓣) → Ω 𝓣))
    → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → (IH₁ : A → Ω 𝓣) (IH₂ : B → Ω 𝓣)
         → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
         → f ≲ g → ρ f IH₁ holds → ρ g IH₂ holds)
    → Σ ϕ ꞉ (𝕍 → Ω 𝓣) , ({A : 𝓤 ̇ } (f : A → 𝕍) (IH : A → Ω 𝓣)
                      → ϕ (𝕍-set f) ＝ ρ f IH)
   𝕍-prop-recursion-with-computation {𝓣} ρ τ =
    ( 𝕍-recursion (Ω-is-set fe pe) ρ τ'
    , 𝕍-recursion-computes (Ω-is-set fe pe) ρ τ')
     where
      τ' : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → (IH₁ : A → Ω 𝓣) (IH₂ : B → Ω 𝓣)
         → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
         → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , IH₂ b ＝ IH₁ a ∥)
         → f ≈ g → ρ f IH₁ ＝ ρ g IH₂
      τ' f g IH₁ IH₂ hIH₁ hIH₂ (m₁ , m₂) =
       Ω-extensionality fe pe (τ f g IH₁ IH₂ hIH₁ m₁)
                              (τ g f IH₂ IH₁ hIH₂ m₂)

  𝕍-prop-recursion : {𝓣 : Universe}
                   → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → (A → Ω 𝓣) → Ω 𝓣))
                   → ({A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                       → (IH₁ : A → Ω 𝓣) (IH₂ : B → Ω 𝓣)
                       → ((a : A) → ∥ Σ b ꞉ B ,
                                      Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
                     → f ≲ g → ρ f IH₁ holds → ρ g IH₂ holds)
                   → 𝕍 → Ω 𝓣
  𝕍-prop-recursion {𝓣} ρ τ =
   pr₁ (𝕍-prop-recursion-with-computation ρ τ)

  𝕍-prop-recursion-computes : {𝓣 : Universe}
                            → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → (A → Ω 𝓣) → Ω 𝓣))
                            → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                                 → (IH₁ : A → Ω 𝓣) (IH₂ : B → Ω 𝓣)
                                 → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b ,
                                                  IH₁ a ＝ IH₂ b ∥)
                                 → f ≲ g → ρ f IH₁ holds → ρ g IH₂ holds)
                            → ({A : 𝓤 ̇ } (f : A → 𝕍) (IH : A → Ω 𝓣)
                              → 𝕍-prop-recursion ρ τ (𝕍-set f) ＝ ρ f IH)
  𝕍-prop-recursion-computes ρ τ f =
   pr₂ (𝕍-prop-recursion-with-computation ρ τ) f

  𝕍-prop-simple-recursion : {𝓣 : Universe}
                          → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → Ω 𝓣))
                          → ({A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                            → f ≲ g → ρ f holds → ρ g holds)
                          → 𝕍 → Ω 𝓣
  𝕍-prop-simple-recursion {𝓣} ρ τ =
   𝕍-prop-recursion (λ f _ → ρ f) (λ f g _ _ _ → τ f g)

  𝕍-prop-simple-recursion-computes :
      {𝓣 : Universe}
    → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → Ω 𝓣))
    → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → f ≲ g → ρ f holds → ρ g holds)
    → ({A : 𝓤 ̇ } (f : A → 𝕍) → 𝕍-prop-simple-recursion ρ τ (𝕍-set f) ＝ ρ f)
  𝕍-prop-simple-recursion-computes ρ τ f =
   𝕍-prop-recursion-computes (λ f _ → ρ f) (λ f g _ _ _ → τ f g)
                             f (λ _ → 𝟙 , 𝟙-is-prop)

\end{code}

\begin{code}

  _∈[Ω]_ : 𝕍 → 𝕍 → Ω (𝓤 ⁺)
  _∈[Ω]_ x = 𝕍-prop-simple-recursion
              (λ {A} f → (∃ a ꞉ A , f a ＝ x) , ∃-is-prop) e
   where
    e : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
      → f ≲ g → (∃ a ꞉ A , f a ＝ x) → (∃ b ꞉ B , g b ＝ x)
    e {A} {B} f g s = ∥∥-rec ∃-is-prop
                             (λ (a , p)
                                → ∥∥-functor (λ (b , q)
                                                → b , (q ∙ p)) (s a))

  _∈_ : 𝕍 → 𝕍 → 𝓤 ⁺ ̇
  x ∈ y = (x ∈[Ω] y) holds

  ∈-is-prop-valued : {x y : 𝕍} → is-prop (x ∈ y)
  ∈-is-prop-valued {x} {y} = holds-is-prop (x ∈[Ω] y)

  ∈-for-𝕍-sets : (x : 𝕍) {A : 𝓤 ̇ } (f : A → 𝕍)
               → (x ∈ 𝕍-set f) ＝ (∃ a ꞉ A , f a ＝ x)
  ∈-for-𝕍-sets x f = ap pr₁ (𝕍-prop-simple-recursion-computes _ _ f)

  from-∈-of-𝕍-sets : {x : 𝕍} {A : 𝓤 ̇ } {f : A → 𝕍}
                    → (x ∈ 𝕍-set f) → (∃ a ꞉ A , f a ＝ x)
  from-∈-of-𝕍-sets {x} {A} {f} = Idtofun (∈-for-𝕍-sets x f)

  to-∈-of-𝕍-sets : {x : 𝕍} {A : 𝓤 ̇ } {f : A → 𝕍}
                  → (∃ a ꞉ A , f a ＝ x) → (x ∈ 𝕍-set f)
  to-∈-of-𝕍-sets {x} {A} {f} = back-Idtofun (∈-for-𝕍-sets x f)

  _⊆_ : 𝕍 → 𝕍 → 𝓤 ⁺ ̇
  x ⊆ y = (v : 𝕍) → v ∈ x → v ∈ y

  ⊆-to-≲ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → 𝕍-set f ⊆ 𝕍-set g → f ≲ g
  ⊆-to-≲ {A} {B} f g s a = from-∈-of-𝕍-sets m
   where
    m : f a ∈ 𝕍-set g
    m = s (f a) (to-∈-of-𝕍-sets ∣ a , refl ∣)

  ≲-to-⊆ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → f ≲ g → 𝕍-set f ⊆ 𝕍-set g
  ≲-to-⊆ {A} {B} f g s x m = to-∈-of-𝕍-sets n
   where
    m' : ∃ a ꞉ A , f a ＝ x
    m' = from-∈-of-𝕍-sets m
    n : ∃ b ꞉ B , g b ＝ x
    n = ∥∥-rec ∃-is-prop
               (λ (a , p) → ∥∥-functor (λ (b , q) → b , (q ∙ p)) (s a)) m'

  ⊆-is-prop-valued : {x y : 𝕍} → is-prop (x ⊆ y)
  ⊆-is-prop-valued = Π₂-is-prop fe (λ _ _ → ∈-is-prop-valued)

  ⊆-is-reflexive : {x : 𝕍} → x ⊆ x
  ⊆-is-reflexive _ = id

  ＝-to-⊆ : {x y : 𝕍} → x ＝ y → x ⊆ y
  ＝-to-⊆ refl = ⊆-is-reflexive

\end{code}

\begin{code}

  pre-extensionality : {A : 𝓤 ̇ } (f : A → 𝕍) (x : 𝕍)
                     → x ⊆ 𝕍-set f → 𝕍-set f ⊆ x → x ＝ 𝕍-set f
  pre-extensionality f =
   𝕍-prop-simple-induction (λ x → x ⊆ 𝕍-set f → 𝕍-set f ⊆ x → x ＝ 𝕍-set f)
                           (λ _ → Π₂-is-prop fe (λ _ _ → 𝕍-is-set))
                           γ
    where
     γ : {B : 𝓤 ̇  } (g : B → 𝕍)
       → 𝕍-set g ⊆ 𝕍-set f → 𝕍-set f ⊆ 𝕍-set g → 𝕍-set g ＝ 𝕍-set f
     γ g s t = 𝕍-set-ext g f (⊆-to-≲ g f s , ⊆-to-≲ f g t)

  ∈-extensionality : (x y : 𝕍) → x ⊆ y → y ⊆ x → x ＝ y
  ∈-extensionality x y =
   𝕍-prop-simple-induction (λ v → x ⊆ v → v ⊆ x → x ＝ v)
                           (λ _ → Π₂-is-prop fe (λ _ _ → 𝕍-is-set))
                           (λ f → pre-extensionality f x)
                           y

  ∈-induction : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
              → ((x : 𝕍) → is-prop (P x))
              → ((x : 𝕍) → ((y : 𝕍) → y ∈ x → P y) → P x)
              → (x : 𝕍) → P x
  ∈-induction P P-is-prop-valued h = 𝕍-prop-induction P P-is-prop-valued γ
   where
    γ : {A : 𝓤 ̇ } (f : A → 𝕍) → ((a : A) → P (f a)) → P (𝕍-set f)
    γ {A} f IH = h (𝕍-set f) c
     where
      c : (y : 𝕍) → y ∈ 𝕍-set f → P y
      c y m = ∥∥-rec (P-is-prop-valued y) (λ (a , p) → transport P p (IH a)) m'
       where
        m' : ∃ a ꞉ A , f a ＝ y
        m' = from-∈-of-𝕍-sets m

\end{code}
