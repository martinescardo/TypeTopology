Tom de Jong 25th May 2019

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Subsingletons hiding (⊥)
open import UF-FunExt
open import UF-PropTrunc hiding (⊥)

module LiftingDcpo'
  (𝓣 : Universe) -- fix a universe for the propositions
  (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
  (pe : propext 𝓣)
  (pt : propositional-truncations-exist)
  where

open import UF-Base
open import Lifting 𝓣
open import LiftingSet 𝓣
open import Dcpos pt fe 𝓤₀
open PropositionalTruncation pt 
open import UF-ImageAndSurjection
open ImageAndSurjection pt
open import UF-Equiv
open import LiftingMonad 𝓣


\end{code}

We prefer to work with this version of the order.
We also develop some lemmas about it. This duplicates some material in
LiftingUnivalentPrecategory, as we do not want to assume univalence here.

Eventually, we should move this code to a more sensible place.
Perhaps LiftingUnivalentPrecategory.

\begin{code}
module _ 
  {𝓤 : Universe}
  (X : 𝓤 ̇)
  (s : is-set X)
  where

 open import LiftingUnivalentPrecategory 𝓣 X

 _⊑'_ : (l m : 𝓛 X) → 𝓤 ⊔ 𝓣 ⁺ ̇
 -- Note: this maps into a bigger universe than _⊑_ (!)
 l ⊑' m = is-defined l → l ≡ m

 ⊑-to-⊑' : {l m : 𝓛 X} → l ⊑ m → l ⊑' m
 ⊑-to-⊑' {l} {m} a d = ⊑-anti pe fe fe (a , b) where
  b : m ⊑ l
  b = c , v where
   c : is-defined m → is-defined l
   c = λ _ → d
   v : (e : is-defined m) → value m e ≡ value l d
   v e = value m e         ≡⟨ ap (value m)
                             (being-defined-is-a-prop m e (pr₁ a d)) ⟩
         value m (pr₁ a d) ≡⟨ g ⁻¹ ⟩
         value l d         ∎ where
    h : is-defined l → is-defined m
    h = pr₁ a
    g : value l d ≡ value m (pr₁ a d)
    g = pr₂ a d

 ⊑'-to-⊑ : {l m : 𝓛 X} → l ⊑' m → l ⊑ m
 ⊑'-to-⊑ {l} {m} a = back-eqtofun e g where
  e : (l ⊑ m) ≃ (is-defined l → l ⊑ m)
  e = ⊑-open fe fe fe l m
  g : is-defined l → l ⊑ m
  g d = transport (_⊑_ l) (a d) (𝓛-id l)


 ⊑'-is-reflexive : is-reflexive (_⊑'_)
 ⊑'-is-reflexive l d = refl

 ⊑'-is-transitive : is-transitive (_⊑'_)
 ⊑'-is-transitive l m n a b d = l ≡⟨ a d ⟩
                                m ≡⟨ b (transport is-defined (a d) d) ⟩
                                n ∎

 ⊑'-is-antisymmetric : is-antisymmetric (_⊑'_)
 ⊑'-is-antisymmetric l m a b = ⊑-anti pe fe fe (⊑'-to-⊑ a , ⊑'-to-⊑ b)

 ⊑'-prop-valued : is-prop-valued (_⊑'_)
 ⊑'-prop-valued l _ = Π-is-prop fe λ (d : is-defined l) → lifting-of-set-is-a-set fe fe pe X s

 ≡-of-values-from-≡ : {l m : 𝓛 X} → l ≡ m
                    → {d : is-defined l}
                    → {e : is-defined m}
                    → value l d ≡ value m e
 ≡-of-values-from-≡ {l} refl {d} {e} = ap (value l) (being-defined-is-a-prop l d e)
 
 ≡-to-is-defined : {l m : 𝓛 X} → l ≡ m → is-defined l → is-defined m
 ≡-to-is-defined e d = transport is-defined e d

 family-value-map : {I : 𝓤₀ ̇}
                  → (α : I → 𝓛 X)
                  → Σ (\(i : I) → is-defined (α i)) → X
 family-value-map α (i , d) = value (α i) d

 directed-family-value-map-is-constant : {I : 𝓤₀ ̇}
                                       → (α : I → 𝓛 X)
                                       → (δ : is-directed _⊑'_ α )
                                       → constant (family-value-map α)
 directed-family-value-map-is-constant {I} α δ (i₀ , d₀) (i₁ , d₁) =
  γ (is-directed-order _⊑'_ α δ i₀ i₁) where
   f : Σ (λ i → is-defined (α i)) → X
   f = family-value-map α
   γ : ∃ (\(k : I) → (α i₀ ⊑' α k) × (α i₁ ⊑' α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
   γ = ∥∥-rec s g where
    g : Σ (\(k : I) → (α i₀ ⊑' α k) × (α i₁ ⊑' α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
    g (k , l , m) = 
     f (i₀ , d₀)                             ≡⟨ refl ⟩
     value (α i₀) d₀                         ≡⟨ ≡-of-values-from-≡ (l d₀) ⟩
     value (α k) (≡-to-is-defined (l d₀) d₀) ≡⟨ ≡-of-values-from-≡ ((m d₁) ⁻¹) ⟩
     value (α i₁) d₁                         ≡⟨ refl ⟩
     f (i₁ , d₁)                             ∎ 

 lifting-sup-value : {I : 𝓤₀ ̇}
                   → (α : I → 𝓛 X)
                   → (δ : is-directed _⊑'_ α )
                   → ∃ (\(i : I) → is-defined (α i)) → X
 lifting-sup-value {I} α δ = 
  constant-map-to-set-truncation-of-domain-map
   (Σ \(i : I) → is-defined (α i))
   s (family-value-map α) (directed-family-value-map-is-constant α δ)

 lifting-sup : {I : 𝓤₀ ̇} → (α : I → 𝓛 X) → (δ : is-directed _⊑'_ α) → 𝓛 X
 lifting-sup {I} α δ =
  ∃ (\(i : I) → is-defined (α i)) , lifting-sup-value α δ , ∥∥-is-a-prop

 lifting-sup-is-upperbound : {I : 𝓤₀ ̇} → (α : I → 𝓛 X) → (δ : is-directed _⊑'_ α)
                           → (i : I) → α i ⊑' lifting-sup α δ
 lifting-sup-is-upperbound {I} α δ i = γ where
  γ : α i ⊑' lifting-sup α δ
  γ = ⊑-to-⊑' (f , v) where
   f : is-defined (α i) → is-defined (lifting-sup α δ)
   f d = ∣ i , d ∣
   v : (d : is-defined (α i)) → value (α i) d ≡ value (lifting-sup α δ) (f d)
   v d = value (α i) d                 ≡⟨ constant-map-to-set-factors-through-truncation-of-domain
                                          (Σ (\(j : I) → is-defined (α j))) s
                                          (family-value-map α)
                                          (directed-family-value-map-is-constant α δ)
                                          (i , d) ⟩
         lifting-sup-value α δ (f d)   ≡⟨ refl ⟩
         value (lifting-sup α δ) (f d) ∎

 family-defined-somewhere-sup-≡ : {I : 𝓤₀ ̇} {α : I → 𝓛 X}
                                → (δ : is-directed _⊑'_ α)
                                → (i : I)
                                → is-defined (α i)
                                → α i ≡ lifting-sup α δ
 family-defined-somewhere-sup-≡ {I} {α} δ i d =
  (lifting-sup-is-upperbound α δ i) d

 lifting-sup-is-lowerbound-of-upperbounds : {I : 𝓤₀ ̇}
                                          → {α : I → 𝓛 X}
                                          → (δ : is-directed _⊑'_ α)
                                          → (v : 𝓛 X)
                                          → ((i : I) → α i ⊑' v)
                                          → lifting-sup α δ ⊑' v
 lifting-sup-is-lowerbound-of-upperbounds {I} {α} δ v b = h where
  h : lifting-sup α δ ⊑' v
  h d = ∥∥-rec (lifting-of-set-is-a-set fe fe pe X s) g d where
   g : (Σ (\(i : I) → is-defined (α i))) → lifting-sup α δ ≡ v
   g (i , dᵢ) = lifting-sup α δ ≡⟨ (family-defined-somewhere-sup-≡ δ i dᵢ) ⁻¹ ⟩
                α i             ≡⟨ b i dᵢ ⟩
                v               ∎

 𝓛-DCPO : DCPO {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛-DCPO = 𝓛 X , _⊑'_ , sl , p , r , t , a , c where
  sl : is-set (𝓛 X)
  sl = lifting-of-set-is-a-set fe fe pe X s
  p : is-prop-valued (_⊑'_)
  p = ⊑'-prop-valued 
  r : is-reflexive (_⊑'_)
  r = ⊑'-is-reflexive
  a : is-antisymmetric (_⊑'_)
  a = ⊑'-is-antisymmetric
  t : is-transitive (_⊑'_)
  t = ⊑'-is-transitive
  c : (I : 𝓤₀ ̇) (α : I → 𝓛 X) → is-directed _⊑'_ α → has-sup _⊑'_ α
  c I α δ = lifting-sup α δ ,
            lifting-sup-is-upperbound α δ ,
            lifting-sup-is-lowerbound-of-upperbounds δ

 𝓛-DCPO⊥ : DCPO⊥ {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛-DCPO⊥ = 𝓛-DCPO , ⊥ , λ l → 𝟘-elim

module _
  {𝓤 : Universe}
  {𝓥 : Universe}
  (X : 𝓤 ̇)
  (Y : 𝓥 ̇)
  (s₀ : is-set X)
  (s₁ : is-set Y)
  where

 ♯-is-defined : (f : X → 𝓛 Y) (l : 𝓛 X) → is-defined ((f ♯) l) → is-defined l
 ♯-is-defined f l = pr₁

 ♯-is-monotone : (f : X → 𝓛 Y) → is-monotone (𝓛-DCPO X s₀) (𝓛-DCPO Y s₁) (f ♯)
 ♯-is-monotone f l m ineq d = ap (f ♯) (ineq (♯-is-defined f l d))

 ♯-is-continuous : (f : X → 𝓛 Y) → is-continuous (𝓛-DCPO X s₀) (𝓛-DCPO Y s₁) (f ♯)
 ♯-is-continuous f I α δ = u , v where
  u : (i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO Y s₁) ⟩ (f ♯) (∐ (𝓛-DCPO X s₀) δ)
  u i = ♯-is-monotone f (α i) (∐ (𝓛-DCPO X s₀) δ) (∐-is-upperbound (𝓛-DCPO X s₀) δ i)
  v : (m : ⟨ 𝓛-DCPO Y s₁ ⟩)
    → ((i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO Y s₁) ⟩ m)
    → (f ♯) (∐ (𝓛-DCPO X s₀) δ) ⊑⟨ (𝓛-DCPO Y s₁) ⟩ m
  v m ineqs d =
   ∥∥-rec (lifting-of-set-is-a-set fe fe pe Y s₁) g (♯-is-defined f (∐ (𝓛-DCPO X s₀) δ) d) where
    g : Σ (\(i : I) → is-defined (α i)) → (f ♯) (∐ (𝓛-DCPO X s₀) δ) ≡ m
    g (i , dᵢ) = (f ♯) (∐ (𝓛-DCPO X s₀) δ) ≡⟨ h i dᵢ ⟩
                 (f ♯) (α i)               ≡⟨ ineqs i (≡-to-is-defined Y s₁ (h i dᵢ) d) ⟩
                 m                         ∎ where
     h : (i : I) → is-defined (α i) → (f ♯) (∐ (𝓛-DCPO X s₀) δ) ≡ (f ♯) (α i)
     h i d = ap (f ♯) ((family-defined-somewhere-sup-≡ X s₀ δ i d) ⁻¹)

 open import LiftingUnivalentPrecategory 𝓣 Y

 𝓛̇-♯-∼ : (f : X → Y) → (η ∘ f) ♯ ∼ 𝓛̇ f
 𝓛̇-♯-∼ f l = ⊑-anti pe fe fe (a , b) where
  a : ((η ∘ f) ♯) l ⊑ (𝓛̇ f) l
  a = p , q where
   p : is-defined (((η ∘ f) ♯) l) → is-defined (𝓛̇ f l)
   p = ♯-is-defined (η ∘ f) l
   q : (d : is-defined (((η ∘ f) ♯) l))
     → value (((η ∘ f) ♯) l) d ≡ value (𝓛̇ f l) (pr₁ d)
   q d = refl
  b : (𝓛̇ f) l ⊑ ((η ∘ f) ♯) l
  b = r , s where
   r : is-defined (𝓛̇ f l) → is-defined (((η ∘ f) ♯) l)
   r d = d , *
   s : (d : is-defined (𝓛̇ f l))
     → value (𝓛̇ f l) d ≡ value (((η ∘ f) ♯) l) (r d)
   s d = refl

  𝓛̇-continuous : (f : X → Y) → is-continuous (𝓛-DCPO X s₀) (𝓛-DCPO Y s₁) (𝓛̇ f)
  𝓛̇-continuous f = transport
                     (is-continuous (𝓛-DCPO X s₀) (𝓛-DCPO Y s₁))
                     (dfunext fe (𝓛̇-♯-∼ f))
                     (♯-is-continuous (η ∘ f)) where
\end{code}
