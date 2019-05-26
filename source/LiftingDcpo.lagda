Tom de Jong 25th May 2019

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Subsingletons
open import UF-FunExt
open import UF-PropTrunc

module LiftingDcpo
  (𝓣 : Universe) -- fix a universe for the propositions
  (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
  (pe : propext 𝓣)
  (pt : propositional-truncations-exist)
  {𝓤 : Universe}
  (X : 𝓤 ̇)
  (s : is-set X)
  where

open import UF-Base
--open import UF-Retracts
--open import UF-Subsingletons-FunExt
open import Lifting 𝓣
open import LiftingUnivalentPrecategory 𝓣 X
open import LiftingSet 𝓣
open import Dcpos pt fe 𝓤₀
open PropositionalTruncation pt
open import UF-ImageAndSurjection
open ImageAndSurjection pt
open import UF-Equiv

\end{code}

We prefer to work with this version of the order.
We also develop some lemmas about it. This duplicates some material in
LiftingUnivalentPrecategory, as we do not want to assume univalence here.

Eventually, we should move this code to a more sensible place.
Perhaps LiftingUnivalentPrecategory.

\begin{code}
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

≡-of-values-from-≡ : {l m : 𝓛 X} → l ≡ m
                   → (d : is-defined l)
                   → (e : is-defined m)
                   → value l d ≡ value m e
≡-of-values-from-≡ {l} refl d e = ap (value l) (being-defined-is-a-prop l d e)

family-value-map : {I : 𝓤₀ ̇}
                 → (α : I → 𝓛 X)
                 → Σ (\(i : I) → is-defined (α i)) → X
family-value-map α (i , d) = value (α i) d

directed-family-value-map-is-constant : {I : 𝓤₀ ̇}
                                      → (α : I → 𝓛 X)
                                      → (δ : is-directed _⊑_ α )
                                      → constant (family-value-map α)
directed-family-value-map-is-constant {I} α δ (i₀ , d₀) (i₁ , d₁) =
 γ (δ i₀ i₁) where
  f : Σ (λ i → is-defined (α i)) → X
  f = family-value-map α
  γ : ∃ (\(k : I) → (α i₀ ⊑ α k) × (α i₁ ⊑ α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
  γ = ∥∥-rec s g where
   g : Σ (\(k : I) → (α i₀ ⊑ α k) × (α i₁ ⊑ α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
   g (k , l , m) =
    f (i₀ , d₀)         ≡⟨ refl ⟩
    value (α i₀) d₀     ≡⟨ b₀ ⟩
    value (α k) (a₀ d₀) ≡⟨ ap (value (α k))
                          (being-defined-is-a-prop (α k) (a₀ d₀) (a₁ d₁)) ⟩
    value (α k) (a₁ d₁) ≡⟨ b₁ ⁻¹ ⟩
    value (α i₁) d₁     ≡⟨ refl ⟩
    f (i₁ , d₁)         ∎ where
     a₀ : is-defined (α i₀) → is-defined (α k)
     a₀ = pr₁ l
     b₀ : value (α i₀) d₀ ≡ value (α k) (a₀ d₀)
     b₀ = pr₂ l d₀
     a₁ : is-defined (α i₁) → is-defined (α k)
     a₁ = pr₁ m
     b₁ : value (α i₁) d₁ ≡ value (α k) (a₁ d₁)
     b₁ = pr₂ m d₁

lifting-sup-value : {I : 𝓤₀ ̇}
                  → (α : I → 𝓛 X)
                  → (δ : is-directed _⊑_ α )
                  → ∃ (\(i : I) → is-defined (α i)) → X
lifting-sup-value {I} α δ = 
 constant-map-to-set-truncation-of-domain-map
  (Σ \(i : I) → is-defined (α i))
  s (family-value-map α) (directed-family-value-map-is-constant α δ)

lifting-sup : {I : 𝓤₀ ̇} → {α : I → 𝓛 X} → (δ : is-directed _⊑_ α) → 𝓛 X
lifting-sup {I} {α} δ =
 ∃ (\(i : I) → is-defined (α i)) , lifting-sup-value α δ , ∥∥-is-a-prop

lifting-of-set-is-a-dcpo : is-set X → DCPO -- {!!} {!!}
lifting-of-set-is-a-dcpo s = 𝓛 X , _⊑_ , d where
 d : dcpo-axioms _⊑_
 d = j , p , r , t , a ,
      (λ {I} {α} δ →
       ((∃ \(i : I) → is-defined (α i)) ,
        lifting-sup-value α δ ,
        ∥∥-is-a-prop) ,
       (λ (i : I) →
        (λ (d : is-defined (α i)) → ∣ i , d ∣) ,
        (λ (d : is-defined (α i)) →
         constant-map-to-set-factors-through-truncation-of-domain
          (Σ( \(i : I) → is-defined (α i))) {!!} (family-value-map α) -- something weird here
          (directed-family-value-map-is-constant α δ) (i , d))) ,
       (λ (u : 𝓛 X) (b : (i : I) → α i ⊑ u) → 
        (λ d → ∥∥-rec (being-defined-is-a-prop u)
         (λ p → pr₁ (b (pr₁ p)) (pr₂ p)) d) ,
        λ d → ≡-of-values-from-≡ {!!} d {!!} )) 
     where
  j : is-set (𝓛 X)
  j = lifting-of-set-is-a-set fe fe pe X s
  p : is-prop-valued (_⊑_)
  p = ⊑-prop-valued fe fe s
  r : is-reflexive (_⊑_)
  r = 𝓛-id
  a : is-antisymmetric (_⊑_)
  a l m p q = ⊑-anti pe fe fe (p , q)
  t : is-transitive (_⊑_)
  t = 𝓛-comp

\end{code}
