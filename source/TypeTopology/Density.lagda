Martin Escardo 2011

A function is dense if the complement of its image is empty. Maybe
¬¬-surjective or ¬¬-dense would be a better terminology.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.Density where

open import MLTT.Spartan
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

is-dense : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-dense {𝓤} {𝓥} {X} {Y} f = ¬ (Σ y ꞉ Y , ¬ (Σ x ꞉ X , f x ＝ y))

being-dense-is-prop : Fun-Ext
                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → is-prop (is-dense f)
being-dense-is-prop fe f = negations-are-props fe

\end{code}

The following gives the intended meaning of density, but the above
equivalent definition avoids the use of propositional truncations.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

 density-characterization : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                          → is-dense f ↔ is-empty (complement-of-image f)
 density-characterization {𝓤} {𝓥} {X} {Y} f = (ϕ , γ)
  where
   ϕ : is-dense f → is-empty (complement-of-image f)
   ϕ d (y , ν) = d (y , (λ (φ : fiber f y) → ν ∣ φ ∣))

   γ : is-empty (complement-of-image f) → is-dense f
   γ e (y , ν) = e (y , (∥∥-rec 𝟘-is-prop ν))

 density-characterization-≃ : Fun-Ext
                            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                          → is-dense f ≃ is-empty (complement-of-image f)
 density-characterization-≃ fe f =
  logically-equivalent-props-are-equivalent
   (being-dense-is-prop fe f)
   (negations-are-props fe)
   (lr-implication (density-characterization f))
   (rl-implication (density-characterization f))


dense-maps-into-¬¬-separated-types-are-rc' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
                                            {h : X → Y} {f g : Π Z}
                                           → is-dense h
                                           → ((y : Y) → is-¬¬-separated (Z y))
                                           → f ∘ h ∼ g ∘ h
                                           → f ∼ g
dense-maps-into-¬¬-separated-types-are-rc' {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {h} {f} {g} d s p = γ
 where
  a : (y : Y) → (Σ x ꞉ X , h x ＝ y) → ¬ (f y ≠ g y)
  a y (x , q) ψ = ψ (f y                     ＝⟨ (apd f q )⁻¹ ⟩
                     transport Z q (f (h x)) ＝⟨ ap (transport Z q) (p x) ⟩
                     transport Z q (g (h x)) ＝⟨ apd g q ⟩
                     g y                     ∎)

  b : (y : Y) → ¬ (f y ≠ g y)
  b y ψ = d (y , λ σ → a y σ ψ)

  γ : f ∼ g
  γ y = s y (f y) (g y) (b y)

dense-maps-into-¬¬-separated-types-are-rc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                                            {h : X → Y} {f g : Y → Z}
                                          → is-dense h
                                          → is-¬¬-separated Z
                                          → f ∘ h ∼ g ∘ h
                                          → f ∼ g
dense-maps-into-¬¬-separated-types-are-rc d s =
 dense-maps-into-¬¬-separated-types-are-rc' d (λ _ → s)

id-is-dense : {X : 𝓤 ̇ } → is-dense (id {𝓤} {X})
id-is-dense (y , n) = n (y , refl)

comp-is-dense : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                {f : X → Y} {g : Y → Z}
              → is-dense f
              → is-dense g
              → is-dense (g ∘ f)
comp-is-dense {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} e d = h
 where
  h : ¬ (Σ z ꞉ Z , ¬ fiber (g ∘ f) z)
  h (z , n) = d (z , k)
   where
    k : ¬ fiber g z
    k (y , refl) = e (y , l)
     where
      l : ¬ fiber f y
      l (x , refl) = n (x , refl)


_↪ᵈ_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ᵈ Y = Σ f ꞉ (X → Y) , is-embedding f × is-dense f

module _ {𝓤 𝓥} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } where

 retraction-is-dense : (r : X → Y) → has-section r → is-dense r
 retraction-is-dense r (s , rs) (y , n) = n (s y , rs y)

 equivs-are-dense : (f : X → Y) → is-equiv f → is-dense f
 equivs-are-dense f e = retraction-is-dense f (equivs-have-sections f e)

 equivs-are-dense' : (f : X ≃ Y) → is-dense ⌜ f ⌝
 equivs-are-dense' (f , e) = equivs-are-dense f e

 equiv-dense-embedding : X ≃ Y → X ↪ᵈ Y
 equiv-dense-embedding e = ⌜ e ⌝ ,
                           equivs-are-embeddings ⌜ e ⌝ (⌜⌝-is-equiv e),
                           equivs-are-dense      ⌜ e ⌝ (⌜⌝-is-equiv e)

 detofun : (X ↪ᵈ Y) → X → Y
 detofun = pr₁

 is-embedding-detofun : (e : X ↪ᵈ Y) → is-embedding (detofun e)
 is-embedding-detofun e = pr₁ (pr₂ e)

 is-dense-detofun : (e : X ↪ᵈ Y) → is-dense (detofun e)
 is-dense-detofun e = pr₂ (pr₂ e)

\end{code}
