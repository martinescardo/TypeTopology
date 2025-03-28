Martin Escardo 2011

A function is dense if the complement of its image is empty. Maybe
¬¬-surjective would be a better terminology.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.Density where

open import MLTT.Spartan
open import NotionsOfDecidability.Decidable
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.LeftCancellable
open import UF.Retracts
open import UF.Subsingletons

is-dense : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-dense {𝓤} {𝓥} {X} {Y} f = ¬ (Σ y ꞉ Y , ¬ (Σ x ꞉ X , f x ＝ y))

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

Added on 26 March 2025 by Fredrik Bakke.

Every function can be factored essentially uniquely into a dense map followed by
a double negation stable embedding through its "double negation image". We
appeal to a relaxation of the function extensionality axiom: that negations are
propositions.

\begin{code}

is-¬¬-stable-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-¬¬-stable-map {𝓤} {𝓥} {X} {Y} f = each-fiber-of f ¬¬-stable

_∈¬¬-image_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y → (X → Y) → 𝓤 ⊔ 𝓥 ̇
y ∈¬¬-image f = ¬¬ (fiber f y)

being-in-the-¬¬-image-is-prop : ({A : 𝓤 ⊔ 𝓥 ̇ } → is-prop (¬ A))
                              → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y : Y) (f : X → Y)
                              → is-prop (y ∈¬¬-image f)
being-in-the-¬¬-image-is-prop negations-are-props y f = negations-are-props

¬¬-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
¬¬-image f = Σ y ꞉ codomain f , y ∈¬¬-image f

¬¬-restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
               → ¬¬-image f → Y
¬¬-restriction f (y , _) = y

¬¬-corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                 → X → ¬¬-image f
¬¬-corestriction f x = (f x , ¬¬-intro (x , refl))

¬¬-image-factorization : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → f ∼ ¬¬-restriction f ∘ ¬¬-corestriction f
¬¬-image-factorization f x = refl

¬¬-corestrictions-are-dense : ({A : 𝓤 ⊔ 𝓥 ̇ } → is-prop (¬ A))
                            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-dense (¬¬-corestriction f)
¬¬-corestrictions-are-dense negations-are-props f ((y , nnp) , nq) =
  nnp (λ (x , p) → nq (x , to-Σ-＝ (p , negations-are-props _ nnp)))

¬¬-restrictions-are-embeddings : ({A : 𝓤 ⊔ 𝓥 ̇ } → is-prop (¬ A))
                               → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                               → is-embedding (¬¬-restriction f)
¬¬-restrictions-are-embeddings negations-are-props f = pr₁-is-embedding
                                                        (λ y →
                                                         negations-are-props)

¬¬-restrictions-are-left-cancellable : ({A : 𝓤 ⊔ 𝓥 ̇ } → is-prop (¬ A))
                                     → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                     → left-cancellable (¬¬-restriction f)
¬¬-restrictions-are-left-cancellable negations-are-props f =
 embeddings-are-lc (¬¬-restriction f)
  (¬¬-restrictions-are-embeddings negations-are-props f)

¬¬-restrictions-are-¬¬-stable : ({A : 𝓤 ⊔ 𝓥 ̇ } → is-prop (¬ A))
                              → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → is-¬¬-stable-map (¬¬-restriction f)
¬¬-restrictions-are-¬¬-stable negations-are-props f y nnip = ((y , a) , refl)
 where
  a : y ∈¬¬-image f
  a np = nnip b
   where
    b : ¬ (Σ v ꞉ ¬¬-image f , ¬¬-restriction f v ＝ y)
    b (v , p) = ¬¬-corestrictions-are-dense negations-are-props f c
     where
      c : Σ v ꞉ ¬¬-image f , ¬ (fiber (¬¬-corestriction f) v)
      c = (v , d)
       where
        d : ¬ (fiber (¬¬-corestriction f) v)
        d (x , q) = np (x , (ap (¬¬-restriction f) q ∙ p))


\end{code}

Double negation stability is a form of split support and lets us conclude from
left cancellability that a map is an embedding.

\begin{code}

¬¬-stable-left-cancellable-maps-are-embeddings
 : ({A : 𝓤 ⊔ 𝓥 ̇ } → is-prop (¬ A))
 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (f : X → Y)
 → left-cancellable f
 → is-¬¬-stable-map f
 → is-embedding f
¬¬-stable-left-cancellable-maps-are-embeddings negations-are-props f lc s = f-is-embedding
 where
  ¬¬-corestriction-f-is-split-surjective : (u : ¬¬-image f)
                                         → fiber (¬¬-corestriction f) u
  ¬¬-corestriction-f-is-split-surjective (y , nnp) =
   let
    (x , p) = s y nnp
   in
   ( x , ¬¬-restrictions-are-left-cancellable negations-are-props f p)

  ¬¬-corestriction-f-is-equiv : is-equiv (¬¬-corestriction f)
  ¬¬-corestriction-f-is-equiv =
   lc-split-surjections-are-equivs
    (¬¬-corestriction f)
    (factor-is-lc (¬¬-corestriction f) (¬¬-restriction f) lc)
    (¬¬-corestriction-f-is-split-surjective)

  ¬¬-corestriction-f-is-embedding : is-embedding (¬¬-corestriction f)
  ¬¬-corestriction-f-is-embedding = equivs-are-embeddings
                                     (¬¬-corestriction f)
                                     (¬¬-corestriction-f-is-equiv)

  f-is-embedding : is-embedding f
  f-is-embedding = ∘-is-embedding
                    (¬¬-corestriction-f-is-embedding)
                    (¬¬-restrictions-are-embeddings negations-are-props f)

decidable-maps-are-¬¬-stable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                             → (f : X → Y)
                             → is-decidable-map f
                             → is-¬¬-stable-map f
decidable-maps-are-¬¬-stable f d x = ¬¬-stable-if-decidable (fiber f x) (d x)

decidable-left-cancellable-maps-are-embeddings
 : ({A : 𝓤 ⊔ 𝓥 ̇ } → is-prop (¬ A))
 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (f : X → Y)
 → left-cancellable f
 → is-decidable-map f
 → is-embedding f
decidable-left-cancellable-maps-are-embeddings negations-are-props f lc d =
 ¬¬-stable-left-cancellable-maps-are-embeddings negations-are-props f lc
  (decidable-maps-are-¬¬-stable f d)

\end{code}
