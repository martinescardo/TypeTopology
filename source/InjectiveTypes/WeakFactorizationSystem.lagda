Tom de Jong, 22 May 2025
A weak factorization system of embeddings and fiberwise injective maps

An anonymous reviewer of our TYPES abstract [1] suggested that some of our
results could be generalized to weak factorization systems. Here we consider a
factorization system based on embeddings and maps whose fibers are all injective
types. We are also thinking about the connections to *algebraic* weak
factorization systems.

[1] Tom de Jong and Martı́n Hötzel Escardó.
    "Examples and counter-examples of injective types in univalent mathematics".
    Abstract for the 31st International Conference on Types for Proofs and
    Programs (TYPES). 2025.
    url: https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper6.pdf.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module InjectiveTypes.WeakFactorizationSystem
        (fe : FunExt)
       where

open import InjectiveTypes.Blackboard fe

open import MLTT.Spartan

open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.IdEmbedding
open import UF.Univalence

\end{code}

We define a fiberwise algebraically injective map to be one whose fibers are all
algebraically injective types.

NB. It may be that fiberwise flabbiness is more convenient to work with.

\begin{code}

fiberwise-ainjective : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (𝓦 𝓣 : Universe)
                     → ((𝓦 ⊔ 𝓣) ⁺ ⊔ 𝓤 ⊔ 𝓥) ̇
fiberwise-ainjective f 𝓦 𝓣 =
 each-fiber-of f (λ F → ainjective-type F 𝓦 𝓣)

\end{code}

Any map can be factored as an embedding followed by a fiberwise algebraically
injective map.

\begin{code}

embedding-fiberwise-ainjective-factorization
 : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
 → is-univalent (𝓤 ⊔ 𝓥)
 → (f : A → B)
 → Σ X ꞉ (𝓤 ⊔ 𝓥)⁺ ̇  ,
   Σ l ꞉ (A → X) ,
   Σ r ꞉ (X → B) , (f ＝ r ∘ l)
                 × is-embedding l
                 × fiberwise-ainjective r (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
embedding-fiberwise-ainjective-factorization {𝓤} {𝓥} {A} {B} ua f =
 X , l , r , refl , l-is-embedding ua , r-fiberwise-ainjective ua
  where
   X : (𝓤 ⊔ 𝓥) ⁺ ̇
   X = Σ b ꞉ B , (fiber f b → (𝓤 ⊔ 𝓥) ̇ )

   ι : (Y : 𝓤' ̇ ) → Y → (Y → 𝓤' ̇ )
   ι Y = Id

   ι-is-embedding : is-univalent 𝓤' → (Y : 𝓤' ̇ ) → is-embedding (ι Y)
   ι-is-embedding ua _ = UA-Id-embedding ua fe

   l : A → X
   l = NatΣ (λ b → ι (fiber f b)) ∘ ⌜ domain-is-total-fiber f ⌝

   l-is-embedding : is-univalent (𝓤 ⊔ 𝓥) → is-embedding l
   l-is-embedding ua =
    ∘-is-embedding
     (equivs-are-embeddings' (domain-is-total-fiber f))
     (NatΣ-is-embedding
       (fiber f)
       (λ b → fiber f b → 𝓤 ⊔ 𝓥 ̇ )
       (λ b → ι (fiber f b))
       (λ b → ι-is-embedding ua (fiber f b)))

   r : X → B
   r = pr₁

   r-fiberwise-ainjective : is-univalent (𝓤 ⊔ 𝓥)
                          → fiberwise-ainjective r (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
   r-fiberwise-ainjective ua b =
    equiv-to-ainjective
     (fiber r b)
     (fiber f b → 𝓤 ⊔ 𝓥 ̇ )
     (power-of-ainjective (universes-are-ainjective-Π' ua))
     (pr₁-fiber-equiv b)

\end{code}

We have (specified) diagonal lifts of embeddings against fiberwise algebraically
injective maps.

We consider a commutative square with j an embedding and r fiberwise
algebraically injective and we look to find diagonal filler: a map e : Y → D
making the resulting triangles commute.

       f
  X ------> D
  |       ^ |
  |      /  |
j |  ∃e /   | r
  |    /    |
  |   /     |
  v  /      v
  Y ------> E
       g

Note that in our case we have a designated filler.

\begin{code}

module lifting-problem
        {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {D : 𝓦 ̇ } {E : 𝓣 ̇ }
        (j : X → Y) (f : X → D) (r : D → E) (g : Y → E)
        (j-is-embedding : is-embedding j)
        (r-fiberwise-ainjective : fiberwise-ainjective r (𝓤 ⊔ 𝓥) 𝓣')
        -- NB. The last universe parameter is arbitrary.
        (comm-sq : r ∘ f ∼ g ∘ j)
       where

 lifting-problem-has-a-solution : Σ e ꞉ (Y → D) , (e ∘ j ∼ f) × (r ∘ e ∼ g)
 lifting-problem-has-a-solution = e , e-upper-triangle , e-lower-triangle
  where
   module _ (y : Y) where

    f̅ : fiber j y → fiber r (g y)
    f̅ (x , e) = (f x , (r (f x) ＝⟨ comm-sq x ⟩
                        g (j x) ＝⟨ ap g e ⟩
                        g y     ∎))

    𝕖 : Σ e ꞉ fiber r (g y) , ((p : fiber j y) → e ＝ f̅ p)
    𝕖 = ainjective-types-are-aflabby
         (fiber r (g y))
         (r-fiberwise-ainjective (g y))
         (fiber j y)
         (j-is-embedding y)
         f̅

    eʸ = pr₁ 𝕖
    eʸ-extends : (p : fiber j y) → eʸ ＝ f̅ p
    eʸ-extends = pr₂ 𝕖

   e : Y → D
   e y = pr₁ (eʸ y)

   e-lower-triangle : r ∘ e ∼ g
   e-lower-triangle y = pr₂ (eʸ y)

   e-upper-triangle : e ∘ j ∼ f
   e-upper-triangle x = ap pr₁ I
    where
     I : eʸ (j x) ＝ f̅ (j x) (x , refl)
     I = eʸ-extends (j x) (x , refl)

\end{code}

In the above it is important to work with *algebraically* injective types: if we
instead had assumed that each fiber of r is only injective, then we would have
gotten for each y : Y an unspecified element of D only, which, in the absence of
choice, fails to produce a function.

Finally, since propositions and injective types are closed under retracts and
because retractions of maps induce retractions of their fibers [HoTTBook,
Lemma 4.7.3], the embeddings and the fiberwise injective maps are closed under
retracts, so that by the "retract argument" [Rie14, Lemma 11.2.3], the
embeddings and fiberwise injective maps indeed give rise to a weak factorization
system.

TODO. Formalize this and, as a preliminary, retracts of maps.

[Rie14] Emily Riehl. Categorical Homotopy Theory.
        New Mathematical Monographs 24.
        Cambridge University Press, 2014.
        doi: 10.1017/ CBO9781107261457.
        url: https://math.jhu.edu/~eriehl/cathtpy.pdf.