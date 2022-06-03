Martin Escardo 25th October 2018.

We show that the natural map into the lifting is an embedding.  See
the module LiftingEmbeddingViaSIP for an alternative approach via the
structure identity principle.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

module LiftingEmbeddingDirectly (𝓣 : Universe) where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Embeddings
open import UF-Equiv
open import UF-FunExt

open import Lifting 𝓣

\end{code}

Our strategy here to show that η is an embedding (has subsingleton
fibers) is to exhibit it as the composite of two embeddings (the first
of which is actually an equivalence).

\begin{code}

𝓚 : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ̇
𝓚 X = Σ P ꞉ 𝓣 ̇ , (P → X) × is-singleton P

κ : {X : 𝓤 ̇ } → X → 𝓚 X
κ x = 𝟙 , (λ _ → x) , 𝟙-is-singleton

ζ : (X : 𝓤 ̇ ) (P : 𝓣 ̇ ) → (P → X) × is-singleton P → (P → X) × is-prop P
ζ X P (φ , i) = φ , singletons-are-props i

𝓚→𝓛 : (X : 𝓤 ̇ ) → 𝓚 X → 𝓛 X
𝓚→𝓛 X = NatΣ (ζ X)

η-composite : funext 𝓣 𝓣
            → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
            → {X : 𝓤 ̇ } → η ≡ 𝓚→𝓛 X ∘ κ
η-composite fe fe' {X} = dfunext fe' h
 where
  h : (x : X) → (𝟙 , (λ _ → x) , 𝟙-is-prop)
              ≡ (𝟙 , (λ _ → x) , singletons-are-props (𝟙-is-singleton))
  h x = to-Σ-≡ (refl , to-×-≡ refl (being-prop-is-prop fe _ _))

\end{code}

The fact that 𝓚→𝓛 is an embedding can be proved by obtaining it as
a combination of maps that we already know to be embeddings, using
×-embedding, maps-of-props-are-embeddings, id-is-embedding, and
NatΣ-embedding.:

\begin{code}

ζ-is-embedding : funext 𝓣 𝓣 → (X : 𝓤 ̇ ) (P : 𝓣 ̇ ) → is-embedding (ζ X P)
ζ-is-embedding fe X P = ×-embedding
                          id
                          singletons-are-props
                          id-is-embedding
                          (maps-of-props-are-embeddings
                            singletons-are-props
                            (being-singleton-is-prop fe)
                            (being-prop-is-prop fe))

𝓚→𝓛-is-embedding : funext 𝓣 𝓣 → (X : 𝓤 ̇ ) → is-embedding (𝓚→𝓛 X)
𝓚→𝓛-is-embedding fe X = NatΣ-is-embedding
                          (λ P → (P → X) × is-singleton P)
                          (λ P → (P → X) × is-prop P)
                          (ζ X)
                          (ζ-is-embedding fe X)

\end{code}

That κ is an equivalence corresponds to the fact that the lifting of a
type X with respect to the dominance "is-singleton" is equivalent to X
itself.

\begin{code}

κ-is-equiv : propext 𝓣
           → funext 𝓣 𝓣
           → funext 𝓣 𝓤
           → {X : 𝓤 ̇ } → is-equiv (κ {𝓤} {X})
κ-is-equiv {𝓤} pe fe fe' {X} = qinvs-are-equivs κ (ρ , (ρκ , κρ))
 where
  ρ : {X : 𝓤 ̇ } → 𝓚 X → X
  ρ (P , φ , i) = φ (center i)
  ρκ : {X : 𝓤 ̇ } (x : X) → ρ (κ x) ≡ x
  ρκ x = refl
  κρ : (m : 𝓚 X) → κ (ρ m) ≡ m
  κρ (P , φ , i) = u
   where
    t : 𝟙 ≡ P
    t = pe 𝟙-is-prop (singletons-are-props i)
                     (λ _ → center i)
                     unique-to-𝟙
    s : (t : 𝟙 ≡ P)
      → transport (λ - → (- → X) × is-singleton -)
                  t ((λ _ → φ (center i)),
        𝟙-is-singleton)
      ≡ φ , i
    s refl = to-×-≡ a b
     where
      a : (λ x → φ (center i)) ≡ φ
      a = dfunext fe' (λ x → ap φ (𝟙-is-prop (center i) x))
      b : 𝟙-is-singleton ≡ i
      b = (singletons-are-props (pointed-props-are-singletons
                                   𝟙-is-singleton (being-singleton-is-prop fe))
                                 𝟙-is-singleton i)
    u : 𝟙 , (λ _ → φ (center i)) , 𝟙-is-singleton ≡ P , φ , i
    u = to-Σ-≡ (t , s t)

κ-is-embedding : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
               → {X : 𝓤 ̇ } → is-embedding (κ {𝓤} {X})
κ-is-embedding pe fe fe' = equivs-are-embeddings κ (κ-is-equiv pe fe fe')

\end{code}

Finally, η is an embedding because it is equal to the composition of
two embeddings:

\begin{code}

η-is-embedding : propext 𝓣
               → funext 𝓣 𝓣
               → funext 𝓣 𝓤
               → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
               → {X : 𝓤 ̇ } → is-embedding (η {𝓤} {X})
η-is-embedding pe fe fe' fe'' {X} =
  transport⁻¹
   is-embedding
   (η-composite fe fe'')
   (∘-is-embedding (κ-is-embedding pe fe fe') (𝓚→𝓛-is-embedding fe X))
\end{code}
