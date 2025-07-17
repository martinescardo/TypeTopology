Martin Escardo, July 2025.

𝟚-injecting maps and 𝟚-injective types.

The motivation for this discussion is two-fold:

(1) Injective types don't have any non-trivial decidable properties in general.

(2) In particular, totally separated types, which have plenty of
    decidable properties by definition, are not innjective in general.

    Can the totally separated types be the injective types with
    respect to *some* class of maps?

    We consider 𝟚-injecting maps as a candidate for that. But, for the
    moment, they are not necessarily the answer, although we can show
    that injective types over 𝟚-injecting maps are totally separared.

\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import UF.FunExt

module gist.2-injective-types (fe : FunExt) where

open import MLTT.Spartan
open import TypeTopology.TotallySeparated
open import UF.Embeddings
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

\end{code}

The double-dualization monad with base 𝟚, incompletely defined.

\begin{code}

K : 𝓤 ̇ → 𝓤 ̇
K X = (X → 𝟚) → 𝟚

K-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → K X → K Y
K-functor f ϕ v = ϕ (v ∘ f)

η : {X : 𝓤 ̇ } → X → K X
η x u = u x

μ : {X : 𝓤 ̇ } → K (K X) → K X
μ F u = F (λ ϕ → ϕ u)

K-ext : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → K Y) → K X → K Y
K-ext f ϕ v = ϕ (λ x → f x v)

K-strength : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × K Y → K (X × Y)
K-strength (x , γ) w = γ (λ y → w (x , y))

K-prod : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → K X × K Y → K (X × Y)
K-prod (ϕ , γ) w = ϕ (λ x → γ (λ y → w (x , y)))

K-depprod : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → K X → (X → K Y) → K (X × Y)
K-depprod ϕ γ w = ϕ (λ x → γ x (λ y → w (x , y)))

\end{code}

(We probably defined above more than what we need for now, but we may
need it in the future to answer some of the questions below.)

A map j : X → Y is 𝟚-injecting if the type 𝟚 is algebraically
injective with respect to it. We don't require 𝟚-injecting maps to be
embeddings (but see the discussion below).

\begin{code}

𝟚-injecting : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
𝟚-injecting j = (f : domain j → 𝟚) → Σ f' ꞉ (codomain j → 𝟚) , f' ∘ j ∼ f

\end{code}

A type is 𝟚-injective if it is injective over 𝟚-injecting maps.

\begin{code}

𝟚-injective : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓦 ⊔ (𝓤 ⊔ 𝓥)⁺ ̇
𝟚-injective {𝓦} D 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          (j : X → Y)
                        → 𝟚-injecting j
                        → (f : X → D)
                        → Σ f' ꞉ (Y → D) , f' ∘ j ∼ f

\end{code}

We name the two projections `extension` and `extension-property`.

\begin{code}

module _
         {D : 𝓦 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
         (i : 𝟚-injective D 𝓤 𝓥)
         (j : X → Y)
         (k : 𝟚-injecting j)
         (f : X → D)
       where

 extension : (Y → D)
 extension = pr₁ (i j k f)

 extension-property : extension ∘ j ∼ f
 extension-property = pr₂ (i j k f)

\end{code}

We'll see below that the extension property really is property, rather
than general data.

By construction, the type 𝟚 is 𝟚-injective.

\begin{code}

𝟚-is-𝟚-injective : 𝟚-injective 𝟚 𝓤 𝓥
𝟚-is-𝟚-injective j = id

\end{code}

The 𝟚-injective types are closed under products and retracts.

\begin{code}

𝟚-injectives-closed-under-Π : {I : 𝓣 ̇ } {D : I → 𝓦 ̇ }
                            → ((i : I) → 𝟚-injective (D i) 𝓤 𝓥)
                            → 𝟚-injective (Π D) 𝓤 𝓥
𝟚-injectives-closed-under-Π {𝓣} {𝓦} {I} {D} D-𝟚-inj j j-𝟚-injecting f =
 (λ y i → extension (D-𝟚-inj i) j j-𝟚-injecting (λ x → f x i) y) ,
 (λ x → dfunext fe'
 (λ i → extension-property (D-𝟚-inj i) j j-𝟚-injecting (λ x → f x i) x))

\end{code}

Free algebras of the 𝟚-based double dualization monad are injective.

\begin{code}

K-𝟚-injective : {X : 𝓣 ̇ } → 𝟚-injective (K X) 𝓤 𝓥
K-𝟚-injective = 𝟚-injectives-closed-under-Π (λ i → 𝟚-is-𝟚-injective)

\end{code}

The unit of the monad is 𝟚-injecting.

\begin{code}

η-𝟚-injecting : {X : 𝓤 ̇ } → 𝟚-injecting (η {𝓤} {X})
η-𝟚-injecting f = (λ ϕ → ϕ f) , (λ x → refl)

\end{code}

For future reference, notice that the map η {𝓤} {X} is not in general
an embedding.

Hence every 𝟚-injective type is a retract of a free algebra.

\begin{code}

𝟚-injectives-are-K-retracts : {D : 𝓤 ̇ }
                            → 𝟚-injective D 𝓤 𝓤
                            → retract D of K D
𝟚-injectives-are-K-retracts D-𝟚-inj =
 extension D-𝟚-inj η η-𝟚-injecting id ,
 η ,
 extension-property D-𝟚-inj η η-𝟚-injecting id

\end{code}

And therefore the 𝟚-injective types are all totally separated, because
the type 𝟚 is totally separated, and the totally separated types are
closed under products and retracts.

\begin{code}

K-is-totally-separated : {X : 𝓤 ̇ } → is-totally-separated (K X)
K-is-totally-separated = Π-is-totally-separated fe' (λ _ → 𝟚-is-totally-separated)

𝟚-injectives-are-totally-separated : {D : 𝓤 ̇ }
                                   → 𝟚-injective D 𝓤 𝓤
                                   → is-totally-separated D
𝟚-injectives-are-totally-separated D-𝟚-inj =
 retract-of-totally-separated
  (𝟚-injectives-are-K-retracts D-𝟚-inj)
  K-is-totally-separated

\end{code}

This shows that 𝟚-injecting map doesn't need to be an
embedding. Indeed, we have seen that the map η : X → K X is always
𝟚-injecting, but we also know that it is an embedding if and only if X
is totally separated.

\begin{code}

_ : {X : 𝓤 ̇ } → is-embedding (η {𝓤} {X}) ↔ is-totally-separated X
_ = totally-separated₂-gives-totally-separated fe' ,
    totally-separated-gives-totally-separated₂ fe'

\end{code}

The extension property really is property, even though the choice of
extension is data.

\begin{code}

module _
         {D : 𝓤 ̇ } {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
         (i : 𝟚-injective D 𝓤 𝓤)
         (j : X → Y)
         (k : 𝟚-injecting j)
         (f : X → D)
       where

 extension-property-is-prop : is-prop (extension i j k f ∘ j ∼ f)
 extension-property-is-prop =
  Π-is-prop fe'
   (λ x → totally-separated-types-are-sets fe' D
           (𝟚-injectives-are-totally-separated i))

\end{code}

TODO. Can we generalize the universes in `𝟚-injectives-are-totally-separated`
and (hence) the above?

Can we show that every totally separated type A is 𝟚-injective? I
can't even show, at the time of writing, that ℕ, a totally separated
type, is 𝟚-injective.

Do totally separated types "think that 𝟚-injective types are
embeddings"? Formulate this question precisely.

Can we show that the totally separated types are precisely the
algebras of the 𝟚-based double dualization monad?

Now let's go back to (algebraic) injectivity with respect to all
embeddings. Say that a map j : X → Y is injecting if all algebraically
injective types with respect to embeddings are injective with respect
to j. Question. Can we show that j is necessarily an embedding?
