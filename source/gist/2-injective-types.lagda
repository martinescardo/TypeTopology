Martin Escardo, July 2025.

𝟚-injecting maps and 𝟚-injective types.

The motivation for this discussion is two-fold:

(1) Injective types don't have any non-trivial decidable properties in general.

(2) In particular, totally separated types, which have plenty of
    decidable properties by definition, fail badly to be injective in general.

    Can the totally separated types always be the injective types with
    respect to *some* class of maps?

    We consider 𝟚-injecting maps as a candidate for that. But, for the
    moment, they are not necessarily the answer, although we can show
    that injective types over 𝟚-injecting maps are totally separared.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt

module gist.2-injective-types (fe : FunExt) where

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import TypeTopology.TotallySeparated
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Embeddings
open import UF.PropTrunc
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

ηᴷ : {X : 𝓤 ̇ } → X → K X
ηᴷ x u = u x

μᴷ : {X : 𝓤 ̇ } → K (K X) → K X
μᴷ F u = F (λ ϕ → ϕ u)

extᴷ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → K Y) → K X → K Y
extᴷ f ϕ v = ϕ (λ x → f x v)

strengthᴷ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × K Y → K (X × Y)
strengthᴷ (x , γ) w = γ (λ y → w (x , y))

\end{code}

(We probably defined above more than what we need for now, but we may
need it in the future to answer some of the questions below.)

\begin{code}

_is-injective-over_ : (D : 𝓣 ̇ ) {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
D is-injective-over j = (f : domain j → D) → Σ f' ꞉ (codomain j → D) , f' ∘ j ∼ f

\end{code}

If D is injective over j, we also say that j is D-injecting.

We name the two projections.

\begin{code}

module _
         {D : 𝓦 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
         (j : X → Y)
         (i : D is-injective-over j)
         (f : X → D)
       where

 extension : (Y → D)
 extension = pr₁ (i f)

 extension-extends : extension ∘ j ∼ f
 extension-extends = pr₂ (i f)

\end{code}

The D-injecting maps form a wild category.

\begin{code}

injective-over-id : (D : 𝓣 ̇ ) {X : 𝓤 ̇ }
                  → D is-injective-over (𝑖𝑑 X)
injective-over-id D f = f , ∼-refl

injective-over-∘ : (D : 𝓣 ̇ ) {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                   {j : X → Y} {k : Y → Z}
                 → D is-injective-over j
                 → D is-injective-over k
                 → D is-injective-over (k ∘ j)
injective-over-∘ D {X} {Y} {Z} {j} {k} ji ki f = f'' , f''-extends-f
 where
  f' : Y → D
  f' = extension j ji f

  f'-extends-f : f' ∘ j ∼ f
  f'-extends-f = extension-extends j ji f

  f'' : Z → D
  f'' = extension k ki f'

  f''-extends-f' : f'' ∘ k ∼ f'
  f''-extends-f' = extension-extends k ki f'

  f''-extends-f : f'' ∘ (k ∘ j) ∼ f
  f''-extends-f x = f'' (k (j x)) ＝⟨ f''-extends-f' (j x) ⟩
                    f' (j x)      ＝⟨ f'-extends-f x ⟩
                    f x           ∎

\end{code}

The natural instinct in the following is to assume that D is pointed,
but, more generally, we can assume that D is pointed if Y is pointed,
that is, we have some given function Y → D. Also, it is enough to
assume that j is left-cancellable, rather than an embedding.

\begin{code}

module _ (D : 𝓣 ̇ ) {X : 𝓤 ̇ } {Y : 𝓥 ̇ } where

 lc-map-with-decidable-fibers-is-universally-injecting
  : (j : X → Y)
  → left-cancellable j
  → each-fiber-of j is-decidable
  → (Y → D)
  → D is-injective-over j
 lc-map-with-decidable-fibers-is-universally-injecting j j-lc δ g f
  = f' , f'-extends-f
  where
   h : (y : Y) → is-decidable (fiber j y) → D
   h y (inl (x , e)) = f x
   h y (inr ν)       = g y

   f' : Y → D
   f' y = h y (δ y)

   H : (x : X) (d : is-decidable (fiber j (j x))) → h (j x) d ＝ f x
   H x (inl (x' , e)) = ap f (j-lc e)
   H x (inr ν)        = 𝟘-elim (ν (x , refl))

   f'-extends-f : f' ∘ j ∼ f
   f'-extends-f x = H x (δ (j x))

 inl-is-injective-over : (Y → D) → D is-injective-over (inl {𝓤} {𝓥} {X} {Y})
 inl-is-injective-over g f = cases f g , ∼-refl

 inr-is-injective-over : (X → D) → D is-injective-over (inr {𝓤} {𝓥} {X} {Y})
 inr-is-injective-over g f = cases g f , ∼-refl

\end{code}

In this file we are mostly interesting in the case D = 𝟚. We don't
require 𝟚-injecting maps to be embeddings (but see the discussion
below).

\begin{code}

is-𝟚-injecting : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-𝟚-injecting j = 𝟚 is-injective-over j

\end{code}

In topological terms, the above means that every clopen of X can be
extended to a clopen of Y along j.

We say that a type is 𝟚-injective if it is injective over 𝟚-injecting
maps.

\begin{code}

𝟚-injective : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓦 ⊔ (𝓤 ⊔ 𝓥)⁺ ̇
𝟚-injective {𝓦} D 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
                        → is-𝟚-injecting j
                        → D is-injective-over j

\end{code}

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
 (λ y i → extension j (D-𝟚-inj i j j-𝟚-injecting) (λ x → f x i) y) ,
 (λ x → dfunext fe'
 (λ i → extension-extends j (D-𝟚-inj i j j-𝟚-injecting) (λ x → f x i) x))

retract-of-𝟚-injective : (D' : 𝓣' ̇ ) (D : 𝓣 ̇ )
                       → 𝟚-injective D 𝓤 𝓥
                       → retract D' of D
                       → 𝟚-injective D' 𝓤 𝓥
retract-of-𝟚-injective D' D i (r , s , rs) {X} {Y} j e f = φ a
  where
   a : Σ f' ꞉ (Y → D) , f' ∘ j ∼ s ∘ f
   a = i j e (s ∘ f)

   φ : (Σ f' ꞉ (Y → D) , f' ∘ j ∼ s ∘ f) → Σ f'' ꞉ (Y → D') , f'' ∘ j ∼ f
   φ (f' , h) = r ∘ f' , (λ x → ap r (h x) ∙ rs (f x))

\end{code}

TODO. Formulate the above in more generality with the same proof.

The free algebras of the 𝟚-based double dualization monad are 𝟚-injective.

\begin{code}

first-dual-is-𝟚-injective : {X : 𝓣 ̇ } → 𝟚-injective (X → 𝟚) 𝓤 𝓥
first-dual-is-𝟚-injective = 𝟚-injectives-closed-under-Π (λ i → 𝟚-is-𝟚-injective)

K-is-𝟚-injective : {X : 𝓣 ̇ } → 𝟚-injective (K X) 𝓤 𝓥
K-is-𝟚-injective = first-dual-is-𝟚-injective

\end{code}

So, for example, the Cantor type (ℕ → 𝟚) is 𝟚-injective, and hence so
is ℕ∞, because it is a retract of the Cantor type).

The unit of the monad is 𝟚-injecting.

\begin{code}

ηᴷ-is-𝟚-injecting : {X : 𝓤 ̇ } → is-𝟚-injecting (ηᴷ {𝓤} {X})
ηᴷ-is-𝟚-injecting f = (λ ϕ → ϕ f) , ∼-refl

\end{code}

Hence every 𝟚-injective type is a retract of a free algebra.

\begin{code}

𝟚-injectives-are-K-retracts : {D : 𝓤 ̇ }
                            → 𝟚-injective D 𝓤 𝓤
                            → retract D of K D
𝟚-injectives-are-K-retracts D-𝟚-inj =
 extension ηᴷ (D-𝟚-inj ηᴷ ηᴷ-is-𝟚-injecting) id ,
 ηᴷ ,
 extension-extends ηᴷ (D-𝟚-inj ηᴷ ηᴷ-is-𝟚-injecting) id

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

The above shows that a 𝟚-injecting map doesn't need to be an
embedding. Indeed, we have seen that the map ηᴷ : X → K X is always
𝟚-injecting, but we also know that it is an embedding if and only if X
is totally separated.

\begin{code}

_ : {X : 𝓤 ̇ } → is-embedding (ηᴷ {𝓤} {X}) ↔ is-totally-separated X
_ = totally-separated₂-gives-totally-separated fe' ,
    totally-separated-gives-totally-separated₂ fe'

\end{code}

The extension requirement is property, even though the choice of
extension is data.

\begin{code}

module _
         {D : 𝓤 ̇ } {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
         (i : 𝟚-injective D 𝓤 𝓤)
         (j : X → Y)
         (k : is-𝟚-injecting j)
         (f : X → D)
       where

 extension-extends-is-prop : is-prop (extension j (i j k) f ∘ j ∼ f)
 extension-extends-is-prop =
  Π-is-prop fe'
   (λ x → totally-separated-types-are-sets fe' D
           (𝟚-injectives-are-totally-separated i))

\end{code}

As discussed above, we didn't require 2-injecting maps to be
embeddings. We now show, in a number of steps, that we could have
required them to be embeddings without loss of generality.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y) (ji : is-𝟚-injecting j) where

 𝟚-injecting-map-with-totally-separated-domain-is-lc
  : is-totally-separated X → left-cancellable j
 𝟚-injecting-map-with-totally-separated-domain-is-lc  ts {x} {x'} e = ts I
  where
   I : (p : X → 𝟚) → p x ＝ p x'
   I p = e'
    where
     p' : Y → 𝟚
     p' = pr₁ (ji p)

     p'-extends-p : p' ∘ j ∼ p
     p'-extends-p = pr₂ (ji p)

     e' = p x       ＝⟨ (p'-extends-p x)⁻¹ ⟩
          p' (j x)  ＝⟨ ap p' e ⟩
          p' (j x') ＝⟨ p'-extends-p x' ⟩
          p x'      ∎

 𝟚-injecting-map-of-totally-separated-types-is-embedding
  : is-totally-separated X → is-totally-separated Y → is-embedding j
 𝟚-injecting-map-of-totally-separated-types-is-embedding X-ts Y-ts
  = lc-maps-into-sets-are-embeddings j
     (𝟚-injecting-map-with-totally-separated-domain-is-lc X-ts)
     (totally-separated-types-are-sets fe' Y Y-ts)

\end{code}

We now need to assume that propositional truncations exist, to be able
to construct the totally separated reflection of a type.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open totally-separated-reflection fe pt

\end{code}

The unit of the totally separated reflection is 𝟚-injecting.

\begin{code}

 ηᵀ-is-𝟚-injecting : {X : 𝓤 ̇ } → is-𝟚-injecting (ηᵀ {𝓤} {X})
 ηᵀ-is-𝟚-injecting {𝓤} {X} f = extᵀ 𝟚-is-totally-separated f ,
                               ext-ηᵀ 𝟚-is-totally-separated f

\end{code}

The reflection of any 𝟚-injecting map is again 𝟚-injecting, and also
always an embedding.

\begin{code}

 module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y) (ji : is-𝟚-injecting j) where

  𝕋-is-𝟚-injecting : is-𝟚-injecting (𝕋-functor j)
  𝕋-is-𝟚-injecting q = q' , q'-extends-q
   where
    p : X → 𝟚
    p = q ∘ ηᵀ

    p' : Y → 𝟚
    p' = extension j ji p

    p'-extends-p : p' ∘ j ∼ p
    p'-extends-p = extension-extends j ji p

    q' : 𝕋 Y → 𝟚
    q' = extᵀ 𝟚-is-totally-separated p'

    q'-extends-q : q' ∘ 𝕋-functor j ∼ q
    q'-extends-q =
     ηᵀ-induction
      (λ t → q' (𝕋-functor j t) ＝ q t)
      (λ t → 𝟚-is-set)
      (λ x → q' (𝕋-functor j (ηᵀ x))            ＝⟨refl⟩
             extᵀ _ p' (extᵀ _ (ηᵀ ∘ j) (ηᵀ x)) ＝⟨ I x ⟩
             extᵀ _ p' (ηᵀ (j x))               ＝⟨ II x ⟩
             p' (j x)                           ＝⟨ p'-extends-p x ⟩
             p x                                ＝⟨refl⟩
             q (ηᵀ x)                           ∎)
      where
       I  = λ x → ap (extᵀ _ p') (ext-ηᵀ _ (ηᵀ ∘ j) x)
       II = λ x → ext-ηᵀ _ p' (j x)

  𝕋-is-embedding : is-embedding (𝕋-functor j)
  𝕋-is-embedding = 𝟚-injecting-map-of-totally-separated-types-is-embedding
                    (𝕋-functor j)
                    𝕋-is-𝟚-injecting
                    𝕋-is-totally-separated
                    𝕋-is-totally-separated
\end{code}

TODO. The above proof probably doesn't need induction. The reflection
laws should suffice.

The formulation of the following doesn't use propositional
truncations, but its construction does, indirectly.

The following are equivalent for any type D.

1. D is injective over 𝟚-injecting maps.

2. D is totally separated and injective over 𝟚-injecting embeddings of
   totally separated types.

\begin{code}

 is-injective-over-𝟚-injecting-embeddings-of-ts-types
  : 𝓣 ̇ → (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ⊔ 𝓣 ̇
 is-injective-over-𝟚-injecting-embeddings-of-ts-types D 𝓤 𝓥
  = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
  → is-𝟚-injecting j
  → is-embedding j
  → is-totally-separated X
  → is-totally-separated Y
  → D is-injective-over j

 characterization-of-𝟚-injectivity
  : (D : 𝓤 ̇ )
  → 𝟚-injective D 𝓤 𝓤
  ↔ (is-totally-separated D
    × is-injective-over-𝟚-injecting-embeddings-of-ts-types D 𝓤 𝓤)
 characterization-of-𝟚-injectivity {𝓤} D
  = (λ D-𝟚-inj → 𝟚-injectives-are-totally-separated D-𝟚-inj ,
                 (λ j ji _ _ _ → D-𝟚-inj j ji)) ,
    I
  where
   I : is-totally-separated D
     × is-injective-over-𝟚-injecting-embeddings-of-ts-types D 𝓤 𝓤
     → 𝟚-injective D 𝓤 𝓤
   I (D-ts , D-inj) {X} {Y} j ji f = f' , f'-extends-f
    where
     g : 𝕋 X → D
     g = extᵀ D-ts f

     II : D is-injective-over (𝕋-functor j)
     II = D-inj
           (𝕋-functor j)
           (𝕋-is-𝟚-injecting j ji)
           (𝕋-is-embedding j ji)
           𝕋-is-totally-separated
           𝕋-is-totally-separated

     g' : 𝕋 Y → D
     g' = extension (𝕋-functor j) II g

     g'-extends-g : g' ∘ 𝕋-functor j ∼ g
     g'-extends-g = extension-extends (𝕋-functor j) II g

     f' : Y → D
     f' = g' ∘ ηᵀ

     f'-extends-f : f' ∘ j ∼ f
     f'-extends-f x =
      f' (j x)                ＝⟨refl⟩
      g' (ηᵀ (j x))           ＝⟨ ap g' ((𝕋-natural j x)⁻¹) ⟩
      g' (𝕋-functor j (ηᵀ x)) ＝⟨ g'-extends-g (ηᵀ x) ⟩
      g (ηᵀ x)                ＝⟨refl⟩
      extᵀ D-ts f (ηᵀ x)      ＝⟨ ext-ηᵀ D-ts f x ⟩
      f x                     ∎

\end{code}

TODO.

  (1) Can we generalize the universes in
      `𝟚-injectives-are-totally-separated` and (hence much of) the above?

  (2) Can we show that every totally separated type is 𝟚-injective? I
      can't even show, at the time of writing, that ℕ, a totally
      separated type, is 𝟚-injective.

  (3) Can we show that the totally separated types are precisely the
      algebras of the 𝟚-based double dualization monad?

  (4) Now let's go back to (algebraic) injectivity with respect to all
      embeddings. Say that a map j : X → Y is injecting if all
      algebraically injective types with respect to embeddings are
      injective with respect to j. Question. Can we show that j is
      necessarily an embedding?  Perhaps an embedding is precisely the
      same thing as an Ω-injecting map.

We now show that if all functions 𝟚ᴺ → 𝟚 are uniformly continuous,
then ℕ is 𝟚-injective.

\begin{code}

open import MLTT.Two-Properties
open import Naturals.Order
open import Naturals.Properties
open import Notation.Order
open import TypeTopology.Cantor

open notions-of-continuity 𝟚 𝟚-is-discrete

ℕ-is-𝟚-injective-if-all-functions-𝟚ᴺ→𝟚-are-uc
 : ((f : 𝟚ᴺ → 𝟚) → is-uniformly-continuous f)
 → 𝟚-injective ℕ 𝓤 𝓥
ℕ-is-𝟚-injective-if-all-functions-𝟚ᴺ→𝟚-are-uc {𝓤} {𝓥} brouwer
 = ℕ-is-𝟚-injective
 where
  I : (n : ℕ) → (succ n) is-a-modulus-of-uc-of (ηᴷ n)
  I 0        α β (e , _ ) = e
  I (succ n) α β (_ , es) = I n (tail α) (tail β) es

  II : (n k : ℕ)
    → k is-a-modulus-of-uc-of (ηᴷ n)
    → ¬ (k ≤ n)
  II n k is-mod l = impossible
   where
    have-is-mod : (α β : 𝟚ᴺ) → α ＝⟦ k ⟧ β → α n ＝ β n
    have-is-mod = is-mod

    have-l : k ≤ n
    have-l = l

    γ : ℕ → 𝟚ᴺ
    γ 0        = 𝟏
    γ (succ k) = cons ₀ (γ k)

    γ-property₀ : (n k : ℕ) → k ≤ n → 𝟎 ＝⟦ k ⟧ (γ k)
    γ-property₀ n 0        l = ⋆
    γ-property₀ n (succ k) l =
     refl , γ-property₀ n k (≤-trans k (succ k) n (≤-succ k) l)

    γ-property₁ : (n k : ℕ) → k ≤ n → ₀ ≠ γ k n
    γ-property₁ n        0        l e = zero-is-not-one e
    γ-property₁ (succ n) (succ k) l e = γ-property₁ n k l e

    impossible : 𝟘
    impossible = γ-property₁ n k l (is-mod 𝟎 (γ k) (γ-property₀ n k l))

  III : (n k : ℕ)
      → k is-a-modulus-of-uc-of (ηᴷ n)
      → succ n ≤ k
  III n k is-mod = not-less-bigger-or-equal (succ n) k (II n k is-mod)

  UC : 𝓤₀ ̇
  UC = Σ f ꞉ (𝟚ᴺ → 𝟚) , is-uniformly-continuous f

  s : ℕ → UC
  s n = ηᴷ n , succ n , I n , III n

  r : UC → ℕ
  r (_ , m , _) = pred m

  rs : r ∘ s ∼ id
  rs n = refl

  ℕ-retract-of-UC : retract ℕ of UC
  ℕ-retract-of-UC = r , s , rs

  IV : UC ≃ (𝟚ᴺ → 𝟚)
  IV = pr₁ ,
       pr₁-is-equiv
        (𝟚ᴺ → 𝟚)
        is-uniformly-continuous
        (λ f → pointed-props-are-singletons
                (brouwer f)
                (being-uniformly-continuous-is-prop fe' f))

  ℕ-retract-of-𝟚ᴺ→𝟚 : retract ℕ of (𝟚ᴺ → 𝟚)
  ℕ-retract-of-𝟚ᴺ→𝟚 = retracts-compose (≃-gives-◁ IV) ℕ-retract-of-UC

  ℕ-is-𝟚-injective : 𝟚-injective ℕ 𝓤 𝓥
  ℕ-is-𝟚-injective = retract-of-𝟚-injective ℕ (𝟚ᴺ → 𝟚)
                      K-is-𝟚-injective
                      ℕ-retract-of-𝟚ᴺ→𝟚
\end{code}

Originally I tried to prove that UC is 𝟚-injective, to avoid the
Brouwerian assumption, but I didn't succeed, and I doubt this can be done.

TODO. In the topological topos, we in fact have that ℕ ≃ (𝟚ᴺ → 𝟚),
and, indeed, this can be proved from our Brouwerian assumption.

Question. Can ℕ be proved to be 𝟚-injective unconditionally? Or does
the 𝟚-injectivity of ℕ give a cotaboo such as the above Brouwerian assumption?

Notice also that a map X → ℕ can be seen as a partition of X by
countably many clopens. Hence asking ℕ to be 𝟚-injective amounts to
saying that from the ability to extend clopens along j : X → Y, we
should be able to extend countable clopen partitions to countable
clopen partitions along j.
