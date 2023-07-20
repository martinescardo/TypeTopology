Martin Escardo & Tom de Jong, June 2023.

Iterative sets.

We define the type of iterative sets as a subtype of that of multisets.

See the module Iterative.index for bibliographic references regarding
this file.

The previous module Iterative.Multisets doesn't make significant use
of univalence, and so we assumed it only for specific
constructions. But here the use of univalence is more pervasive, and
so we assume it globally.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Sets
        (𝓤 : Universe)
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Iterative.Multisets 𝓤
open import Iterative.W-Properties (𝓤 ̇ ) id
open import MLTT.W
open import Ordinals.Notions
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

An iterative set is a multiset whose subforests are all
embeddings. The effect of that is the the membership relation on
iterative sets is proposition-valued, rather than just type-valued, as
is the case for multisets.

\begin{code}

is-iterative-set : 𝕄 → 𝓤⁺ ̇
is-iterative-set (ssup X φ) = is-embedding φ
                            × ((x : X) → is-iterative-set (φ x))

\end{code}

It is convenient to name the projections for the sake of clarity:

\begin{code}

𝕄-forest-is-embedding : (M : 𝕄)
                      → is-iterative-set M
                      → is-embedding (𝕄-forest M)
𝕄-forest-is-embedding (ssup _ _) = pr₁

𝕄-subtrees-are-iterative : (M : 𝕄)
                         → is-iterative-set M
                         → (x : 𝕄-root M) → is-iterative-set (𝕄-forest M x)
𝕄-subtrees-are-iterative (ssup _ _) = pr₂

\end{code}

It is crucial that the notion of iterative set is property rather than
data:

\begin{code}

being-iset-is-prop : (M : 𝕄) → is-prop (is-iterative-set M)
being-iset-is-prop (ssup X φ) =
 ×-is-prop
  (being-embedding-is-prop fe φ)
  (Π-is-prop fe (λ x → being-iset-is-prop (φ x)))

\end{code}

The type of iterative sets as a subtype of that of iterative
multisets:

\begin{code}

𝕍 : 𝓤⁺ ̇
𝕍 = Σ M ꞉ 𝕄 , is-iterative-set M

𝕍-is-locally-small : is-locally-small 𝕍
𝕍-is-locally-small = subtype-is-locally-small
                      being-iset-is-prop
                      (𝕄-is-locally-small ua)
\end{code}

We again name the projections for the sake of clarity:

\begin{code}

underlying-mset : 𝕍 → 𝕄
underlying-mset = pr₁

isets-are-iterative : (A : 𝕍) → is-iterative-set (underlying-mset A)
isets-are-iterative = pr₂

\end{code}

Because the notion of iterative set is property, we get that 𝕍 is a
subtype of 𝕄.

\begin{code}

underlying-mset-is-embedding : is-embedding underlying-mset
underlying-mset-is-embedding = pr₁-is-embedding being-iset-is-prop

\end{code}

We define the root and the forest of an iterative set in terms of
those for multisets, but we need to add a "proof obligation" in the
case of the forest.

\begin{code}

𝕍-root : 𝕍 → 𝓤 ̇
𝕍-root A = 𝕄-root (underlying-mset A)

𝕍-forest : (A : 𝕍) → 𝕍-root A → 𝕍
𝕍-forest A x = 𝕄-forest (underlying-mset A) x ,
               𝕄-subtrees-are-iterative
                (underlying-mset A)
                (isets-are-iterative A)
                x

\end{code}

A criterion for equality in 𝕍:

\begin{code}

to-𝕍-＝ : {X Y : 𝓤 ̇ }
          {φ : X → 𝕄}
          {γ : Y → 𝕄}
        → (Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
        → (i : is-iterative-set (ssup X φ))
          (j : is-iterative-set (ssup Y γ))
        → (ssup X φ , i) ＝[ 𝕍 ] (ssup Y γ , j)
to-𝕍-＝ σ i j = to-subtype-＝ being-iset-is-prop (to-𝕄-＝ σ)

\end{code}

We define membership of iterative sets in terms of that for multisets:

\begin{code}

_∈_ : 𝕍 → 𝕍 → 𝓤⁺ ̇
A ∈ B = underlying-mset A ⁅ underlying-mset B

\end{code}

As is the case for iterative multisets, there is a resized down,
equivalent definition of membership, and we need the large and the
small ones:

\begin{code}

_∈⁻_ : 𝕍 → 𝕍 → 𝓤 ̇
A ∈⁻ B = underlying-mset A ⁅⁻ underlying-mset B

∈⁻≃∈ : (A B : 𝕍) → (A ∈ B) ≃ (A ∈⁻ B)
∈⁻≃∈ A B = ⁅⁻≃⁅ ua (underlying-mset A) (underlying-mset B)

\end{code}

As discussed above, the membership relation becomes a proposition
precisely because we required forests to be embeddings to define the
subtype of iterative sets.

\begin{code}

∈-is-prop-valued : (A B : 𝕍) → is-prop (A ∈ B)
∈-is-prop-valued (M , _) (ssup X φ , φ-emb , _) = φ-emb M

\end{code}

The following fact is trivial, but it is good to have a name for it
for the sake of clarity.

\begin{code}

𝕍-forest-is-∈ : (A : 𝕍) (x : 𝕍-root A) → 𝕍-forest A x ∈ A
𝕍-forest-is-∈ _ x = x , refl

\end{code}

The subset relation is defined in the usual way and is
proposition-valued:

\begin{code}

_⊆_ : 𝕍 → 𝕍 → 𝓤⁺ ̇
A ⊆ B = (C : 𝕍) → C ∈ A → C ∈ B

⊆-is-prop-valued : (A B : 𝕍) → is-prop (A ⊆ B)
⊆-is-prop-valued A B = Π₂-is-prop fe (λ C _ → ∈-is-prop-valued C B)

\end{code}

It is in the following that the univalence axiom is used for the first
time, to establish the extensionality axiom for iterative sets:

\begin{code}

∈-is-extensional : (A B : 𝕍) → A ⊆ B → B ⊆ A → A ＝ B
∈-is-extensional A@(ssup X φ , φ-emb , g) B@(ssup Y γ , γ-emb , h) u v = V
 where
  have-uv : (A ⊆ B) × (B ⊆ A)
  have-uv = u , v

  I : (x : X) → Σ y ꞉ Y , γ y ＝ φ x
  I x = u (φ x , g x) (x , refl)

  II : (y : Y) → Σ x ꞉ X , φ x ＝ γ y
  II y = v (γ y , h y) (y , refl)

  f : X → Y
  f x = pr₁ (I x)

  f⁻¹ : Y → X
  f⁻¹ y = pr₁ (II y)

  η : f⁻¹ ∘ f ∼ id
  η x = embeddings-are-lc φ φ-emb
         (φ (f⁻¹ (f x)) ＝⟨ pr₂ (II (f x)) ⟩
          γ (f x)       ＝⟨ pr₂ (I x) ⟩
          φ x           ∎)

  ε : f ∘ f⁻¹ ∼ id
  ε y = embeddings-are-lc γ γ-emb
         (γ (f (f⁻¹ y)) ＝⟨ pr₂ (I (f⁻¹ y)) ⟩
          φ (f⁻¹ y)     ＝⟨ pr₂ (II y) ⟩
          γ y           ∎)

  𝕗 : X ≃ Y
  𝕗 = qinveq f (f⁻¹ , η , ε)

  p : X ＝ Y
  p = eqtoid (ua 𝓤) X Y 𝕗

  III : Idtofun p ＝ f
  III = Idtofun-eqtoid (ua 𝓤) 𝕗

  IV : (x : X) → φ x ＝ γ (Idtofun p x)
  IV x =
   φ x             ＝⟨ (pr₂ (I x))⁻¹ ⟩
   γ (f x)         ＝⟨ ap (λ - → γ (- x)) (III ⁻¹) ⟩
   γ (Idtofun p x) ∎

  V : A ＝ B
  V = to-𝕍-＝ (p , dfunext fe IV) (φ-emb , g) (γ-emb , h)

\end{code}

It follows that 𝕍 is 0-type, or set, in the sense of the HoTT
book. But notice that we now have two notions of set in this
discussion: the "material" (iterative set) one and the "structural"
one (0-type or set). The reader should keep this distinction in mind
when reading the comments and code below.

\begin{code}

𝕍-is-set : is-set 𝕍
𝕍-is-set = extensionally-ordered-types-are-sets _∈_ fe'
             ∈-is-prop-valued
             ∈-is-extensional

\end{code}

Here is a second, more direct, proof.

The following says that ssup φ ＝ M is a proposition for every M : 𝕄
if φ is an embedding.

\begin{code}

𝕄-ssup-is-h-isolated : (X : 𝓤 ̇ ) (φ : X → 𝕄)
                     → is-embedding φ
                     → is-h-isolated (ssup X φ)
𝕄-ssup-is-h-isolated X φ φ-emb {M} = III
 where
  I = (ssup X φ ＝ M)                        ≃⟨ ＝-flip ⟩
      (M ＝ ssup X φ)                        ≃⟨ 𝕄-＝' M (ssup X φ) ⟩
      fiber ((φ ∘_) ∘ Idtofun) (𝕄-forest M)  ■

  II : is-embedding ((φ ∘_) ∘ Idtofun)
  II = ∘-is-embedding
        (Idtofun-is-embedding (ua 𝓤) fe)
        (precomp-is-embedding fe' φ φ-emb)

  III : is-prop (ssup X φ ＝ M)
  III = equiv-to-prop I (II (𝕄-forest M))

\end{code}

And a particular case of this is that if M is an iterative set then
M ＝ N is a proposition for every *multiset* N.

\begin{code}

isets-are-h-isolated : (M : 𝕄)
                     → is-iterative-set M
                     → is-h-isolated M
isets-are-h-isolated (ssup X φ) (φ-emb , _) = 𝕄-ssup-is-h-isolated X φ φ-emb

\end{code}

Because a subtype of any type whatsoever consisting of h-isolated
elements is a 0-type, we get a second proof that the type of iterative
sets is a 0-type.

\begin{code}

𝕍-is-set' : is-set 𝕍
𝕍-is-set' {M , M-is-is-set} =
 equiv-to-prop
  (≃-sym (to-subtype-＝-≃ being-iset-is-prop))
  (isets-are-h-isolated M M-is-is-set)

\end{code}

By definition, an iterative multiset is an iterative set if its
forests are all embeddings. The 𝕍-forests are also embeddings:

\begin{code}

𝕍-forest-is-embedding : (A : 𝕍) → is-embedding (𝕍-forest A)
𝕍-forest-is-embedding A@(ssup X φ , φ-emb , is) =
 pair-fun-is-embedding-special φ is φ-emb being-iset-is-prop

\end{code}

We construct elements of 𝕄 using the constructor ssup. We now
introduce a corresponding constructor 𝕍-ssup to construct elements of 𝕍.

\begin{code}

𝕍-ssup : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) → is-embedding ϕ → 𝕍
𝕍-ssup X ϕ ϕ-emb = ssup X φ , φ-emb , φ-iset
 where
  φ : X → 𝕄
  φ = underlying-mset ∘ ϕ

  φ-iset : (x : X) → is-iterative-set (φ x)
  φ-iset = isets-are-iterative ∘ ϕ

  φ-emb : is-embedding φ
  φ-emb = ∘-is-embedding ϕ-emb underlying-mset-is-embedding

\end{code}

It behaves as expected with respect to the corresponding destructors:

\begin{code}

𝕍-ssup-root : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
            → 𝕍-root (𝕍-ssup X ϕ e) ＝ X
𝕍-ssup-root X ϕ e = refl

𝕍-ssup-forest : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
              → 𝕍-forest (𝕍-ssup X ϕ e) ＝ ϕ
𝕍-ssup-forest X ϕ e = refl

\end{code}

Notice that the identifications are definitional.

We have the following η rules for 𝕍, where the first is more general
and the second is more natural. In both cases the identifications are
not definitional.

\begin{code}

𝕍-η' : (A : 𝕍) (e : is-embedding (𝕍-forest A))
     → 𝕍-ssup (𝕍-root A) (𝕍-forest A) e ＝ A
𝕍-η' (ssup _ _ , _) _ = to-subtype-＝ being-iset-is-prop refl

𝕍-η : (A : 𝕍) → 𝕍-ssup (𝕍-root A) (𝕍-forest A) (𝕍-forest-is-embedding A) ＝ A
𝕍-η A = 𝕍-η' A (𝕍-forest-is-embedding A)

\end{code}

Here are two characterizations of the membership relation:

\begin{code}

∈-behaviour : (A : 𝕍) (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
            → A ∈ 𝕍-ssup X ϕ e ≃ (Σ x ꞉ X , ϕ x ＝ A)
∈-behaviour A X ϕ e =
 (A ∈ 𝕍-ssup X ϕ e)                                     ≃⟨ ≃-refl _ ⟩
 (Σ x ꞉ X , underlying-mset (ϕ x) ＝ underlying-mset A) ≃⟨ Σ-cong I ⟩
 (Σ x ꞉ X , ϕ x ＝ A)                                   ■
  where
   I : (x : X) → (underlying-mset (ϕ x) ＝ underlying-mset A) ≃ (ϕ x ＝ A)
   I x = embedding-criterion-converse
          underlying-mset
          underlying-mset-is-embedding
          (ϕ x)
          A

∈-behaviour' : (A B : 𝕍) → A ∈ B ≃ (Σ x ꞉ 𝕍-root B , 𝕍-forest B x ＝ A)
∈-behaviour' A B =
 transport
  (λ - → A ∈ - ≃ (Σ x ꞉ 𝕍-root - , 𝕍-forest - x ＝ A))
  (𝕍-η B)
  (∈-behaviour A (𝕍-root B) (𝕍-forest B) (𝕍-forest-is-embedding B))

\end{code}

It also follows from the facts that 𝕍 is a set and that 𝕍-forest is an
embedding that the root of any iterative set is a 0-type:

\begin{code}

𝕍-root-is-set : (A : 𝕍) → is-set (𝕍-root A)
𝕍-root-is-set A = subtypes-of-sets-are-sets
                   (𝕍-forest A)
                   (𝕍-forest-is-embedding A)
                   𝕍-is-set
\end{code}

It would be nice if we could define 𝕍 as follows:

 data 𝕍 : 𝓤⁺ ̇ where
  𝕍-ssup : (X : 𝓤 ̇ ) (φ : X → 𝕍) → is-embedding φ → 𝕍

However, this is not a strictly positive definition, for the criterion
of strict positivity used by Agda, and so it is not accepted.

Nevertheless, all iterative sets *are* generated by the "constructor"
𝕍-ssup, in the following sense, so that we can view 𝕍 as really
defined by the above data declaration.

\begin{code}

𝕍-induction : (P : 𝕍 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
                  → ((x : X) → P (ϕ x))
                  → P (𝕍-ssup X ϕ e))
            → (A : 𝕍) → P A
𝕍-induction P f (M , i) = h M i
 where
  h : (M : 𝕄) (i : is-iterative-set M) → P (M , i)
  h M@(ssup X φ) i@(φ-emb , φ-iter) = II
   where
    A : 𝕍
    A = (M , i)

    IH : (x : X) → P (𝕍-forest A x)
    IH x = h (φ x) (φ-iter x)

    I : P (𝕍-ssup X (𝕍-forest A) (𝕍-forest-is-embedding A))
    I = f X (𝕍-forest A) (𝕍-forest-is-embedding A) IH

    II : P A
    II = transport P (𝕍-η A) I

\end{code}

So we are essentially working with (an encoding) of the above
non-strictly positive data type.

The usual induction principle for iterative sets follows directly from
the above form of induction.

\begin{code}

∈-induction : (P : 𝕍 → 𝓥 ̇ )
            → ((A : 𝕍) → ((B : 𝕍) → B ∈ A → P B) → P A)
            → (A : 𝕍) → P A
∈-induction P g = 𝕍-induction P f
 where
  f : (X : 𝓤 ̇) (ϕ : X → 𝕍) (e : is-embedding ϕ)
    → ((x : X) → P (ϕ x))
    → P (𝕍-ssup X ϕ e)
  f X ϕ e u = g A s
   where
    A : 𝕍
    A = 𝕍-ssup X ϕ e

    s : (B : 𝕍) → B ∈ A → P B
    s B@(_ , j) (x , refl) = II
     where
      I : P (ϕ x)
      I = u x

      II : P (underlying-mset (ϕ x) , j)
      II = transport P (to-subtype-＝ being-iset-is-prop refl) I

\end{code}

And then is follows immediately that the membership relation is
accessible:

\begin{code}

∈-is-accessible : (A : 𝕍) → is-accessible _∈_ A
∈-is-accessible = ∈-induction (is-accessible _∈_) (λ _ → acc)

\end{code}
