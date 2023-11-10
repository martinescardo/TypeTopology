Martin Escardo & Tom de Jong, June 2023.

Iterative sets.

We define the type of iterative sets as a subtype of that of multisets.

  * H. R. Gylterud, "From multisets to sets in homotopy type theory".
    The Journal of Symbolic Logic, vol. 83, no. 3, pp. 1132–1146,
    2018. https://doi.org/10.1017/jsl.2017.84

See the module Iterative.index for further bibliographic references.

The previous module Iterative.Multisets doesn't make significant use
of univalence, and so we assumed it only for specific
constructions. But here the use of univalence is more pervasive, and
so we assume it globally.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Sets
        (ua : Univalence)
        (𝓤 : Universe)
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
open import Ordinals.Notions
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Retracts
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import W.Type
open import W.Properties (𝓤 ̇ ) id

\end{code}

An iterative set is a multiset whose subforests are all
embeddings. The effect of that is that the membership relation on
iterative sets is proposition-valued, rather than just type-valued, as
is the case for general multisets.

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

Because the notion of iterative set is property, we get that 𝕍 is
indeed a subtype of 𝕄.

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
equivalent definition of membership.

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

𝕍-forest-∈ : (A : 𝕍) (x : 𝕍-root A) → 𝕍-forest A x ∈ A
𝕍-forest-∈ A x = 𝕄-forest-⁅ (underlying-mset A) x

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
∈-is-extensional A@(M@(ssup X φ) , φ-emb , g)
                 B@(N@(ssup Y γ) , γ-emb , h) u v = V
 where
  have-uv : (A ⊆ B) × (B ⊆ A)
  have-uv = u , v

  I : (x : X) → Σ y ꞉ Y , γ y ＝ φ x
  I x = u (φ x , g x) (𝕄-forest-⁅ M x)

  II : (y : Y) → Σ x ꞉ X , φ x ＝ γ y
  II y = v (γ y , h y) (𝕄-forest-⁅ N y)

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

  IV = λ x →
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
for the comments and code below.

The following uses the fact that any type with an extensional order is
automatically a set.

\begin{code}

𝕍-is-set : is-set 𝕍
𝕍-is-set = extensionally-ordered-types-are-sets _∈_ fe'
            ∈-is-prop-valued
            ∈-is-extensional

\end{code}

Here is a second, more direct, proof of this fact.

The following says that ssup φ ＝ M is a proposition for every M : 𝕄
if φ is an embedding.

The following doesn't seem to have been observed before in the
literature.

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
        (postcomp-is-embedding fe' φ φ-emb)

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
𝕄-forests are all embeddings. The 𝕍-forests are also embeddings:

\begin{code}

𝕍-forest-is-embedding : (A : 𝕍) → is-embedding (𝕍-forest A)
𝕍-forest-is-embedding A@(ssup X φ , φ-emb , φ-iter) =
 pair-fun-is-embedding-special φ φ-iter φ-emb being-iset-is-prop

\end{code}

We construct elements of 𝕄 using the constructor ssup. We now
introduce a corresponding constructor 𝕍-ssup to construct elements of
the type 𝕍.

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

private
 ∈-remark : (A B : 𝕍) → A ∈ B ≃ fiber (𝕍-forest B) A
 ∈-remark = ∈-behaviour'

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

It would be nice if we could define 𝕍 inductively as follows:

 data 𝕍 : 𝓤⁺ ̇ where
  𝕍-ssup : (X : 𝓤 ̇ ) (φ : X → 𝕍) → is-embedding φ → 𝕍

However, this is not a strictly positive definition, for the criterion
of strict positivity adopted by Agda, and so it is not accepted.

Nevertheless, all iterative sets *are* generated by the "constructor"
𝕍-ssup, in the following sense, so that we can view 𝕍 as really
inductively defined by the above data declaration.

The following result, implementing the above idea, seems to be new.

\begin{code}

𝕍-Induction'
 : (P : 𝕍 → 𝓥 ̇ )
   (f : (A : 𝕍) → ((x : 𝕍-root A) → P (𝕍-forest A x)) → P A)
 → Σ h ꞉ ((A : 𝕍) → P A)
       , ((A : 𝕍) → h A ＝ f A (λ x → h (𝕍-forest A x)))
𝕍-Induction' P f = (λ (M , i) → H M i) , p
 where
  H : (M : 𝕄) (i : is-iterative-set M) → P (M , i)
  H M@(ssup X φ) i@(_ , φ-iter) = f (M , i) (λ x → H (φ x) (φ-iter x))

  p : (A : 𝕍) → _ ＝ _
  p (M@(ssup X φ) , i@(_ , φ-iter)) = refl

𝕍-Induction
 : (P : 𝕍 → 𝓥 ̇ )
 → (f : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
      → ((x : X) → P (ϕ x))
      → P (𝕍-ssup X ϕ e))
 → Σ h ꞉ ((A : 𝕍) → P A)
       , ((X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
       → h (𝕍-ssup X ϕ e) ＝ f X ϕ e (λ x → h (ϕ x)))
𝕍-Induction {𝓥} P f = h , IV
 where
  f' : (A : 𝕍) → ((x : 𝕍-root A) → P (𝕍-forest A x)) → P A
  f' A@(M@(ssup X φ) , i@(φ-emb , φ-iter)) g = II
   where
    I : P (𝕍-ssup X (𝕍-forest A) (𝕍-forest-is-embedding A))
    I = f X (𝕍-forest A) (𝕍-forest-is-embedding A) g

    II : P A
    II = transport P (𝕍-η A) I

  h : (A : 𝕍) → P A
  h = pr₁ (𝕍-Induction' P f')

  III : (A : 𝕍) → h A ＝ f' A (λ x → h (𝕍-forest A x))
  III = pr₂ (𝕍-Induction' P f')

  IV : (X : 𝓤 ̇) (ϕ : X → 𝕍) (e : is-embedding ϕ)
     → h (𝕍-ssup X ϕ e) ＝ f X ϕ e (λ x → h (ϕ x))
  IV X ϕ e =
   h A                                                               ＝⟨ III A ⟩
   f' A (λ x → h (ϕ x))                                              ＝⟨ refl ⟩
   t P                (𝕍-η A)             (f X ϕ e' (λ x → h (ϕ x))) ＝⟨ i ⟩
   t P                (ap (𝕍-ssup X ϕ) p) (f X ϕ e' (λ x → h (ϕ x))) ＝⟨ ii ⟩
   t (P ∘ 𝕍-ssup X ϕ) p                   (f X ϕ e' (λ x → h (ϕ x))) ＝⟨ iii ⟩
   f X ϕ e (λ x → h (ϕ x))                                           ∎
    where
     t = transport
     A  = 𝕍-ssup X ϕ e
     e' = 𝕍-forest-is-embedding A

     p : e' ＝ e
     p = being-embedding-is-prop fe ϕ e' e

     q : 𝕍-η A ＝ ap (𝕍-ssup X ϕ) p
     q = 𝕍-is-set _ _

     i   = ap (λ - → t P - (f X ϕ e' (λ x → h (ϕ x)))) q
     ii  = (transport-ap P (𝕍-ssup X ϕ) p)⁻¹
     iii = apd (λ - → f X ϕ - (λ x → h (ϕ x))) p

𝕍-induction : (P : 𝕍 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
                  → ((x : X) → P (ϕ x))
                  → P (𝕍-ssup X ϕ e))
            → (A : 𝕍) → P A
𝕍-induction P f = pr₁ (𝕍-Induction P f)

𝕍-induction-behaviour
 : (P : 𝕍 → 𝓥 ̇ )
 → (f : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
      → ((x : X) → P (ϕ x))
      → P (𝕍-ssup X ϕ e))
 → (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
 → 𝕍-induction P f (𝕍-ssup X ϕ e) ＝ f X ϕ e (λ x → 𝕍-induction P f (ϕ x))
𝕍-induction-behaviour P f = pr₂ (𝕍-Induction P f)

𝕍-recursion : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕍)
                  → is-embedding ϕ
                  → (X → P)
                  → P)
            → 𝕍 → P
𝕍-recursion P = 𝕍-induction (λ _ → P)

𝕍-recursion-behaviour
 : (P : 𝓥 ̇ )
 → (f : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
      → (X → P)
      → P)
 → (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
 → 𝕍-recursion P f (𝕍-ssup X ϕ e) ＝ f X ϕ e (λ x → 𝕍-recursion P f (ϕ x))
𝕍-recursion-behaviour P = 𝕍-induction-behaviour (λ _ → P)

𝕍-iteration : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → P) → P)
            → 𝕍 → P
𝕍-iteration P f = 𝕍-recursion P (λ X ϕ e → f X)

𝕍-iteration-behaviour
 : (P : 𝓥 ̇ )
 → (f : (X : 𝓤 ̇ ) → (X → P) → P)
 → (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
 → 𝕍-iteration P f (𝕍-ssup X ϕ e) ＝ f X (λ x → 𝕍-iteration P f (ϕ x))
𝕍-iteration-behaviour P f = 𝕍-recursion-behaviour P (λ X ϕ e → f X)

\end{code}

So we are essentially working with (an encoding) of the above
non-strictly positive data type.

The usual induction principle for iterative sets follows directly from
the above form of induction. This consequence is already in Gylterud [4].

\begin{code}

∈-induction : (P : 𝕍 → 𝓥 ̇ )
            → ((A : 𝕍) → ((B : 𝕍) → B ∈ A → P B) → P A)
            → (A : 𝕍) → P A
∈-induction P IH = 𝕍-induction P f
 where
  f : (X : 𝓤 ̇) (ϕ : X → 𝕍) (e : is-embedding ϕ)
    → ((x : X) → P (ϕ x))
    → P (𝕍-ssup X ϕ e)
  f X ϕ e IH' = IH A s
   where
    A : 𝕍
    A = 𝕍-ssup X ϕ e

    s : (B : 𝕍) → B ∈ A → P B
    s B@(.(underlying-mset (ϕ x)) , j) (x , refl) = II
     where
      I : P (ϕ x)
      I = IH' x

      II : P (underlying-mset (ϕ x) , j)
      II = transport P (to-subtype-＝ being-iset-is-prop refl) I

\end{code}

And then it follows immediately that the membership relation is
accessible:

\begin{code}

∈-is-accessible : (A : 𝕍) → is-accessible _∈_ A
∈-is-accessible = ∈-induction (is-accessible _∈_) (λ _ → acc)

\end{code}

Singleton sets can be constructed as follows.

\begin{code}

❴_❵ : (A : 𝕍) → 𝕍
❴ A ❵ = 𝕍-ssup 𝟙 (λ _ → A) (global-point-is-embedding (λ _ → A) 𝕍-is-set)

❴❵-behaviour : (A : 𝕍) (B : 𝕍) → B ∈ ❴ A ❵ ≃ (B ＝ A)
❴❵-behaviour A B = B ∈ ❴ A ❵    ≃⟨ ∈-behaviour' B ❴ A ❵ ⟩
                   𝟙 × (A ＝ B) ≃⟨ 𝟙-lneutral ⟩
                   (A ＝ B)     ≃⟨ ＝-flip ⟩
                   (B ＝ A)     ■

\end{code}

Given a family of iterative sets indexed by a small type, we construct
its union as in [4].

We make use of propositional truncations (to define the image of a
map) and of set replacement (which follows from having set quotients).

\begin{code}

open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

 module unions-of-iterative-sets (sr : Set-Replacement pt) where

  private
   module union-construction
          {I : 𝓤 ̇  }
          (𝓐 : I → 𝕍)
         where

    im : 𝓤⁺ ̇
    im = image 𝓐
    im-is-small : image 𝓐 is 𝓤 small
    im-is-small = sr 𝓐 (I , ≃-refl I) 𝕍-is-locally-small 𝕍-is-set
    im⁻ : 𝓤 ̇
    im⁻ = resized im im-is-small
    im⁻-≃-im : im⁻ ≃ im
    im⁻-≃-im = resizing-condition im-is-small
    π : im → 𝕍
    π = restriction 𝓐
    π⁻ : im⁻ → 𝕍
    π⁻ = π ∘ ⌜ im⁻-≃-im ⌝
    π-is-embedding : is-embedding π
    π-is-embedding = restrictions-are-embeddings 𝓐
    π⁻-is-embedding : is-embedding π⁻
    π⁻-is-embedding = ∘-is-embedding
                       (equivs-are-embeddings
                         ⌜ im⁻-≃-im ⌝
                         (⌜⌝-is-equiv im⁻-≃-im))
                       π-is-embedding

  ⋃ : {I : 𝓤 ̇  } (𝓐 : I → 𝕍) → 𝕍
  ⋃ {I} 𝓐 = 𝕍-ssup im⁻ π⁻ π⁻-is-embedding
   where
    open union-construction 𝓐

  ⋃-behaviour : {I : 𝓤 ̇  } (𝓐 : I → 𝕍) (B : 𝕍)
              → B ∈ ⋃ 𝓐 ≃ (∃ i ꞉ I , B ＝ 𝓐 i)
  ⋃-behaviour {I} 𝓐 B =
   B ∈ ⋃ 𝓐                                    ≃⟨ ∈-behaviour' B (⋃ 𝓐) ⟩
   (Σ j ꞉ im⁻ , π⁻ j ＝ B)                    ≃⟨ e₁ ⟩
   (Σ j ꞉ im , π j ＝ B)                      ≃⟨ Σ-assoc ⟩
   (Σ C ꞉ 𝕍 , C ∈image 𝓐 × (C ＝ B))          ≃⟨ Σ-cong (λ C → ×-comm) ⟩
   (Σ C ꞉ 𝕍 , (C ＝ B) × (C ∈image 𝓐))        ≃⟨ ≃-sym Σ-assoc ⟩
   (Σ s ꞉ singleton-type' B , pr₁ s ∈image 𝓐) ≃⟨ ≃-sym e₂ ⟩
   𝟙 {𝓤} × B ∈image 𝓐                         ≃⟨ 𝟙-lneutral ⟩
   (∃ i ꞉ I , 𝓐 i ＝ B)                       ≃⟨ ∃-cong pt (λ i → ＝-flip) ⟩
   (∃ i ꞉ I , B ＝ 𝓐 i)                       ■
    where
     open union-construction 𝓐
     e₁ = Σ-change-of-variable-≃ _ im⁻-≃-im
     e₂ = Σ-change-of-variable-≃ _
           (singleton-≃-𝟙' (singleton-types'-are-singletons B))

\end{code}

Any iterative set is the union of its 𝕍-forest.

\begin{code}

  ⋃-η : (A : 𝕍) → ⋃ (𝕍-forest A) ＝ A
  ⋃-η A = ∈-is-extensional (⋃ (𝕍-forest A)) A i j
   where
    i : ⋃ (𝕍-forest A) ⊆ A
    i B m = ∥∥-rec (∈-is-prop-valued B A) f (⌜ ⋃-behaviour (𝕍-forest A) B ⌝ m)
     where
      f : (Σ a ꞉ 𝕍-root A , B ＝ 𝕍-forest A a) → B ∈ A
      f (a , refl) = 𝕍-forest-∈ A a
    j : A ⊆ ⋃ (𝕍-forest A)
    j B m = ⌜ ⋃-behaviour (𝕍-forest A) B ⌝⁻¹ ∣ a , e ∣
     where
      abstract
       m' : Σ a ꞉ 𝕍-root A , 𝕍-forest A a ＝ B
       m' = ⌜ ∈-behaviour' B A ⌝ m
       a : 𝕍-root A
       a = pr₁ m'
       e : B ＝ 𝕍-forest A a
       e = (pr₂ m') ⁻¹

\end{code}

Unions allow us to construct a retraction of the inclusion 𝕍 ↪ 𝕄, and
this seems to be a new result.

\begin{code}

  𝕄-to-𝕍 : 𝕄 → 𝕍
  𝕄-to-𝕍 (ssup X φ) = ⋃ (𝕄-to-𝕍 ∘ φ)

  𝕄-to-𝕍-is-retraction-of-inclusion : 𝕄-to-𝕍 ∘ underlying-mset ＝ id
  𝕄-to-𝕍-is-retraction-of-inclusion = dfunext fe (∈-induction _ f)
   where
    f : (A : 𝕍) → ((B : 𝕍) → B ∈ A → (𝕄-to-𝕍 ∘ underlying-mset) B ＝ B)
      → (𝕄-to-𝕍 ∘ underlying-mset) A ＝ A
    f A IH = 𝕄-to-𝕍 Aₘ                                 ＝⟨ I ⟩
             𝕄-to-𝕍 (ssup (𝕍-root A) (𝕄-forest Aₘ))    ＝⟨ refl ⟩
             ⋃ (𝕄-to-𝕍 ∘ 𝕄-forest Aₘ)                  ＝⟨ refl ⟩
             ⋃ (𝕄-to-𝕍 ∘ underlying-mset ∘ 𝕍-forest A) ＝⟨ II ⟩
             ⋃ (𝕍-forest A)                            ＝⟨ ⋃-η A ⟩
             A                                         ∎
              where
               Aₘ : 𝕄
               Aₘ = underlying-mset A
               I  = ap (𝕄-to-𝕍 ∘ underlying-mset) (𝕍-η A ⁻¹)
               II = ap ⋃ (dfunext fe (λ a → IH (𝕍-forest A a) (𝕍-forest-∈ A a)))

  𝕍-is-retract-of-𝕄 : retract 𝕍 of 𝕄
  𝕍-is-retract-of-𝕄 = 𝕄-to-𝕍 ,
                      underlying-mset ,
                      happly 𝕄-to-𝕍-is-retraction-of-inclusion

\end{code}
