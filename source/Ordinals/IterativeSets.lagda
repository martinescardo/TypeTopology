Martin Escardo & Tom de Jong, June 2023.

Iterative multisets, iterative sets, and iterative ordinals.

The following is based on

  * Peter Aczel. "The Type Theoretic Interpretation of Constructive
    Set Theory". Studies in Logic and the Foundations of Mathematics,
    Volume 96, 1978, Pages 55-66.
    https://doi.org/10.1016/S0049-237X(08)71989-X

  * Gerald, Leversha. "Formal Systems for Constructive Mathematics".
    PhD Thesis, 1976, The University of Manchester (United
    Kingdom). Department of Pure and Applied Mathematics.
    https://www.librarysearch.manchester.ac.uk/permalink/44MAN_INST/1r887gn/alma992983521804701631

  * Håkon Gylterud. "Multisets in type theory".  Mathematical
    Proceedings of the Cambridge Philosophical Society, Volume 169,
    Issue 1, 2020, pp. 1-18. https://doi.org/10.1017/S0305004119000045

  * H. R. Gylterud, "From multisets to sets in homotopy type theory".
    The Journal of Symbolic Logic, vol. 83, no. 3, pp. 1132–1146,
    2018. https://doi.org/10.1017/jsl.2017.84

  * Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and
    Chuangjie Xu. "Set-Theoretic and Type-Theoretic Ordinals
    Coincide". To appear at LICS 2023, June 2023.

    https://arxiv.org/abs/2301.10696

TODO. Add lots of explanation.

In short, some of the development of "Set-Theoretic and Type-Theoretic Ordinals
Coincide" is carried out but using Gylterud's construction of the cumulative
hierarchy 𝕍 as iterative sets, instead of (axiomatically) working with the
higher inductive presentation. The type 𝕆 of hereditarily transitive sets is the
type of iterative ordinals and corresponds to 𝕍ᵒʳᵈ in the original development
OrdinalsCumulativeHierarchy.lagda.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.Univalence

module Ordinals.IterativeSets
        (𝓤 : Universe)
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

𝓤⁺ = 𝓤 ⁺

open PropositionalTruncation pt

open import UF.FunExt
open import UF.UA-FunExt

fe : Fun-Ext
fe = Univalence-gives-Fun-Ext ua

fe' : FunExt
fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Games.TypeTrees using ()
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropIndexedPiSigma
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import NotionsOfDecidability.Decidable
open import UF.Embeddings
open import UF.PairFun
open import Ordinals.Notions

\end{code}

The type of iterative multisets:

\begin{code}

data 𝕄 : 𝓤⁺ ̇ where
 sup : (X : 𝓤 ̇ ) (φ : X → 𝕄) → 𝕄

𝕄-root : 𝕄 → 𝓤 ̇
𝕄-root (sup X φ) = X

𝕄-forest : (M : 𝕄) → 𝕄-root M → 𝕄
𝕄-forest (sup X φ) = φ


to-𝕄-＝ : {X Y : 𝓤 ̇ }
          {φ : X → 𝕄}
          {γ : Y → 𝕄}
        → Σ p ꞉ X ＝ Y , ((x : X) → φ x ＝ γ (Idtofun p x))
        → (sup X φ) ＝ (sup Y γ)
to-𝕄-＝ {X} (refl , f) = ap (sup X) (dfunext fe f)

\end{code}

The type of iterative sets:

\begin{code}

is-iterative-set : 𝕄 → 𝓤⁺ ̇
is-iterative-set (sup X φ) = is-embedding φ
                           × ((x : X) → is-iterative-set (φ x))

being-iterative-set-is-prop : (A : 𝕄)
                            → is-prop (is-iterative-set A)
being-iterative-set-is-prop (sup X φ) =
 ×-is-prop
  (being-embedding-is-prop fe φ)
  (Π-is-prop fe (λ x → being-iterative-set-is-prop (φ x)))

𝕍 : 𝓤⁺ ̇
𝕍 = Σ M ꞉ 𝕄 , is-iterative-set M

to-𝕍-＝ : {X Y : 𝓤 ̇ }
          {φ : X → 𝕄}
          {γ : Y → 𝕄}
        → Σ p ꞉ X ＝ Y , ((x : X) → φ x ＝ γ (Idtofun p x))
        → (i : is-iterative-set (sup X φ))
          (j : is-iterative-set (sup Y γ))
        → (sup X φ , i) ＝[ 𝕍 ] (sup Y γ , j)
to-𝕍-＝ {X} σ i j = to-subtype-＝ being-iterative-set-is-prop (to-𝕄-＝ σ)

_∈_ : 𝕍 → 𝕍 → 𝓤⁺ ̇
(M , _) ∈ (sup X φ , _) = fiber φ M

∈-is-prop-valued : (A B : 𝕍) → is-prop (A ∈ B)
∈-is-prop-valued (M , _) (sup Y γ , γ-emb , _) = γ-emb M

_⊆_ : 𝕍 → 𝕍 → 𝓤⁺ ̇
A ⊆ B = (C : 𝕍) → C ∈ A → C ∈ B

⊆-is-prop-valued : (A B : 𝕍) → is-prop (A ⊆ B)
⊆-is-prop-valued A B = Π₂-is-prop fe (λ C _ → ∈-is-prop-valued C B)

∈-is-extensional : (A B : 𝕍) → A ⊆ B → B ⊆ A → A ＝ B
∈-is-extensional A@(sup X φ , φ-emb , g) B@(sup Y γ , γ-emb , h) u v = V
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

  V' : (sup X φ , φ-emb , g) ＝ (sup Y γ , γ-emb , h)
  V' = to-𝕍-＝ (p , IV) (φ-emb , g) (γ-emb , h)

  V : A ＝ B
  V = V'

𝕍-is-set : is-set 𝕍
𝕍-is-set = extensionally-ordered-types-are-sets _∈_ fe'
            ∈-is-prop-valued
            ∈-is-extensional

𝕍-root : 𝕍 → 𝓤 ̇
𝕍-root (sup X φ , _) = X

𝕍-forest : (A : 𝕍) → 𝕍-root A → 𝕍
𝕍-forest (sup X φ , _ , i) x = φ x , i x

𝕍-sup : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) → is-embedding ϕ → 𝕍
𝕍-sup X ϕ ϕ-emb = sup X φ , I , φi
 where
  φ : X → 𝕄
  φ = pr₁ ∘ ϕ

  φi : (x : X) → is-iterative-set (φ x)
  φi = pr₂ ∘ ϕ

  I : is-embedding (pr₁ ∘ ϕ)
  I = ∘-is-embedding ϕ-emb (pr₁-is-embedding being-iterative-set-is-prop)

∈-behaviour : (A : 𝕍) (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
            → A ∈ 𝕍-sup X ϕ e ≃ (Σ x ꞉ X , ϕ x ＝ A)
∈-behaviour A X ϕ e =
 (A ∈ 𝕍-sup X ϕ e)              ≃⟨ ≃-refl _ ⟩
 (Σ x ꞉ X , pr₁ (ϕ x) ＝ pr₁ A) ≃⟨ Σ-cong I ⟩
 (Σ x ꞉ X , ϕ x ＝ A)           ■
  where
   I : (x : X) → (pr₁ (ϕ x) ＝ pr₁ A) ≃ (ϕ x ＝ A)
   I x = embedding-criterion-converse
          pr₁
          (pr₁-is-embedding being-iterative-set-is-prop)
          (ϕ x)
          A

𝕍-sup-root : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
           → 𝕍-root (𝕍-sup X ϕ e) ＝ X
𝕍-sup-root X ϕ e = refl

𝕍-sup-forest : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
             → 𝕍-forest (𝕍-sup X ϕ e) ＝ ϕ
𝕍-sup-forest X ϕ e = refl

𝕍-forest-is-embedding : (A : 𝕍) → is-embedding (𝕍-forest A)
𝕍-forest-is-embedding (sup X φ , φ-emb , i) B@(M , j) = III
 where
  I = (Σ x ꞉ X , (φ x , i x) ＝ B)                                         ≃⟨ a ⟩
      (Σ x ꞉ X , Σ p ꞉ φ x ＝ M , transport is-iterative-set p (i x) ＝ j) ≃⟨ b ⟩
      (Σ (x , p) ꞉ fiber φ M , transport is-iterative-set p (i x) ＝ j)    ■
       where
        a = Σ-cong (λ x → Σ-＝-≃)
        b = ≃-sym Σ-assoc

  II : is-prop (Σ (x , p) ꞉ fiber φ M , transport is-iterative-set p (i x) ＝ j)
  II = Σ-is-prop (φ-emb M) (λ _ → props-are-sets (being-iterative-set-is-prop M))

  III : is-prop (Σ x ꞉ X , (φ x , i x) ＝ B)
  III = equiv-to-prop I II

𝕍-root-is-set : (A : 𝕍) → is-set (𝕍-root A)
𝕍-root-is-set A = subtypes-of-sets-are-sets
                   (𝕍-forest A)
                   (𝕍-forest-is-embedding A)
                   𝕍-is-set

𝕍-η : (A : 𝕍) → 𝕍-sup (𝕍-root A) (𝕍-forest A) (𝕍-forest-is-embedding A) ＝ A
𝕍-η (sup X φ , e , i) = to-subtype-＝ being-iterative-set-is-prop refl

𝕍-induction : (P : 𝕍 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
                  → ((x : X) → P (ϕ x))
                  → P (𝕍-sup X ϕ e))
            → (A : 𝕍) → P A
𝕍-induction P f (M , i) = h M i
 where
  h : (M : 𝕄) (i : is-iterative-set M) → P (M , i)
  h M@(sup X φ) i@(φ-emb , φ-iter) = II
   where
    A : 𝕍
    A = (M , i)

    IH : (x : X) → P (𝕍-forest A x)
    IH x = h (φ x) (φ-iter x)

    I : P (𝕍-sup X (𝕍-forest A) (𝕍-forest-is-embedding A))
    I = f X (𝕍-forest A) (𝕍-forest-is-embedding A) IH

    II : P A
    II = transport P (𝕍-η A) I

∈-induction : (P : 𝕍 → 𝓥 ̇ )
            → ((A : 𝕍) → ((B : 𝕍) → B ∈ A → P B) → P A)
            → (A : 𝕍) → P A
∈-induction P g = 𝕍-induction P f
 where
  f : (X : 𝓤 ̇) (ϕ : X → 𝕍) (e : is-embedding ϕ)
    → ((x : X) → P (ϕ x))
    → P (𝕍-sup X ϕ e)
  f X ϕ e u = g A s
   where
    A : 𝕍
    A = 𝕍-sup X ϕ e

    s : (B : 𝕍) → B ∈ A → P B
    s (.(pr₁ (ϕ x)) , j) (x , refl) = II
     where
      I : P (ϕ x)
      I = u x

      II : P (pr₁ (ϕ x) , j)
      II = transport P (to-subtype-＝ being-iterative-set-is-prop refl) I

∈-is-accessible : (A : 𝕍) → is-accessible _∈_ A
∈-is-accessible = ∈-induction (is-accessible _∈_) (λ A → step)

is-transitive-iset : 𝕍 → 𝓤⁺ ̇
is-transitive-iset A = (B C : 𝕍) → B ∈ A → C ∈ B → C ∈ A

being-transitive-iset-is-prop : (A : 𝕍) → is-prop (is-transitive-iset A)
being-transitive-iset-is-prop A = Π₄-is-prop fe (λ B C l m → ∈-is-prop-valued C A)

is-iterative-ordinal : 𝕍 → 𝓤⁺ ̇
is-iterative-ordinal A = is-transitive-iset A
                       × ((B : 𝕍) → B ∈ A → is-transitive-iset B)

being-iterative-ordinal-is-prop : (A : 𝕍) → is-prop (is-iterative-ordinal A )
being-iterative-ordinal-is-prop A =
 ×-is-prop
  (being-transitive-iset-is-prop A)
  (Π₂-is-prop fe (λ B l → being-transitive-iset-is-prop B))

ordinal-is-hereditary : (A B : 𝕍)
                      → B ∈ A
                      → is-iterative-ordinal A
                      → is-iterative-ordinal B
ordinal-is-hereditary A B B-in-A (A-trans , A-trans-h) = III
 where
  I : is-transitive-iset B
  I = A-trans-h B B-in-A

  II : (C : 𝕍) → C ∈ B → is-transitive-iset C
  II C C-in-B = A-trans-h C (A-trans B C B-in-A C-in-B)

  III : is-iterative-ordinal B
  III = I , II

𝕆 : 𝓤⁺ ̇
𝕆 = Σ A ꞉ 𝕍 , is-iterative-ordinal A

_<_ : 𝕆 → 𝕆 → 𝓤⁺ ̇
(A , _) < (B , _) = A ∈ B

_≤_ : 𝕆 → 𝕆 → 𝓤⁺ ̇
α ≤ β = ∀ γ → γ < α → γ < β

-- TODO (direct). (A , _) ≤ (B , _) ⇔ A ⊆ B

⟪_⟫ : 𝕆 → 𝓤 ̇
⟪ (sup X _ , _) , _ ⟫ = X

_↡_ : (α : 𝕆) (x : ⟪ α ⟫) → 𝕆
(A@(sup X φ , φ-emb , is) , io) ↡ x = B , B-io
 where
  B : 𝕍
  B = φ x , is x

  m : B ∈ A
  m = (x , refl)

  B-io : is-iterative-ordinal B
  B-io = ordinal-is-hereditary A B m io

↡-is-< : (α : 𝕆) (x : ⟪ α ⟫) → (α ↡ x) < α
↡-is-< ((sup X φ , φ-emb , is) , io) x = x , refl

-- TODO: (β < α) ＝ (Σ x ꞉ ⟪ α ⟫ , β = (α ↡ x)). (Direct.)

<-is-prop-valued : (α β : 𝕆) → is-prop (α < β)
<-is-prop-valued (A , _) (B , _) = ∈-is-prop-valued A B

<-is-transitive : (α β γ : 𝕆) → α < β → β < γ → α < γ
<-is-transitive (A , _) (B , _) (C , C-trans , _) u v = I
 where
  I : A ∈ C
  I = C-trans B A v u

<-is-extensional : is-extensional _<_
<-is-extensional α@(A@(sup X φ , φ-emb , g) , A-io@(A-trans , A-trans-h))
                 β@(B@(sup Y γ , γ-emb , h) , B-io@(B-trans , B-trans-h)) u v = VI
 where
  have-uv : (α ≤ β) × (β ≤ α)
  have-uv = u , v

  I : (x : X) → Σ y ꞉ Y , γ y ＝ φ x
  I x = u (α ↡ x) (↡-is-< α x)

  II : (y : Y) → Σ x ꞉ X , φ x ＝ γ y
  II y = v (β ↡ y) (↡-is-< β y)

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

  V : (sup X φ , φ-emb , g) ＝ (sup Y γ , γ-emb , h)
  V = to-𝕍-＝ (p , IV) (φ-emb , g) (γ-emb , h)

  VI : α ＝ β
  VI = to-subtype-＝ (being-iterative-ordinal-is-prop) V

<-is-accessible : (α : 𝕆) → is-accessible _<_ α
<-is-accessible ((M , is) , io) = h M is io
 where
  h : (M : 𝕄) (is : is-iterative-set M) (io : is-iterative-ordinal (M , is))
    → is-accessible _<_ ((M , is) , io)
  h M@(sup X φ) (φ-emb , i) io@(io₁ , io₂) = step III
   where
    have-i : (x : X) → is-iterative-set (φ x)
    have-i = i

    have-io : is-iterative-ordinal (sup X φ , φ-emb , i)
    have-io = io

    A : 𝕍
    A = M , φ-emb , i

    α : 𝕆
    α = A , io

    A' : X → 𝕍
    A' x = φ x , i x

    m : (x : X) → A' x ∈ A
    m x = (x , refl)

    I : (x : X) (B : 𝕍) → B ∈ A' x → is-transitive-iset B
    I x B b = I₂
     where
      I₁ : B ∈ A
      I₁ = io₁ (A' x) B (m x) b

      I₂ : is-transitive-iset B
      I₂ = io₂ B I₁

    IH : (x : X) → is-accessible _<_ (A' x , io₂ (A' x) (m x) , I x)
    IH x = h (φ x) (i x) (io₂ (A' x) (m x) , I x)

    II : (M : 𝕄) (j : is-iterative-set M) (k : is-iterative-ordinal (M , j))
       → fiber φ M
       → is-accessible _<_ ((M , j) , k)
    II .(φ x) j k (x , refl) = II₂
     where
      II₁ : (A' x , io₂ (A' x) (m x) , I x) ＝[ 𝕆 ] ((φ x , j) , k)
      II₁ = to-subtype-＝
             being-iterative-ordinal-is-prop
             (ap (λ - → φ x , -)
                 (being-iterative-set-is-prop (φ x) (i x) j))

      II₂ : is-accessible _<_ ((φ x , j) , k)
      II₂ = transport (is-accessible _<_) II₁ (IH x)

    III : (β : 𝕆) → β < α → is-accessible _<_ β
    III ((N , is) , io) = II N is io

open import Ordinals.Type

𝓞 : Ordinal 𝓤⁺
𝓞 = 𝕆 ,
    _<_ ,
    <-is-prop-valued ,
    <-is-accessible ,
    <-is-extensional ,
    <-is-transitive

\end{code}

To be continued.
