Martin Escardo & Tom de Jong, June 2023.

Iterative sets.

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
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Iterative.Multisets 𝓤
open import Ordinals.Notions
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

An iterative set is a multiset whose forests are all embeddings.

\begin{code}

is-iterative-set : 𝕄 → 𝓤 ⁺ ̇
is-iterative-set (lim X φ) = is-embedding φ
                           × ((x : X) → is-iterative-set (φ x))

𝕄-forest-is-embedding : (M : 𝕄)
                      → is-iterative-set M
                      → is-embedding (𝕄-forest M)
𝕄-forest-is-embedding (lim X φ) = pr₁

𝕄-subtrees-are-iterative : (M : 𝕄)
                         → is-iterative-set M
                         → (x : 𝕄-root M) → is-iterative-set (𝕄-forest M x)
𝕄-subtrees-are-iterative (lim X φ) = pr₂

being-iset-is-prop : (A : 𝕄)
                   → is-prop (is-iterative-set A)
being-iset-is-prop (lim X φ) =
 ×-is-prop
  (being-embedding-is-prop fe φ)
  (Π-is-prop fe (λ x → being-iset-is-prop (φ x)))

\end{code}

The type of iterative sets:

\begin{code}

𝕍 : 𝓤 ⁺ ̇
𝕍 = Σ M ꞉ 𝕄 , is-iterative-set M

underlying-mset : 𝕍 → 𝕄
underlying-mset = pr₁

underlying-mset-is-embedding : is-embedding underlying-mset
underlying-mset-is-embedding = pr₁-is-embedding being-iset-is-prop

isets-are-iterative : (A : 𝕍) → is-iterative-set (underlying-mset A)
isets-are-iterative = pr₂

\end{code}

A criterion for equality in 𝕍:

\begin{code}

to-𝕍-＝ : {X Y : 𝓤 ̇ }
          {φ : X → 𝕄}
          {γ : Y → 𝕄}
        → (Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
        → (i : is-iterative-set (lim X φ))
          (j : is-iterative-set (lim Y γ))
        → (lim X φ , i) ＝[ 𝕍 ] (lim Y γ , j)
to-𝕍-＝ {X} σ i j = to-subtype-＝ being-iset-is-prop (to-𝕄-＝ σ)

_∈_ : 𝕍 → 𝕍 → 𝓤 ⁺ ̇
(M , _) ∈ (lim X φ , _) = Σ x ꞉ X , φ x ＝ M

∈-is-prop-valued : (A B : 𝕍) → is-prop (A ∈ B)
∈-is-prop-valued (M , _) (lim X φ , φ-emb , _) = φ-emb M

_⊆_ : 𝕍 → 𝕍 → 𝓤 ⁺ ̇
A ⊆ B = (C : 𝕍) → C ∈ A → C ∈ B

⊆-is-prop-valued : (A B : 𝕍) → is-prop (A ⊆ B)
⊆-is-prop-valued A B = Π₂-is-prop fe (λ C _ → ∈-is-prop-valued C B)

∈-is-extensional : (A B : 𝕍) → A ⊆ B → B ⊆ A → A ＝ B
∈-is-extensional A@(lim X φ , φ-emb , g) B@(lim Y γ , γ-emb , h) u v = V
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

It follows that 𝕍 is a set, or 0-type, in the sense of the HoTT book:

\begin{code}

𝕍-is-set : is-set 𝕍
𝕍-is-set = extensionally-ordered-types-are-sets _∈_ fe'
            ∈-is-prop-valued
            ∈-is-extensional

𝕍-root : 𝕍 → 𝓤 ̇
𝕍-root (lim X φ , _) = X

𝕍-forest : (A : 𝕍) → 𝕍-root A → 𝕍
𝕍-forest (lim X φ , _ , is) x = φ x , is x

𝕍-forest-is-embedding : (A : 𝕍) → is-embedding (𝕍-forest A)
𝕍-forest-is-embedding A@(lim X φ , φ-emb , is) =
 pair-fun-is-embedding-special φ is φ-emb being-iset-is-prop

𝕍-lim : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) → is-embedding ϕ → 𝕍
𝕍-lim X ϕ ϕ-emb = lim X φ , I , φi
 where
  φ : X → 𝕄
  φ = pr₁ ∘ ϕ

  φi : (x : X) → is-iterative-set (φ x)
  φi = pr₂ ∘ ϕ

  I : is-embedding (pr₁ ∘ ϕ)
  I = ∘-is-embedding ϕ-emb (pr₁-is-embedding being-iset-is-prop)

∈-behaviour : (A : 𝕍) (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
            → A ∈ 𝕍-lim X ϕ e ≃ (Σ x ꞉ X , ϕ x ＝ A)
∈-behaviour A X ϕ e =
 (A ∈ 𝕍-lim X ϕ e)              ≃⟨ ≃-refl _ ⟩
 (Σ x ꞉ X , pr₁ (ϕ x) ＝ pr₁ A) ≃⟨ Σ-cong I ⟩
 (Σ x ꞉ X , ϕ x ＝ A)           ■
  where
   I : (x : X) → (pr₁ (ϕ x) ＝ pr₁ A) ≃ (ϕ x ＝ A)
   I x = embedding-criterion-converse
          pr₁
          (pr₁-is-embedding being-iset-is-prop)
          (ϕ x)
          A

𝕍-lim-root : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
           → 𝕍-root (𝕍-lim X ϕ e) ＝ X
𝕍-lim-root X ϕ e = refl

𝕍-lim-forest : (X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
             → 𝕍-forest (𝕍-lim X ϕ e) ＝ ϕ
𝕍-lim-forest X ϕ e = refl

\end{code}

It also follows from the fact that 𝕍 is a set and that 𝕍-forest in an
embedding that the root of any iterative set is a 0-type:

\begin{code}

𝕍-root-is-set : (A : 𝕍) → is-set (𝕍-root A)
𝕍-root-is-set A = subtypes-of-sets-are-sets
                   (𝕍-forest A)
                   (𝕍-forest-is-embedding A)
                   𝕍-is-set

𝕍-η : (A : 𝕍) → 𝕍-lim (𝕍-root A) (𝕍-forest A) (𝕍-forest-is-embedding A) ＝ A
𝕍-η (lim _ _ , _) = to-subtype-＝ being-iset-is-prop refl

\end{code}

All iterative set are generated by the "constructor" 𝕍-lim, in the
following sense:

\begin{code}

𝕍-induction : (P : 𝕍 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
                  → ((x : X) → P (ϕ x))
                  → P (𝕍-lim X ϕ e))
            → (A : 𝕍) → P A
𝕍-induction P f (M , i) = h M i
 where
  h : (M : 𝕄) (i : is-iterative-set M) → P (M , i)
  h M@(lim X φ) i@(φ-emb , φ-iter) = II
   where
    A : 𝕍
    A = (M , i)

    IH : (x : X) → P (𝕍-forest A x)
    IH x = h (φ x) (φ-iter x)

    I : P (𝕍-lim X (𝕍-forest A) (𝕍-forest-is-embedding A))
    I = f X (𝕍-forest A) (𝕍-forest-is-embedding A) IH

    II : P A
    II = transport P (𝕍-η A) I

\end{code}

The usual induction principle follows directly from the above form of
induction.

\begin{code}

∈-induction : (P : 𝕍 → 𝓥 ̇ )
            → ((A : 𝕍) → ((B : 𝕍) → B ∈ A → P B) → P A)
            → (A : 𝕍) → P A
∈-induction P g = 𝕍-induction P f
 where
  f : (X : 𝓤 ̇) (ϕ : X → 𝕍) (e : is-embedding ϕ)
    → ((x : X) → P (ϕ x))
    → P (𝕍-lim X ϕ e)
  f X ϕ e u = g A s
   where
    A : 𝕍
    A = 𝕍-lim X ϕ e

    s : (B : 𝕍) → B ∈ A → P B
    s (.(pr₁ (ϕ x)) , j) (x , refl) = II
     where
      I : P (ϕ x)
      I = u x

      II : P (pr₁ (ϕ x) , j)
      II = transport P (to-subtype-＝ being-iset-is-prop refl) I

∈-is-accessible : (A : 𝕍) → is-accessible _∈_ A
∈-is-accessible = ∈-induction (is-accessible _∈_) (λ _ → step)

\end{code}

TODO. 𝕍 is locally small.
