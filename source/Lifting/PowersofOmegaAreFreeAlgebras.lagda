Martin Escardo, 2nd December 2025.

In any 1-topos, powers of Ω are free algebras.

The same argument seems to show that products of free algebras are
free, but this is still under development.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

module Lifting.PowersOfOmegaAreFreeAlgebras
        (fe       : Fun-Ext)
        (pe       : Prop-Ext)
        (pt       : propositional-truncations-exist)
        (𝓣        : Universe)
        (X : 𝓣 ̇ )
       where

open import Lifting.Construction 𝓣
open import Lifting.Algebras 𝓣
open import Lifting.Identity 𝓣
open import Lifting.TwoAlgebrasOnOmega 𝓣 fe pe renaming (Σ-alg-on-Ω to Ω∃)

open import UF.Embeddings
open import UF.Equiv
open import UF.Logic
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier-Properties
open import UF.SubtypeClassifier renaming (Ω to Ω-of-universe ;
                                           ⊥ to ⊥Ω ;
                                           ⊤ to ⊤Ω)

private
 𝓣⁺ = 𝓣 ⁺

 Ω : 𝓣⁺ ̇
 Ω = Ω-of-universe 𝓣

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open PropositionalTruncation pt

\end{code}

We let π range over Ωˣ.

\begin{code}

Ωˣ : 𝓣 ⁺ ̇
Ωˣ = X → Ω

Ωˣ-is-set : is-set Ωˣ
Ωˣ-is-set = Π-is-set fe (λ (_ : X) → Ω-is-set fe pe)

Ωˣ-𝓛-alg : 𝓛-alg Ωˣ
Ωˣ-𝓛-alg = Π-is-alg fe (λ (_ : X) → Ω) (λ (_ : X) → Ω∃)

∐ : extension-op Ωˣ
∐ = 𝓛-alg-structure Ωˣ-𝓛-alg

is-pos : Ωˣ → 𝓣 ̇
is-pos π = ∃ x ꞉ X , π x holds

being-pos-is-prop : (π : Ωˣ) → is-prop (is-pos π)
being-pos-is-prop π = ∃-is-prop

is-Pos : Ωˣ → Ω
is-Pos π = is-pos π , being-pos-is-prop π

G : 𝓣 ⁺ ̇
G = Σ π ꞉ Ωˣ , is-pos π

G-is-set : is-set G
G-is-set = Σ-is-set
            (Π-is-set fe (λ (_ : X) → Ω-is-set fe pe))
            (λ (_ : Ωˣ) → props-are-sets ∃-is-prop)

ι : G → Ωˣ
ι = pr₁

ι-is-pos : (g : G) → is-pos (ι g)
ι-is-pos = pr₂

ι-is-embedding : is-embedding ι
ι-is-embedding = pr₁-is-embedding being-pos-is-prop

open free-algebras-in-the-category-of-sets pe fe G G-is-set

𝓛G : 𝓛-alg (𝓛 G)
𝓛G = free

h : 𝓛 G → Ωˣ
h = 𝓛-extension Ωˣ-is-set Ωˣ-𝓛-alg ι

h-explicitly : (l@(P , φ , i) : 𝓛 G)
             → h l ＝ λ x → ∑ (λ (p : P) → ι (φ p) x)
h-explicitly l = by-definition

h-is-hom : is-hom 𝓛G Ωˣ-𝓛-alg h
h-is-hom = 𝓛-extension-is-hom Ωˣ-is-set Ωˣ-𝓛-alg ι

h-extends-ι : h ∘ η ∼ ι
h-extends-ι = 𝓛-extension-extends Ωˣ-is-set Ωˣ-𝓛-alg ι

\end{code}

Our aim is to fill this diagram with a homomorphism h⁻¹ inverting h:

       η
  G ────────→ 𝓛 G
   ╲         │  ↑
    ╲        │  │
     ╲       │  │
    ι ╲    h │  │ h⁻¹
       ╲     │  │
        ╲    │  │
         ╲   │  │
          ╲  ↓  │
           ➘  Ωˣ.

\begin{code}

open Conjunction

h⁻¹ : Ωˣ → 𝓛 G
h⁻¹ π = is-pos π , (λ i → π , i) , being-pos-is-prop π

h⁻¹-is-section : h ∘ h⁻¹ ∼ id
h⁻¹-is-section π =
 h (h⁻¹ π)                          ＝⟨ h-explicitly (h⁻¹ π) ⟩
 (λ x → ∑ (λ (_ : is-pos π) → π x)) ＝⟨by-definition⟩
 (λ x → is-Pos π ∧ π x)             ＝⟨ I ⟩
 (λ x → π x)                        ＝⟨by-definition⟩
 π                                  ∎
  where
   I = dfunext fe (λ x → Ω-extensionality pe fe
                          pr₂
                          (λ (h : π x holds) → ∣ x , h ∣ , h))

\end{code}

To show that h⁻¹ is also a retraction, and that it is a homomorphism,
we will use the following two definitional equalities tacitly.

\begin{code}

module NB
        (l@(P , φ , i) : 𝓛 G)
        (φ : P → Ωˣ)
       where

 NB₀ : is-defined (h⁻¹ (∐ i φ)) ＝ (∃ x ꞉ X , Σ p ꞉ P , φ p x holds)
 NB₀ = refl

 NB₁ : is-defined (⨆ i (h⁻¹ ∘ φ)) ＝ (Σ p ꞉ P , ∃ x ꞉ X , φ p x holds)
 NB₁ = refl

h⁻¹-is-retraction : h⁻¹ ∘ h ∼ id
h⁻¹-is-retraction l@(P , φ , i) = II
 where
  f : (∃ x ꞉ X , Σ p ꞉ P , ι (φ p) x holds) → P
  f = ∥∥-rec i (λ (x , p , h) → p)

  g : P → ∃ x ꞉ X , Σ p ꞉ P , ι (φ p) x holds
  g p = ∥∥-rec ∃-is-prop (λ (x , h) → ∣ x , p , h ∣) e
   where
    e : ∃ x ꞉ X , ι (φ p) x holds
    e = ι-is-pos (φ p)

  I : {e : ∃ x ꞉ X , Σ p ꞉ P , ι (φ p) x holds}
    → (λ x → ∑ (λ (p : P) → ι (φ p) x)) ＝ ι (φ (f e))
  I {e} = dfunext fe (λ x → to-subtype-＝ (λ _ → being-prop-is-prop fe) (I₀ x))
   where
    I₀ : (x : X) → (Σ p ꞉ P , ι (φ p) x holds) ＝ (ι (φ (f e)) x holds)
    I₀ x = pe (Σ-is-prop i (λ p → holds-is-prop (ι (φ p) x)))
              (holds-is-prop (ι (φ (f e)) x))
              (λ (p , h) → transport (λ - → ι (φ -) x holds) (i p (f e)) h)
              (λ (h : ι (φ (f e)) x holds) → f e , h)

  II : h⁻¹ (h l) ＝ l
  II = from-⋍ pe fe fe ((f , g) , (λ s → to-subtype-＝ being-pos-is-prop I))

\end{code}

So Ωˣ is equivalent to a free algebra.

\begin{code}

Ωˣ-is-𝓛G : Ωˣ ≃ 𝓛 G
Ωˣ-is-𝓛G = qinveq h⁻¹ (h , h⁻¹-is-section , h⁻¹-is-retraction)

\end{code}

The equivalence is an algebra homomorphism.

\begin{code}

h⁻¹-is-hom : is-hom Ωˣ-𝓛-alg 𝓛G h⁻¹
h⁻¹-is-hom P i φ = IV
 where
  I : (∃ x ꞉ X , Σ p ꞉ P , φ p x holds) → (Σ p ꞉ P , ∃ x ꞉ X , φ p x holds)
  I = ∥∥-rec (Σ-is-prop i λ _ → ∃-is-prop) (λ (x , p , h) → p , ∣ x , h ∣)

  II : (Σ p ꞉ P , ∃ x ꞉ X , φ p x holds) → (∃ x ꞉ X , Σ p ꞉ P , φ p x holds)
  II (p , e) = ∥∥-functor (λ (x , h) → x , p , h) e

  III : value (h⁻¹ (∐ i φ)) ∼ (λ x → value (⨆ i (h⁻¹ ∘ φ)) (I x))
  III e = III₁
   where
    p : P
    p = pr₁ (I e)

    III₀ : ∐ i φ ＝ φ p
    III₀ = 𝓛-alg-Law₀-gives₀' pe fe fe ∐ (𝓛-alg-law₀ Ωˣ-𝓛-alg) P i φ p

    III₁ : (∐ i φ , e) ＝ (φ p , pr₂ (I e))
    III₁ = to-subtype-＝ being-pos-is-prop III₀

  IV : h⁻¹ (∐ i φ) ＝ ⨆ i (h⁻¹ ∘ φ)
  IV = from-⋍ pe fe fe ((I , II) , III)

h⁻¹-extends-η : h⁻¹ ∘ ι ∼ η
h⁻¹-extends-η g = h⁻¹ (ι g)     ＝⟨ ap h⁻¹ (h-extends-ι g ⁻¹) ⟩
                  h⁻¹ (h (η g)) ＝⟨ h⁻¹-is-retraction (η g) ⟩
                  η g           ∎

\end{code}

Finally, it follows by a standard categorical argument that Ωˣ is
freely generated by G with insertion of generators ι.

\begin{code}

Ωˣ-is-free-𝓛-alg : is-free-𝓛-alg Ωˣ-𝓛-alg G ι
Ωˣ-is-free-𝓛-alg {𝓦} {A} A-is-set 𝓐 f = III
 where
  I : ∃! (f̅ , _) ꞉ Hom 𝓛G 𝓐 , f̅ ∘ η ∼ f
  I = 𝓛-is-free A-is-set 𝓐 f

  II : (Σ  (f̅ , _) ꞉ Hom 𝓛G       𝓐 , f̅ ∘ η ∼ f)
     → (∃! (f̅̅ , _) ꞉ Hom Ωˣ-𝓛-alg 𝓐 , f̅̅ ∘ ι ∼ f)
  II ((f̅ , f̅-is-hom) , e) = II₀₂
   where
    f̅̅ : Ωˣ → A
    f̅̅ = f̅ ∘ h⁻¹

    f̅̅-is-hom : is-hom Ωˣ-𝓛-alg 𝓐 f̅̅
    f̅̅-is-hom = ∘-is-hom Ωˣ-𝓛-alg 𝓛G 𝓐 h⁻¹ f̅ h⁻¹-is-hom f̅-is-hom

    e̅ :  f̅̅ ∘ ι ∼ f
    e̅ g = f̅̅ (ι g)       ＝⟨by-definition⟩
          f̅ (h⁻¹ (ι g)) ＝⟨ ap f̅ (h⁻¹-extends-η g) ⟩
          f̅ (η g)       ＝⟨ e g ⟩
          f g           ∎

    c : Σ (f̅̅ , _) ꞉ Hom Ωˣ-𝓛-alg 𝓐 , f̅̅ ∘ ι ∼ f
    c = (f̅̅ , f̅̅-is-hom) , e̅

    II₀ : is-prop (type-of c)
    II₀ ((f₀ , f₀-is-hom) , e₀) ((f₁ , f₁-is-hom) , e₁) = II₀₁
     where
      f₀-agrees-with-f₁ : f₀ ∼ f₁
      f₀-agrees-with-f₁ π =
       f₀ π           ＝⟨ ap f₀ ((h⁻¹-is-section π)⁻¹) ⟩
       f₀ (h (h⁻¹ π)) ＝⟨ II₀₀ (h⁻¹ π) ⟩
       f₁ (h (h⁻¹ π)) ＝⟨ ap f₁ (h⁻¹-is-section π) ⟩
       f₁ π           ∎
        where
         II₀₀ : f₀ ∘ h ∼ f₁ ∘ h
         II₀₀ = hom-agreement A-is-set 𝓐 f
                 ((f₀ ∘ h , ∘-is-hom 𝓛G Ωˣ-𝓛-alg 𝓐 h f₀ h-is-hom f₀-is-hom) ,
                  (λ g → f₀ (h (η g)) ＝⟨ ap f₀ (h-extends-ι g) ⟩
                         f₀ (ι g)     ＝⟨ e₀ g ⟩
                         f g          ∎))
                 ((f₁ ∘ h , ∘-is-hom 𝓛G Ωˣ-𝓛-alg 𝓐 h f₁ h-is-hom f₁-is-hom) ,
                  (λ g → f₁ (h (η g)) ＝⟨ ap f₁ (h-extends-ι g) ⟩
                         f₁ (ι g)     ＝⟨ e₁ g ⟩
                         f g          ∎))

      II₀₁ : ((f₀ , f₀-is-hom) , e₀) ＝ ((f₁ , f₁-is-hom) , e₁)
      II₀₁ = to-subtype-＝
              (λ σ → Π-is-prop fe (λ (_ : G) → A-is-set))
              (to-subtype-＝
                (λ (fₙ : Ωˣ → A) → Π₃-is-prop fe (λ P i φ → A-is-set))
                (dfunext fe f₀-agrees-with-f₁))

    II₀₂ : ∃! (f̅̅ , _) ꞉ Hom Ωˣ-𝓛-alg 𝓐 , f̅̅ ∘ ι ∼ f
    II₀₂ = pointed-props-are-singletons c II₀

  III : ∃! (f̅̅ , _) ꞉ Hom Ωˣ-𝓛-alg 𝓐 , f̅̅ ∘ ι ∼ f
  III = II (center I)

\end{code}

Under development. It seems that the same argument shows that products
of free algebras are themselves free. Nothing special about Ω was used
here.
