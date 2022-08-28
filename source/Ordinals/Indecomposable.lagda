Martin Escardo, 25th August 2022,
written down in Agda 27th August 2022 while travelling back from
Thierry Coquand's 60th birthday celebration

The type of ordinals is decomposable as a disjoint union of two
pointed types if and only weak excluded middle holds.

Equivalently, there is a function f : Ordinal 𝓤 → 𝟚 such that f α ＝ 0 and f β = 1 for some ordinals α and β if and only if weak excluded middle holds (every negated proposition is decidable, which is equivalent to De Morgan's Law). https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Indecomposable.html

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF.Univalence

module Ordinals.Indecomposable (ua : Univalence) where

open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv
open import UF.UA-FunExt
open import UF.FunExt
open import UF.ExcludedMiddle
open import UF.Size

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import MLTT.Spartan
open import MLTT.Two-Properties

open import Ordinals.Type
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Arithmetic fe

\end{code}

A type X is decomposable if there are designated pointed types X₀ and
X₁ with X ≃ X₀ + X₁. Equivalently, X is decomposable if there is a
designated non-constant function f : X → 𝟚, in the strong sense that
there are designated x₀ and x₁ : X that are mapped to respectively ₀
and ₁ by f.

\begin{code}

decomposable : 𝓤 ̇ → 𝓤 ̇
decomposable X = Σ x₀ ꞉ X , Σ x₁ ꞉ X , Σ f ꞉ (X → 𝟚) , (f x₀ ＝ ₀) × (f x₁ ＝ ₁)

decomposable₁ : 𝓤 ̇ → 𝓤 ⁺ ̇
decomposable₁ {𝓤} X = Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (X ≃ X₀ + X₁)

\end{code}

TODO. decomposable X ≃ decomposable₁ X. Is this already proved
somewhere in TypeTopology? This equivalence was already used in a
publication with coathors.

\begin{code}

WEM-gives-decomposability-of-two-pointed-types : WEM 𝓤
                                               → (X : 𝓤 ̇ )
                                               → has-two-distinct-points X
                                               → decomposable X
WEM-gives-decomposability-of-two-pointed-types wem X ((x₀ , x₁) , d) = γ
 where
  g : (x : X) → ¬ (x ≠ x₀) + ¬¬ (x ≠ x₀) → 𝟚
  g x (inl _) = ₀
  g x (inr _) = ₁

  h : (x : X) → ¬ (x ≠ x₀) + ¬¬ (x ≠ x₀)
  h x = wem (x ≠ x₀) (negations-are-props fe')

  f : X → 𝟚
  f x = g x (h x)

  f₀ : (δ : ¬ (x₀ ≠ x₀) + ¬¬ (x₀ ≠ x₀)) → g x₀ δ ＝ ₀
  f₀ (inl _) = refl
  f₀ (inr u) = 𝟘-elim (three-negations-imply-one u refl)

  e₀ : f x₀ ＝ ₀
  e₀ = f₀ (h x₀)

  f₁ : (δ : ¬ (x₁ ≠ x₀) + ¬¬ (x₁ ≠ x₀)) → g x₁ δ ＝ ₁
  f₁ (inl ϕ) = 𝟘-elim (ϕ (≠-sym d))
  f₁ (inr _) = refl

  e₁ : f x₁ ＝ ₁
  e₁ = f₁ (h x₁)

  γ : decomposable X
  γ = x₀ , x₁ , f , e₀ , e₁

WEM-gives-decomposability-of-ordinals-type⁺ : WEM (𝓤 ⁺) → decomposable (Ordinal 𝓤)
WEM-gives-decomposability-of-ordinals-type⁺ {𝓤} wem =
 WEM-gives-decomposability-of-two-pointed-types wem (Ordinal 𝓤)
  ((𝟙ₒ , 𝟘ₒ) , (λ (e : 𝟙ₒ ＝ 𝟘ₒ) → 𝟘-elim (idtofun 𝟙 𝟘 (ap ⟨_⟩ e) ⋆)))

\end{code}

We can strengthen this to WEM 𝓤 → decomposable (Ordinal 𝓤 ̇) using
the fact that Ordinal 𝓤 ̇ is locally small.

\begin{code}

WEM-gives-decomposability-of-two-pointed-types⁺ : WEM 𝓤
                                               → (X : 𝓤 ⁺ ̇ )
                                               → is-locally-small X
                                               → has-two-distinct-points X
                                               → decomposable X
WEM-gives-decomposability-of-two-pointed-types⁺ {𝓤} wem X l ((x₀ , x₁) , d) = γ
 where
  g : (x : X) → ¬ (x ≠⟦ l ⟧ x₀) + ¬¬ (x ≠⟦ l ⟧ x₀) → 𝟚
  g x (inl _) = ₀
  g x (inr _) = ₁

  h : (x : X) → ¬ (x ≠⟦ l ⟧ x₀) + ¬¬ (x ≠⟦ l ⟧ x₀)
  h x = wem (x ≠⟦ l ⟧ x₀) (negations-are-props fe')

  f : X → 𝟚
  f x = g x (h x)

  f₀ : (δ : ¬ (x₀ ≠⟦ l ⟧ x₀) + ¬¬ (x₀ ≠⟦ l ⟧ x₀)) → g x₀ δ ＝ ₀
  f₀ (inl _) = refl
  f₀ (inr u) = 𝟘-elim (three-negations-imply-one u ⟦ l ⟧-refl)

  e₀ : f x₀ ＝ ₀
  e₀ = f₀ (h x₀)

  f₁ : (δ : ¬ (x₁ ≠⟦ l ⟧ x₀) + ¬¬ (x₁ ≠⟦ l ⟧ x₀)) → g x₁ δ ＝ ₁
  f₁ (inl ϕ) = 𝟘-elim (ϕ (≠-gives-≠⟦ l ⟧ (≠-sym d)))
  f₁ (inr _) = refl

  e₁ : f x₁ ＝ ₁
  e₁ = f₁ (h x₁)

  γ : decomposable X
  γ = x₀ , x₁ , f , e₀ , e₁

WEM-gives-decomposability-of-ordinals-type : WEM 𝓤 → decomposable (Ordinal 𝓤)
WEM-gives-decomposability-of-ordinals-type {𝓤} wem =
 WEM-gives-decomposability-of-two-pointed-types⁺ wem (Ordinal 𝓤)
  the-type-of-ordinals-is-locally-small
  ((𝟙ₒ , 𝟘ₒ) , (λ (e : 𝟙ₒ ＝ 𝟘ₒ) → 𝟘-elim (idtofun 𝟙 𝟘 (ap ⟨_⟩ e) ⋆)))

\end{code}

For the converse, we use the following notion, where Ω 𝓤 is the type
of truth values, or propositions, in the universe 𝓤.

\begin{code}

Ω-Path : {X : 𝓤 ̇ } (𝓥 : Universe) → X → X → 𝓤 ⊔ (𝓥 ⁺) ̇
Ω-Path {𝓤} {X} 𝓥 x y = Σ f ꞉ (Ω 𝓥 → X) , (f ⊥Ω ＝ x) × (f ⊤Ω ＝ y)

has-Ω-paths : (𝓥 : Universe) → 𝓤 ̇  → 𝓤 ⊔ (𝓥 ⁺) ̇
has-Ω-paths 𝓥 X = (x y : X) → Ω-Path 𝓥 x y

type-of-ordinals-has-Ω-paths : has-Ω-paths 𝓤 (Ordinal 𝓤)
type-of-ordinals-has-Ω-paths {𝓤} α β = f , γ⊥ , γ⊤
 where
  f : Ω 𝓤 → Ordinal 𝓤
  f p = (Ω-to-ordinal (not fe' p) ×ₒ α) +ₒ (Ω-to-ordinal p ×ₒ β)

  γ⊥ : f ⊥Ω ＝ α
  γ⊥ = eqtoidₒ (f ⊥Ω) α (u , o , e , p)
   where
    u : ⟨ f ⊥Ω ⟩ → ⟨ α ⟩
    u (inl (x , a)) = a

    o : is-order-preserving (f ⊥Ω) α u
    o (inl (x , a)) (inl (x , b)) (inr (refl , l)) = l

    v : ⟨ α ⟩ → ⟨ f ⊥Ω ⟩
    v a = inl (𝟘-elim , a)

    vu : v ∘ u ∼ id
    vu (inl (x , a)) = ap inl (to-×-＝ (dfunext fe' (λ z → 𝟘-elim z)) refl)

    uv : u ∘ v ∼ id
    uv a = refl

    e : is-equiv u
    e = qinvs-are-equivs u (v , vu , uv)

    p : is-order-preserving α (f ⊥Ω) v
    p a b l = inr (refl , l)

  γ⊤ : f ⊤Ω ＝ β
  γ⊤ = eqtoidₒ (f ⊤Ω) β (u , o , e , p)
   where
    u : ⟨ f ⊤Ω ⟩ → ⟨ β ⟩
    u (inl (f , _)) = 𝟘-elim (f ⋆)
    u (inr (⋆ , b)) = b

    o : is-order-preserving (f ⊤Ω) β u
    o (inl (f , _)) y l = 𝟘-elim (f ⋆)
    o (inr (⋆ , _)) (inr (⋆ , _)) (inr (_ , l)) = l

    v : ⟨ β ⟩ → ⟨ f ⊤Ω ⟩
    v b = inr (⋆ , b)

    vu : v ∘ u ∼ id
    vu (inl (f , _)) = 𝟘-elim (f ⋆)
    vu (inr (⋆ , b)) = refl

    uv : u ∘ v ∼ id
    uv b = refl

    e : is-equiv u
    e = qinvs-are-equivs u (v , vu , uv)

    p : is-order-preserving β (f ⊤Ω) v
    p b c l = inr (refl , l)

non-constant-map-Ω-to-𝟚-gives-WEM :
        (Σ f ꞉ (Ω 𝓤 → 𝟚) , Σ p₀ ꞉ Ω 𝓤 , Σ p₁ ꞉ Ω 𝓤 , (f p₀ ＝ ₀) × (f p₁ ＝ ₁))
      → WEM 𝓤
non-constant-map-Ω-to-𝟚-gives-WEM {𝓤} (f , p₀@(P₀ , i₀) , p₁@(P₁ , i₁) , e₀ , e₁) = IV
 where
  g : Ω 𝓤 → Ω 𝓤
  g (Q , j) = ((P₀ × Q) + (P₁ × ¬ Q)) , k
   where
    k : is-prop ((P₀ × Q) + (P₁ × ¬ Q))
    k (inl (a , b)) (inl (u , v)) = ap inl (to-×-＝ (i₀ a u) (j b v))
    k (inl (a , b)) (inr (u , v)) = 𝟘-elim (v b)
    k (inr (a , b)) (inl (u , v)) = 𝟘-elim (b v)
    k (inr (a , b)) (inr (u , v)) = ap inr (to-×-＝
                                             (i₁ a u)
                                             (negations-are-props fe' b v))

  I₀ : (q : Ω 𝓤) → q holds → f (g q) ＝ ₀
  I₀ q h = II
   where
    I : g q ＝ p₀
    I = to-subtype-＝
          (λ _ → being-prop-is-prop fe')
          (univalence-gives-propext (ua 𝓤) (pr₂ (g q)) i₀
            (cases pr₁ (λ (_ , n) → 𝟘-elim (n h)))
            (λ x → inl (x , h)))

    II = f (g q) ＝⟨ ap f I ⟩
         f p₀    ＝⟨ e₀ ⟩
         ₀       ∎

  I₁ : (q : Ω 𝓤) → ¬ (q holds) → f (g q) ＝ ₁
  I₁ q n = II
   where
    I : g q ＝ p₁
    I = to-subtype-＝
          (λ _ → being-prop-is-prop fe')
          (univalence-gives-propext (ua 𝓤) (pr₂ (g q)) i₁
          (cases (λ (_ , h) → 𝟘-elim (n h)) pr₁)
          (λ x → inr (x , n)))

    II = f (g q) ＝⟨ ap f I ⟩
         f p₁    ＝⟨ e₁ ⟩
         ₁       ∎

  III₀ : (q : Ω 𝓤) → f (g q) ＝ ₀ → ¬ (q holds) + ¬¬ (q holds)
  III₀ q e = inr (contrapositive (I₁ q) (equal-₀-different-from-₁ e))

  III₁ : (q : Ω 𝓤) → f (g q) ＝ ₁ → ¬ (q holds) + ¬¬ (q holds)
  III₁ q e = inl (contrapositive (I₀ q) (equal-₁-different-from-₀ e))

  IV : (Q : 𝓤  ̇) → is-prop Q → ¬ Q + ¬¬ Q
  IV Q j = 𝟚-equality-cases (III₀ (Q , j)) (III₁ (Q , j))


decomposable-type-with-Ω-paths-gives-WEM : {X : 𝓤 ̇ }
                                         → decomposable X
                                         → has-Ω-paths 𝓥 X
                                         → WEM 𝓥
decomposable-type-with-Ω-paths-gives-WEM {𝓤} {𝓥} {X} (x₀ , x₁ , f , e₀ , e₁) c = γ
 where
  g : Ω 𝓥 → X
  g = pr₁ (c x₀ x₁)

  gp : (g ⊥Ω ＝ x₀) × (g ⊤Ω ＝ x₁)
  gp = pr₂ (c x₀ x₁)

  I₀ = f (g ⊥Ω) ＝⟨ ap f (pr₁ gp) ⟩
       f x₀     ＝⟨ e₀ ⟩
       ₀        ∎

  I₁ = f (g ⊤Ω) ＝⟨ ap f (pr₂ gp) ⟩
       f x₁     ＝⟨ e₁ ⟩
       ₁        ∎

  γ : WEM 𝓥
  γ = non-constant-map-Ω-to-𝟚-gives-WEM (f ∘ g , ⊥Ω , ⊤Ω , I₀ , I₁)

decomposability-of-ordinals-type-gives-WEM : decomposable (Ordinal 𝓤) → WEM 𝓤
decomposability-of-ordinals-type-gives-WEM d =
 decomposable-type-with-Ω-paths-gives-WEM d type-of-ordinals-has-Ω-paths

Ordinal-decomposable-iff-WEM : decomposable (Ordinal 𝓤) ⇔ WEM 𝓤
Ordinal-decomposable-iff-WEM = decomposability-of-ordinals-type-gives-WEM ,
                               WEM-gives-decomposability-of-ordinals-type

\end{code}

TODO. Because WEM 𝓤 is a proposition, it follows that
∥ decomposable (Ordinal 𝓤) ∥ ⇔ WEM 𝓤, and hence also
∥ decomposable (Ordinal 𝓤) ∥ → decomposable (Ordinal 𝓤).
