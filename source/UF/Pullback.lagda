Martin Escardo, 23rd May 2025.

Homotopy pullbacks and some basic properties to begin with.

This is loosely based on

[1] Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine.
    Homotopy limits in type theory, 2015 (first version 2013).
    https://arxiv.org/abs/1304.0680

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Pullback where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Subsingletons

\end{code}

We assume a cospan

                 B
                 |
                 | g
                 |
                 v
      A -------> C
           f

\begin{code}

module _ {𝓤 𝓥 𝓦 : Universe}
         {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇}
         (f : A → C) (g : B → C)
       where

\end{code}

And we consider commutative squares of the form

           q
      X -------> B
      |          |
    p |          | g
      |          |
      v          v
      A -------> C
            f

completing the cospan.

\begin{code}

 commutative-square : {X : 𝓣 ̇ } → (X → A) × (X → B) → 𝓦 ⊔ 𝓣 ̇
 commutative-square (p , q) = f ∘ p ∼ g ∘ q

\end{code}

A cone over the cospan is the totality of these data.

\begin{code}

 cone : 𝓣 ̇ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 cone X = Σ pq ꞉ ((X → A) × (X → B)) , commutative-square pq

\end{code}

It is convenient to collect all cones in a universe into a single
type.

\begin{code}

 Cone : (𝓣 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ (𝓣 ⁺) ̇
 Cone 𝓣 = Σ P ꞉ 𝓣 ̇ , cone P

 source : Cone 𝓣 → 𝓣 ̇
 source (P , c) = P

 cone-of : (𝓒 : Cone 𝓣) → cone (source 𝓒)
 cone-of (P , c) = c

\end{code}

If we have a cone

            q
      P -------> B
      |          |
    p |          | g
      |          |
      v          v
      A -------> C
            f

and a map u : X → P, we get a cone

          q ∘ u
      X -------> B
      |          |
p ∘ u |          | g
      |          |
      v          v
      A -------> C
            f

\begin{code}

 cone-map : {P : 𝓣' ̇ } (X : 𝓣 ̇ ) → cone P → (X → P) → cone X
 cone-map X ((p , q) , e) u = (p ∘ u , q ∘ u) , e ∘ u

\end{code}

We say that a cone

            q
      P -------> B
      |          |
    p |          | g
      |          |
      v          v
      A -------> C
            f

is a (homotopy) pullback if the cone map is an equivalence for every X.

\begin{code}

 is-pullback : Cone 𝓣 → 𝓤ω
 is-pullback (P , c) = {𝓣' : Universe} (X : 𝓣' ̇ ) → is-equiv (cone-map X c)

 module _ (𝓒@(P , c@((p₁ , p₂) , s)) : Cone 𝓣)
          (i : is-pullback 𝓒)
        where

  pullback-equivalence : (X : 𝓣' ̇ ) → (X → P) ≃ cone X
  pullback-equivalence X = cone-map X c , i X

  module _ (𝓓@(X , d@((h₁ , h₂) , t)) : Cone 𝓣') where

   universal-property
    : ∃! u ꞉ (X → P) , ((p₁ ∘ u , p₂ ∘ u) , s ∘ u) ＝ ((h₁ , h₂) , t)
   universal-property
    = equivs-are-vv-equivs (cone-map X c) (i X) d

   mediating-map : (X → P)
   mediating-map = pr₁ (center universal-property)

   _ : mediating-map ＝ ⌜ pullback-equivalence X ⌝⁻¹ d
   _ = refl

   mediating-map-eq₁ : p₁ ∘ mediating-map ＝ h₁
   mediating-map-eq₁ = ap (pr₁ ∘ pr₁) (pr₂ (center universal-property))

   mediating-map-eq₂ : p₂ ∘ mediating-map ＝ h₂
   mediating-map-eq₂ = ap (pr₂ ∘ pr₁) (pr₂ (center universal-property))

\end{code}

We now show that pullbacks exist, and call them simply pullbacks,
although perhaps we should call them standard pullbacks, or chosen
pullbacks.

\begin{code}

 pullback-source : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 pullback-source = Σ (a , b) ꞉ A × B , f a ＝ g b

 private
  P = pullback-source

\end{code}

We denote the pullback projections by pb₁ and pb₂.

\begin{code}

 pb₁ : P → A
 pb₁ ((a , b) , e) = a

 pb₂ : P → B
 pb₂ ((a , b) , e) = b

 pullback-square : commutative-square (pb₁ , pb₂)
 pullback-square ((a , b) , e) = e

 pullback-cone : cone P
 pullback-cone = ((pb₁ , pb₂) , pullback-square)

 Pullback-Cone : Cone (𝓤 ⊔ 𝓥 ⊔ 𝓦)
 Pullback-Cone = P , pullback-cone

 pullback-cone-map : (X : 𝓣' ̇ ) → (X → P) → cone X
 pullback-cone-map X = cone-map X pullback-cone

 pullback-mediating-map : {X : 𝓣 ̇ } → cone X → (X → P)
 pullback-mediating-map ((p , q) , s) x = (p x , q x) , s x

 pullback-Cone-is-pullback : is-pullback Pullback-Cone
 pullback-Cone-is-pullback X =
  qinvs-are-equivs
   (pullback-cone-map X)
   (pullback-mediating-map , (λ x → refl) , (λ c → refl))

 _ : (X : 𝓣' ̇ ) (c : cone X)
   → pullback-mediating-map c
   ＝ mediating-map Pullback-Cone pullback-Cone-is-pullback (X , c)
 _ = λ X c → refl

\end{code}

Pullbacks of embeddings are embeddings.

\begin{code}

 pb₂-is-embedding : is-embedding f → is-embedding pb₂
 pb₂-is-embedding f-is-embedding b = I
   where
    _ : fiber pb₂ b ＝ (Σ ((x , b') , e) ꞉ pullback-source ,  b' ＝ b)
    _ = refl

    I : is-prop (fiber pb₂ b)
    I (((x₁ , .b) , e₁) , refl) (((x₂ , .b) , e₂) , refl) = III II
     where
      II : (x₁ , e₁) ＝ (x₂ , e₂)
      II = f-is-embedding (g b) (x₁ , e₁) (x₂ , e₂)

      III : {σ τ : fiber f (g b)}
          → σ ＝ τ
          → (((fiber-point σ , b) , fiber-identification σ) , refl)
          ＝[ fiber pb₂ b ]
            (((fiber-point τ , b) , fiber-identification τ) , refl)
      III refl = refl

\end{code}

This is a "biased" version. Of course, also if g is an embedding, then
the projection pb₁ is also an enbedding, just by switching the roles
of f and g, and then pb₁ and pb₂.

TODO. Implement other results from [1].

\begin{code}

fiber-is-pullback
 : {𝓥 : Universe} {A : 𝓤 ̇ } {C : 𝓦 ̇ }
   (f : A → C) (c : C)
 → is-pullback f (λ (_ : 𝟙 {𝓥}) → c)
    (fiber f c ,
     ((fiber-point , unique-to-𝟙) , fiber-identification))
fiber-is-pullback f c X = qinvs-are-equivs ϕ (γ , (λ u → refl) , (λ c → refl))
 where
  ϕ : (X → fiber f c) → cone f (λ _ → c) X
  ϕ = cone-map f (λ _ → c) X ((fiber-point , unique-to-𝟙) , fiber-identification)

  γ : cone f (λ _ → c) X → X → fiber f c
  γ ((p , q) , s) x = p x , s x

\end{code}
