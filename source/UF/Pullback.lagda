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
open import UF.Embeddings
open import UF.Equiv
open import UF.Subsingletons

\end{code}

We assume a cospan

                 Y
                 |
                 | g
                 |
                 v
      X -------> C
           f

\begin{code}

module pullback
        {𝓤 𝓥 𝓦 : Universe}
        {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
        (f : X → Z) (g : Y → Z)
       where

\end{code}

And we consider commutative squares of the form

           q
      A -------> X
      |          |
    p |          | g
      |          |
      v          v
      Y -------> Z
            f

completing the cospan.

\begin{code}

 commutative-square : {A : 𝓣 ̇ } → (A → X) × (A → Y) → 𝓦 ⊔ 𝓣 ̇
 commutative-square (p , q) = f ∘ p ∼ g ∘ q

\end{code}

A cone over the cospan is the totality of these data.

\begin{code}

 cone : 𝓣 ̇ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 cone A = Σ pq ꞉ ((A → X) × (A → Y)) , commutative-square pq

\end{code}

It is convenient to collect all cones in a universe into a single
type.

\begin{code}

 Cone : (𝓣 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ (𝓣 ⁺) ̇
 Cone 𝓣 = Σ A ꞉ 𝓣 ̇ , cone A

 source : Cone 𝓣 → 𝓣 ̇
 source (P , c) = P

 cone-of : (𝓒 : Cone 𝓣) → cone (source 𝓒)
 cone-of (P , c) = c

\end{code}

If we have a cone

            q
      P -------> Y
      |          |
    p |          | g
      |          |
      v          v
      X -------> Z
            f

and a map u : A → P, we get a cone

          q ∘ u
      A -------> Y
      |          |
p ∘ u |          | g
      |          |
      v          v
      X -------> Z
            f

\begin{code}

 cone-map : {P : 𝓣' ̇ } (A : 𝓣 ̇ ) → cone P → (A → P) → cone A
 cone-map X ((p , q) , e) u = (p ∘ u , q ∘ u) , e ∘ u

\end{code}

We say that a cone

            q
      P -------> Y
      |          |
    p |          | g
      |          |
      v          v
      X -------> Z
            f

is a (homotopy) pullback if the cone map is an equivalence for every A.

\begin{code}

 is-pullback : Cone 𝓣 → 𝓤ω
 is-pullback (P , c) = {𝓣' : Universe} (A : 𝓣' ̇ ) → is-equiv (cone-map A c)

\end{code}

We record the equivalence explicitly.

\begin{code}

 module _ (𝓒@(P , c@((p₁ , p₂) , s)) : Cone 𝓣)
          (i : is-pullback 𝓒)
        where

  pullback-equivalence : (A : 𝓣' ̇ ) → (A → P) ≃ cone A
  pullback-equivalence A = cone-map A c , i A

\end{code}

And we can formulate the universal property of pullbacks in terms of
(homotopy) unique existence.

\begin{code}

  module _ (𝓓@(A , d@((h₁ , h₂) , t)) : Cone 𝓣') where

   universal-property
    : ∃! u ꞉ (A → P) , ((p₁ ∘ u , p₂ ∘ u) , s ∘ u) ＝ ((h₁ , h₂) , t)
   universal-property
    = equivs-are-vv-equivs (cone-map A c) (i A) d

\end{code}

It is convenient to name the uniquely existing u as the "mediating
map", and record the equations it satisfies.

\begin{code}

   mediating-map : (A → P)
   mediating-map = pr₁ (center universal-property)

   _ : mediating-map ＝ ⌜ pullback-equivalence A ⌝⁻¹ d
   _ = refl

   mediating-map-eq₁ : p₁ ∘ mediating-map ＝ h₁
   mediating-map-eq₁ = ap (pr₁ ∘ pr₁) (pr₂ (center universal-property))

   mediating-map-eq₂ : p₂ ∘ mediating-map ＝ h₂
   mediating-map-eq₂ = ap (pr₂ ∘ pr₁) (pr₂ (center universal-property))

\end{code}

We now show that pullbacks exist, and call them simply pullbacks,
although perhaps we should call them standard pullbacks, or chosen
pullbacks.

The construction is illustrated in the following diagram.

                                   pb₂
 Σ (x , y) ꞉ X × Y , f x ＝ g y  -------> Y
           |                              |
      pb₁  |                              | g
           |                              |
           v                              v
           X ---------------------------> Z
                                   f
\begin{code}

 pullback : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 pullback = Σ (x , y) ꞉ X × Y , f x ＝ g y

 private
  P = pullback

 pb₁ : P → X
 pb₁ ((x , y) , s) = x

 pb₂ : P → Y
 pb₂ ((x , y) , s) = y

 pullback-square : commutative-square (pb₁ , pb₂)
 pullback-square ((x , y) , s) = s

 pullback-cone : cone P
 pullback-cone = ((pb₁ , pb₂) , pullback-square)

 Pullback-Cone : Cone (𝓤 ⊔ 𝓥 ⊔ 𝓦)
 Pullback-Cone = P , pullback-cone

 pullback-cone-map : (A : 𝓣' ̇ ) → (A → P) → cone A
 pullback-cone-map A = cone-map A pullback-cone

 pullback-mediating-map : {A : 𝓣 ̇ } → cone A → (A → P)
 pullback-mediating-map ((p , q) , s) a = (p a , q a) , s a

 pullback-Cone-is-pullback : is-pullback Pullback-Cone
 pullback-Cone-is-pullback A =
  qinvs-are-equivs
   (pullback-cone-map A)
   (pullback-mediating-map , (λ u → refl) , (λ c → refl))

 _ : (A : 𝓣' ̇ ) (c : cone A)
   → pullback-mediating-map c
   ＝ mediating-map Pullback-Cone pullback-Cone-is-pullback (A , c)
 _ = λ A c → refl

\end{code}

Pullbacks of embeddings are embeddings.

\begin{code}

 pb₂-is-embedding : is-embedding f → is-embedding pb₂
 pb₂-is-embedding f-is-embedding y = I
   where
    I : is-prop (fiber pb₂ y)
    I (((x₁ , y) , e₁) , refl) (((x₂ , y) , e₂) , refl) = III II
     where
      II : (x₁ , e₁) ＝ (x₂ , e₂)
      II = f-is-embedding (g y) (x₁ , e₁) (x₂ , e₂)

      III : {(x₁ , e₁) (x₂ , e₂) : fiber f (g y)}
          → (x₁ , e₁) ＝ (x₂ , e₂)
          → (((x₁ , y) , e₁) , refl) ＝[ fiber pb₂ y ] (((x₂ , y) , e₂) , refl)
      III refl = refl

\end{code}

We have a pullback

           fiber f c ----> 𝟙
              |            |
  fiber-point |            | c
              |            |
              v            v
              X ---------> Z
                     f

\begin{code}

module _ {𝓤 𝓥 𝓦 : Universe}
         {X : 𝓤 ̇ }
         {Z : 𝓦 ̇ }
         (f : X → Z)
         (z : Z)
       where

 open pullback f (λ (_ : 𝟙 {𝓥}) → z)

 fiber-is-pullback
  : is-pullback (fiber f z , (fiber-point , unique-to-𝟙) , fiber-identification)
 fiber-is-pullback A
  = qinvs-are-equivs ϕ (γ , (λ u → refl) , (λ c → refl))
  where
   ϕ : (A → fiber f z) → cone A
   ϕ = cone-map A ((fiber-point , unique-to-𝟙) , fiber-identification)

   γ : cone A → (A → fiber f z)
   γ ((p , q) , s) a = p a , s a

\end{code}

TODO. Implement other results from [1].
