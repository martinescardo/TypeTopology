Martin Escardo, 23rd May 2025.

Pullbacks.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Pullback where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Subsingletons

\end{code}

We assume a span

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

completing the span.

\begin{code}

 commutative-square : {X : 𝓣 ̇ } → (X → A) → (X → B) → 𝓦 ⊔ 𝓣 ̇
 commutative-square p q = f ∘ p ∼ g ∘ q

\end{code}

A cone over the span is the totality of these data.

\begin{code}

 cone : 𝓣 ̇ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 cone X = Σ p ꞉ (X → A) , Σ q ꞉ (X → B) , commutative-square p q

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
 cone-map X (p , q , e) u = p ∘ u , q ∘ u , e ∘ u

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

is a (homotopy) pullback if this map is an equivalence for every X.

\begin{code}

 is-pullback : Cone 𝓣 → 𝓤ω
 is-pullback (P , c) = {𝓣' : Universe} (X : 𝓣' ̇ ) → is-equiv (cone-map X c)

 pullback-equivalence : (𝓒 : Cone 𝓣)
                      → is-pullback 𝓒
                      → (X : 𝓣' ̇ ) → (X → source 𝓒) ≃ cone X
 pullback-equivalence (P , c) i X = cone-map X c , i X

 mediating-map : (𝓒 : Cone 𝓣)
               → is-pullback 𝓒
               → (X : 𝓣' ̇ ) → cone X → (X → source 𝓒)
 mediating-map 𝓒 i X = ⌜ pullback-equivalence 𝓒 i X ⌝⁻¹

\end{code}

We now show that pullbacks exist, and call them simply pullbacks,
although perhaps we should call them standard pullbacks, or chosen
pullbacks.

\begin{code}

 pullback-source : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 pullback-source = Σ a ꞉ A , Σ b ꞉ B , f a ＝ g b

 private
  P = pullback-source

\end{code}

We denote the pullback projections by pb₁ and pb₂.

\begin{code}

 pb₁ : P → A
 pb₁ (a , b , e) = a

 pb₂ : P → B
 pb₂ (a , b , e) = b

 pullback-square : commutative-square pb₁ pb₂
 pullback-square (a , b , e) = e

 pullback-cone : cone P
 pullback-cone = (pb₁ , pb₂ , pullback-square)

 Pullback-Cone : Cone (𝓤 ⊔ 𝓥 ⊔ 𝓦)
 Pullback-Cone = P , pullback-cone

 pullback-cone-map : (X : 𝓣' ̇ ) → (X → P) → cone X
 pullback-cone-map X = cone-map X pullback-cone

 pullback-mediating-map : {X : 𝓣 ̇ } → cone X → (X → P)
 pullback-mediating-map (p , q , s) x = p x , q x , s x

 pullback-Cone-is-pullback : is-pullback Pullback-Cone
 pullback-Cone-is-pullback X =
  qinvs-are-equivs
   (pullback-cone-map X)
   (pullback-mediating-map , (λ x → refl) , (λ c → refl))

\end{code}
