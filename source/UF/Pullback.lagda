Martin Escardo, 23rd May 2025.

Pullbacks.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Pullback where

open import MLTT.Spartan
open import UF.Equiv

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
      |          v
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

If we have a cone

            q
      P -------> B
      |          |
    p |          | g
      |          |
      |          v
      A -------> C
            f

and a map u : X → P, we get a cone

          q ∘ u
      X -------> B
      |          |
p ∘ u |          | g
      |          |
      |          v
      A -------> C
            f

\begin{code}

 cone-map : (P : 𝓣' ̇ ) (X : 𝓣 ̇ ) → cone P → (X → P) → cone X
 cone-map P X (p , q , e) u = p ∘ u , q ∘ u , e ∘ u

\end{code}

We say that a cone

            q
      P -------> B
      |          |
    p |          | g
      |          |
      |          v
      A -------> C
            f

is a (homotopy) pullback if this map is an equivalence for every X.

\begin{code}

 is-pullback : (P : 𝓣 ̇ ) → cone P → 𝓤ω
 is-pullback P c = {𝓣' : Universe} (X : 𝓣' ̇ ) → is-equiv (cone-map P X c)

\end{code}

We now show that pullbacks exist.

\begin{code}

 standard-pullback : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 standard-pullback = Σ x ꞉ A , Σ y ꞉ B , f x ＝ g y

 pb₁ : standard-pullback → A
 pb₁ (x , y , e) = x

 pb₂ : standard-pullback → B
 pb₂ (x , y , e) = y

 pb-square : commutative-square pb₁ pb₂
 pb-square (x , y , e) = e

 standard-pullback-cone : cone standard-pullback
 standard-pullback-cone = (pb₁ , pb₂ , pb-square)

 standard-pullback-map : (X : 𝓣' ̇ ) → (X → standard-pullback) → cone X
 standard-pullback-map X = cone-map standard-pullback X standard-pullback-cone

 standard-pullback-is-pullback : is-pullback standard-pullback standard-pullback-cone
 standard-pullback-is-pullback X = γ
  where
   standard-pullback-map⁻¹ : cone X → (X → standard-pullback)
   standard-pullback-map⁻¹ (p , q , s) x = p x , q x , s x

   η : standard-pullback-map⁻¹ ∘ standard-pullback-map X ∼ id
   η x = refl

   ε : standard-pullback-map X ∘ standard-pullback-map⁻¹ ∼ id
   ε c = refl

   γ : is-equiv (standard-pullback-map X)
   γ = qinvs-are-equivs
        (standard-pullback-map X)
        (standard-pullback-map⁻¹ , η , ε)

\end{code}
