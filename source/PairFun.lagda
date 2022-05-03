Martin Escardo 2011

Combining two functions to get a function Σ A → Σ B, and properties of
the resulting function.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module PairFun where

open import SpartanMLTT
open import Density

open import UF-Subsingletons
open import UF-Equiv
open import UF-Embeddings

module _ {𝓤 𝓥 𝓦 𝓣}
         {X : 𝓤 ̇ }
         {A : X → 𝓥 ̇ }
         {Y : 𝓦 ̇ }
         {B : Y → 𝓣 ̇ }
         (f : X → Y)
         (g : (x : X) → A x → B (f x))
       where

 pair-fun : Σ A → Σ B
 pair-fun (x , a) = (f x , g x a)

 pair-fun-fiber' : (y : Y) → B y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 pair-fun-fiber' y b = Σ (x , a) ꞉ fiber f y , fiber (g x) (transport⁻¹ B a b)

 pair-fun-fiber-≃ : (y : Y) (b : B y)
                  → fiber pair-fun (y , b)
                  ≃ pair-fun-fiber' y b
 pair-fun-fiber-≃  y b = qinveq φ (γ , γφ , φγ)
  where
   φ : fiber pair-fun (y , b) → pair-fun-fiber' y b
   φ ((x , a) , refl) = (x , refl) , (a , refl)

   γ : pair-fun-fiber' y b → fiber pair-fun (y , b)
   γ ((x , refl) , (a , refl)) = (x , a) , refl

   γφ : (t : fiber pair-fun (y , b)) → γ (φ t) ≡ t
   γφ ((x , a) , refl) = refl

   φγ : (s : pair-fun-fiber' y b) → φ (γ s) ≡ s
   φγ ((x , refl) , (a , refl)) = refl


 pair-fun-is-embedding : is-embedding f
                       → ((x : X) → is-embedding (g x))
                       → is-embedding pair-fun
 pair-fun-is-embedding e d (y , b) = h
  where
   i : is-prop (pair-fun-fiber' y b)
   i = subtype-of-prop-is-prop
        pr₁
        (pr₁-lc (λ {w} → d (pr₁ w) (transport⁻¹ B (pr₂ w) b)))
        (e y)

   h : is-prop (fiber pair-fun (y , b))
   h = equiv-to-prop (pair-fun-fiber-≃ y b) i

 pair-fun-is-vv-equiv : is-vv-equiv f
                      → ((x : X) → is-vv-equiv (g x))
                      → is-vv-equiv pair-fun
 pair-fun-is-vv-equiv e d (y , b) = h
  where
   k : is-prop (fiber pair-fun (y , b))
   k = pair-fun-is-embedding
        (equivs-are-embeddings f (vv-equivs-are-equivs f e))
        (λ x → equivs-are-embeddings (g x) (vv-equivs-are-equivs (g x) (d x)))
        (y , b)

   x : X
   x = fiber-point (center (e y))

   i : f x ≡ y
   i = fiber-identification (center (e y))

   w : pair-fun-fiber' y b
   w = (center (e y) , center (d x (transport⁻¹ B i b)))

   h : is-singleton (fiber pair-fun (y , b))
   h = pointed-props-are-singletons (⌜ pair-fun-fiber-≃ y b ⌝⁻¹ w) k

 pair-fun-is-equiv : is-equiv f
                   → ((x : X) → is-equiv (g x))
                   → is-equiv pair-fun
 pair-fun-is-equiv e d = vv-equivs-are-equivs pair-fun
                          (pair-fun-is-vv-equiv
                            (equivs-are-vv-equivs f e)
                            (λ x → equivs-are-vv-equivs (g x) (d x)))

 pair-fun-dense : is-dense f
                → ((x : X) → is-dense (g x))
                → is-dense pair-fun
 pair-fun-dense i j = contrapositive γ i
  where
   γ : (Σ w ꞉ Σ B , ¬ fiber pair-fun w) → Σ y ꞉ Y , ¬ fiber f y
   γ ((y , b) , n) = y , m
    where
     m : ¬ fiber f y
     m (x , refl) = j x (b , l)
      where
       l : ¬ fiber (g x) b
       l (a , refl) = n ((x , a) , refl)

 open import UF-PropTrunc
 open import UF-ImageAndSurjection

 module pair-fun-surjection (pt : propositional-truncations-exist) where

  open PropositionalTruncation pt
  open ImageAndSurjection pt

  pair-fun-is-surjection : is-surjection f
                         → ((x : X) → is-surjection (g x))
                         → is-surjection pair-fun
  pair-fun-is-surjection s t (y , b) = γ
   where
    γ : ∃ (x , a) ꞉ Σ A , (pair-fun (x , a) ≡ y , b)
    γ = ∥∥-rec ∃-is-prop
         (λ {(x , refl) → ∥∥-rec ∃-is-prop
                           (λ {(a , refl) → ∣ (x , a) , refl ∣})
                           (t x b)})
         (s y)

\end{code}
