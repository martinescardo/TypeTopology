Nicolai kraus, 2012

Adapted to our development.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-KrausLemma where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons

fix : ∀ {U} {X : U ̇} → (f : X → X) → U ̇
fix f = Σ \x → x ≡ f x

key-lemma : ∀ {U} {X Y : U ̇} (f : X → Y) (g : constant f) {x y : X} (p : x ≡ y) 
         → ap f p ≡ (g x x)⁻¹ ∙ g x y
key-lemma f g {x} refl = sym-is-inverse (g x x) 

key-insight : ∀ {U} {X Y : U ̇} (f : X → Y) → constant f → {x : X} (p : x ≡ x) → ap f p ≡ refl
key-insight f g p = key-lemma f g p ∙ (sym-is-inverse(g _ _))⁻¹

transport-paths-along-paths : ∀ {U} {X Y : U ̇} {x y : X} (p : x ≡ y) (h k : X → Y) (q : h x ≡ k x) 
                           → transport (λ x → h x ≡ k x) p q ≡ (ap h p)⁻¹ ∙ q ∙ ap k p
transport-paths-along-paths refl h k q = refl-left-neutral ⁻¹

transport-paths-along-paths' : ∀ {U} {X : U ̇} {x : X} (p : x ≡ x) (f : X → X) (q : x ≡ f x) 
                            → transport (λ x → x ≡ f x) p q ≡ (p ⁻¹ ∙ q) ∙ ap f p
transport-paths-along-paths'  p f q = transport-paths-along-paths p id f q
                                    ∙ ap (λ pr → pr ⁻¹ ∙ q ∙ (ap f p)) ((ap-id-is-id p)⁻¹)

Kraus-Lemma : ∀ {U} {X : U ̇} → (f : X → X) → constant f → isProp(fix f)
Kraus-Lemma {U} {X} f g (x , p) (y , q) = 
  -- p : x ≡ f x
  -- q : y ≡ f y
  (x , p)        ≡⟨ to-Σ-≡ x y p p' r refl ⟩
  (y , p')       ≡⟨ to-Σ-≡ y y p' q s t ⟩           
  (y , q) ∎
    where
     r : x ≡ y
     r = x ≡⟨ p ⟩
       f x ≡⟨ g x y ⟩
       f y ≡⟨ q ⁻¹ ⟩
         y ∎
     p' : y ≡ f y
     p' = transport (λ x → x ≡ f x) r p
     s : y ≡ y
     s = y   ≡⟨ p' ⟩
         f y ≡⟨ q ⁻¹ ⟩
         y   ∎
     q' : y ≡ f y
     q' = transport (λ y → y ≡ f y) s p'
     t : q' ≡ q
     t = q'                        ≡⟨ transport-paths-along-paths' s f p' ⟩
         (s ⁻¹ ∙ p') ∙ ap f s      ≡⟨ assoc (s ⁻¹) p' (ap f s) ⟩
         s ⁻¹ ∙ (p' ∙ ap f s)      ≡⟨ ap (λ pr → s ⁻¹ ∙ (p' ∙ pr)) (key-insight f g s) ⟩
         s ⁻¹ ∙ (p' ∙ refl)        ≡⟨ ap (λ pr → s ⁻¹ ∙ pr) ((refl-right-neutral p')⁻¹) ⟩ 
         s ⁻¹ ∙ p'                 ≡⟨ refl ⟩ 
        (p' ∙ (q ⁻¹))⁻¹ ∙ p'       ≡⟨ ap (λ pr → pr ∙ p') ((⁻¹-contravariant p' (q ⁻¹))⁻¹) ⟩
        ((q ⁻¹)⁻¹ ∙ (p' ⁻¹)) ∙ p'  ≡⟨ ap (λ pr → (pr ∙ (p' ⁻¹)) ∙ p') (⁻¹-involutive q) ⟩
        (q ∙ (p' ⁻¹)) ∙ p'         ≡⟨ assoc q (p' ⁻¹) p' ⟩
         q ∙ ((p' ⁻¹) ∙ p')        ≡⟨ ap (λ pr → q ∙ pr) ((sym-is-inverse p')⁻¹) ⟩
         q ∙ refl                  ≡⟨ (refl-right-neutral q)⁻¹ ⟩
         q  ∎

from-fix : ∀ {U} {X : U ̇} (f : X → X) → fix f → X
from-fix f = pr₁

to-fix : ∀ {U} {X : U ̇} (f : X → X) → constant f → X → fix f
to-fix f g x = (f x , g x (f x))

\end{code}
