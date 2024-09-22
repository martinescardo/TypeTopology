Nicolai Kraus 2012.

This is adapted to our TypeTopology development by Martin Escardo, but
we keep Nicolai's original proof.

The main result is that the type of fixed-points of a weakly constant
endomap is a proposition, in pure MLTT without HoTT/UF extensions.

We also add some consequences obtained in joint work with Martin
Escardo, Thierry Coquand, and Thorsten Altenkirch.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.KrausLemma where

open import MLTT.Spartan
open import UF.Base
open import UF.Hedberg
open import UF.Subsingletons

fix : {X : 𝓤 ̇ } → (f : X → X) → 𝓤 ̇
fix f = Σ x ꞉ domain f , x ＝ f x

key-lemma : {X Y : 𝓤 ̇ } (f : X → Y) (g : wconstant f) {x y : X} (p : x ＝ y)
          → ap f p ＝ (g x x)⁻¹ ∙ g x y
key-lemma f g {x} refl = sym-is-inverse (g x x)

key-insight : {X Y : 𝓤 ̇ } (f : X → Y)
            → wconstant f
            → {x : X} (p : x ＝ x) → ap f p ＝ refl
key-insight f g p = key-lemma f g p ∙ (sym-is-inverse (g _ _))⁻¹

transport-ids-along-ids
 : {X Y : 𝓤 ̇ }
   {x y : X}
   (p : x ＝ y)
   (h k : X → Y)
   (q : h x ＝ k x)
 → transport (λ - → h - ＝ k -) p q ＝ (ap h p)⁻¹ ∙ q ∙ ap k p
transport-ids-along-ids refl h k q = refl-left-neutral ⁻¹

transport-ids-along-ids'
 : {X : 𝓤 ̇ }
   {x : X}
   (p : x ＝ x)
   (f : X → X)
   (q : x ＝ f x)
 → transport (λ - → - ＝ f -) p q ＝ (p ⁻¹ ∙ q) ∙ ap f p
transport-ids-along-ids' {𝓤} {X} {x} p f q = γ
 where
  g : x ＝ x → x ＝ f x
  g r = r ⁻¹ ∙ q ∙ (ap f p)

  γ : transport (λ - → - ＝ f -) p q ＝ p ⁻¹ ∙ q ∙ ap f p
  γ = transport-ids-along-ids p id f q ∙ ap g ((ap-id-is-id' p)⁻¹)

\end{code}

The following is what we refer to as Kraus Lemma:

\begin{code}

fix-is-prop : {X : 𝓤 ̇ } → (f : X → X) → wconstant f → is-prop (fix f)
fix-is-prop {𝓤} {X} f g (x , p) (y , q) =
  (x , p)  ＝⟨ to-Σ-＝ (r , refl) ⟩
  (y , p') ＝⟨ to-Σ-＝ (s , t) ⟩
  (y , q)  ∎
    where
     r : x ＝ y
     r = x   ＝⟨ p ⟩
         f x ＝⟨ g x y ⟩
         f y ＝⟨ q ⁻¹ ⟩
           y ∎

     p' : y ＝ f y
     p' = transport (λ - → - ＝ f -) r p

     s : y ＝ y
     s = y   ＝⟨ p' ⟩
         f y ＝⟨ q ⁻¹ ⟩
         y   ∎

     q' : y ＝ f y
     q' = transport (λ - → - ＝ f -) s p'

     t : q' ＝ q
     t = q'                        ＝⟨ I ⟩
         (s ⁻¹ ∙ p') ∙ ap f s      ＝⟨ II ⟩
         s ⁻¹ ∙ (p' ∙ ap f s)      ＝⟨ III ⟩
         s ⁻¹ ∙ (p' ∙ refl)        ＝⟨ IV ⟩
         s ⁻¹ ∙ p'                 ＝⟨ refl ⟩
        (p' ∙ (q ⁻¹))⁻¹ ∙ p'       ＝⟨ V ⟩
        ((q ⁻¹)⁻¹ ∙ (p' ⁻¹)) ∙ p'  ＝⟨ VI ⟩
        (q ∙ (p' ⁻¹)) ∙ p'         ＝⟨ VII ⟩
         q ∙ ((p' ⁻¹) ∙ p')        ＝⟨ VIII ⟩
         q ∙ refl                  ＝⟨ IX ⟩
         q                         ∎
          where
           I    = transport-ids-along-ids' s f p'
           II   = ∙assoc (s ⁻¹) p' (ap f s)
           III  = ap (λ - → s ⁻¹ ∙ (p' ∙ -)) (key-insight f g s)
           IV   = ap (λ - → s ⁻¹ ∙ -) ((refl-right-neutral p')⁻¹)
           V    = ap (λ - → - ∙ p') ((⁻¹-contravariant p' (q ⁻¹))⁻¹)
           VI   = ap (λ - → (- ∙ (p' ⁻¹)) ∙ p') (⁻¹-involutive q)
           VII  = ∙assoc q (p' ⁻¹) p'
           VIII = ap (λ - → q ∙ -) ((sym-is-inverse p')⁻¹)
           IX   = (refl-right-neutral q)⁻¹
\end{code}

A main application is to show that, in pure spartan MLTT, if a type
has a wconstant endfunction then it has a propositional truncation.

\begin{code}

from-fix : {X : 𝓤 ̇ } (f : X → X) → fix f → X
from-fix f = pr₁

from-fix-is-fixed : {X : 𝓤 ̇ } (f : X → X) (φ : fix f)
                  → from-fix f φ ＝ f (from-fix f φ)
from-fix-is-fixed f = pr₂

to-fix : {X : 𝓤 ̇ } (f : X → X) → wconstant f → X → fix f
to-fix f g x = (f x , g x (f x))

from-to-fix : {X : 𝓤 ̇ } (f : X → X) (κ : wconstant f)
            → from-fix f ∘ to-fix f κ ∼ f
from-to-fix f κ w = refl

to-from-fix : {X : 𝓤 ̇ } (f : X → X) (κ : wconstant f)
            → to-fix f κ ∘ from-fix f ∼ id
to-from-fix f κ _ = fix-is-prop f κ _ _

has-split-support' : 𝓤 ̇ → 𝓤 ⁺ ̇
has-split-support' {𝓤} X = Σ P ꞉ 𝓤 ̇ , is-prop P × (X ↔ P)

fix-has-split-support' : {X : 𝓤 ̇ }
                       → collapsible X
                       → has-split-support' X
fix-has-split-support' {𝓤} {X} (f , κ) = fix f , fix-is-prop f κ , to-fix f κ , from-fix f

has-prop-truncation : (𝓥 : Universe) → 𝓤 ̇ → (𝓤 ⊔ 𝓥)⁺ ̇
has-prop-truncation {𝓤} 𝓥 X = Σ X' ꞉ 𝓤 ̇ , is-prop X'
                                        × (X → X')
                                        × ((P : 𝓥 ̇ ) → is-prop P → (X → P) → X' → P)

split-truncation : {X : 𝓤 ̇ } → has-split-support' X → ∀ 𝓥 → has-prop-truncation 𝓥 X
split-truncation {𝓤} {X} (X' , i , f , g) V = X' , i , f , λ P j h x' → h (g x')

collapsible-has-prop-truncation : {X : 𝓤 ̇ }
                                → collapsible X
                                → ∀ 𝓥 → has-prop-truncation 𝓥 X
collapsible-has-prop-truncation {𝓤} {X} c = split-truncation (fix-has-split-support' c)

open import UF.PropTrunc

module split-support-and-collapsibility (pe : propositional-truncations-exist) where

 open PropositionalTruncation pe

 has-split-support : 𝓤 ̇ → 𝓤 ̇
 has-split-support X = ∥ X ∥ → X

 has-split-support→ : {X : 𝓤 ̇ } → has-split-support X → has-split-support' X
 has-split-support→ {𝓤} {X} f = ∥ X ∥ , ∥∥-is-prop , (λ x → ∣ x ∣) , f

 has-split-support← : {X : 𝓤 ̇ } → has-split-support' X → has-split-support X
 has-split-support← {𝓤} {X} (P , P-is-prop , g , f) = f ∘ ∥∥-rec P-is-prop g

\end{code}

TODO: Are the above two functions mutually inverse and hence we get an
equivalence?

\begin{code}

 collapsible-gives-split-support : {X : 𝓤 ̇ }
                                 → collapsible X
                                 → has-split-support X
 collapsible-gives-split-support {𝓤} {X} (f , κ) s = x
  where
   g : ∥ X ∥ → fix f
   g = ∥∥-rec (fix-is-prop f κ) (to-fix f κ)

   x : X
   x = from-fix f (g s)

 exit-prop-trunc : {X : 𝓤 ̇ }
                 → (f : X → X)
                 → wconstant f
                 → ∥ X ∥ → X
 exit-prop-trunc f κ = collapsible-gives-split-support (f , κ)

 exit-prop-trunc-is-fixed : {X : 𝓤 ̇ }
                            (f : X → X)
                            (κ : wconstant f)
                            (s : ∥ X ∥)
                          → f (exit-prop-trunc f κ s) ＝ exit-prop-trunc f κ s
 exit-prop-trunc-is-fixed f κ s =
  (from-fix-is-fixed f (∥∥-rec (fix-is-prop f κ) (to-fix f κ) s))⁻¹

 split-support-gives-collapsible : {X : 𝓤 ̇ }
                                 → has-split-support X
                                 → collapsible X
 split-support-gives-collapsible {𝓤} {X} g = γ
  where
   f : X → X
   f x = g ∣ x ∣

   κ : (x y : X) → f x ＝ f y
   κ x y = ap g (∥∥-is-prop ∣ x ∣ ∣ y ∣)

   γ : collapsible X
   γ = f , κ

\end{code}
