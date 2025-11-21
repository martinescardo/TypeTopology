Nicolai Kraus 2012.

This is adapted to our TypeTopology development by Martin Escardo, but
we keep Nicolai's original proof.

The main result is that the type of fixed-points of a weakly constant
endomap is a proposition, in pure MLTT without HoTT/UF extensions.

1. Nicolai Kraus, Martín Escardó, Thierry Coquand & Thorsten Altenkirch.
   Generalizations of Hedberg’s Theorem.
   TLCA 2013
   https://doi.org/10.1007/978-3-642-38946-7_14

2. Nicolai Kraus, Martín Escardó, Thierry Coquand & Thorsten Altenkirch.
   Notions of Anonymous Existence in Martin-Löf Type Theory.
   Logical Methods in Computer Science, March 24, 2017, Volume 13, Issue 1.
   https://doi.org/10.23638/LMCS-13(1:15)2017

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.KrausLemma where

open import MLTT.Spartan
open import UF.Base
open import UF.Hedberg
open import UF.Subsingletons

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

fix-is-prop : {X : 𝓤 ̇ } (f : X → X) → wconstant f → is-prop (fix f)
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
         s ⁻¹ ∙ p'                 ＝⟨refl⟩
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
