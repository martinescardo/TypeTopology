Martin Escardo, 17 May 2018,
while visiting the Hausdorff Research Institute for Mathematics in Bonn

This is an "improvement method" I learned from Peter Lumsdaine, 7th
July 2017 at the Newton Institute in Cambridge, adapted from an Agda
rendering by Andy Pitts of Peter's Coq code from 14th October 2015.

Given an identity system (Id, refl , J) with no given "computation
rule" for J, Peter produces another identity system (Id, refl , J' ,
J'-comp) with a "propositional computation rule" J'-comp for J'.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import Universes

module Lumsdaine
        {𝓤}
        (Id : ∀ {X : 𝓤 ̇ } → X → X → 𝓤 ̇ )
        (refl : ∀ {X : 𝓤 ̇ } {x : X} → Id x x)
        (J : ∀ {X : 𝓤 ̇ } (x : X) (A : (y : X) → Id x y → 𝓤 ̇ )
           → A x refl → (y : X) (p : Id x y) → A y p)
        where

private
  record Σ {𝓤 𝓥 } {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
   constructor _,_
   field
    pr₁ : X
    pr₂ : Y pr₁

  open Σ

  Sigma : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  Sigma X Y = Σ Y

  syntax Sigma A (λ x → b) = Σ x ꞉ A , b

  infixr -1 Sigma

  id : {X : 𝓤 ̇ }  → X → X
  id x = x

  lc-maps : (X Y : 𝓤 ̇ ) → 𝓤 ̇
  lc-maps X Y = Σ f ꞉ (X → Y) , ({x x' : X} → Id (f x) (f x') → Id x x')

  id-lc-maps : {X : 𝓤 ̇ } → lc-maps X X
  id-lc-maps = (id , id)

module _ {X : 𝓤 ̇ }
         {x : X}
         (A : (y : X) → Id x y → 𝓤 ̇ )
 where
  private
    g : {t z : X} (p : Id x t) (q : Id x z) → lc-maps (A t p) (A z q)
    g {t} {z} p q = J x B (J x C id-lc-maps t p) z q
     where
      B : (y : X) → Id x y → 𝓤 ̇
      B y q = lc-maps (A t p) (A y q)
      C : (y : X) → Id x y → 𝓤 ̇
      C y p = lc-maps (A y p ) (A x refl)

    h : (b : A x refl) {y : X} (p : Id x y)
      → Σ x ꞉ A y p , Id (pr₁ (g p p) x) (pr₁ (g refl p) b)
    h b {y} p = J x B (b , refl) y p
     where
      B : (y : X) (p : Id x y) → 𝓤 ̇
      B y p = Σ x ꞉ A y p , Id (pr₁ (g p p) x) (pr₁ (g refl p) b)

  J' : A x refl → (y : X) (p : Id x y) → A y p
  J' b y p = pr₁ (h b p)

  J'-comp : (b : A x refl) → Id (J' b x refl) b
  J'-comp b = pr₂ (g refl refl) (pr₂ (h b refl))

\end{code}
