Martin Escardo, 17 May 2018,
while visiting the Hausdorff Research Institute for Mathematics in Bonn

This is an "improvement method" I learned from Peter Lumsdaine, 7th
July 2017 at the Newton Institute in Cambridge, adapted from an Agda
rendering by Andy Pitts of Peter's Coq code from 14th October 2015.

Given an identity system (Id, refl , J) with no given "computation
rule" for J, Peter produces another identity system (Id, refl , J' ,
J'-comp) with a "propositional computation rule" J'-comp for J'.

\begin{code}

open import Universes

module Lumsdaine
        {U}
        (Id : ∀ {X : U ̇} → X → X → U ̇)
        (refl : ∀ {X : U ̇} {x : X} → Id x x)
        (J : ∀ {X : U ̇} (x : X) (A : (y : X) → Id x y → U ̇)
           → A x refl → (y : X) (p : Id x y) → A y p)
        where

private
  record Σ {U V : Universe} {X : U ̇} (Y : X → V ̇) : U ⊔ V ̇ where
   constructor _,_
   field
    pr₁ : X
    pr₂ : Y pr₁

  open Σ

  id : ∀ {U} {X : U ̇}  → X → X
  id x = x

  lc-maps : (X Y : U ̇) → U ̇ 
  lc-maps X Y = Σ \(f : X → Y) → {x x' : X} → Id (f x) (f x') → Id x x'

  id-lc-maps : {X : U ̇} → lc-maps X X
  id-lc-maps = (id , id)

module _ {X : U ̇}
         {x : X}
         (A : (y : X) → Id x y → U ̇)
 where
  private
    g : {t z : X} (p : Id x t) (q : Id x z) → lc-maps (A t p) (A z q)
    g {t} {z} p q = J x A' (J x Z id-lc-maps t p) z q
     where
      A' : (y : X) → Id x y → U ̇
      A' y q = lc-maps (A t p) (A y q)
      Z : (y : X) → Id x y → U ̇
      Z y p = lc-maps (A y p ) (A x refl) 
  
    h : (b : A x refl) {y : X} (p : Id x y)
      → Σ \(x : A y p) → Id (pr₁ (g p p) x) (pr₁ (g refl p) b)
    h b {y} p = J x A' (b , refl) y p
     where
      A' : (y : X) (p : Id x y) → U ̇
      A' y p = Σ \(x : A y p) → Id (pr₁ (g p p) x) (pr₁ (g refl p) b)
  
  J' : A x refl → (y : X) (p : Id x y) → A y p
  J' b y p = pr₁ (h b p)
  
  J'-comp : (b : A x refl) → Id (J' b x refl) b
  J'-comp b = pr₂ (g refl refl) (pr₂ (h b refl))
  
\end{code}
