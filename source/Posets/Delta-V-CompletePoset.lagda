Ian Ray, 25 July 2023.

Formalizing the auxilary notion of a delta-V-complete poset which is
sufficient for the main theorems of *link Tom de Jong's thesis*
involving impredicativity (in the form of resizing axioms) and order theory.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.FunExt
open import UF.PropTrunc
open import UF.Logic

open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Posets.Delta-V-CompletePoset
 (pt : propositional-truncations-exist)
 (fe : Fun-Ext)
  where

open import Locales.Frame pt fe

open import Posets.2ElementPoset pt fe

module δ_𝓥-complete-poset {𝓤 𝓦 : Universe} (𝓥 : Universe) (A : Poset 𝓤 𝓦) where
 δ : (x y : ∣ A ∣ₚ) → (P : Ω 𝓥) → (𝟙{𝓥} + P holds) → ∣ A ∣ₚ 
 δ x y P (inl _) = x
 δ x y P (inr _) = y

 open Joins (rel-syntax A)

 is-δ_𝓥-complete : 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ̇ 
 is-δ_𝓥-complete = (x y : ∣ A ∣ₚ) → (x ≤[ A ] y) holds → (P : Ω 𝓥) →
   Σ s ꞉ ∣ A ∣ₚ , (s is-lub-of ((𝟙 + P holds) , (δ x y P))) holds

\end{code}

Future work: I would be nice to show that classically every poset is
δ_𝓥 complete and to provide the critical examples of δ_𝓥 complete posets
such as 𝓥-sup lattices, etc. We should also show that is-δ_𝓥-complete is
a subsingleton.

We now define the type of δ_𝓥 complete posets.

\begin{code}

δ_𝓥-complete-Poset : (𝓤 𝓦 𝓥 : Universe) → (𝓤 ⁺) ⊔ (𝓦 ⁺) ⊔ (𝓥 ⁺) ̇
δ_𝓥-complete-Poset 𝓤 𝓦 𝓥 = Σ A ꞉ Poset 𝓤 𝓦 , δ_𝓥-complete-poset.is-δ_𝓥-complete 𝓥 A

Poset-δ : (D : δ_𝓥-complete-Poset 𝓤 𝓦 𝓥) → Poset 𝓤 𝓦
Poset-δ D = pr₁ D

is-δ_𝓥-complete-δ : (D : δ_𝓥-complete-Poset 𝓤 𝓦 𝓥) →
  δ_𝓥-complete-poset.is-δ_𝓥-complete 𝓥 (Poset-δ D)
is-δ_𝓥-complete-δ D = pr₂ D

\end{code}

\begin{code}

module non-trivial-posets {𝓤  𝓦  𝓥 : Universe} (A : Poset 𝓤 𝓦) where
 is-non-trivial-poset : 𝓤 ⊔ 𝓦 ̇
 is-non-trivial-poset =  Σ x ꞉ ∣ A ∣ₚ ,
  ( Σ y ꞉ ∣ A ∣ₚ , (x ≤[ A ] y) holds × ¬ (x ＝ y))

 lower : is-non-trivial-poset → ∣ A ∣ₚ
 lower i = pr₁ i

 upper : is-non-trivial-poset → ∣ A ∣ₚ
 upper i = pr₁ (pr₂ i)

 order : (i : is-non-trivial-poset) → (lower i ≤[ A ] upper i) holds
 order i = pr₁ (pr₂ (pr₂ i))

 nequal : (i : is-non-trivial-poset) → ¬ (lower i ＝ upper i)
 nequal i = pr₂ (pr₂ (pr₂ i))

 open Joins (rel-syntax A)
 open δ_𝓥-complete-poset 𝓥 A

 wlem-lemma : (i : is-non-trivial-poset) → (P : Ω 𝓥) →
  (((lower i) is-lub-of ((𝟙 + P holds) , (δ (lower i) (upper i) P))) holds → ¬ (P holds)) ×
  (((upper i) is-lub-of ((𝟙 + P holds) , (δ (lower i) (upper i) P))) holds → ¬ ¬ (P holds)) 
 pr₁ (wlem-lemma i P) r p = nequal i (≤-is-antisymmetric A (order i) (pr₁ r (inr p)))
 pr₂ (wlem-lemma i P) r np = nequal i (≤-is-antisymmetric A (order i) (pr₂ r (( lower i , h ))))
  where
   h : ((lower i) is-an-upper-bound-of ((𝟙 + P holds) , δ (lower i) (upper i) P)) holds
   h (inl ✯) = ≤-is-reflexive A (lower i)
   h (inr p) = 𝟘-induction (np p)
    
\end{code}

We now show that the two element poset is δ_𝓥 complete only if WLEM holds.

\begin{code}

2-is-non-trivial : non-trivial-posets.is-non-trivial-poset 2-Poset
2-is-non-trivial = (₀ , ₁ , ⋆ , zero-is-not-one)

2-is-δ_𝓥-complete-WLEM : {𝓥 : Universe} →
 δ_𝓥-complete-poset.is-δ_𝓥-complete {𝓤₀} {𝓤₀} 𝓥 2-Poset →
 (P : Ω 𝓥) → is-decidable (¬ (P holds))
2-is-δ_𝓥-complete-WLEM {𝓥} i P = decide-¬P
 where
  open Joins (rel-syntax 2-Poset)
  open δ_𝓥-complete-poset 𝓥 2-Poset
  open non-trivial-posets 2-Poset

  h : Σ s ꞉ ∣ 2-Poset ∣ₚ , (s is-lub-of ((𝟙 + P holds) , (δ ₀ ₁ P))) holds
  h = i ₀  ₁ ⋆ P

  g : Σ s ꞉ ∣ 2-Poset ∣ₚ , (s is-lub-of ((𝟙 + P holds) , (δ ₀ ₁ P))) holds →
    is-decidable (¬ (P holds))
  g (₀ , sup) = inl (pr₁ (wlem-lemma 2-is-non-trivial P) sup)
  g (₁ , sup) = inr (pr₂ (wlem-lemma 2-is-non-trivial P) sup)

  decide-¬P : is-decidable (¬ (P holds))
  decide-¬P = g h

\end{code}

Since non-trivial is a negated concept it only has enough strength to derive WLEM, we now introduce the stronger concept of positivity.

\begin{code}

module positive-posets {𝓤  𝓦  𝓥 : Universe} (A : Poset 𝓤 𝓦) where
 open Joins (rel-syntax A)
 open δ_𝓥-complete-poset 𝓥 A
 open Universal fe
 open PosetReasoning A

 _is-strictly-below_ : (x y : ∣ A ∣ₚ) → {i : is-δ_𝓥-complete} → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ̇ 
 _is-strictly-below_ x y = (x ≤[ A ] y) holds ×
  ((z : ∣ A ∣ₚ) → (y ≤[ A ] z) holds → (P : Ω 𝓥) →
  (z is-lub-of ((𝟙 + P holds) , δ x z P)) holds → P holds)

 order : {x y : ∣ A ∣ₚ} → x is-strictly-below y → (x ≤[ A ] y) holds
 order c = pr₁ c

 sup-condition : {x y : ∣ A ∣ₚ} → x is-strictly-below y →
  ((z : ∣ A ∣ₚ) → (y ≤[ A ] z) holds → (P : Ω 𝓥) →
  (z is-lub-of ((𝟙 + P holds) , δ x z P)) holds → P holds)
 sup-condition c = pr₂ c

 strictly-below-implies-non-trivial : (x y : ∣ A ∣ₚ) → is-δ_𝓥-complete → (x is-strictly-below y)
  → (x ≤[ A ] y) holds × ¬ (x ＝ y)
 pr₁ (strictly-below-implies-non-trivial x y i c) = order c
 pr₂ (strictly-below-implies-non-trivial x y i c) p =
  𝟘-induction (sup-condition c y (≤-is-reflexive A y) ((𝟘{𝓥} , 𝟘-is-prop {𝓥})) ((g , h)))
   where
    g : (y is-an-upper-bound-of ((𝟙 + ((𝟘 , 𝟘-is-prop) holds)) , δ x y (𝟘 , 𝟘-is-prop))) holds
    g (inl ⋆) = order c

    h : (Ɐ u ꞉ (upper-bound ((𝟙 + ((𝟘 , 𝟘-is-prop) holds)) , δ x y (𝟘 , 𝟘-is-prop))) ,
     y ≤[ A ] (pr₁ u)) holds
    h u = y ＝⟨ p ⁻¹ ⟩ₚ pr₂ u (inl ⋆)

\end{code}

We could show that if the converse holds then so does LEM in 𝓥.

\begin{code}

 transitivity-lemma : (x y z : ∣ A ∣ₚ) → is-δ_𝓥-complete →
  (((x ≤[ A ] y) holds × y is-strictly-below z) → x is-strictly-below z) ×
  ((x is-strictly-below y × (y ≤[ A ] z) holds) → x is-strictly-below z)
 pr₁ (transitivity-lemma x y z i) r = (≤-is-transitive A x y z (pr₁ r) (order (pr₂ r)) , h)
  where
   h : (w : ∣ A ∣ₚ) → (z ≤[ A ] w) holds → (P : Ω 𝓥) →
    (w is-lub-of ((𝟙 + (P holds)) , δ x w P)) holds → P holds
   h w q P l = sup-condition (pr₂ r) w q P ((a , b))
    where
     a : (w is-an-upper-bound-of ((𝟙 + (P holds)) , δ y w P)) holds
     a (inl ⋆) = ≤-is-transitive A y z w (order (pr₂ r)) q
     a (inr p) = ≤-is-reflexive A w

     b : (Ɐ u ꞉ (upper-bound ((𝟙 + (P holds)) , δ y w P)) , w ≤[ A ] (pr₁ u)) holds 
     b u = pr₂ l ((pr₁ u , c))
      where
       c : (pr₁ u is-an-upper-bound-of ((𝟙 + (P holds)) , δ x w P)) holds
       c (inl ⋆) = ≤-is-transitive A x y (pr₁ u) (pr₁ r) (pr₂ u (inl ⋆))
       c (inr p) = pr₂ u (inr p)

 pr₂ (transitivity-lemma x y z i) r =
  (≤-is-transitive A x y z (order (pr₁ r)) (pr₂ r) , a)
   where
    a : (w : ∣ A ∣ₚ) → rel-syntax A z w holds → (P : Ω 𝓥) →
      (w is-lub-of ((𝟙 + (P holds)) , δ x w P)) holds → P holds
    a w q P l = sup-condition (pr₁ r) w (≤-is-transitive A y z w (pr₂ r) q) P l

 is-positive : {i : is-δ_𝓥-complete} → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ̇ 
 is-positive = Σ x ꞉ ∣ A ∣ₚ , (Σ y ꞉ ∣ A ∣ₚ , x is-strictly-below y)

\end{code}

Maybe we add syntax for the strictly below relation...

I have been considering altering some of the above modules to take δ_𝓥-complete Posets rather than
simply Posets. Then I could remove explicit assumption of is-δ_𝓥-complete from many of the
definitions/lemma/propositions. The main issue I see with this choice is the lack of consistency;
for the non-trivial module applies to posets in general. I will leave this up to Martin/etc. to
review and advise.
