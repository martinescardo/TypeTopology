Martin Escardo, 6th September 2025.

We construct two distinct 𝓛-algebra structures on the subtype
classifier Ω, with structure maps given by Σ (the free algebra) and Π,
where 𝓛 is the lifting monad, also known as the partial map classifier
monad.

This is just an adaptation of the fact that Σ and Π are 𝓛-structure
maps on the universe, already proved in the file Lifting.Algebras,
which uses univalence.

We could prove that Σ and Π are structure maps on Ω by showing that a
subtype of an algebra closed under the structure map is itself an
algebra, and apply this to the subtype Ω of the universe. However, we
want a proof that doesn't use univalence, so that it makes sense in
the internal language of a 1-topos. We use propositional and
functional extensionality instead, which are validated in any 1-topos.

So notice that not even classically do we have "every algebra is a
free algebra". What we do have classically (i.e. in boolean toposes)
is that the underlying set of any algebra is isomorphic to the
underlying set of a free algebra, that is, it is isomorphic to 𝓛 X
for some X.

Question. In an arbitrary 1-topos, is it the case that the underlying
set of any algebra is isomorphic to 𝓛 X for some X?

I very much doubt that this would be the case.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons

module Lifting.TwoAlgebrasOnOmega
        (𝓣 : Universe)
        (fe : Fun-Ext)
        (pe : propext 𝓣)
       where

open import Lifting.Algebras 𝓣
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

private
 sum : {P : 𝓣 ̇ } → is-prop P → (P → Ω 𝓣) → Ω 𝓣
 sum {P} i f = (Σ p ꞉ P , f p holds) ,
               (Σ-is-prop i (λ p → holds-is-prop (f p)))

Σ-algebra-on-Ω : 𝓛-alg (Ω 𝓣)
Σ-algebra-on-Ω = sum , k , ι
 where
  k : (P : Ω 𝓣) → sum 𝟙-is-prop (λ (_ : 𝟙) → P) ＝ P
  k P = Ω-extensionality' pe fe 𝟙-lneutral

  ι : (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ ) (i : is-prop P)
      (j : (p : P) → is-prop (Q p)) (f : Σ Q → Ω 𝓣)
    → sum (Σ-is-prop i j) f
    ＝ sum i (λ p → sum (j p) (λ q → f (p , q)))
  ι P Q i j f = Ω-extensionality' pe fe Σ-assoc

private
 prod : {P : 𝓣 ̇ } → is-prop P → (P → Ω 𝓣) → Ω 𝓣
 prod {P} i f = (Π p ꞉ P , f p holds) ,
                 Π-is-prop fe (λ p → holds-is-prop (f p))

Π-algebra-on-Ω : 𝓛-alg (Ω 𝓣)
Π-algebra-on-Ω = prod , k , ι
 where
  k : (P : Ω 𝓣) → prod 𝟙-is-prop (λ (_ : 𝟙) → P) ＝ P
  k P = Ω-extensionality' pe fe (≃-sym (𝟙→ fe))

  ι : (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ ) (i : is-prop P)
      (j : (p : P) → is-prop (Q p)) (f : Σ Q → Ω 𝓣)
    → prod (Σ-is-prop i j) f
     ＝ prod i (λ p → prod (j p) (λ q → f (p , q)))
  ι P Q i j f = Ω-extensionality' pe fe (curry-uncurry' fe fe)

Σ-and-Π-disagree
 : ¬ (  {P : 𝓣 ̇ }
        (i : is-prop P)
        (f : P → Ω 𝓣)
      → (Σ p ꞉ P , f p holds) ＝ (Π p ꞉ P , f p holds))
Σ-and-Π-disagree a
 = II
 where
  I = 𝟘       ≃⟨ ×𝟘 ⟩
      𝟘 × 𝟘   ≃⟨ idtoeq _ _ (a 𝟘-is-prop λ _ → (𝟘 , 𝟘-is-prop)) ⟩
      (𝟘 → 𝟘) ≃⟨ ≃-sym (𝟘→ fe) ⟩
      𝟙 {𝓤₀}  ■

  II : 𝟘
  II = ⌜ I ⌝⁻¹ ⋆

Σ-and-Π-algebra-on-Ω-disagree : Σ-algebra-on-Ω ≠ Π-algebra-on-Ω
Σ-and-Π-algebra-on-Ω-disagree e = Σ-and-Π-disagree V
  where
   I : (λ {P} → sum {P}) ＝ prod
   I = ap pr₁ e

   II : (P : 𝓣 ̇ ) → sum {P} ＝ prod {P}
   II = implicit-happly I

   III : (P : 𝓣 ̇ ) (i : is-prop P) → sum {P} i ＝ prod {P} i
   III P = happly (II P)

   IV : (P : 𝓣 ̇ ) (i : is-prop P) (f : P → Ω 𝓣) → sum {P} i f ＝ prod {P} i f
   IV P i = happly (III P i)

   V : {P : 𝓣 ̇ }
       (i : is-prop P)
       (f : P → Ω 𝓣)
     → (Σ p ꞉ P , f p holds) ＝ (Π p ꞉ P , f p holds)
   V {P} i f = ap pr₁ (IV P i f)

\end{code}
