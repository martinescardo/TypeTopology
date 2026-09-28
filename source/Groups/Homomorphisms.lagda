--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandifsu.edu
Keri D'Angelo kd349@cornell.edu

August 28, 2021
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons
open import UF.Equiv
open import UF.Embeddings
open import UF.PropTrunc
open import Groups.Type renaming (_≅_ to _≣_)

open import Groups.Triv
open import Groups.Kernel
open import Groups.Image


\end{code}

\section{Injective homomorphisms}

We define an injective group homomorphism in the obvious way, and we
show this definition is equivalent to the statement that the kernel is
isomorphic to the trivial group. It is also equivalent to the
underlying function being left-cancellable.

We take the trivial group in the same universe as the kernel.

Here are the definitions:

\begin{code}

module Groups.Homomorphisms
         (X : Group 𝓤) (Y : Group 𝓥)
         (f : ⟨ X ⟩ → ⟨ Y ⟩) (isf : is-hom X Y f)
         where

is-injective-hom : _
is-injective-hom = (x : ⟨ X ⟩) → f x ＝ e⟨ Y ⟩ → x ＝ e⟨ X ⟩

has-triv-kernel : _
has-triv-kernel = is-iso (triv {𝓤 ⊔ 𝓥}) (kernel X Y f isf) (triv-initial (kernel X Y f isf))

\end{code}

Being injective in the naive sense employed above is the same as having a
left-cancellable underlying function.

\begin{code}

lc-hom-is-inj : left-cancellable f → is-injective-hom
lc-hom-is-inj lc x p = lc {x} {unit X} q
  where
    q : f x ＝ f (unit X)
    q = p ∙ (homs-preserve-unit X Y f isf) ⁻¹


inj-hom-is-lc : is-injective-hom → left-cancellable f
inj-hom-is-lc i {x} {x'} p = x                             ＝⟨ (unit-right X x) ⁻¹ ⟩
                             x ·⟨ X ⟩ e⟨ X ⟩                 ＝⟨ ap (λ v → x ·⟨ X ⟩ v) (inv-left X x') ⁻¹ ⟩
                             x ·⟨ X ⟩ ((inv X x') ·⟨ X ⟩ x') ＝⟨ (assoc X _ _ _) ⁻¹  ⟩
                             (x ·⟨ X ⟩ (inv X x')) ·⟨ X ⟩ x' ＝⟨ ap (λ v → v ·⟨ X ⟩ x') u  ⟩
                             e⟨ X ⟩ ·⟨ X ⟩ x'                ＝⟨ unit-left X x' ⟩
                             x' ∎
                where
                  q : f (x ·⟨ X ⟩ (inv X x')) ＝ e⟨ Y ⟩
                  q = f (x ·⟨ X ⟩ (inv X x'))     ＝⟨ isf ⟩
                      f x ·⟨ Y ⟩ f (inv X x')     ＝⟨ ap (λ v → f x ·⟨ Y ⟩ v) (homs-preserve-invs X Y f isf _) ⟩
                      f x ·⟨ Y ⟩ (inv Y (f x'))   ＝⟨ ap (λ v → v ·⟨ Y ⟩ (inv Y (f x')) ) p ⟩
                      f x' ·⟨ Y ⟩ (inv Y (f x'))  ＝⟨ inv-right Y _ ⟩
                      e⟨ Y ⟩ ∎

                  u : x ·⟨ X ⟩ (inv X x') ＝ e⟨ X ⟩
                  u = i (x ·⟨ X ⟩ (inv X x')) q

\end{code}

A homomorphism with trivial kernel is injective in the above
sense. There are two proofs that injective homs have trivial kernels;
the second uses the fact that kernels of injective homs are
contractible.

\begin{code}

triv-kernel-implies-inj-hom : has-triv-kernel → is-injective-hom
triv-kernel-implies-inj-hom is x p = ap pr₁ u
  where
    k : ⟨ kernel X Y f isf ⟩
    k = x , p

    u : k ＝ unit ( kernel X Y f isf )
    u = to-Σ-＝ ((ap pr₁ (pr₂ (pr₁ (pr₁ (is))) k) ⁻¹) , (groups-are-sets Y _ _))


inj-hom-has-triv-kernel : is-injective-hom → has-triv-kernel
pr₁ (pr₁ (inj-hom-has-triv-kernel is)) = (triv-terminal (kernel X Y f isf))
                                       , (λ { (x , p) → to-Σ-＝ (((is x p) ⁻¹) , groups-are-sets Y _ _ )})
pr₂ (pr₁ (inj-hom-has-triv-kernel is)) = (triv-terminal (kernel X Y f isf))
                                       , (λ x → refl)
pr₂ (inj-hom-has-triv-kernel is) = triv-initial-is-hom {𝓥 = 𝓤 ⊔ 𝓥} (kernel X Y f isf)



inj-hom-has-contractible-kernel : is-injective-hom → is-singleton (⟨ kernel X Y f isf ⟩)
pr₁ (inj-hom-has-contractible-kernel is) = unit (kernel X Y f isf)
pr₂ (inj-hom-has-contractible-kernel is) (x , p) = to-Σ-＝ (((is x p) ⁻¹) , (groups-are-sets Y _ _))

inj-hom-has-triv-kernel₁ : is-injective-hom → has-triv-kernel
inj-hom-has-triv-kernel₁ is = pr₂ (group-is-singl-is-triv' (kernel X Y f isf) i)
  where
    i : is-singleton ( ⟨ kernel X Y f isf ⟩ )
    i = inj-hom-has-contractible-kernel is

\end{code}

And, finally, injective homomorphisms are embeddings:

\begin{code}

inj-hom-is-embedding : is-injective-hom → is-embedding f
inj-hom-is-embedding is = lc-maps-into-sets-are-embeddings
                        f
                        (inj-hom-is-lc is)
                        (groups-are-sets Y)

embedding-carrier-implies-inj-hom : is-embedding f → is-injective-hom
embedding-carrier-implies-inj-hom is = lc-hom-is-inj (embeddings-are-lc f is)
\end{code}


\section{Surjective homomorphisms}

The definition simply is that they have surjective underlying
functions. To be so, implies the image is isomorphic to the target.

The converse holds assuming the canonical injection is an isomorphism.

TODO: Prove the converse, if possible, under the weaker assumption
that we just have an isomorphism.

\begin{code}

module _ (pt : propositional-truncations-exist) where

    open PropositionalTruncation pt
    open import UF.ImageAndSurjection pt

    --
    -- Shorten notation in the following
    --
    private
      I : Group _
      I = group-image pt X Y f isf

      inj : ⟨ I ⟩ → ⟨ Y ⟩
      inj = group-image-inj pt X Y f isf
    --
    -- ---------------------------------
    --

    is-surjective-hom : _
    is-surjective-hom = is-surjection f

    surjective-homs-give-image-equiv : is-surjective-hom → is-equiv (group-image-inj pt X Y f isf)
    surjective-homs-give-image-equiv is = surjective-embeddings-are-equivs
                                                          (group-image-inj pt X Y f isf)
                                                          (group-image-inj-is-embedding pt X Y f isf)
                                                          image-is-surj
      where
        image-is-surj : is-surjection (group-image-inj pt X Y f isf)
        image-is-surj y = do
          x , p ← is y
          ∣ ((y , ∣ (x , p) ∣) , refl) ∣

    surjective-homs-have-complete-images : is-surjective-hom → (group-image pt X Y f isf) ≣ Y
    pr₁ (surjective-homs-have-complete-images is) = group-image-inj pt X Y f isf
    pr₁ (pr₂ (surjective-homs-have-complete-images is)) = surjective-homs-give-image-equiv is
    pr₂ (pr₂ (surjective-homs-have-complete-images is)) {x} {y} = group-image-inj-is-hom pt X Y f isf {x} {y}



    image-equiv-gives-surjective-hom : is-equiv (group-image-inj pt X Y f isf) → is-surjective-hom
    image-equiv-gives-surjective-hom e y = do
                                          x , p ← pr₂ (j y)
                                          ∣ (x , (p ∙ u)) ∣
      where
        i : ⟨ group-image pt X Y f isf ⟩ → ⟨ Y ⟩
        i = group-image-inj pt X Y f isf

        j : ⟨ Y ⟩ → ⟨ group-image pt X Y f isf ⟩
        j = inverse i e

        u : i (j y) ＝ y
        u = inverses-are-sections i e y

    complete-image-implies-surjective-hom : is-iso I Y inj → is-surjective-hom
    complete-image-implies-surjective-hom iso = image-equiv-gives-surjective-hom (pr₁ iso)

\end{code}


\section{Homomorphisms with normal image}

The homomorphism $f ∶ X → Y$ has normal image if $∀ z ∈ Y$ and $∀ y ,
p ∈ \mathrm{Im} (f)$, the conjugation of $z y z^{-1}$, suitably
defined, is still in the image.

We are still inside the anonymous module where propositional
truncation is assumed.

\begin{code}

    has-normal-image : _
    has-normal-image = (z : ⟨ Y ⟩ ) ((y , p) : ⟨ I ⟩) → ((z ·⟨ Y ⟩ y) ·⟨ Y ⟩ (inv Y z)) ∈image f

\end{code}
