Martin Escardo, August 2018.

A structure identity principle for types, rather than categories as in
the HoTT Book.

This tries to make previous work by Coquand and Danielsson [1] more
general.

[1] https://www.sciencedirect.com/science/article/pii/S0019357713000694 , 2013

The abstract development is followed by some concrete examples.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Univalence
open import UF-Yoneda

module UF-GSIP where

\end{code}

For the moment we postulate the computation rule for equivalence
induction JEq (module UF-Univalence) because we haven't proved it yet,
but it is known to hold (and we have the material needed to show it):

\begin{code}

postulate
 JEq-comp : ∀ {U} (ua : is-univalent U)
           {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇) (b : A X (≃-refl X))
        → JEq ua X A b X (≃-refl X) ≡ b
{-
JEq-comp ua X A b = γ
 where
  γ : transport (A X)
        (idtoeq-eqtoid ua X X (≃-refl X))
        (Jbased X (λ Y p → A Y (idtoeq X Y p)) b X (eqtoid ua X X (≃-refl X)))
    ≡ b
  γ = {!!}
-}

\end{code}

We consider the type 𝕊 of types X : U ̇ equipped with structure m : S X,
where the universe U is univalent and S : U ̇ → V ̇ is a parameter:

\begin{code}

module gsip₀
        (U V : Universe)
        (ua : is-univalent U)
        (S : U ̇ → V ̇)
       where

 𝕊 : U ′ ⊔ V ̇
 𝕊 = Σ \(X : U ̇) → S X

\end{code}

The underlying set and structure are given by the first and second
projections:

\begin{code}

 ⟨_⟩ : 𝕊 → U ̇
 ⟨ X , m ⟩ = X

 structure : (A : 𝕊) → S ⟨ A ⟩
 structure (X , m) = m

\end{code}

 If S comes with suitable data, including S-equiv discussed below, we
 can characterize equality in 𝕊 as equivalence of underlying sets
 subject to a suitable condition involving the data:

   (A ≡ B) ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩) → Σ \(e : is-equiv f) → S-equiv A B f e

 It is important that such a condition is not necessarily property but
 actually data in general.

 Thus

  (1) For an equivalence f : ⟨ A ⟩ → ⟨ B ⟩ we want data that
      establishes that it is an equivalence in the sense of
      S-structure, in some abstract sense, specified by S-equiv.

 One possible list of data for S and S-equiv is the following:

  (2) When f is the identity equivalence, we want the data S-equiv to
      be given, and we name it S-refl.

  (3) Moreover, when f : ⟨ X , m ⟩ → ⟨ X , n ⟩ is the identity
      function, we want the data for (1) to give data for the equality
      m ≡ n of structures. This is specified by the function
      ≡-S-structure.

  (4) We need a technical transport condition (which is not
      surprising, as equality of Σ-types is given by transport of the
      second component), specified by the function S-transport below,
      relating the data specified by the functions ≡-S-structure and
      S-refl.

These assumptions (1)-(4) are given as module parameters for gsip₁:

\begin{code}

 module gsip₁
         (S-equiv : (A B : 𝕊) → (f : ⟨ A ⟩ → ⟨ B ⟩) → is-equiv f → U ⊔ V ̇)
         (S-refl : (A : 𝕊) → S-equiv A A id (id-is-equiv ⟨ A ⟩))
         (≡-S-structure : (X : U ̇) (m n : S X) → S-equiv (X , m) (X , n) id (id-is-equiv X) → m ≡ n)
         (S-transport : (A : 𝕊) (m : S ⟨ A ⟩) (t : S-equiv (⟨ A ⟩ , structure A) (⟨ A ⟩ , m) id (id-is-equiv ⟨ A ⟩))
                      → transport (λ - → S-equiv A (⟨ A ⟩ , -) id (id-is-equiv ⟨ ⟨ A ⟩ , - ⟩))
                               (≡-S-structure ⟨ A ⟩ (structure A) m t)
                               (S-refl A)
                      ≡ t)
        where

\end{code}

 Under these assumptions, we show that equality in 𝕊 is equivalent
 to _≃ₛ_ defined as follows:

\begin{code}

  _≃ₛ_ : 𝕊 → 𝕊 → U ⊔ V ̇
  A ≃ₛ B = Σ \(f : ⟨ A ⟩ → ⟨ B ⟩) → Σ \(e : is-equiv f) → S-equiv A B f e

\end{code}

This defines an 𝕊-equivalence to be an equivalence of underlying sets
that is an S-structure equivalence in the sense abstractly specified
by the function S-equiv. Then the assumption S-refl allows us to have
an equivalence of any element of 𝕊 with itself:

\begin{code}

  ≃ₛ-refl : (A : 𝕊) → A ≃ₛ A
  ≃ₛ-refl A = id , id-is-equiv ⟨ A ⟩ , S-refl A

\end{code}

And hence an equality gives an 𝕊-equivalence by induction in the usual
way:

\begin{code}

  idtoeqₛ : (A B : 𝕊) → A ≡ B → A ≃ₛ B
  idtoeqₛ A .A refl = ≃ₛ-refl A

\end{code}

We use the following auxiliary constructions to define an inverse of
idtoeqₛ by equivalence induction (the function JEq):

\begin{code}

  private
    Ψ : (A : 𝕊) (Y : U ̇) → ⟨ A ⟩ ≃ Y → U ′ ⊔ V ̇
    Ψ A Y (f , e) = (m : S Y) (t : S-equiv A (Y , m) f e) → A ≡ (Y , m)
    ψ : (A : 𝕊) → Ψ A ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    ψ A m t = to-Σ-≡' (≡-S-structure ⟨ A ⟩ (structure A) m t)

  eqtoidₛ : (A B : 𝕊) → A ≃ₛ B → A ≡ B
  eqtoidₛ A B (f , e , t) = JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ B ⟩ (f , e) (structure B) t

\end{code}

So far we have used the hypotheses

   * S-equiv (to define _≡ₛ_),
   * S-refl (to define idtoeqₛ),
   * and ≡-S-structure (to define eqtoidₛ).

Next we use the remaining hypothesis S-transport to show that eqtoidₛ
is a left-inverse of idtoeqₛ:

\begin{code}

  idtoeq-eqtoidₛ : (A B : 𝕊) (ψ : A ≃ₛ B) → idtoeqₛ A B (eqtoidₛ A B ψ) ≡ ψ
  idtoeq-eqtoidₛ A B (f , e , t) = JEq ua ⟨ A ⟩ Φ φ ⟨ B ⟩ (f , e) (structure B) t
   where
    Φ : (Y : U ̇) → ⟨ A ⟩ ≃ Y → U ⊔ V ̇
    Φ Y (f , e) = (m : S Y)
                  (t : S-equiv A (Y , m) f e)
                → idtoeqₛ A (Y , m) (eqtoidₛ A (Y , m) (f , e , t)) ≡ f , e , t
    φ : Φ ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    φ m t = γ
     where
      A' : 𝕊
      A' = ⟨ A ⟩ , m
      observation₀ : A ≡ A'
      observation₀ = JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ A ⟩ (≃-refl ⟨ A ⟩) m t
      observation₁ : S-equiv A A' id (id-is-equiv ⟨ A ⟩)
      observation₁ = t
      refl' : A ≃ₛ A'
      refl' = id , id-is-equiv ⟨ A ⟩ , t
      observation₂ : eqtoidₛ A A' refl' ≡ JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ A ⟩ (≃-refl ⟨ A ⟩) m t
      observation₂ = refl
      p : structure A ≡ m
      p = ≡-S-structure ⟨ A ⟩ (structure A) m t
      q : JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ A ⟩ (≃-refl ⟨ A ⟩) m t ≡ to-Σ-≡' p
      q = ap (λ h → h m t) (JEq-comp ua ⟨ A ⟩ (Ψ A) (ψ A))
      r : idtoeqₛ A A' (eqtoidₛ A A' refl') ≡ idtoeqₛ A A' (to-Σ-≡' p)
      r = ap (idtoeqₛ A A') q
      s : structure A ≡ m → S-equiv A A' id (id-is-equiv ⟨ A ⟩)
      s p = transport (λ - → S-equiv A (⟨ A ⟩ , -) id (id-is-equiv ⟨ ⟨ A ⟩ , - ⟩)) p (S-refl A)
      u : s p ≡ t
      u = S-transport A m t
      v : id , id-is-equiv ⟨ A ⟩ , s p ≡ refl'
      v = to-Σ-≡' (to-Σ-≡' u)
      w : (p : structure A ≡ m) → idtoeqₛ A A' (to-Σ-≡' p) ≡ id , id-is-equiv ⟨ A ⟩ , s p
      w refl = refl
      x : idtoeqₛ A A' (to-Σ-≡' p) ≡ refl'
      x = w p ∙ v
      γ : idtoeqₛ A A' (eqtoidₛ A A' refl') ≡ refl'
      γ = r ∙ x

\end{code}

Being a natural left-inverse of idtoeqₛ, the function eqtoidₛ is also
a right-inverse, by a general property of the identity type (namely
the one called nat-retraction-is-equiv in our development (in the
module UF-Yoneda):

\begin{code}

  uaₛ : (A B : 𝕊) → is-equiv (idtoeqₛ A B)
  uaₛ A = nat-retraction-is-equiv A
            (idtoeqₛ A)
            (λ B → eqtoidₛ A B , idtoeq-eqtoidₛ A B)

  eqtoid-idtoeqₛ : (A B : 𝕊) (p : A ≡ B) →  eqtoidₛ A B (idtoeqₛ A B p) ≡ p
  eqtoid-idtoeqₛ A B = pr₁(pr₂ (is-equiv-qinv (idtoeqₛ A B) (uaₛ A B)))

\end{code}

We now consider some examples to illustrate how this works in practice.

An ∞-magma is a type, not assumed to be a set, equipped with a binary
operation. The above gives a characterization of equality of ∞-magmas:

\begin{code}

module ∞-magma (U : Universe) (ua : is-univalent U) where

 open gsip₀ U U ua (λ X → X → X → X)
 open gsip₁ (λ A B f e → (λ x x' → f (structure A x x')) ≡ (λ x x' → structure B (f x) (f x')))
            (λ A → refl)
            (λ X m n t → t)
            (λ A m t → refl-left-neutral)

 fact : (A B : 𝕊)
      → (A ≡ B) ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩) → is-equiv f × ((λ x x' → f (structure A x x'))
                                                      ≡ (λ x x' → structure B (f x) (f x')))
 fact A B = idtoeqₛ A B , uaₛ A B

\end{code}

Perhaps the following reformulation is more appealing:

\begin{code}

 fact' : (X Y : U ̇) (m : X → X → X) (n : Y → Y → Y)
       → ((X , m) ≡ (Y , n))
         ≃ Σ \(f : X → Y) → is-equiv f × ((λ x x' → f (m x x')) ≡ (λ x x' → n (f x) (f x')))
 fact' X Y m n = fact (X , m) (Y , n)

\end{code}

Of course, the condition (λ x x' → f (m x x')) ≡ (λ x x' → n (f x) (f x'))
is equivalent to (x x' : X) → f (m x x') ≡ n (f x) (f x') by function
extensionality, which is the natural formulation of magma
homomorphism.

As a second example, a topology on a set X is a set of subsets of X
satisfying suitable axioms. A set of subsets amounts to a map
(X → Ω) → Ω. Dropping the assumption that the type X is a set and the
axioms for topologies, and generalizing Ω to an arbitrary type R, we
get ∞-proto-topological spaces.

\begin{code}

module ∞-proto-topological-spaces (U V : Universe) (ua : is-univalent U) (R : V ̇) where

 open gsip₀ U (U ⊔ V) ua (λ X → (X → R) → R)
 open gsip₁ (λ A B f e → (λ V → structure A (V ∘ f)) ≡ structure B)
            (λ A → refl)
            (λ X m n p → p)
            (λ A m t → refl-left-neutral)

 fact : (A B : 𝕊)
      → (A ≡ B) ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩) → is-equiv f × ((λ V → structure A (λ x → V (f x))) ≡ structure B)
 fact A B = idtoeqₛ A B , uaₛ A B

\end{code}

Or in perhaps more appealing terms:

\begin{code}

 fact' : (X Y : U ̇) (τ : (X → R) → R) (σ : (Y → R) → R)
       → ((X , τ) ≡ (Y , σ)) ≃ Σ \(f : X → Y) → is-equiv f × ((λ V → τ (V ∘ f)) ≡ σ)
 fact' X Y σ τ = fact (X , σ) (Y , τ)

\end{code}

If we say that an equivalence f : X → Y is an ∞-homeomorphism when a
"R-set" V : Y → R is σ-open precisely when its f-inverse image
V ∘ f : X → R is τ-open, then the above says that two
∞-proto-topological spaces are equal iff they are ∞-homeomorphic.

Perhaps it is possible to derive the SIP for 1-categories from the
above SIP for types equipped with structure. But this is not the point
we are trying to make. The point is to give a criterion for natural
characterizations of equality of types equipped with structure, before
we know they form (∞-)categories, and even if they don't.

Another example that should be accounted for by the methods developed
here is equality of ordinals (in the module OrdinalOfOrdinals), which
is what prompted us to think about the subject of this module.

TODO. Add many more examples, including monoids (sets equipped with an
associative binary operation with a neutral element), topologies (sets
equipped with a set of subsets closed under finite intersections and
arbitrary unions (of families, to avoid having to rely on resizing)),
among other natural ones to prove the usefulness of the above abstract
formulation and proof of equality of types equipped with structure.
