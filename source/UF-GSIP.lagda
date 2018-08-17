Martin Escardo, August 2018.

A structure identity principle for types, rather than categories as in
the HoTT Book.

This tries to make previous work by Coquand and Danielsson [1] more
general.

[1] https://www.sciencedirect.com/science/article/pii/S0019357713000694 , 2013

The abstract development is followed by some concrete examples.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Univalence
open import UF-Yoneda

module UF-GSIP where

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
 ⟨ X , s ⟩ = X

 structure : (A : 𝕊) → S ⟨ A ⟩
 structure (X , s) = s

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

  (3) Moreover, when f : ⟨ X , s ⟩ → ⟨ X , t ⟩ is the identity
      function, we want the data for (1) to give data for the equality
      s ≡ t of structures. This is specified by the function
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
         (≡-S-structure : (X : U ̇) (s t : S X) → S-equiv (X , s) (X , t) id (id-is-equiv X) → s ≡ t)
         (S-transport : (A : 𝕊) (s : S ⟨ A ⟩) (υ : S-equiv (⟨ A ⟩ , structure A) (⟨ A ⟩ , s) id (id-is-equiv ⟨ A ⟩))
                      → transport (λ - → S-equiv A (⟨ A ⟩ , -) id (id-is-equiv ⟨ ⟨ A ⟩ , - ⟩))
                               (≡-S-structure ⟨ A ⟩ (structure A) s υ)
                               (S-refl A)
                      ≡ υ)
        where

\end{code}

 Under these assumptions, we show that equality in 𝕊 is equivalent
 to _≃ₛ_ defined as follows:

\begin{code}

  _≃ₛ_ : 𝕊 → 𝕊 → U ⊔ V ̇
  A ≃ₛ B = Σ \(f : ⟨ A ⟩ → ⟨ B ⟩) → Σ \(e : is-equiv f) → S-equiv A B f e

\end{code}

  This defines an 𝕊-equivalence to be an equivalence of underlying
  sets that is an S-structure equivalence in the sense abstractly
  specified by the function S-equiv. Then the assumption S-refl allows
  us to have an equivalence of any element of 𝕊 with itself:

\begin{code}

  ≃ₛ-refl : (A : 𝕊) → A ≃ₛ A
  ≃ₛ-refl A = id , id-is-equiv ⟨ A ⟩ , S-refl A

\end{code}

  And hence an equality gives an 𝕊-equivalence by induction in the
  usual way:

\begin{code}

  idtoeqₛ : (A B : 𝕊) → A ≡ B → A ≃ₛ B
  idtoeqₛ A .A refl = ≃ₛ-refl A

\end{code}

  We use the following auxiliary constructions to define an inverse of
  idtoeqₛ by equivalence induction (the function JEq):

\begin{code}

  private
    Ψ : (A : 𝕊) (Y : U ̇) → ⟨ A ⟩ ≃ Y → U ′ ⊔ V ̇
    Ψ A Y (f , e) = (s : S Y) → S-equiv A (Y , s) f e → A ≡ (Y , s)
    ψ : (A : 𝕊) → Ψ A ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    ψ A s υ = to-Σ-≡' (≡-S-structure ⟨ A ⟩ (structure A) s υ)

  eqtoidₛ : (A B : 𝕊) → A ≃ₛ B → A ≡ B
  eqtoidₛ A B (f , e , υ) = JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ B ⟩ (f , e) (structure B) υ

\end{code}

  So far we have used the hypotheses

     * S-equiv (to define _≡ₛ_),
     * S-refl (to define idtoeqₛ), and
     * ≡-S-structure (to define eqtoidₛ).

  Next we use the remaining hypothesis S-transport to show that
  eqtoidₛ is a left-inverse of idtoeqₛ:

\begin{code}

  idtoeq-eqtoidₛ : (A B : 𝕊) (ε : A ≃ₛ B) → idtoeqₛ A B (eqtoidₛ A B ε) ≡ ε
  idtoeq-eqtoidₛ A B (f , e , υ) = JEq ua ⟨ A ⟩ Φ φ ⟨ B ⟩ (f , e) (structure B) υ
   where
    Φ : (Y : U ̇) → ⟨ A ⟩ ≃ Y → U ⊔ V ̇
    Φ Y (f , e) = (m : S Y)
                  (υ : S-equiv A (Y , m) f e)
                → idtoeqₛ A (Y , m) (eqtoidₛ A (Y , m) (f , e , υ)) ≡ f , e , υ
    φ : Φ ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    φ s υ = z
     where
      A' : 𝕊
      A' = ⟨ A ⟩ , s
      observation₀ : A ≡ A'
      observation₀ = JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ A ⟩ (≃-refl ⟨ A ⟩) s υ
      observation₁ : S-equiv A A' id (id-is-equiv ⟨ A ⟩)
      observation₁ = υ
      refl' : A ≃ₛ A'
      refl' = id , id-is-equiv ⟨ A ⟩ , υ
      observation₂ : eqtoidₛ A A' refl' ≡ JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ A ⟩ (≃-refl ⟨ A ⟩) s υ
      observation₂ = refl
      p : structure A ≡ s
      p = ≡-S-structure ⟨ A ⟩ (structure A) s υ
      q : JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ A ⟩ (≃-refl ⟨ A ⟩) s υ ≡ to-Σ-≡' p
      q = ap (λ h → h s υ) (JEq-comp ua ⟨ A ⟩ (Ψ A) (ψ A))
      r : idtoeqₛ A A' (eqtoidₛ A A' refl') ≡ idtoeqₛ A A' (to-Σ-≡' p)
      r = ap (idtoeqₛ A A') q
      u : structure A ≡ s → S-equiv A A' id (id-is-equiv ⟨ A ⟩)
      u p = transport (λ - → S-equiv A (⟨ A ⟩ , -) id (id-is-equiv ⟨ ⟨ A ⟩ , - ⟩)) p (S-refl A)
      v : u p ≡ υ
      v = S-transport A s υ
      w : id , id-is-equiv ⟨ A ⟩ , u p ≡ refl'
      w = to-Σ-≡' (to-Σ-≡' v)
      x : (p : structure A ≡ s) → idtoeqₛ A A' (to-Σ-≡' p) ≡ id , id-is-equiv ⟨ A ⟩ , u p
      x refl = refl
      y : idtoeqₛ A A' (to-Σ-≡' p) ≡ refl'
      y = x p ∙ w
      z : idtoeqₛ A A' (eqtoidₛ A A' refl') ≡ refl'
      z = r ∙ y

\end{code}

  Being a natural left-inverse of idtoeqₛ, the function eqtoidₛ is
  also a right-inverse, by a general property of the identity type
  (namely the one called nat-retraction-is-equiv in our development
  (in the module UF-Yoneda):

\begin{code}

  uaₛ : (A B : 𝕊) → is-equiv (idtoeqₛ A B)
  uaₛ A = nat-retraction-is-equiv A
            (idtoeqₛ A)
            (λ B → eqtoidₛ A B , idtoeq-eqtoidₛ A B)

  eqtoid-idtoeqₛ : (A B : 𝕊) (p : A ≡ B) →  eqtoidₛ A B (idtoeqₛ A B p) ≡ p
  eqtoid-idtoeqₛ A B = pr₁(pr₂ (is-equiv-qinv (idtoeqₛ A B) (uaₛ A B)))

\end{code}

This completes the proof of the abstract SIP considered here.

We now consider some concrete examples to illustrate how this works in
practice.

An ∞-magma is a type, not assumed to be a set, equipped with a binary
operation. The above gives a characterization of equality of ∞-magmas:

\begin{code}

module ∞-magma (U : Universe) (ua : is-univalent U) where

 open gsip₀ U U ua (λ X → X → X → X)
 open gsip₁ (λ A B f e → (λ x x' → f (structure A x x')) ≡ (λ x x' → structure B (f x) (f x')))
            (λ A → refl)
            (λ X m n → id)
            (λ A m υ → refl-left-neutral)

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
            (λ X τ σ → id)
            (λ A τ υ → refl-left-neutral)

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

 Again by function extensionality, structure preservation is equivalent
 to (V : Y → R) → τ(V ∘ f) ≡ σ V. We can read this, at least when R is
 the type Ω of truth-values, by saying that a set V : Y → R is σ-open
 precisely when its inverse image V ∘ f is τ-open.

 Thus, if we say that an equivalence f : X → Y is an ∞-homeomorphism
 when an "R-set" V : Y → R is σ-open precisely when its f-inverse image
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
