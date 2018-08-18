Martin Escardo, August 2018.

A structure identity principle (sip) for types, rather than categories
as in the HoTT Book.

This tries to make previous work by Coquand and Danielsson [1] more
general.

[1] https://www.sciencedirect.com/science/article/pii/S0019357713000694 , 2013

Contents:

 * The submodule gsip has a very abstract version of sip.

 * This is followed by various submodules that consider more concrete
   examples such as ∞-magmas.

 * The submodule gsip-with-axioms considers structures subject to
   axioms, to easily account for mathematical structures such as
   monoids, groups, spaces, etc. This module performs a reduction to
   the module gsip.

 * This is followed by monoids as an example.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base hiding (assoc)
open import UF-Equiv
open import UF-Univalence
open import UF-Yoneda

module UF-GSIP where

\end{code}

We consider the type 𝕊 of types X : U ̇ equipped with structure s : S X,
where the universe U is univalent and S : U ̇ → V ̇ is a parameter:

The underlying set and structure are given by the first and second
projections:

\begin{code}


⟨_⟩ : {U V : Universe} {S : U ̇ → V ̇} → Σ S → U ̇
⟨_⟩ = pr₁

structure : {U V : Universe} {S : U ̇ → V ̇} (A : Σ S) → S ⟨ A ⟩
structure = pr₂

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
      S-≡-structure.

  (4) We need a technical transport condition (which is not
      surprising, as equality of Σ-types is given by transport of the
      second component), specified by the function S-transport below,
      relating the data specified by the functions S-≡-structure and
      S-refl.

 These assumptions (1)-(4) are given as module parameters for gsip:

\begin{code}

module gsip

  (U V : Universe)

  (ua : is-univalent U)

  (S : U ̇ → V ̇)

  (S-equiv : (A B : Σ S) (f : ⟨ A ⟩ → ⟨ B ⟩) → is-equiv f → U ⊔ V ̇)

  (S-refl : (A : Σ S) → S-equiv A A id (id-is-equiv ⟨ A ⟩))

  (S-≡-structure : (X : U ̇) (s t : S X)
                 → S-equiv (X , s) (X , t) id (id-is-equiv X) → s ≡ t)

  (S-transport : (A : Σ S)
                 (s : S ⟨ A ⟩)
                 (υ : S-equiv A (⟨ A ⟩ , s) id (id-is-equiv ⟨ A ⟩))
               → transport
                    (λ - → S-equiv A (⟨ A ⟩ , -) id (id-is-equiv ⟨ A ⟩))
                    (S-≡-structure ⟨ A ⟩ (structure A) s υ)
                    (S-refl A)
               ≡ υ)
  where

\end{code}

  Under these assumptions, we show that equality in Σ S is equivalent
  to _≃ₛ_ defined as follows:

\begin{code}

  _≃ₛ_ : Σ S → Σ S → U ⊔ V ̇
  A ≃ₛ B = Σ \(f : ⟨ A ⟩ → ⟨ B ⟩) → Σ \(e : is-equiv f) → S-equiv A B f e

\end{code}

  This defines an Σ S-equivalence to be an equivalence of underlying
  sets that is an S-structure equivalence in the sense abstractly
  specified by the function S-equiv. Then the assumption S-refl allows
  us to have an equivalence of any element of Σ S with itself:

\begin{code}

  ≃ₛ-refl : (A : Σ S) → A ≃ₛ A
  ≃ₛ-refl A = id , id-is-equiv ⟨ A ⟩ , S-refl A

\end{code}

  And hence an equality gives an Σ S-equivalence by induction in the
  usual way:

\begin{code}

  idtoeqₛ : (A B : Σ S) → A ≡ B → A ≃ₛ B
  idtoeqₛ A .A refl = ≃ₛ-refl A

\end{code}

  We use the following auxiliary constructions to define an inverse of
  idtoeqₛ by equivalence induction (the function JEq):

\begin{code}

  private
    Ψ : (A : Σ S) (Y : U ̇) → ⟨ A ⟩ ≃ Y → U ′ ⊔ V ̇
    Ψ A Y (f , e) = (s : S Y) → S-equiv A (Y , s) f e → A ≡ (Y , s)
    ψ : (A : Σ S) → Ψ A ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    ψ A s υ = to-Σ-≡' (S-≡-structure ⟨ A ⟩ (structure A) s υ)

  eqtoidₛ : (A B : Σ S) → A ≃ₛ B → A ≡ B
  eqtoidₛ A B (f , e , υ) = JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ B ⟩ (f , e) (structure B) υ

\end{code}

  So far we have used the hypotheses

     * S-equiv (to define _≡ₛ_),
     * S-refl (to define idtoeqₛ), and
     * S-≡-structure (to define eqtoidₛ).

  Next we use the remaining hypothesis S-transport to show that
  eqtoidₛ is a left-inverse of idtoeqₛ:

\begin{code}

  idtoeq-eqtoidₛ : (A B : Σ S) (ε : A ≃ₛ B) → idtoeqₛ A B (eqtoidₛ A B ε) ≡ ε
  idtoeq-eqtoidₛ A B (f , e , υ) = JEq ua ⟨ A ⟩ Φ φ ⟨ B ⟩ (f , e) (structure B) υ
   where
    Φ : (Y : U ̇) → ⟨ A ⟩ ≃ Y → U ⊔ V ̇
    Φ Y (f , e) = (m : S Y)
                  (υ : S-equiv A (Y , m) f e)
                → idtoeqₛ A (Y , m) (eqtoidₛ A (Y , m) (f , e , υ)) ≡ f , e , υ
    φ : Φ ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    φ s υ =
      idtoeqₛ A A' (eqtoidₛ A A' refl') ≡⟨ ap (λ h → idtoeqₛ A A' (h s υ)) (JEq-comp ua ⟨ A ⟩ (Ψ A) (ψ A)) ⟩
      idtoeqₛ A A' (to-Σ-≡' p)          ≡⟨ h p ⟩
      id , id-is-equiv ⟨ A ⟩ , g p      ≡⟨ to-Σ-≡' (to-Σ-≡' (S-transport A s υ)) ⟩
      refl' ∎
     where
      A' : Σ S
      A' = ⟨ A ⟩ , s
      refl' : A ≃ₛ A'
      refl' = id , id-is-equiv ⟨ A ⟩ , υ
      g : structure A ≡ s → S-equiv A A' id (id-is-equiv ⟨ A ⟩)
      g p = transport (λ - → S-equiv A (⟨ A ⟩ , -) id (id-is-equiv ⟨ A ⟩)) p (S-refl A)
      h : (p : structure A ≡ s) → idtoeqₛ A A' (to-Σ-≡' p) ≡ id , id-is-equiv ⟨ A ⟩ , g p
      h refl = refl
      p : structure A ≡ s
      p = S-≡-structure ⟨ A ⟩ (structure A) s υ

\end{code}

  Being a natural left-inverse of idtoeqₛ, the function eqtoidₛ is
  also a right-inverse, by a general property of the identity type
  (namely the one called nat-retraction-is-equiv in our development
  (in the module UF-Yoneda)):

\begin{code}

  uaₛ : (A B : Σ S) → is-equiv (idtoeqₛ A B)
  uaₛ A = nat-retraction-is-equiv A
            (idtoeqₛ A)
            (λ B → eqtoidₛ A B , idtoeq-eqtoidₛ A B)

  eqtoid-idtoeqₛ : (A B : Σ S) (p : A ≡ B) → eqtoidₛ A B (idtoeqₛ A B p) ≡ p
  eqtoid-idtoeqₛ A B = pr₁(pr₂ (is-equiv-qinv (idtoeqₛ A B) (uaₛ A B)))

  ≡-is-≃ₛ : (A B : Σ S) → (A ≡ B) ≃ (A ≃ₛ B)
  ≡-is-≃ₛ A B = idtoeqₛ A B , uaₛ A B

\end{code}

  This completes the proof of the abstract SIP considered here.


We now consider some concrete examples to illustrate how this works in
practice.

An ∞-magma is a type, not assumed to be a set, equipped with a binary
operation. The above gives a characterization of equality of ∞-magmas:

\begin{code}

module ∞-magma (U : Universe) (ua : is-univalent U) where

 S : U ̇ → U ̇
 S X = X → X → X

 open gsip
       U U ua S
       (λ A B f e → (λ x x' → f (structure A x x')) ≡ (λ x x' → structure B (f x) (f x')))
       (λ A → refl)
       (λ X m n → id)
       (λ A m υ → refl-left-neutral)

 fact : (A B : Σ S)
      → (A ≡ B) ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩)
                       → is-equiv f
                       × ((λ x x' → f (structure A x x')) ≡ (λ x x' → structure B (f x) (f x')))
 fact = ≡-is-≃ₛ

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

 S : U ̇ → U ⊔ V ̇
 S X = (X → R) → R

 open gsip
       U (U ⊔ V) ua S
       (λ A B f e → (λ V → structure A (V ∘ f)) ≡ structure B)
       (λ A → refl)
       (λ X τ σ → id)
       (λ A τ υ → refl-left-neutral)

 fact : (A B : Σ S)
      → (A ≡ B) ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩)
                       → is-equiv f × ((λ V → structure A (λ x → V (f x))) ≡ structure B)
 fact = ≡-is-≃ₛ

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

Another example generalizes metric spaces (when R is a type of reals)
and ordered sets (when R is Ω and d=_≺_, reflexive or not):

\begin{code}

module ∞-proto-metric-spaces (U V : Universe) (ua : is-univalent U) (R : V ̇) where

 S : U ̇ → U ⊔ V ̇
 S X = X → X → R

 open gsip
       U (U ⊔ V) ua (λ X → X → X → R)
       (λ A B f e → structure A ≡ (λ x x' → structure B (f x) (f x')))
       (λ A → refl)
       (λ X d e → id)
       (λ A s υ → refl-left-neutral)

 fact : (A B : Σ S)
      → (A ≡ B) ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩)
                        → is-equiv f × (structure A ≡ (λ x x' → structure B (f x) (f x')))
 fact = ≡-is-≃ₛ

 fact' : (X Y : U ̇) (d : X → X → R) (e : Y → Y → R)
       → ((X , d) ≡ (Y , e)) ≃ Σ \(f : X → Y) → is-equiv f × (d ≡ (λ x x' → e (f x) (f x')))
 fact' X Y σ τ = fact (X , σ) (Y , τ)

\end{code}

 Notice that here the S-equivalences are the isometries (metric-space case)
 or order preserving-reflecting maps (ordered-set case).

The following example is related to searchable sets:

\begin{code}

module selection-spaces (U V : Universe) (ua : is-univalent U) (R : V ̇) where

 S : U ̇ → U ⊔ V ̇
 S X = (X → R) → X

 open gsip
       U (U ⊔ V) ua S
       (λ A B f e → (λ V → f (structure A (V ∘ f))) ≡ structure B)
       (λ A → refl)
       (λ X ε δ → id)
       (λ A τ υ → refl-left-neutral)

 fact : (A B : Σ S)
      → (A ≡ B) ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩)
                        → is-equiv f × ((λ V → f(structure A (λ x → V (f x)))) ≡ structure B)
 fact = ≡-is-≃ₛ

 fact' : (X Y : U ̇) (ε : (X → R) → X) (δ : (Y → R) → Y)
       → ((X , ε) ≡ (Y , δ)) ≃ Σ \(f : X → Y) → is-equiv f × ((λ V → f(ε (V ∘ f))) ≡ δ)
 fact' X Y σ τ = fact (X , σ) (Y , τ)

\end{code}

We now continue our abstract development, to account for things such
as monoids and groups. We consider given axioms on X and its
structure.

\begin{code}

open import UF-Subsingletons

module gsip-with-axioms

 (U V : Universe)

 (ua : is-univalent U)

 (S : U ̇ → V ̇)

 (Axioms : (X : U ̇) → S X → V ̇)

 (Axioms-is-prop : (X : U ̇) (s : S X) → is-prop (Axioms X s))

 (S-equiv : (A B : Σ S) (f : ⟨ A ⟩ → ⟨ B ⟩) → is-equiv f → U ⊔ V ̇)

 (S-refl : (A : Σ S) → S-equiv A A id (id-is-equiv ⟨ A ⟩))

 (S-≡-structure : (X : U ̇) (s t : S X)
                → S-equiv (X , s) (X , t) id (id-is-equiv X) → s ≡ t)

 (S-transport : (A : Σ S)
                (s : S ⟨ A ⟩)
                (υ : S-equiv A (⟨ A ⟩ , s) id (id-is-equiv ⟨ A ⟩))
              → transport
                   (λ - → S-equiv A (⟨ A ⟩ , -) id (id-is-equiv ⟨ A ⟩))
                   (S-≡-structure ⟨ A ⟩ (structure A) s υ)
                   (S-refl A)
              ≡ υ)
 where

   S' : U ̇ → V ̇
   S' X = Σ \(s : S X) → Axioms X s

   S'-equiv : (A' B' : Σ S') (f : ⟨ A' ⟩ → ⟨ B' ⟩) → is-equiv f → U ⊔ V ̇
   S'-equiv (X , s , α) (Y , t , β) f e = S-equiv (X , s) (Y , t) f e

   S'-refl : (A' : Σ S') → S'-equiv A' A' id (id-is-equiv ⟨ A' ⟩)
   S'-refl (X , s , α) = S-refl (X , s)

   S'-≡-structure : (X : U ̇) (s' t' : S' X)
                  → S'-equiv (X , s') (X , t') id (id-is-equiv X) → s' ≡ t'
   S'-≡-structure X (s , α) (t , β) υ' = to-Σ-≡ (S-≡-structure X s t υ' , Axioms-is-prop X t _ _)

   S'-transport : (A' : Σ S')
                  (s' : S' ⟨ A' ⟩)
                  (υ' : S'-equiv A' (⟨ A' ⟩ , s') id (id-is-equiv ⟨ A' ⟩))
                → transport
                     (λ - → S'-equiv A' (⟨ A' ⟩ , -) id (id-is-equiv ⟨ A' ⟩))
                     (S'-≡-structure ⟨ A' ⟩ (structure A') s' υ')
                     (S'-refl A')
                ≡ υ'
   S'-transport (X , s , α) (t , β) υ' =
    f (S'-≡-structure X (s , α) (t , β) υ')          ≡⟨ transport-ap F pr₁ (S'-≡-structure X (s , α) (t , β) υ') ⟩
    g (ap pr₁ (S'-≡-structure X (s , α) (t , β) υ')) ≡⟨ ap g r ⟩
    g (S-≡-structure X s t υ')                       ≡⟨ S-transport (X , s) t υ' ⟩
    υ' ∎
    where
     F : S X → U ⊔ V ̇
     F t = S-equiv (X , s) (X  , t) id (id-is-equiv X)
     f : (s , α) ≡ (t , β) → F t
     f q = transport (F ∘ pr₁) q (S-refl (X , s))
     g : s ≡ t → F t
     g p = transport F p (S-refl (X , s))
     r : ap pr₁ (S'-≡-structure X (s , α) (t , β) υ') ≡ S-≡-structure X s t υ'
     r = ap-pr₁-to-Σ-≡ _

   open gsip U V ua S' S'-equiv S'-refl S'-≡-structure S'-transport public

\end{code}

We consider monoids to illustrate how this can be applied.

\begin{code}

open import UF-FunExt

module monoids (U : Universe) (ua : is-univalent U) where

 open import UF-Subsingletons-FunExt
 open import UF-UA-FunExt

 fe : funext U U
 fe = funext-from-univalence ua

 S : U ̇ → U ̇
 S X = (X → X → X) × X

 Axioms : (X : U ̇) → S X → U ̇
 Axioms X (_·_ , e) = is-set X ×
                      ((x y z : X) → (x · y) · z ≡ x · (y · z)) ×
                      ((x : X) → (e · x ≡ x) × (x · e ≡ x))

 Axioms-is-prop : (X : U ̇) (s : S X) → is-prop (Axioms X s)
 Axioms-is-prop X (_·_ , e) (i , α , ν) = ×-is-prop
                                           (is-prop-is-set fe)
                                           (×-is-prop
                                              (Π-is-prop fe
                                                 λ x → Π-is-prop fe
                                                         λ y → Π-is-prop fe
                                                                 λ z → i)
                                              (Π-is-prop fe λ x → ×-is-prop i i))
                                          (i , α , ν)

 mul : (A : Σ S) → ⟨ A ⟩ → ⟨ A ⟩ → ⟨ A ⟩
 mul (X , _·_ , e) = _·_

 neutral : (A : Σ S) → ⟨ A ⟩
 neutral (X , _·_ , e) = e

 open gsip-with-axioms
       U U ua S
       Axioms
       Axioms-is-prop
       (λ A B f e → ((λ x x' → f (mul A x x')) ≡ (λ x x' → mul B (f x) (f x')))
                  × (f (neutral A) ≡ neutral B))
       (λ A → refl , refl)
       (λ X m n υ → ×-≡ (pr₁ υ) (pr₂ υ))
       (λ { A m (refl , refl) → refl })

 Monoid : U ′ ̇
 Monoid = Σ \(X : U ̇) → Σ \(s : S X) → Axioms X s

 μ : (A : Monoid) → ⟨ A ⟩ → ⟨ A ⟩ → ⟨ A ⟩
 μ (X , s , a) = mul (X , s)

 η : (A : Monoid) → ⟨ A ⟩
 η (X , s , a) = neutral (X , s)

 fact : (A B : Monoid)
     → (A ≡ B)
     ≃ Σ \(f : ⟨ A ⟩ → ⟨ B ⟩)
             → is-equiv f
             × ((λ x x' → f (μ A x x')) ≡ (λ x x' → μ B (f x) (f x')))
             × (f (η A) ≡ η B)
 fact = ≡-is-≃ₛ

 fact' : (X : U ̇) (_·_ : X → X → X) (d : X) (α : Axioms X (_·_ , d))
         (Y : U ̇) (_⋆_ : Y → Y → Y) (e : Y) (β : Axioms Y (_⋆_ , e))
       → ((X , (_·_ , d) , α) ≡ (Y , (_⋆_ , e) , β))
       ≃ Σ \(f : X → Y)
               → is-equiv f
               × ((λ x x' → f (x · x')) ≡ (λ x x' → f x ⋆ f x'))
               × (f d ≡ e)
 fact' X _·_ d α Y _⋆_ e β = fact (X , ((_·_ , d) , α)) (Y , ((_⋆_ , e) , β))

\end{code}

Perhaps it is possible to derive the SIP for 1-categories from the
above SIP for types equipped with structure. But this is not the point
we are trying to make. The point is to give a criterion for natural
characterizations of equality of types equipped with structure, before
we know they form (∞-)categories, and even if they don't.

Another example that should be accounted for by the methods developed
here is equality of ordinals (in the module OrdinalOfOrdinals), which
is what prompted us to think about the subject of this module.
