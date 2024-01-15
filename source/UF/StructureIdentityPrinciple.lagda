Martin Escardo, August 2018. A structure identity principle.

There is a much better treatment of this here and so this file is
obsolete:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/

This is also ported in the module UF.SIP.

A structure identity principle (sip) for types, rather than categories
as in the HoTT Book.

This tries to make previous work by Coquand and Danielsson [1] more
general.

[1] https://www.sciencedirect.com/science/article/pii/S0019357713000694 , 2013

Contents:

 * The submodule UF.gsip has a very abstract version of sip.

 * This is followed by various submodules that consider more concrete
   examples such as ∞-magmas and much more.

 * The submodule UF.gsip-with-axioms considers structures subject to
   axioms, to easily account for mathematical structures such as
   monoids, groups, spaces, etc. This module UF.performs a reduction to
   the module UF.gsip.

 * This is followed by monoids as an example.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Sets
open import UF.Sets-Properties
open import UF.Univalence
open import UF.Yoneda

module UF.StructureIdentityPrinciple where

\end{code}

We consider the type Σ S of types X : 𝓤 ̇ equipped with structure s : S X,
where the universe U is univalent and S : 𝓤 ̇ → 𝓥 ̇ is a parameter.

The underlying set and structure are given by the first and second
projections:

\begin{code}

⟨_⟩ : {𝓤 𝓥 : Universe} {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
⟨_⟩ = pr₁

structure : {𝓤 𝓥 : Universe} {S : 𝓤 ̇ → 𝓥 ̇ } (A : Σ S) → S ⟨ A ⟩
structure = pr₂

\end{code}

 If S comes with suitable data, including S-equiv discussed
 below, we can characterize identity of elements of Σ S as equivalence
 of underlying sets subject to a suitable condition involving the
 data:

   (A ＝ B) ≃ Σ f ꞉ ⟨ A ⟩ → ⟨ B ⟩ , Σ e ꞉ is-equiv f , S-equiv A B (f , e)

 It is important that such a condition is not necessarily property but
 actually data in general.

 Thus

  (1) For an equivalence f : ⟨ A ⟩ → ⟨ B ⟩ we want data that
      establishes that it is an equivalence in the sense of
      S-structure, in some abstract sense, specified by S-equiv.

 One possible list of data for S and S-equiv is the following:

  (2) We want data showing that the identity equivalence ≃-refl ⟨ A ⟩
      is an S-equivalence, given by S-refl.

  (3) Moreover, when f : ⟨ X , s ⟩ → ⟨ X , t ⟩ is the identity
      function, we want the data for (1) to give data for the identity
      s ＝ t of structures. This is specified by the function
      S-id-structure.

  (4) We need a technical transport condition (which is not
      surprising, as identity in Σ-types is given by transport of the
      second component), specified by the function S-transport below,
      relating the data specified by the functions S-id-structure and
      S-refl.

 These assumptions (1)-(4) are given as module UF.parameters for gsip:

\begin{code}

module gsip

  (𝓤 𝓥 : Universe)

  (ua : is-univalent 𝓤)

  (S : 𝓤 ̇ → 𝓥 ̇ )

  (S-equiv : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇ )

  (S-refl : (A : Σ S) → S-equiv A A (≃-refl ⟨ A ⟩))

  (S-id-structure : (X : 𝓤 ̇ ) (s t : S X)
                  → S-equiv (X , s) (X , t) (≃-refl X) → s ＝ t)

  (S-transport : (A : Σ S)
                 (s : S ⟨ A ⟩)
                 (υ : S-equiv A (⟨ A ⟩ , s) (≃-refl ⟨ A ⟩))
               → transport
                    (λ - → S-equiv A (⟨ A ⟩ , -) (≃-refl ⟨ A ⟩))
                    (S-id-structure ⟨ A ⟩ (structure A) s υ)
                    (S-refl A)
               ＝ υ)
  where

\end{code}

  Under these assumptions, we show that identity in Σ S is equivalent
  to _≃ₛ_ defined as follows:

\begin{code}

  _≃ₛ_ : Σ S → Σ S → 𝓤 ⊔ 𝓥 ̇
  A ≃ₛ B = Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩) , Σ e ꞉ is-equiv f , S-equiv A B (f , e)

\end{code}

  This defines a Σ S - equivalence to be an equivalence of underlying
  sets that is an S-structure equivalence in the sense abstractly
  specified by the function S-equiv. Then the assumption S-refl
  allows us to have an equivalence of any element of Σ S with itself:

\begin{code}

  ≃ₛ-refl : (A : Σ S) → A ≃ₛ A
  ≃ₛ-refl A = pr₁(≃-refl ⟨ A ⟩) , pr₂(≃-refl ⟨ A ⟩) , S-refl A

\end{code}

  And hence an identity gives a Σ S - equivalence by induction in the
  usual way:

\begin{code}

  idtoeqₛ : (A B : Σ S) → A ＝ B → A ≃ₛ B
  idtoeqₛ A .A refl = ≃ₛ-refl A

\end{code}

  We use the following auxiliary constructions to define an inverse of
  idtoeqₛ by equivalence induction (the function JEq):

\begin{code}

  private
    Ψ : (A : Σ S) (Y : 𝓤 ̇ ) → ⟨ A ⟩ ≃ Y → 𝓤 ⁺ ⊔ 𝓥 ̇
    Ψ A Y e = (s : S Y) → S-equiv A (Y , s) e → A ＝ (Y , s)
    ψ : (A : Σ S) → Ψ A ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    ψ A s υ = to-Σ-＝' (S-id-structure ⟨ A ⟩ (structure A) s υ)

  eqtoidₛ : (A B : Σ S) → A ≃ₛ B → A ＝ B
  eqtoidₛ A B (f , e , υ) = JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ B ⟩ (f , e) (structure B) υ

\end{code}

  So far we have used the hypotheses

     * S-equiv (to define _＝ₛ_),
     * S-refl (to define idtoeqₛ), and
     * S-id-structure (to define eqtoidₛ).

  Next we use the remaining hypothesis S-transport to show that
  eqtoidₛ is a section of idtoeqₛ:

\begin{code}

  idtoeq-eqtoidₛ : (A B : Σ S) (ε : A ≃ₛ B) → idtoeqₛ A B (eqtoidₛ A B ε) ＝ ε
  idtoeq-eqtoidₛ A B (f , e , υ) = JEq ua ⟨ A ⟩ Φ φ ⟨ B ⟩ (f , e) (structure B) υ
   where
    Φ : (Y : 𝓤 ̇ ) → ⟨ A ⟩ ≃ Y → 𝓤 ⊔ 𝓥 ̇
    Φ Y (f , e) = (s : S Y)
                  (υ : S-equiv A (Y , s) (f , e))
                 → idtoeqₛ A (Y , s) (eqtoidₛ A (Y , s) (f , e , υ)) ＝ f , e , υ
    φ : Φ ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    φ s υ =
      idtoeqₛ A A' (eqtoidₛ A A' refl')
            ＝⟨ ap (λ h → idtoeqₛ A A' (h s υ)) (JEq-comp ua ⟨ A ⟩ (Ψ A) (ψ A)) ⟩
      idtoeqₛ A A' (to-Σ-＝' p)
            ＝⟨ h p ⟩
      pr₁(≃-refl ⟨ A ⟩) , pr₂(≃-refl ⟨ A ⟩) , g p
            ＝⟨ to-Σ-＝' (to-Σ-＝' (S-transport A s υ)) ⟩
      refl' ∎
     where
      A' : Σ S
      A' = ⟨ A ⟩ , s
      refl' : A ≃ₛ A'
      refl' = pr₁(≃-refl ⟨ A ⟩) , pr₂(≃-refl ⟨ A ⟩) , υ
      g : structure A ＝ s → S-equiv A A' (≃-refl ⟨ A ⟩)
      g p = transport (λ - → S-equiv A (⟨ A ⟩ , -) (≃-refl ⟨ A ⟩)) p (S-refl A)
      h : (p : structure A ＝ s) → idtoeqₛ A A' (to-Σ-＝' p)
                                ＝ pr₁(≃-refl ⟨ A ⟩) , pr₂(≃-refl ⟨ A ⟩) , g p
      h refl = refl
      p : structure A ＝ s
      p = S-id-structure ⟨ A ⟩ (structure A) s υ

\end{code}

  Being a natural section of idtoeqₛ, the function eqtoidₛ is also a
  retraction, by a general property of the identity type (namely the
  one called nat-retraction-is-equiv in our development (in the module
  UF.Yoneda)):

\begin{code}

  uaₛ : (A B : Σ S) → is-equiv (idtoeqₛ A B)
  uaₛ A = nats-with-sections-are-equivs A
            (idtoeqₛ A)
            (λ B → eqtoidₛ A B , idtoeq-eqtoidₛ A B)

  eqtoid-idtoeqₛ : (A B : Σ S) (p : A ＝ B) → eqtoidₛ A B (idtoeqₛ A B p) ＝ p
  eqtoid-idtoeqₛ A B = pr₁(pr₂ (equivs-are-qinvs (idtoeqₛ A B) (uaₛ A B)))

  ＝-is-≃ₛ : (A B : Σ S) → (A ＝ B) ≃ (A ≃ₛ B)
  ＝-is-≃ₛ A B = idtoeqₛ A B , uaₛ A B

  _≃ₛ'_ : Σ S → Σ S → 𝓤 ⊔ 𝓥 ̇
  A ≃ₛ' B = Σ p ꞉ ⟨ A ⟩ ≃ ⟨ B ⟩ , S-equiv A B (pr₁ p , pr₂ p)

  ≃ₛ-is-≃ₛ' : (A B : Σ S) → (A ≃ₛ B) ≃ (A ≃ₛ' B)
  ≃ₛ-is-≃ₛ' A B = ≃-sym Σ-assoc

  ＝-is-≃ₛ' : (A B : Σ S) → (A ＝ B) ≃ (A ≃ₛ' B)
  ＝-is-≃ₛ' A B = (＝-is-≃ₛ A B) ● (≃ₛ-is-≃ₛ' A B)

\end{code}

  This completes the proof of the abstract SIP considered here.


We now consider some concrete examples to illustrate how this works in
practice.

An ∞-magma is a type, not assumed to be a set, equipped with a binary
operation. The above gives a characterization of identity of ∞-magmas:

\begin{code}

module ∞-magma (𝓤 : Universe) (ua : is-univalent 𝓤) where

 S : 𝓤 ̇ → 𝓤 ̇
 S X = X → X → X

 S-equiv : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
 S-equiv A B (f , e) = (λ x x' → f (structure A x x')) ＝ (λ x x' → structure B (f x) (f x'))

 S-refl : (A : Σ S) → S-equiv A A (≃-refl ⟨ A ⟩)
 S-refl A = refl

 S-id-structure : (X : 𝓤 ̇ ) (s t : S X) → S-equiv (X , s) (X , t) (≃-refl X) → s ＝ t
 S-id-structure X m n = id

 S-transport : (A : Σ S)
                 (s : S ⟨ A ⟩)
                 (υ : S-equiv A (⟨ A ⟩ , s) (≃-refl ⟨ A ⟩))
               → transport
                    (λ - → S-equiv A (⟨ A ⟩ , -) (≃-refl ⟨ A ⟩))
                    (S-id-structure ⟨ A ⟩ (structure A) s υ)
                    (S-refl A)
               ＝ υ
 S-transport A m υ = refl-left-neutral

 open gsip 𝓤 𝓤 ua S S-equiv S-refl S-id-structure S-transport

 ∞-Magma : 𝓤 ⁺ ̇
 ∞-Magma = Σ S

 fact : (A B : ∞-Magma)
      → (A ＝ B) ≃ (Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩)
                       , is-equiv f
                       × ((λ x x' → f (structure A x x')) ＝ (λ x x' → structure B (f x) (f x'))))
 fact = ＝-is-≃ₛ

\end{code}

 Perhaps the following reformulation is more appealing, where Agda
 infers that (X , _·_) and (Y , _*_) are ∞-Magmas from the *proof*
 "fact" of "fact'":

\begin{code}

 fact' : (X Y : 𝓤 ̇ ) (_·_ : X → X → X) (_*_ : Y → Y → Y)
       → ((X , _·_) ＝ (Y , _*_))
       ≃ (Σ f ꞉ (X → Y) , is-equiv f × ((λ x x' → f (x · x')) ＝ (λ x x' → f x * f x')))
 fact' X Y _·_ _*_ = fact (X , _·_) (Y , _*_)

\end{code}

 Of course, the condition (λ x x' → f (x · x')) ＝ (λ x x' → f x ⋆ f x')
 is equivalent to (x x' : X) → f (x · x') ＝ f x ⋆ f x' by function
 extensionality. Hence the congruence of the type-theoretic operations
 gives that the identifications of ∞-Magmas are (equivalent to) a
 homomorphic equivalences:

\begin{code}

 open import UF.FunExt
 open import UF.UA-FunExt
 open import UF.EquivalenceExamples

 fe : funext 𝓤 𝓤
 fe = univalence-gives-funext ua

 fact'' : (X Y : 𝓤 ̇ ) (_·_ : X → X → X) (_*_ : Y → Y → Y)
        → ((X , _·_) ＝ (Y , _*_))
        ≃ (Σ f ꞉ (X → Y) , is-equiv f × ((x x' : X) → f (x · x') ＝ f x * f x'))
 fact'' X Y _·_ _*_ =
   ((X , _·_) ＝ (Y , _*_))
       ≃⟨ fact' X Y _·_ _*_ ⟩
   (Σ f ꞉ (X → Y) , is-equiv f × ((λ x x' → f (x · x')) ＝ (λ x x' → f x * f x')))
       ≃⟨ Σ-cong (λ f → ×-cong (≃-refl (is-equiv f)) (≃-funext₂ fe fe _ _)) ⟩
   (Σ f ꞉ (X → Y) , is-equiv f × ((x x' : X) → f (x · x') ＝ f x * f x')) ■

\end{code}

 It is automatic that the inverse of f is also a magma homomorphism
 (exercise, perhaps worth adding). However, it is not the case, in the
 absence of the underlying types being sets, that equivalences of
 ∞-magmas are pairs of mutually inverse homomorphisms, for the same
 reason that equivalences of types are not in general equivalent to
 pairs of mutually inverse functions (quasi-equivalences, in the
 terminology of the HoTT book).

As a second example, a topology on a set X is a set of subsets of X
satisfying suitable axioms. A set of subsets amounts to a map
(X → Ω) → Ω. Dropping the assumption that the type X is a set and the
axioms for topologies, and generalizing Ω to an arbitrary type R, we
get ∞-proto-topological spaces.

\begin{code}

module ∞-proto-topological-spaces (𝓤 𝓥 : Universe) (ua : is-univalent 𝓤) (R : 𝓥 ̇ ) where

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = (X → R) → R

 open gsip
       𝓤 (𝓤 ⊔ 𝓥) ua S
       (λ {A B (f , e) → (λ V → structure A (V ∘ f)) ＝ structure B})
       (λ A → refl)
       (λ X τ σ → id)
       (λ A τ υ → refl-left-neutral)

 fact : (A B : Σ S)
      → (A ＝ B) ≃ (Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩)
                       , is-equiv f × ((λ V → structure A (λ x → V (f x))) ＝ structure B))
 fact = ＝-is-≃ₛ

\end{code}

 Or in perhaps more appealing terms:

\begin{code}

 fact' : (X Y : 𝓤 ̇ ) (τ : (X → R) → R) (σ : (Y → R) → R)
       → ((X , τ) ＝ (Y , σ)) ≃ (Σ f ꞉ (X → Y) , is-equiv f × ((λ V → τ (V ∘ f)) ＝ σ))
 fact' X Y σ τ = fact (X , σ) (Y , τ)

\end{code}

 Again by function extensionality, structure preservation is equivalent
 to (V : Y → R) → τ(V ∘ f) ＝ σ V. We can read this, at least when R is
 the type Ω of truth-values, as saying that a set V : Y → R is σ-open
 precisely when its inverse image V ∘ f is τ-open.

 Thus, if we say that an equivalence f : X → Y is an ∞-homeomorphism
 when an "R-set" V : Y → R is σ-open precisely when its f-inverse image
 V ∘ f : X → R is τ-open, then the above says that two
 ∞-proto-topological spaces are equal iff they are ∞-homeomorphic.

Another example generalizes metric spaces (when R is a type of reals)
and ordered sets (when R is Ω and d=_≺_, reflexive or not):

\begin{code}

module ∞-proto-metric-spaces (𝓤 𝓥 : Universe) (ua : is-univalent 𝓤) (R : 𝓥 ̇ ) where

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → X → R

 open gsip
       𝓤 (𝓤 ⊔ 𝓥) ua S
       (λ {A B (f , e) → structure A ＝ (λ x x' → structure B (f x) (f x'))})
       (λ A → refl)
       (λ X d e → id)
       (λ A s υ → refl-left-neutral)

 fact : (A B : Σ S)
      → (A ＝ B) ≃ (Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩)
                       , is-equiv f × (structure A ＝ (λ x x' → structure B (f x) (f x'))))
 fact = ＝-is-≃ₛ

 fact' : (X Y : 𝓤 ̇ ) (d : X → X → R) (e : Y → Y → R)
       → ((X , d) ＝ (Y , e)) ≃ (Σ f ꞉ (X → Y) , is-equiv f × (d ＝ (λ x x' → e (f x) (f x'))))
 fact' X Y σ τ = fact (X , σ) (Y , τ)

\end{code}

 Notice that here the S-equivalences are the isometries (metric-space case)
 or order preserving-reflecting maps (ordered-set case).

The following example is related to compact types (in the sense of the
module CompactTypes):

\begin{code}

module selection-spaces (𝓤 𝓥 : Universe) (ua : is-univalent 𝓤) (R : 𝓥 ̇ ) where

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = (X → R) → X

 open gsip
       𝓤 (𝓤 ⊔ 𝓥) ua S
       (λ {A B (f , e) → (λ V → f (structure A (V ∘ f))) ＝ structure B})
       (λ A → refl)
       (λ X ε δ → id)
       (λ A τ υ → refl-left-neutral)

 fact : (A B : Σ S)
      → (A ＝ B) ≃ (Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩)
                       , is-equiv f × ((λ V → f(structure A (λ x → V (f x)))) ＝ structure B))
 fact = ＝-is-≃ₛ

 fact' : (X Y : 𝓤 ̇ ) (ε : (X → R) → X) (δ : (Y → R) → Y)
       → ((X , ε) ＝ (Y , δ)) ≃ (Σ f ꞉ (X → Y) , is-equiv f × ((λ V → f (ε (V ∘ f))) ＝ δ))
 fact' X Y σ τ = fact (X , σ) (Y , τ)

\end{code}

We now continue our abstract development, to account for things such
as monoids and groups and topological spaces. We consider given axioms
on X and its structure.

\begin{code}

open import UF.Subsingletons

module gsip-with-axioms

 (𝓤 𝓥 : Universe)

 (ua : is-univalent 𝓤)

 (S : 𝓤 ̇ → 𝓥 ̇ )

 (Axioms : (X : 𝓤 ̇ ) → S X → 𝓥 ̇ )

 (Axioms-is-prop : (X : 𝓤 ̇ ) (s : S X) → is-prop (Axioms X s))

 (S-equiv : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇ )

 (S-refl : (A : Σ S) → S-equiv A A (≃-refl ⟨ A ⟩))

 (S-id-structure : (X : 𝓤 ̇ ) (s t : S X)
                 → S-equiv (X , s) (X , t) (≃-refl X) → s ＝ t)

 (S-transport : (A : Σ S)
                (s : S ⟨ A ⟩)
                (υ : S-equiv A (⟨ A ⟩ , s) (≃-refl ⟨ A ⟩))
              → transport
                   (λ - → S-equiv A (⟨ A ⟩ , -) (≃-refl ⟨ A ⟩))
                   (S-id-structure ⟨ A ⟩ (structure A) s υ)
                   (S-refl A)
              ＝ υ)
 where

\end{code}

   Our reduction of gsip-with-axioms to gsip is as follows:

\begin{code}

   S' : 𝓤 ̇ → 𝓥 ̇
   S' X = Σ s ꞉ S X , Axioms X s

   S'-preserving : (A' B' : Σ S') → ⟨ A' ⟩ ≃ ⟨ B' ⟩ → 𝓤 ⊔ 𝓥 ̇
   S'-preserving (X , s , α) (Y , t , β) = S-equiv (X , s) (Y , t)

   S'-refl : (A' : Σ S') → S'-preserving A' A' (≃-refl ⟨ A' ⟩)
   S'-refl (X , s , α) = S-refl (X , s)

   S'-id-structure : (X : 𝓤 ̇ ) (s' t' : S' X)
                   → S'-preserving (X , s') (X , t') (≃-refl X) → s' ＝ t'
   S'-id-structure X (s , α) (t , β) υ' = to-Σ-＝ (S-id-structure X s t υ' ,
                                                   Axioms-is-prop X t _ _)

   S'-transport : (A' : Σ S')
                  (s' : S' ⟨ A' ⟩)
                  (υ' : S'-preserving A' (⟨ A' ⟩ , s') (≃-refl ⟨ A' ⟩))
                → transport
                     (λ - → S'-preserving A' (⟨ A' ⟩ , -) (≃-refl ⟨ A' ⟩))
                     (S'-id-structure ⟨ A' ⟩ (structure A') s' υ')
                     (S'-refl A')
                ＝ υ'
   S'-transport (X , s , α) (t , β) υ' =
    f (S'-id-structure X (s , α) (t , β) υ')
        ＝⟨ transport-ap F pr₁ (S'-id-structure X (s , α) (t , β) υ') ⟩
    g (ap pr₁ (S'-id-structure X (s , α) (t , β) υ'))
        ＝⟨ ap g r ⟩
    g (S-id-structure X s t υ')
        ＝⟨ S-transport (X , s) t υ' ⟩
    υ'  ∎
    where
     F : S X → 𝓤 ⊔ 𝓥 ̇
     F t = S-equiv (X , s) (X  , t) (≃-refl X)
     f : (s , α) ＝ (t , β) → F t
     f q = transport (F ∘ pr₁) q (S-refl (X , s))
     g : s ＝ t → F t
     g p = transport F p (S-refl (X , s))
     r : ap pr₁ (S'-id-structure X (s , α) (t , β) υ') ＝ S-id-structure X s t υ'
     r = ap-pr₁-to-Σ-＝ _

\end{code}

   We export gsip with the above data:

\begin{code}

   open gsip 𝓤 𝓥 ua S' S'-preserving S'-refl S'-id-structure S'-transport public

\end{code}

   And this completes the reduction to gsip.

We now consider monoids to illustrate how this can be applied.

\begin{code}

module monoids (𝓤 : Universe) (ua : is-univalent 𝓤) where

 open import UF.FunExt
 open import UF.Subsingletons-FunExt
 open import UF.UA-FunExt

 fe : funext 𝓤 𝓤
 fe = univalence-gives-funext ua

\end{code}

The structure of a monoid with underlying type X consists of a binary
"multiplication" operation X → X → X and a distinguished point of X,
the "unit":

\begin{code}

 S : 𝓤 ̇ → 𝓤 ̇
 S X = (X → X → X) × X

\end{code}

The axioms say that not only multiplication must be associative and
the unit must be neutral for this operation, but also the underlying
type X must a set:

\begin{code}

 Axioms : (X : 𝓤 ̇ ) → S X → 𝓤 ̇
 Axioms X (_·_ , e) = is-set X
                    × ((x y z : X) → (x · y) · z ＝ x · (y · z))
                    × ((x : X) → (e · x ＝ x) × (x · e ＝ x))

\end{code}

The fact that the underlying type is a set gives that the axioms form
a proposition:

\begin{code}

 Axioms-is-prop : (X : 𝓤 ̇ ) (s : S X) → is-prop (Axioms X s)
 Axioms-is-prop X (_·_ , e) (i , α , ν) = ×-is-prop
                                           (being-set-is-prop fe)
                                           (×-is-prop
                                              (Π-is-prop fe
                                                 λ x → Π-is-prop fe
                                                         λ y → Π-is-prop fe
                                                                 λ z → i)
                                              (Π-is-prop fe λ x → ×-is-prop i i))
                                          (i , α , ν)
\end{code}

We use primed capital letters for types equipped with axiomless
structure. The following to functions extract the multiplication and
unit:

\begin{code}

 mul : (A' : Σ S) → ⟨ A' ⟩ → ⟨ A' ⟩ → ⟨ A' ⟩
 mul (X , _·_ , e) = _·_

 unit : (A' : Σ S) → ⟨ A' ⟩
 unit (X , _·_ , e) = e

\end{code}

A monoid is a type equipped with such structure and witnesses for the
axioms:

\begin{code}

 Monoid : 𝓤 ⁺ ̇
 Monoid = Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , Axioms X s

\end{code}

We again have multiplication and unit extraction functions:

\begin{code}

 μ : (A : Monoid) → ⟨ A ⟩ → ⟨ A ⟩ → ⟨ A ⟩
 μ (X , s , α) = mul (X , s)

 η : (A : Monoid) → ⟨ A ⟩
 η (X , s , α) = unit (X , s)

\end{code}

And now we are ready to apply gsip-with-axioms to our situation:

\begin{code}

 open gsip-with-axioms
       𝓤 𝓤 ua S
       Axioms
       Axioms-is-prop
       (λ {A' B' (f , e) → ((λ x x' → f (mul A' x x')) ＝ (λ x x' → mul B' (f x) (f x')))
                         × (f (unit A') ＝ unit B')})
       (λ A' → refl , refl)
       (λ X m n υ → to-×-＝ (pr₁ υ) (pr₂ υ))
       (λ { A' m (refl , refl) → refl })

 fact : (A B : Monoid)
      → (A ＝ B)
      ≃ (Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩)
             , is-equiv f
             × ((λ x x' → f (μ A x x')) ＝ (λ x x' → μ B (f x) (f x')))
             × (f (η A) ＝ η B))
 fact = ＝-is-≃ₛ

 fact' : (X : 𝓤 ̇ ) (_·_ : X → X → X) (d : X) (α : Axioms X (_·_ , d))
         (Y : 𝓤 ̇ ) (_*_ : Y → Y → Y) (e : Y) (β : Axioms Y (_*_ , e))
       → ((X , (_·_ , d) , α) ＝ (Y , (_*_ , e) , β))
       ≃ (Σ f ꞉ (X → Y)
              , is-equiv f
              × ((λ x x' → f (x · x')) ＝ (λ x x' → f x * f x'))
              × (f d ＝ e))
 fact' X _·_ d α Y _*_ e β = fact (X , ((_·_ , d) , α)) (Y , ((_*_ , e) , β))

\end{code}

Perhaps it is possible to derive the SIP for 1-categories from the
above SIP for types equipped with structure. But this is not the point
we are trying to make. The point is to give a criterion for natural
characterizations of identity of types equipped with structure, and
possibly axioms for them, before we know they form (∞-)categories, and
even if they don't.

Another example that should be accounted for by the methods developed
here is identity of ordinals (in the module ), which
is what prompted us to think about the subject of this module.

Added 8th December 2018. I came across a situation where the universe
levels don't work if the axioms apply only to the underlying set (and
not to the structure). Here is a version that addresses that:

\begin{code}

module gsip'

  (𝓤 𝓥 𝓦 : Universe)

  (ua : is-univalent 𝓤)

  (S : 𝓤 ̇ → 𝓥 ̇ )

  (S-equiv : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )

  (S-refl : (A : Σ S) → S-equiv A A (≃-refl ⟨ A ⟩))

  (S-id-structure : (X : 𝓤 ̇ ) (s t : S X)
                  → S-equiv (X , s) (X , t) (≃-refl X) → s ＝ t)

  (S-transport : (A : Σ S)
                 (s : S ⟨ A ⟩)
                 (υ : S-equiv A (⟨ A ⟩ , s) (≃-refl ⟨ A ⟩))
               → transport
                    (λ - → S-equiv A (⟨ A ⟩ , -) (≃-refl ⟨ A ⟩))
                    (S-id-structure ⟨ A ⟩ (structure A) s υ)
                    (S-refl A)
               ＝ υ)
  where

  _≃ₛ_ : Σ S → Σ S → 𝓤 ⊔ 𝓦 ̇
  A ≃ₛ B = Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩) , Σ e ꞉ is-equiv f , S-equiv A B (f , e)

  ≃ₛ-refl : (A : Σ S) → A ≃ₛ A
  ≃ₛ-refl A = pr₁(≃-refl ⟨ A ⟩) , pr₂(≃-refl ⟨ A ⟩) , S-refl A

  idtoeqₛ : (A B : Σ S) → A ＝ B → A ≃ₛ B
  idtoeqₛ A .A refl = ≃ₛ-refl A

  private
    Ψ : (A : Σ S) (Y : 𝓤 ̇ ) → ⟨ A ⟩ ≃ Y → 𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓦 ̇
    Ψ A Y e = (s : S Y) → S-equiv A (Y , s) e → A ＝ (Y , s)
    ψ : (A : Σ S) → Ψ A ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    ψ A s υ = to-Σ-＝' (S-id-structure ⟨ A ⟩ (structure A) s υ)

  eqtoidₛ : (A B : Σ S) → A ≃ₛ B → A ＝ B
  eqtoidₛ A B (f , e , υ) = JEq ua ⟨ A ⟩ (Ψ A) (ψ A) ⟨ B ⟩ (f , e) (structure B) υ

  idtoeq-eqtoidₛ : (A B : Σ S) (ε : A ≃ₛ B) → idtoeqₛ A B (eqtoidₛ A B ε) ＝ ε
  idtoeq-eqtoidₛ A B (f , e , υ) = JEq ua ⟨ A ⟩ Φ φ ⟨ B ⟩ (f , e) (structure B) υ
   where
    Φ : (Y : 𝓤 ̇ ) → ⟨ A ⟩ ≃ Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
    Φ Y (f , e) = (s : S Y)
                  (υ : S-equiv A (Y , s) (f , e))
                 → idtoeqₛ A (Y , s) (eqtoidₛ A (Y , s) (f , e , υ)) ＝ f , e , υ
    φ : Φ ⟨ A ⟩ (≃-refl ⟨ A ⟩)
    φ s υ =
      idtoeqₛ A A' (eqtoidₛ A A' refl')
            ＝⟨ ap (λ h → idtoeqₛ A A' (h s υ)) (JEq-comp ua ⟨ A ⟩ (Ψ A) (ψ A)) ⟩
      idtoeqₛ A A' (to-Σ-＝' p)
            ＝⟨ h p ⟩
      pr₁(≃-refl ⟨ A ⟩) , pr₂(≃-refl ⟨ A ⟩) , g p
            ＝⟨ to-Σ-＝' (to-Σ-＝' (S-transport A s υ)) ⟩
      refl' ∎
     where
      A' : Σ S
      A' = ⟨ A ⟩ , s
      refl' : A ≃ₛ A'
      refl' = pr₁(≃-refl ⟨ A ⟩) , pr₂(≃-refl ⟨ A ⟩) , υ
      g : structure A ＝ s → S-equiv A A' (≃-refl ⟨ A ⟩)
      g p = transport (λ - → S-equiv A (⟨ A ⟩ , -) (≃-refl ⟨ A ⟩)) p (S-refl A)
      h : (p : structure A ＝ s) → idtoeqₛ A A' (to-Σ-＝' p)
                                ＝ pr₁(≃-refl ⟨ A ⟩) , pr₂(≃-refl ⟨ A ⟩) , g p
      h refl = refl
      p : structure A ＝ s
      p = S-id-structure ⟨ A ⟩ (structure A) s υ

  uaₛ : (A B : Σ S) → is-equiv (idtoeqₛ A B)
  uaₛ A = nats-with-sections-are-equivs A
            (idtoeqₛ A)
            (λ B → eqtoidₛ A B , idtoeq-eqtoidₛ A B)

  eqtoid-idtoeqₛ : (A B : Σ S) (p : A ＝ B) → eqtoidₛ A B (idtoeqₛ A B p) ＝ p
  eqtoid-idtoeqₛ A B = pr₁(pr₂ (equivs-are-qinvs (idtoeqₛ A B) (uaₛ A B)))

  ＝-is-≃ₛ : (A B : Σ S) → (A ＝ B) ≃ (A ≃ₛ B)
  ＝-is-≃ₛ A B = idtoeqₛ A B , uaₛ A B

  _≃ₛ'_ : Σ S → Σ S → 𝓤 ⊔ 𝓦 ̇
  A ≃ₛ' B = Σ p ꞉ ⟨ A ⟩ ≃ ⟨ B ⟩ , S-equiv A B (pr₁ p , pr₂ p)

  ≃ₛ-is-≃ₛ' : (A B : Σ S) → (A ≃ₛ B) ≃ (A ≃ₛ' B)
  ≃ₛ-is-≃ₛ' A B = ≃-sym Σ-assoc

  ＝-is-≃ₛ' : (A B : Σ S) → (A ＝ B) ≃ (A ≃ₛ' B)
  ＝-is-≃ₛ' A B = (＝-is-≃ₛ A B) ● (≃ₛ-is-≃ₛ' A B)

module gsip-with-axioms'

 (𝓤 𝓥 𝓦 𝓣 : Universe)

 (ua : is-univalent 𝓤)

 (S : 𝓤 ̇ → 𝓥 ̇ )

 (Axioms : (X : 𝓤 ̇ ) → S X → 𝓣 ̇ )

 (Axioms-is-prop : (X : 𝓤 ̇ ) (s : S X) → is-prop (Axioms X s))

 (S-equiv : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )

 (S-refl : (A : Σ S) → S-equiv A A (≃-refl ⟨ A ⟩))

 (S-id-structure : (X : 𝓤 ̇ ) (s t : S X)
                 → S-equiv (X , s) (X , t) (≃-refl X) → s ＝ t)

 (S-transport : (A : Σ S)
                (s : S ⟨ A ⟩)
                (υ : S-equiv A (⟨ A ⟩ , s) (≃-refl ⟨ A ⟩))
              → transport
                   (λ - → S-equiv A (⟨ A ⟩ , -) (≃-refl ⟨ A ⟩))
                   (S-id-structure ⟨ A ⟩ (structure A) s υ)
                   (S-refl A)
              ＝ υ)
 where

   S' : 𝓤 ̇ → 𝓥 ⊔ 𝓣 ̇
   S' X = Σ s ꞉ S X , Axioms X s

   S'-preserving : (A' B' : Σ S') → ⟨ A' ⟩ ≃ ⟨ B' ⟩ → 𝓦 ̇
   S'-preserving (X , s , α) (Y , t , β) = S-equiv (X , s) (Y , t)

   S'-refl : (A' : Σ S') → S'-preserving A' A' (≃-refl ⟨ A' ⟩)
   S'-refl (X , s , α) = S-refl (X , s)

   S'-id-structure : (X : 𝓤 ̇ ) (s' t' : S' X)
                   → S'-preserving (X , s') (X , t') (≃-refl X) → s' ＝ t'
   S'-id-structure X (s , α) (t , β) υ' = to-Σ-＝ (S-id-structure X s t υ' ,
                                                   Axioms-is-prop X t _ _)

   S'-transport : (A' : Σ S')
                  (s' : S' ⟨ A' ⟩)
                  (υ' : S'-preserving A' (⟨ A' ⟩ , s') (≃-refl ⟨ A' ⟩))
                → transport
                     (λ - → S'-preserving A' (⟨ A' ⟩ , -) (≃-refl ⟨ A' ⟩))
                     (S'-id-structure ⟨ A' ⟩ (structure A') s' υ')
                     (S'-refl A')
                ＝ υ'
   S'-transport (X , s , α) (t , β) υ' =
    f (S'-id-structure X (s , α) (t , β) υ')
        ＝⟨ transport-ap F pr₁ (S'-id-structure X (s , α) (t , β) υ') ⟩
    g (ap pr₁ (S'-id-structure X (s , α) (t , β) υ'))
        ＝⟨ ap g r ⟩
    g (S-id-structure X s t υ')
        ＝⟨ S-transport (X , s) t υ' ⟩
    υ'  ∎
    where
     F : S X → 𝓦 ̇
     F t = S-equiv (X , s) (X  , t) (≃-refl X)
     f : (s , α) ＝ (t , β) → F t
     f q = transport (F ∘ pr₁) q (S-refl (X , s))
     g : s ＝ t → F t
     g p = transport F p (S-refl (X , s))
     r : ap pr₁ (S'-id-structure X (s , α) (t , β) υ') ＝ S-id-structure X s t υ'
     r = ap-pr₁-to-Σ-＝ _

   open gsip' 𝓤 (𝓥 ⊔ 𝓣) 𝓦 ua S' S'-preserving S'-refl S'-id-structure S'-transport public

\end{code}

TODO. Maybe replace the original versions by this last version. This
requires changing the existing code that uses the original, less
general, version. Or redefining the original version as an instance of
the new version.
