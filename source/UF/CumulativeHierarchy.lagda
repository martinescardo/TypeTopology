Tom de Jong, 28 October 2022 - 7 November 2022.
In collaboration with Nicolai Kraus, Fredrik Norvall Forsberg and Chuangjie Xu.

We define the induction principle (with a non-judgemental computation principle)
of the cumulative hierarchy 𝕍 (with respect to a type universe 𝓤) as introduced
in Section 10.5 of the HoTT Book [1]. Using the induction principle we formulate
what it means for the cumulative hierarchy to exist, so that can use it as an
(module) assumption in further developments.

For example, in Ordinals/CumulativeHierarchy we show that the (type theoretic)
ordinal of set theoretic ordinals in 𝕍 (w.r.t. 𝓤) is isomorphic to the ordinal
of ordinals in 𝓤.

This file has three parts:
(I)    Introduction of the cumulative hierarchy 𝕍 and the statement of its
       (most general) induction principle.
(II)   Statements and proofs of some simpler, more specialised, induction and
       recursion principles for 𝕍.
(III)  Basic constructions and proofs for 𝕍, i.e. the definition of set
       membership (∈), subset relation (⊆) and proofs of ∈-extensionality and
       ∈-induction.

The cumulative hierarchy 𝕍 can be seen as a HoTT-refined version of Aczel's [2]
type theoretic interpretation of constructive set theory and draws inspiration
form Joyal and Moerdijk's [3] algebraic set theory.

References
----------

[1] The Univalent Foundations Program
    Homotopy Type Theory: Univalent Foundations of Mathematics
    https://homotopytypetheory.org/book
    Institute for Advanced Study
    2013

[2] Peter Aczel
    The type theoretic interpretation of constructive set theory
    In A. MacIntyre, L. Pacholski, and J. Paris (eds.) Logic Colloquium ’77
    Volume 96 of Studies in Logic and the Foundations of Mathematics
    Pages 55–66
    North-Holland Publishing Company
    1978
    doi:10.1016/S0049-237X(08)71989-X

[3] A. Joyal and I. Moerdijk
    Algebraic set theory
    Volume 220 of London Mathematical Society Lecture Note Series
    Cambridge University Press
    1995
    doi:10.1017/CBO9780511752483

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

module UF.CumulativeHierarchy
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.Base hiding (_≈_)
open import UF.Subsingletons-FunExt

_≲_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓣 ̇ } → (A → X) → (B → X) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
_≲_ {𝓤} {𝓥} {𝓣} {A} {B} f g = (a : A) → ∃ b ꞉ B , g b ＝ f a

-- Note that _≈_ says that f and g have equal images
_≈_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓣 ̇ } → (A → X) → (B → X) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
f ≈ g = f ≲ g × g ≲ f

≈-sym : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓣 ̇ } {f : A → X} {g : B → X}
      → f ≈ g → g ≈ f
≈-sym (u , v) = (v , u)

\end{code}

Part I
------

Introduction of the cumulative hierarchy 𝕍 and the statement of its (most
general) induction principle.

See Section 10.5 of the HoTT Book [1] for more of an explanation regarding the
induction principle of 𝕍.

For comparison, the higher inductive type (HIT) presentation of 𝕍 (w.r.t. 𝓤) is:
  ∙ For every A : 𝓤 and f : A → 𝕍, we have an element 𝕍-set f : 𝕍
  ∙ For every A, B : 𝓤, f : A → 𝕍 and g : B → 𝕍, if f ≈ g, then 𝕍-set f ＝ 𝕍-set g
  ∙ 𝕍 is set-truncated: for every x, y : 𝕍 and p, q : x ＝ y, we have p ＝ q.

We require that the type 𝕍 is a set in the sense of HoTT, i.e. its elements are
equal in at most one way. In the set theoretic sense it is of course a proper
class and not a set: the type 𝕍 lives in the next type universe 𝓤 ⁺. To try to
avoid confusion, we explicitly introduce the definition "is-large-set" below, as
suggested by Martín Escardó.

\begin{code}

module _ (𝓤 : Universe) where

 is-large-set : 𝓤 ⁺ ̇ → 𝓤 ⁺ ̇
 is-large-set = is-set

 record cumulative-hierarchy-exists : 𝓤ω where
  field
   𝕍 : 𝓤 ⁺ ̇
   𝕍-is-large-set : is-large-set 𝕍
   𝕍-set : {A : 𝓤 ̇ } → (A → 𝕍) → 𝕍
   𝕍-set-ext : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍) → f ≈ g → 𝕍-set f ＝ 𝕍-set g
   𝕍-induction : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
               → ((x : 𝕍) → is-set (P x))
               → (ρ : {A : 𝓤 ̇ } (f : A → 𝕍 ) → ((a : A) → P (f a)) → P (𝕍-set f))
               → ({A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍) (e : f ≈ g)
                   → (IH₁ : (a : A) → P (f a))
                   → (IH₂ : (b : B) → P (g b))
                   → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b ,
                                    transport P p (IH₁ a) ＝ IH₂ b ∥)
                   → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a ,
                                    transport P p (IH₂ b) ＝ IH₁ a ∥)
                   → transport P (𝕍-set-ext f g e) (ρ f IH₁) ＝ ρ g IH₂)
               → (x : 𝕍) → P x
   𝕍-induction-computes : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
                        → (σ : (x : 𝕍) → is-set (P x))
                        → (ρ : {A : 𝓤 ̇ } (f : A → 𝕍 ) → ((a : A) → P (f a))
                                                        → P (𝕍-set f))
                        → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍) (e : f ≈ g)
                             → (IH₁ : (a : A) → P (f a))
                             → (IH₂ : (b : B) → P (g b))
                             → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b ,
                                              transport P p (IH₁ a) ＝ IH₂ b ∥)
                             → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a ,
                                              transport P p (IH₂ b) ＝ IH₁ a ∥)
                             → transport P (𝕍-set-ext f g e) (ρ f IH₁) ＝ ρ g IH₂)
                        → {A : 𝓤 ̇ } (f : A → 𝕍) (IH : (a : A) → P (f a))
                           → 𝕍-induction P σ ρ τ (𝕍-set f) ＝ ρ f IH

\end{code}

Part II
-------

Statements and proofs of some simpler, more specialised, induction and recursion
principles for 𝕍.

We start with deriving the recursion principle for 𝕍, i.e. its nondependent
induction principle. It should be noted that this is completely routine.

\begin{code}

  𝕍-recursion-with-computation :
     {𝓣 : Universe} {X : 𝓣 ̇ }
   → (σ : is-set X)
   → (ρ : {A : 𝓤 ̇ } (f : A → 𝕍) → (A → X) → X)
   → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
        → (IH₁ : A → X)
        → (IH₂ : B → X)
        → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
        → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , IH₂ b ＝ IH₁ a ∥)
        → f ≈ g → ρ f IH₁ ＝ ρ g IH₂)
   → Σ ϕ ꞉ (𝕍 → X) , ({A : 𝓤 ̇ } (f : A → 𝕍)
                      (IH : A → X) → ϕ (𝕍-set f) ＝ ρ f IH)
  𝕍-recursion-with-computation {𝓣} {X} σ ρ τ =
   ( 𝕍-induction (λ _ → X) (λ _ → σ) ρ τ'
   , 𝕍-induction-computes (λ _ → X) (λ _ → σ) ρ τ')
      where
       τ' : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
          → (e : f ≈ g) (IH₁ : A → X) (IH₂ : B → X)
          → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b ,
                           transport (λ _ → X) p (IH₁ a) ＝ IH₂ b ∥)
          → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a ,
                           transport (λ _ → X) p (IH₂ b) ＝ IH₁ a ∥)
          → transport (λ _ → X) (𝕍-set-ext f g e) (ρ f IH₁) ＝ ρ g IH₂
       τ' {A} {B} f g e IH₁ IH₂ hIH₁ hIH₂ =
        transport (λ _ → X) e' (ρ f IH₁) ＝⟨ transport-const e'          ⟩
        ρ f IH₁                          ＝⟨ τ f g IH₁ IH₂ hIH₁' hIH₂' e ⟩
        ρ g IH₂                          ∎
         where
          e' = 𝕍-set-ext f g e
          hIH₁' : (a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥
          hIH₁' a = ∥∥-functor
                     (λ (b , p , q) → (b , p , ((transport-const p) ⁻¹ ∙ q)))
                     (hIH₁ a)
          hIH₂' : (b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , IH₂ b ＝ IH₁ a ∥
          hIH₂' b = ∥∥-functor
                     (λ (a , p , q) → (a , p , ((transport-const p) ⁻¹ ∙ q)))
                     (hIH₂ b)

  𝕍-recursion : {𝓣 : Universe} {X : 𝓣 ̇ }
              → is-set X
              → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → (A → X) → X))
              → ({A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                  → (IH₁ : A → X) (IH₂ : B → X)
                  → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
                  → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , IH₂ b ＝ IH₁ a ∥)
                  → f ≈ g → ρ f IH₁ ＝ ρ g IH₂)
              → 𝕍 → X
  𝕍-recursion σ ρ τ = pr₁ (𝕍-recursion-with-computation σ ρ τ)

  𝕍-recursion-computes :
      {𝓣 : Universe} {X : 𝓣 ̇ }
    → (σ : is-set X)
    → (ρ : {A : 𝓤 ̇ } (f : A → 𝕍) → (A → X) → X)
    → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → (IH₁ : A → X) (IH₂ : B → X)
         → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
         → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , IH₂ b ＝ IH₁ a ∥)
         → f ≈ g → ρ f IH₁ ＝ ρ g IH₂)
    → ({A : 𝓤 ̇ } (f : A → 𝕍) (IH : A → X)
        → 𝕍-recursion σ ρ τ (𝕍-set f) ＝ ρ f IH)
  𝕍-recursion-computes σ ρ τ f = pr₂ (𝕍-recursion-with-computation σ ρ τ) f

\end{code}

Next, we observe that when P is a family of propositions, then the induction
principle simplifies significantly.

\begin{code}

  𝕍-prop-induction : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
                   → ((x : 𝕍) → is-prop (P x))
                   → ({A : 𝓤 ̇ } (f : A → 𝕍) → ((a : A) → P (f a)) → P (𝕍-set f))
                   → (x : 𝕍) → P x
  𝕍-prop-induction {𝓣} P P-is-prop-valued ρ =
   𝕍-induction P (λ x → props-are-sets (P-is-prop-valued x)) ρ
                 (λ f g e IH₁ IH₂ _ _ → P-is-prop-valued _ _ _)


  𝕍-prop-simple-induction : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
                          → ((x : 𝕍) → is-prop (P x))
                          → ({A : 𝓤 ̇ } (f : A → 𝕍) → P (𝕍-set f))
                          → (x : 𝕍) → P x
  𝕍-prop-simple-induction P σ ρ = 𝕍-prop-induction P σ (λ f _ → ρ f)

\end{code}

Because implication makes the set Ω into a poset, we can give specialised
recursion principles for 𝕍 → Ω by (roughly) asking that ≲ is mapped to
implication.

\begin{code}

  private
   𝕍-prop-recursion-with-computation :
      {𝓣 : Universe}
    → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → (A → Ω 𝓣) → Ω 𝓣))
    → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → (IH₁ : A → Ω 𝓣) (IH₂ : B → Ω 𝓣)
         → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
         → f ≲ g → ρ f IH₁ holds → ρ g IH₂ holds)
    → Σ ϕ ꞉ (𝕍 → Ω 𝓣) , ({A : 𝓤 ̇ } (f : A → 𝕍) (IH : A → Ω 𝓣)
                      → ϕ (𝕍-set f) ＝ ρ f IH)
   𝕍-prop-recursion-with-computation {𝓣} ρ τ =
    ( 𝕍-recursion (Ω-is-set fe pe) ρ τ'
    , 𝕍-recursion-computes (Ω-is-set fe pe) ρ τ')
     where
      τ' : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → (IH₁ : A → Ω 𝓣) (IH₂ : B → Ω 𝓣)
         → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
         → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , IH₂ b ＝ IH₁ a ∥)
         → f ≈ g → ρ f IH₁ ＝ ρ g IH₂
      τ' f g IH₁ IH₂ hIH₁ hIH₂ (m₁ , m₂) =
       Ω-extensionality fe pe (τ f g IH₁ IH₂ hIH₁ m₁)
                              (τ g f IH₂ IH₁ hIH₂ m₂)

  𝕍-prop-recursion : {𝓣 : Universe}
                   → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → (A → Ω 𝓣) → Ω 𝓣))
                   → ({A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                       → (IH₁ : A → Ω 𝓣) (IH₂ : B → Ω 𝓣)
                       → ((a : A) → ∥ Σ b ꞉ B ,
                                      Σ p ꞉ f a ＝ g b , IH₁ a ＝ IH₂ b ∥)
                     → f ≲ g → ρ f IH₁ holds → ρ g IH₂ holds)
                   → 𝕍 → Ω 𝓣
  𝕍-prop-recursion {𝓣} ρ τ =
   pr₁ (𝕍-prop-recursion-with-computation ρ τ)

  𝕍-prop-recursion-computes : {𝓣 : Universe}
                            → (ρ : ({A : 𝓤 ̇ } (f : A → 𝕍) → (A → Ω 𝓣) → Ω 𝓣))
                            → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                                 → (IH₁ : A → Ω 𝓣) (IH₂ : B → Ω 𝓣)
                                 → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b ,
                                                  IH₁ a ＝ IH₂ b ∥)
                                 → f ≲ g → ρ f IH₁ holds → ρ g IH₂ holds)
                            → ({A : 𝓤 ̇ } (f : A → 𝕍) (IH : A → Ω 𝓣)
                              → 𝕍-prop-recursion ρ τ (𝕍-set f) ＝ ρ f IH)
  𝕍-prop-recursion-computes ρ τ f =
   pr₂ (𝕍-prop-recursion-with-computation ρ τ) f

\end{code}

We also have a simpler version of the above in the case that we don't need to
make recursive calls.

\begin{code}

  𝕍-prop-simple-recursion : {𝓣 : Universe}
                          → (ρ : ({A : 𝓤 ̇ } → (A → 𝕍) → Ω 𝓣))
                          → ({A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                            → f ≲ g → ρ f holds → ρ g holds)
                          → 𝕍 → Ω 𝓣
  𝕍-prop-simple-recursion {𝓣} ρ τ =
   𝕍-prop-recursion (λ f _ → ρ f) (λ f g _ _ _ → τ f g)

  𝕍-prop-simple-recursion-computes :
      {𝓣 : Universe}
    → (ρ : ({A : 𝓤 ̇ } → (A → 𝕍) → Ω 𝓣))
    → (τ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → f ≲ g → ρ f holds → ρ g holds)
    → ({A : 𝓤 ̇ } (f : A → 𝕍) → 𝕍-prop-simple-recursion ρ τ (𝕍-set f) ＝ ρ f)
  𝕍-prop-simple-recursion-computes ρ τ f =
   𝕍-prop-recursion-computes (λ f _ → ρ f) (λ f g _ _ _ → τ f g)
                             f (λ _ → 𝟙 , 𝟙-is-prop)

\end{code}

Part III
--------

Basic constructions and proofs for 𝕍, i.e. the definition of set membership (∈),
subset relation (⊆) and proofs of ∈-extensionality and ∈-induction.

\begin{code}

  _∈[Ω]_ : 𝕍 → 𝕍 → Ω (𝓤 ⁺)
  _∈[Ω]_ x = 𝕍-prop-simple-recursion
              (λ {A} f → (∃ a ꞉ A , f a ＝ x) , ∃-is-prop) e
   where
    e : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
      → f ≲ g → (∃ a ꞉ A , f a ＝ x) → (∃ b ꞉ B , g b ＝ x)
    e {A} {B} f g s = ∥∥-rec ∃-is-prop
                             (λ (a , p)
                                → ∥∥-functor (λ (b , q)
                                                → b , (q ∙ p)) (s a))

  _∈_ : 𝕍 → 𝕍 → 𝓤 ⁺ ̇
  x ∈ y = (x ∈[Ω] y) holds

  ∈-is-prop-valued : {x y : 𝕍} → is-prop (x ∈ y)
  ∈-is-prop-valued {x} {y} = holds-is-prop (x ∈[Ω] y)

  ∈-for-𝕍-sets : (x : 𝕍) {A : 𝓤 ̇ } (f : A → 𝕍)
               → (x ∈ 𝕍-set f) ＝ (∃ a ꞉ A , f a ＝ x)
  ∈-for-𝕍-sets x f = ap pr₁ (𝕍-prop-simple-recursion-computes _ _ f)

  from-∈-of-𝕍-set : {x : 𝕍} {A : 𝓤 ̇ } {f : A → 𝕍}
                    → (x ∈ 𝕍-set f) → (∃ a ꞉ A , f a ＝ x)
  from-∈-of-𝕍-set {x} {A} {f} = Idtofun (∈-for-𝕍-sets x f)

  to-∈-of-𝕍-set : {x : 𝕍} {A : 𝓤 ̇ } {f : A → 𝕍}
                  → (∃ a ꞉ A , f a ＝ x) → (x ∈ 𝕍-set f)
  to-∈-of-𝕍-set {x} {A} {f} = back-Idtofun (∈-for-𝕍-sets x f)

  _⊆_ : 𝕍 → 𝕍 → 𝓤 ⁺ ̇
  x ⊆ y = (v : 𝕍) → v ∈ x → v ∈ y

  ⊆-to-≲ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → 𝕍-set f ⊆ 𝕍-set g → f ≲ g
  ⊆-to-≲ {A} {B} f g s a = from-∈-of-𝕍-set m
   where
    m : f a ∈ 𝕍-set g
    m = s (f a) (to-∈-of-𝕍-set ∣ a , refl ∣)

  ≲-to-⊆ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
         → f ≲ g → 𝕍-set f ⊆ 𝕍-set g
  ≲-to-⊆ {A} {B} f g s x m = to-∈-of-𝕍-set n
   where
    m' : ∃ a ꞉ A , f a ＝ x
    m' = from-∈-of-𝕍-set m
    n : ∃ b ꞉ B , g b ＝ x
    n = ∥∥-rec ∃-is-prop
               (λ (a , p) → ∥∥-functor (λ (b , q) → b , (q ∙ p)) (s a)) m'

  ⊆-is-prop-valued : {x y : 𝕍} → is-prop (x ⊆ y)
  ⊆-is-prop-valued = Π₂-is-prop fe (λ _ _ → ∈-is-prop-valued)

  ⊆-is-reflexive : {x : 𝕍} → x ⊆ x
  ⊆-is-reflexive _ = id

  ＝-to-⊆ : {x y : 𝕍} → x ＝ y → x ⊆ y
  ＝-to-⊆ refl = ⊆-is-reflexive

\end{code}

We now prove, using the induction principles of 𝕍 above, two simple
set-theoretic axioms: ∈-extensionality and ∈-induction.

\begin{code}

  pre-extensionality : {A : 𝓤 ̇ } (f : A → 𝕍) (x : 𝕍)
                     → x ⊆ 𝕍-set f → 𝕍-set f ⊆ x → x ＝ 𝕍-set f
  pre-extensionality f =
   𝕍-prop-simple-induction (λ x → x ⊆ 𝕍-set f → 𝕍-set f ⊆ x → x ＝ 𝕍-set f)
                           (λ _ → Π₂-is-prop fe (λ _ _ → 𝕍-is-large-set))
                           γ
    where
     γ : {B : 𝓤 ̇  } (g : B → 𝕍)
       → 𝕍-set g ⊆ 𝕍-set f → 𝕍-set f ⊆ 𝕍-set g → 𝕍-set g ＝ 𝕍-set f
     γ g s t = 𝕍-set-ext g f (⊆-to-≲ g f s , ⊆-to-≲ f g t)

  ∈-extensionality : (x y : 𝕍) → x ⊆ y → y ⊆ x → x ＝ y
  ∈-extensionality x y =
   𝕍-prop-simple-induction (λ v → x ⊆ v → v ⊆ x → x ＝ v)
                           (λ _ → Π₂-is-prop fe (λ _ _ → 𝕍-is-large-set))
                           (λ f → pre-extensionality f x)
                           y

  ∈-induction : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
              → ((x : 𝕍) → is-prop (P x))
              → ((x : 𝕍) → ((y : 𝕍) → y ∈ x → P y) → P x)
              → (x : 𝕍) → P x
  ∈-induction P P-is-prop-valued h = 𝕍-prop-induction P P-is-prop-valued γ
   where
    γ : {A : 𝓤 ̇ } (f : A → 𝕍) → ((a : A) → P (f a)) → P (𝕍-set f)
    γ {A} f IH = h (𝕍-set f) c
     where
      c : (y : 𝕍) → y ∈ 𝕍-set f → P y
      c y m = ∥∥-rec (P-is-prop-valued y) (λ (a , p) → transport P p (IH a)) m'
       where
        m' : ∃ a ꞉ A , f a ＝ y
        m' = from-∈-of-𝕍-set m

\end{code}

Notice that since 𝕍 is a type in 𝓤 ⁺ the type x ＝ y also lives in 𝓤 ⁺ whenever
x, y : 𝕍. However, as pointed out in the HoTT Book [Section 10.5, 1], it is
possible to define a 𝓤-small relation and prove it equivalent to the identity
type of 𝕍, making 𝕍 (essentially) locally 𝓤-small. This also allows us to define
a 𝓤-small membership relation.

\begin{code}

  open import UF.Subsingleton-Combinators
  open AllCombinators pt fe

  private
   module _
           {A : 𝓤 ̇ }
           (f : A → 𝕍)
           (r : A → 𝕍 → Ω 𝓤)
          where

    ρ₁ : {B : 𝓤 ̇ } → (B → 𝕍) → Ω 𝓤
    ρ₁ {B} g = (Ɐ a ∶ A , Ǝ b ∶ B , r a (g b) holds)
             ∧ (Ɐ b ∶ B , Ǝ a ∶ A , r a (g b) holds)

    τ₁' : {B' B : 𝓤 ̇} (g' : B' → 𝕍) (g : B → 𝕍) → g' ≈ g → ρ₁ g' holds → ρ₁ g holds
    τ₁' {B'} {B} g' g (s , t) (u , v) = ⦅1⦆ , ⦅2⦆
     where
      ⦅1⦆ : (a : A) → ∃ b ꞉ B , r a (g b) holds
      ⦅1⦆ a = ∥∥-rec ∃-is-prop h₁ (u a)
       where
        h₁ : (Σ b' ꞉ B' , r a (g' b') holds) → ∃ b ꞉ B , r a (g b) holds
        h₁ (b' , p) = ∥∥-functor h₂ (s b')
         where
          h₂ : (Σ b ꞉ B , g b ＝ g' b') → Σ b ꞉ B , r a (g b) holds
          h₂ (b , e) = b , transport (λ - → (r a -) holds) (e ⁻¹) p
      ⦅2⦆ : (b : B) → ∃ a ꞉ A , r a (g b) holds
      ⦅2⦆ b = ∥∥-rec ∃-is-prop h₁ (t b)
       where
        h₁ : (Σ b' ꞉ B' , g' b' ＝ g b) → ∃ a ꞉ A , r a (g b) holds
        h₁ (b' , e) = ∥∥-functor h₂ (v b')
         where
          h₂ : (Σ a ꞉ A , r a (g' b') holds) → Σ a ꞉ A , r a (g b) holds
          h₂ (a , p) = a , transport (λ - → (r a -) holds) e p

    τ₁ : {B' B : 𝓤 ̇} (g' : B' → 𝕍) (g : B → 𝕍) → g' ≈ g → ρ₁ g' ＝ ρ₁ g
    τ₁ {B'} {B} g' g e = Ω-extensionality fe pe (τ₁' g' g e) (τ₁' g g' (≈-sym e))

    ρ₂ : 𝕍 → Ω 𝓤
    ρ₂ = 𝕍-recursion (Ω-is-set fe pe) (λ g _ → ρ₁ g)
                     (λ g' g _ _ _ _ e → τ₁ g' g e)

    ρ₂-behaviour : {B : 𝓤 ̇ } (g : B → 𝕍) → ρ₂ (𝕍-set g) ＝ ρ₁ g
    ρ₂-behaviour g =
     𝕍-recursion-computes (Ω-is-set fe pe) (λ g₁ _ → ρ₁ g₁)
                          (λ g' g _ _ _ _ e → τ₁ g' g e)
                          g (λ _ → 𝟙 , 𝟙-is-prop)

   τ' : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
      → (r₁ : A → 𝕍 → Ω 𝓤) (r₂ : B → 𝕍 → Ω 𝓤)
      → ((a : A) → ∃ b ꞉ B , (f a ＝ g b) × (r₁ a ＝ r₂ b))
      → ((b : B) → ∃ a ꞉ A , (g b ＝ f a) × (r₂ b ＝ r₁ a))
      → {C : 𝓤 ̇ } (h : C → 𝕍) → ρ₁ f r₁ h holds → ρ₁ g r₂ h holds
   τ' {A} {B} f g r₁ r₂ s t {C} h (u , v) = ⦅1⦆ , ⦅2⦆
    where
     ⦅1⦆ : (b : B) → ∃ c ꞉ C , r₂ b (h c) holds
     ⦅1⦆ b = ∥∥-rec ∃-is-prop m (t b)
      where
       m : (Σ a ꞉ A , (g b ＝ f a) × (r₂ b ＝ r₁ a))
         → ∃ c ꞉ C , r₂ b (h c) holds
       m (a , _ , q) = ∥∥-functor n (u a)
        where
         n : (Σ c ꞉ C , r₁ a (h c) holds)
           → Σ c ꞉ C , r₂ b (h c) holds
         n (c , w) = c , Idtofun (ap _holds (happly (q ⁻¹) (h c))) w
     ⦅2⦆ : (c : C) → ∃ b ꞉ B , r₂ b (h c) holds
     ⦅2⦆ c = ∥∥-rec ∃-is-prop n (v c)
      where
       n : (Σ a ꞉ A , r₁ a (h c) holds)
         → ∃ b ꞉ B , r₂ b (h c) holds
       n (a , w) = ∥∥-functor m (s a)
        where
         m : (Σ b ꞉ B , (f a ＝ g b) × (r₁ a ＝ r₂ b))
           → Σ b ꞉ B , r₂ b (h c) holds
         m (b , _ , q) = b , Idtofun (ap _holds (happly q (h c))) w

   τ : {A B : 𝓤 ̇} (f : A → 𝕍) (g : B → 𝕍)
       (r₁ : A → 𝕍 → Ω 𝓤) (r₂ : B → 𝕍 → Ω 𝓤)
     → ((a : A) → ∃ b ꞉ B , (f a ＝ g b) × (r₁ a ＝ r₂ b))
     → ((b : B) → ∃ a ꞉ A , (g b ＝ f a) × (r₂ b ＝ r₁ a))
     → f ≈ g → ρ₂ f r₁ ＝ ρ₂ g r₂
   τ {A} {B} f g r₁ r₂ IH₁ IH₂ _ =
    dfunext fe (𝕍-prop-simple-induction (λ x → ρ₂ f r₁ x ＝ ρ₂ g r₂ x)
                                        (λ _ → Ω-is-set fe pe)
                                        σ)
     where
      σ : {C : 𝓤 ̇ } (h : C → 𝕍) → ρ₂ f r₁ (𝕍-set h) ＝ ρ₂ g r₂ (𝕍-set h)
      σ h = ρ₂ f r₁ (𝕍-set h) ＝⟨ ρ₂-behaviour f r₁ h ⟩
            ρ₁ f r₁ h         ＝⟨ e ⟩
            ρ₁ g r₂ h         ＝⟨ (ρ₂-behaviour g r₂ h) ⁻¹ ⟩
            ρ₂ g r₂ (𝕍-set h) ∎
       where
        e = Ω-extensionality fe pe
             (τ' f g r₁ r₂ IH₁ IH₂ h)
             (τ' g f r₂ r₁ IH₂ IH₁ h)

   ＝⁻[Ω]-packaged : Σ ϕ ꞉ (𝕍 → 𝕍 → Ω 𝓤) , ({A : 𝓤 ̇} (f : A → 𝕍)
                                            (r : A → 𝕍 → Ω 𝓤)
                                          → ϕ (𝕍-set f) ＝ ρ₂ f r)
   ＝⁻[Ω]-packaged =
    𝕍-recursion-with-computation (Π-is-set fe (λ _ → Ω-is-set fe pe)) ρ₂ τ

  _＝⁻[Ω]_ : 𝕍 → 𝕍 → Ω 𝓤
  _＝⁻[Ω]_ = pr₁ ＝⁻[Ω]-packaged

  _＝⁻_ : 𝕍 → 𝕍 → 𝓤 ̇
  x ＝⁻ y = (x ＝⁻[Ω] y) holds

  ＝⁻-is-prop-valued : {x y : 𝕍} → is-prop (x ＝⁻ y)
  ＝⁻-is-prop-valued {x} {y} = holds-is-prop (x ＝⁻[Ω] y)

  private
   ＝⁻-behaviour : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                → (𝕍-set f ＝⁻ 𝕍-set g)
                ＝ ( ((a : A) → ∃ b ꞉ B , f a ＝⁻ g b)
                   × ((b : B) → ∃ a ꞉ A , f a ＝⁻ g b))
   ＝⁻-behaviour {A} {B} f g =
    (𝕍-set f ＝⁻ 𝕍-set g)    ＝⟨ ⦅1⦆ ⟩
    (ρ₂ f r (𝕍-set g) holds) ＝⟨ ⦅2⦆ ⟩
    T                        ∎
     where
      T : 𝓤 ̇
      T = ((a : A) → ∃ b ꞉ B , f a ＝⁻ g b)
        × ((b : B) → ∃ a ꞉ A , f a ＝⁻ g b)
      r : A → 𝕍 → Ω 𝓤
      r a y = f a ＝⁻[Ω] y
      ⦅1⦆ = ap _holds (happly (pr₂ ＝⁻[Ω]-packaged f r) (𝕍-set g))
      ⦅2⦆ = ap _holds (ρ₂-behaviour f r g)

   ＝⁻-to-＝ : {x y : 𝕍} → x ＝⁻ y → x ＝ y
   ＝⁻-to-＝ {x} {y} =
    𝕍-prop-induction (λ u → ((v : 𝕍) → u ＝⁻ v → u ＝ v))
                     (λ _ → Π₂-is-prop fe (λ _ _ → 𝕍-is-large-set))
                     (λ {A} f r → 𝕍-prop-simple-induction _
                                   (λ _ → Π-is-prop fe (λ _ → 𝕍-is-large-set))
                                   (λ {B} g → h f g r))
                     x y
     where
      h : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
        → ((a : A) (v : 𝕍) → f a ＝⁻ v → f a ＝ v)
        → 𝕍-set f ＝⁻ 𝕍-set g → 𝕍-set f ＝ 𝕍-set g
      h {A} {B} f g r e = 𝕍-set-ext f g (⦅1⦆ , ⦅2⦆)
       where
        u : (a : A) → ∃ b ꞉ B , f a ＝⁻ g b
        u = pr₁ (Idtofun (＝⁻-behaviour f g) e)
        v : (b : B) → ∃ a ꞉ A , f a ＝⁻ g b
        v = pr₂ (Idtofun (＝⁻-behaviour f g) e)
        ⦅1⦆ : (a : A) → ∃ b ꞉ B , g b ＝ f a
        ⦅1⦆ a = ∥∥-functor (λ (b , p) → b , ((r a (g b) p) ⁻¹)) (u a)
        ⦅2⦆ : (b : B) → ∃ a ꞉ A , f a ＝ g b
        ⦅2⦆ b = ∥∥-functor (λ (a , p) → a , r a (g b) p) (v b)

   ＝⁻-is-reflexive : {x : 𝕍} → x ＝⁻ x
   ＝⁻-is-reflexive {x} = 𝕍-prop-induction (λ - → - ＝⁻ -)
                                           (λ _ → ＝⁻-is-prop-valued)
                                           h x
    where
     h : {A : 𝓤 ̇ } (f : A → 𝕍)
       → ((a : A) → f a ＝⁻ f a)
       → 𝕍-set f ＝⁻ 𝕍-set f
     h {A} f r = back-Idtofun (＝⁻-behaviour f f)
                              ((λ a → ∣ a , r a ∣) , (λ a → ∣ a , r a ∣))

   ＝-to-＝⁻ : {x y : 𝕍} → x ＝ y → x ＝⁻ y
   ＝-to-＝⁻ refl = ＝⁻-is-reflexive

   open import UF.Equiv -- TO DO: move imports
   open import UF.Size

   ＝⁻-≃-＝ : {x y : 𝕍} → (x ＝⁻ y) ≃ (x ＝ y)
   ＝⁻-≃-＝ = logically-equivalent-props-are-equivalent
               ＝⁻-is-prop-valued
               𝕍-is-large-set
               ＝⁻-to-＝
               ＝-to-＝⁻

   𝕍-is-locally-small : is-locally-small 𝕍
   𝕍-is-locally-small x y = (x ＝⁻ y) , ＝⁻-≃-＝

\end{code}
