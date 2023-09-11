Tom de Jong, 4 & 5 April 2022.

Quotients. Much of this material is moved from or abstracted from the
earlier 2018 module Quotient.Large by Martin Escardo.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Quotient.Type where

open import MLTT.Spartan

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

is-prop-valued is-equiv-relation : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued    _≈_ = ∀ x y → is-prop (x ≈ y)
is-equiv-relation _≈_ = is-prop-valued _≈_
                      × reflexive      _≈_
                      × symmetric      _≈_
                      × transitive     _≈_

EqRel : {𝓤 𝓥 : Universe} → 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
EqRel {𝓤} {𝓥} X = Σ R ꞉ (X → X → 𝓥 ̇ ) , is-equiv-relation R

_≈[_]_ : {X : 𝓤 ̇ } → X → EqRel X → X → 𝓥 ̇
x ≈[ _≈_ , _ ] y = x ≈ y

identifies-related-points : {X : 𝓤 ̇ } (≈ : EqRel {𝓤} {𝓥} X) {Y : 𝓦 ̇ }
                          → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
identifies-related-points (_≈_ , _) f = ∀ {x x'} → x ≈ x' → f x ＝ f x'

\end{code}

To account for the module Quotient.Large, and, at the same time, usual
(small) quotients, we introduce a parametric definion of existence of
quotients. For small quotients we take F = id, and for large quotients
we take F = _⁺ (see below).

\begin{code}

record general-set-quotients-exist (F : Universe → Universe) : 𝓤ω where
 field
  _/_ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → EqRel {𝓤} {𝓥} X → 𝓤 ⊔ F 𝓥 ̇
  η/ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (≋ : EqRel {𝓤} {𝓥} X) → X → X / ≋
  η/-identifies-related-points : {𝓤 𝓥 : Universe}
                                 {X : 𝓤 ̇ } (≋ : EqRel {𝓤} {𝓥} X)
                               → identifies-related-points ≋ (η/ ≋)
  /-is-set : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (≋ : EqRel {𝓤} {𝓥} X) → is-set (X / ≋)
  /-universality : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (≋ : EqRel {𝓤} {𝓥} X)
                   {𝓦 : Universe} {Y : 𝓦 ̇ }
                 → is-set Y
                 → (f : X → Y)
                 → identifies-related-points ≋ f
                 → ∃! f̅ ꞉ (X / ≋ → Y) , f̅ ∘ η/ ≋ ∼ f

\end{code}

Added 22 August 2022.
The induction principle follows from the universal property.

\begin{code}

 /-induction : {X : 𝓤 ̇ } (≋ : EqRel {𝓤} {𝓥} X)
               {P : X / ≋ → 𝓦 ̇ }
             → ((x' : X / ≋) → is-prop (P x'))
             → ((x : X) → P (η/ ≋ x)) → (y : X / ≋) → P y
 /-induction {X = X} ≋ {P} P-is-prop-valued ρ y =
  transport P (happly f̅-section-of-pr₁ y) (pr₂ (f̅ y))
   where
    f : X → Σ P
    f x = (η/ ≋ x , ρ x)
    f-identifies-related-points : identifies-related-points ≋ f
    f-identifies-related-points r =
     to-subtype-＝ P-is-prop-valued (η/-identifies-related-points ≋ r)
    ΣP-is-set : is-set (Σ P)
    ΣP-is-set = subsets-of-sets-are-sets (X / ≋) P (/-is-set ≋)
                                         (λ {x'} → P-is-prop-valued x')
    u : ∃! f̅ ꞉ (X / ≋ → Σ P) , f̅ ∘ η/ ≋ ∼ f
    u = /-universality ≋ ΣP-is-set f f-identifies-related-points
    f̅ : X / ≋ → Σ P
    f̅ = ∃!-witness u
    f̅-after-η-is-f : f̅ ∘ η/ ≋ ∼ f
    f̅-after-η-is-f = ∃!-is-witness u
    f̅-section-of-pr₁ : pr₁ ∘ f̅ ＝ id
    f̅-section-of-pr₁ = ap pr₁ (singletons-are-props c (pr₁ ∘ f̅ , h)
                                                      (id , λ x → refl))
     where
      c : ∃! g ꞉ (X / ≋ → X / ≋) , g ∘ η/ ≋ ∼ η/ ≋
      c = /-universality ≋ (/-is-set ≋) (η/ ≋) (η/-identifies-related-points ≋)
      h : pr₁ ∘ f̅ ∘ η/ ≋ ∼ η/ ≋
      h x = ap pr₁ (f̅-after-η-is-f x)

\end{code}

Paying attention to universe levels, it is important to note that the quotient
of X : 𝓤 by a 𝓥-valued equivalence relation is assumed to live in 𝓤 ⊔ 𝓥. In
particular, the quotient of type in 𝓤 by a 𝓤-valued equivalence relation lives
in 𝓤 again.

The following is boilerplate and duplicates some of the material in
Quotient.Large, where large set quotients are constructed using propositional
truncations, function extensionality and propositional extensionality.

We need the boilerplate in OrdinalOfOrdinalsSuprema.lagda, where we use set
quotients to construct small suprema of small ordinals.

A quotient is said to be effective if for every x, y : X, we have x ≈ y whenever
η/ x ＝ ‌η/ y. Notice that we did not include effectivity as a requirement in
'set-quotients-exist'. But actually it follows from the other properties, at
least in the presence of function extensionality and propositonal
extensionality, as Martín observed. The proof is as follows:

(1) First construct propositional truncations using assumed set quotients.
(2) Construct another (large) quotient as described in Quotient.Larges.lagda.
(3) This large quotient is effective, but has to be isomorphic to the assumed
    set quotient, hence this quotient has to be effective as well.

TODO: Implement this in Agda.

\begin{code}

 module _
         {X : 𝓤 ̇ }
         (≋@(_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel {𝓤} {𝓥} X)
        where

  module _
          {A : 𝓦 ̇ }
          (A-is-set : is-set A)
         where

   mediating-map/ : (f : X → A)
                  → identifies-related-points ≋ f
                  → X / ≋ → A
   mediating-map/ f p = ∃!-witness (/-universality ≋ A-is-set f p)

   universality-triangle/ : (f : X → A)
                            (p : identifies-related-points ≋ f)
                          → mediating-map/ f p ∘ η/ ≋ ∼ f
   universality-triangle/ f p = ∃!-is-witness (/-universality ≋ A-is-set f p)

\end{code}

We extend unary and binary prop-valued relations to the quotient.

\begin{code}

 module extending-relations-to-quotient (fe : Fun-Ext) (pe : Prop-Ext) where

  module _
          {X : 𝓤 ̇ }
          (≋@(_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel {𝓤} {𝓥} X)
         where

   module _
           (r : X → Ω 𝓣)
           (p : {x y : X} → x ≈ y → r x ＝ r y)
          where

    extension-rel₁ : X / ≋ → Ω 𝓣
    extension-rel₁ = mediating-map/ ≋ (Ω-is-set fe pe) r p

    extension-rel-triangle₁ : extension-rel₁ ∘ η/ ≋ ∼ r
    extension-rel-triangle₁ = universality-triangle/ ≋ (Ω-is-set fe pe) r p

   module _ (r : X → X → Ω 𝓣)
            (p : {x y x' y' : X} → x ≈ x' → y ≈ y' → r x y ＝ r x' y')
          where

    abstract
     private
      p' : (x : X) {y y' : X} → y ≈ y' → r x y ＝ r x y'
      p' x {y} {y'} = p (≈r x)

      r₁ : X → X / ≋ → Ω 𝓣
      r₁ x = extension-rel₁ (r x) (p' x)

      δ : {x x' : X} → x ≈ x' → (y : X) → r₁ x (η/ ≋ y) ＝ r₁ x' (η/ ≋ y)
      δ {x} {x'} e y =
        r₁ x  (η/ ≋ y)  ＝⟨ extension-rel-triangle₁ (r x) (p (≈r x)) y        ⟩
        r  x     y      ＝⟨ p e (≈r y)                                        ⟩
        r  x'    y      ＝⟨ (extension-rel-triangle₁ (r x') (p (≈r x')) y) ⁻¹ ⟩
        r₁ x' (η/ ≋ y)  ∎

      ρ : (q : X / ≋) {x x' : X} → x ≈ x' → r₁ x q ＝ r₁ x' q
      ρ q {x} {x'} e = /-induction ≋ (λ q → Ω-is-set fe pe) (δ e) q

      r₂ : X / ≋ → X / ≋ → Ω 𝓣
      r₂ = mediating-map/ ≋ (Π-is-set fe (λ _ → Ω-is-set fe pe)) r₁
                            (λ {x} {x'} e → dfunext fe (λ q → ρ q e))

      σ : (x : X) → r₂ (η/ ≋ x) ＝ r₁ x
      σ = universality-triangle/ ≋ (Π-is-set fe (λ _ → Ω-is-set fe pe)) r₁
                                   (λ {x} {x'} e → dfunext fe (λ q → ρ q e))

      τ : (x y : X) → r₂ (η/ ≋ x) (η/ ≋ y) ＝ r x y
      τ x y = r₂ (η/ ≋ x) (η/ ≋ y) ＝⟨ happly (σ x) (η/ ≋ y) ⟩
              r₁ x        (η/ ≋ y) ＝⟨ extension-rel-triangle₁ (r x) (p' x) y ⟩
              r  x            y    ∎

     extension-rel₂ : X / ≋ → X / ≋ → Ω 𝓣
     extension-rel₂ = r₂

     extension-rel-triangle₂ : (x y : X)
                             → extension-rel₂ (η/ ≋ x) (η/ ≋ y) ＝ r x y
     extension-rel-triangle₂ = τ

\end{code}

For proving properties of an extended binary relation, it is useful to have a
binary and ternary versions of quotient induction.

\begin{code}

 module _
         (fe : Fun-Ext)
         {X : 𝓤 ̇ }
         (≋ : EqRel {𝓤 } {𝓥} X)
        where

  /-induction₂ : ∀ {𝓦} {P : X / ≋ → X / ≋ → 𝓦 ̇ }
               → ((x' y' : X / ≋) → is-prop (P x' y'))
               → ((x y : X) → P (η/ ≋ x) (η/ ≋ y))
               → (x' y' : X / ≋) → P x' y'
  /-induction₂ p h =
   /-induction ≋ (λ x' → Π-is-prop fe (p x'))
                 (λ x → /-induction ≋ (p (η/ ≋ x)) (h x))

  /-induction₃ : ∀ {𝓦} → {P : X / ≋ → X / ≋ → X / ≋ → 𝓦 ̇ }
               → ((x' y' z' : X / ≋) → is-prop (P x' y' z'))
               → ((x y z : X) → P (η/ ≋ x) (η/ ≋ y) (η/ ≋ z))
               → (x' y' z' : X / ≋) → P x' y' z'
  /-induction₃ p h =
   /-induction₂ (λ x' y' → Π-is-prop fe (p x' y'))
                (λ x y → /-induction ≋ (p (η/ ≋ x) (η/ ≋ y)) (h x y))

 quotients-equivalent : (X : 𝓤 ̇ ) (R : EqRel {𝓤} {𝓥} X) (R' : EqRel {𝓤} {𝓦} X)
                      → ({x y : X} → x ≈[ R ] y ⇔ x ≈[ R' ] y)
                      → (X / R) ≃ (X / R')
 quotients-equivalent X (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
                        (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t') ε = γ
  where
   ≋  = (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
   ≋' = (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t')
   i : {x y : X} → x ≈ y → η/ ≋' x ＝ η/ ≋' y
   i e = η/-identifies-related-points ≋' (lr-implication ε e)
   i' : {x y : X} → x ≈' y → η/ ≋ x ＝ η/ ≋ y
   i' e = η/-identifies-related-points ≋ (rl-implication ε e)
   f : X / ≋ → X / ≋'
   f = mediating-map/ ≋ (/-is-set ≋') (η/ ≋') i
   f' : X / ≋' → X / ≋
   f' = mediating-map/ ≋' (/-is-set ≋) (η/ ≋) i'
   a : (x : X) → f (f' (η/ ≋' x)) ＝ η/ ≋' x
   a x = f (f' (η/ ≋' x)) ＝⟨ I ⟩
         f (η/ ≋ x)       ＝⟨ II ⟩
         η/ ≋' x          ∎
    where
     I  = ap f (universality-triangle/ ≋' (/-is-set ≋) (η/ ≋) i' x)
     II = universality-triangle/ ≋ (/-is-set ≋') (η/ ≋') i x
   α : f ∘ f' ∼ id
   α = /-induction ≋' (λ _ → /-is-set ≋') a
   a' : (x : X) → f' (f (η/ ≋ x)) ＝ η/ ≋ x
   a' x = f' (f (η/ ≋ x)) ＝⟨ I ⟩
         f' (η/ ≋' x)     ＝⟨ II ⟩
         η/ ≋ x           ∎
    where
     I  = ap f' (universality-triangle/ ≋ (/-is-set ≋') (η/ ≋') i x)
     II = universality-triangle/ ≋' (/-is-set ≋) (η/ ≋) i' x
   α' : f' ∘ f ∼ id
   α' = /-induction ≋ (λ _ → /-is-set ≋) a'
   γ : (X / ≋) ≃ (X / ≋')
   γ = qinveq f (f' , α' , α)

\end{code}

We now define the existence of small and large quotients:

\begin{code}

set-quotients-exist large-set-quotients-exist : 𝓤ω
set-quotients-exist       = general-set-quotients-exist id
large-set-quotients-exist = general-set-quotients-exist (_⁺)

\end{code}

\begin{code}

are-effective : {F : Universe → Universe} → general-set-quotients-exist F → 𝓤ω
are-effective {F} sq = {𝓤 𝓥 : Universe} (X : 𝓤 ̇ )
                       {R : EqRel {𝓤} {𝓥} X}
                       {x y : X}
                     → η/ R x ＝ η/ R y → x ≈[ R ] y
 where
  open general-set-quotients-exist sq

\end{code}
