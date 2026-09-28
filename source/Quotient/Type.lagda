Martin Escardo and Tom de Jong, August 2018, April 2022, September 2023.

Quotients. Much of this material is moved from or abstracted from the
earlier 2018 module Quotient.Large by Martin Escardo.

\begin{code}

{-# OPTIONS --safe --without-K #-}

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

identifies-related-points : {X : 𝓤 ̇ }
                          → EqRel {𝓤} {𝓥} X
                          → {Y : 𝓦 ̇ }
                          → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
identifies-related-points (_≈_ , _) f = ∀ {x x'} → x ≈ x' → f x ＝ f x'

\end{code}

To account for the module Quotient.Large, and, at the same time, usual
(small) quotients, we introduce a parametric definion of existence of
quotients. For small quotients we take ℓ = id, and for large quotients
we take ℓ = (_⁺) (see below).

\begin{code}

record general-set-quotients-exist (ℓ : Universe → Universe) : 𝓤ω where
 field
  _/_ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → EqRel {𝓤} {𝓥} X → 𝓤 ⊔ ℓ 𝓥 ̇
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

The following are facts about quotients, moved from Quotient.Large as
they are of general use.

\begin{code}

 module _
         {X : 𝓤 ̇ }
         (≋@(_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel {𝓤} {𝓥} X)
        where

  module _ (pt : propositional-truncations-exist) where

   open PropositionalTruncation pt
   open import UF.ImageAndSurjection pt

   η/-is-surjection : is-surjection (η/ {𝓤} {𝓥} {X} ≋)
   η/-is-surjection = /-induction ≋
                       (λ x' → being-in-the-image-is-prop x' (η/ ≋))
                       (λ x → ∣ x , refl ∣)
  module _
          {A : 𝓦 ̇ }
          (A-is-set : is-set A)
         where

   mediating-map/ : (f : X → A)
                  → identifies-related-points ≋ f
                  → X / ≋ → A
   mediating-map/ f j = ∃!-witness (/-universality ≋ A-is-set f j)

   universality-triangle/ : (f : X → A)
                            (j : identifies-related-points ≋ f)
                          → mediating-map/ f j ∘ η/ ≋ ∼ f
   universality-triangle/ f j = ∃!-is-witness (/-universality ≋ A-is-set f j)

   at-most-one-mediating-map/ : (g h : X / ≋ → A)
                              → g ∘ η/ ≋ ∼ h ∘ η/ ≋
                              → g ∼ h
   at-most-one-mediating-map/ g h p x = γ
    where
     f : X → A
     f = g ∘ η/ ≋

     j : identifies-related-points ≋ f
     j e = ap g (η/-identifies-related-points ≋ e)

     q : mediating-map/ f j ＝ g
     q = witness-uniqueness (λ f̅ → f̅ ∘ η/ ≋ ∼ f)
          (/-universality ≋ A-is-set f j)
          (mediating-map/ f j)
          g
          (universality-triangle/ f j)
          (λ x → refl)

     r : mediating-map/ f j ＝ h
     r = witness-uniqueness (λ f̅ → f̅ ∘ η/ ≋ ∼ f)
          (/-universality ≋ A-is-set f j)
          (mediating-map/ f j)
          h
          (universality-triangle/ f j)
          (λ x → (p x)⁻¹)

     γ = g x                  ＝⟨ happly (q ⁻¹) x ⟩
         mediating-map/ f j x ＝⟨ happly r x ⟩
         h x                  ∎

  extension/ : (f : X → X / ≋)
             → identifies-related-points ≋ f
             → (X / ≋ → X / ≋)
  extension/ = mediating-map/ (/-is-set ≋)

  extension-triangle/ : (f : X → X / ≋)
                        (i : identifies-related-points ≋ f)
                      → extension/ f i ∘ η/ ≋ ∼ f
  extension-triangle/ = universality-triangle/ (/-is-set ≋)

  module _ (f : X → X)
           (p : {x y : X} → x ≈ y → f x ≈ f y)
         where

   abstract
    private
      π : identifies-related-points ≋ (η/ ≋ ∘ f)
      π e = η/-identifies-related-points ≋ (p e)

   extension₁/ : X / ≋ → X / ≋
   extension₁/ = extension/ (η/ ≋ ∘ f) π

   naturality/ : extension₁/ ∘ η/ ≋ ∼ η/ ≋ ∘ f
   naturality/ = universality-triangle/ (/-is-set ≋) (η/ ≋ ∘ f) π

  module _ (f : X → X → X)
           (p : {x y x' y' : X} → x ≈ x' → y ≈ y' → f x y ≈ f x' y')
         where

   abstract
    private
     π : (x : X) → identifies-related-points ≋ (η/ ≋ ∘ f x)
     π x {y} {y'} e = η/-identifies-related-points ≋ (p {x} {y} {x} {y'} (≈r x) e)

     p' : (x : X) {y y' : X} → y ≈ y' → f x y ≈ f x y'
     p' x {x'} {y'} = p {x} {x'} {x} {y'} (≈r x)

     f₁ : X → X / ≋ → X / ≋
     f₁ x = extension₁/ (f x) (p' x)

     δ : {x x' : X} → x ≈ x' → (y : X) → f₁ x (η/ ≋ y) ＝ f₁ x' (η/ ≋ y)
     δ {x} {x'} e y =
       f₁ x (η/ ≋ y)   ＝⟨ naturality/ (f x) (p' x) y ⟩
       η/ ≋ (f x y)    ＝⟨ η/-identifies-related-points ≋ (p e (≈r y)) ⟩
       η/ ≋ (f x' y)   ＝⟨ (naturality/ (f x') (p' x') y)⁻¹ ⟩
       f₁ x' (η/ ≋ y)  ∎

     ρ : (b : X / ≋) {x x' : X} → x ≈ x' → f₁ x b ＝ f₁ x' b
     ρ b {x} {x'} e = /-induction ≋ (λ y → /-is-set ≋) (δ e) b

     f₂ : X / ≋ → X / ≋ → X / ≋
     f₂ d e = extension/ (λ x → f₁ x e) (ρ e) d

   extension₂/ : X / ≋ → X / ≋ → X / ≋
   extension₂/ = f₂

   abstract
    naturality₂/ : (x y : X) → f₂ (η/ ≋ x) (η/ ≋ y) ＝ η/ ≋ (f x y)
    naturality₂/ x y =
     f₂ (η/ ≋ x) (η/ ≋ y) ＝⟨ extension-triangle/ (λ x → f₁ x (η/ ≋ y)) (ρ (η/ ≋ y)) x ⟩
     f₁ x (η/ ≋ y)        ＝⟨ naturality/ (f x) (p (≈r x)) y ⟩
     η/ ≋ (f x y)         ∎

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
         (≋ : EqRel {𝓤} {𝓥} X)
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
                      → ({x y : X} → x ≈[ R ] y ↔ x ≈[ R' ] y)
                      → (X / R) ≃ (X / R')
 quotients-equivalent X (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
                        (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t') ε = γ
  where
   ≋  = (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
   ≋' = (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t')
   i : {x y : X} → x ≈ y → η/ ≋' x ＝ η/ ≋' y
   i e = η/-identifies-related-points ≋' (lr-implication ε e)
   i⁻¹ : {x y : X} → x ≈' y → η/ ≋ x ＝ η/ ≋ y
   i⁻¹ e = η/-identifies-related-points ≋ (rl-implication ε e)
   f : X / ≋ → X / ≋'
   f = mediating-map/ ≋ (/-is-set ≋') (η/ ≋') i
   f⁻¹ : X / ≋' → X / ≋
   f⁻¹ = mediating-map/ ≋' (/-is-set ≋) (η/ ≋) i⁻¹
   a : (x : X) → f (f⁻¹ (η/ ≋' x)) ＝ η/ ≋' x
   a x = f (f⁻¹ (η/ ≋' x)) ＝⟨ I ⟩
         f (η/ ≋ x)        ＝⟨ II ⟩
         η/ ≋' x           ∎
    where
     I  = ap f (universality-triangle/ ≋' (/-is-set ≋) (η/ ≋) i⁻¹ x)
     II = universality-triangle/ ≋ (/-is-set ≋') (η/ ≋') i x
   α : f ∘ f⁻¹ ∼ id
   α = /-induction ≋' (λ _ → /-is-set ≋') a
   b : (x : X) → f⁻¹ (f (η/ ≋ x)) ＝ η/ ≋ x
   b x = f⁻¹ (f (η/ ≋ x)) ＝⟨ I ⟩
         f⁻¹ (η/ ≋' x)    ＝⟨ II ⟩
         η/ ≋ x           ∎
    where
     I  = ap f⁻¹ (universality-triangle/ ≋ (/-is-set ≋') (η/ ≋') i x)
     II = universality-triangle/ ≋' (/-is-set ≋) (η/ ≋) i⁻¹ x
   β : f⁻¹ ∘ f ∼ id
   β = /-induction ≋ (λ _ → /-is-set ≋) b
   γ : (X / ≋) ≃ (X / ≋')
   γ = qinveq f (f⁻¹ , β , α)

\end{code}

We now define the existence of small and large quotients:

\begin{code}

set-quotients-exist large-set-quotients-exist : 𝓤ω
set-quotients-exist       = general-set-quotients-exist (λ 𝓤 → 𝓤)
large-set-quotients-exist = general-set-quotients-exist (_⁺)

\end{code}

It turns out that quotients, if they exist, are necessarily
effective. This is proved in the module Quotient.Effectivity. But we
need to include the definition here.

\begin{code}

are-effective : {ℓ : Universe → Universe} → general-set-quotients-exist ℓ → 𝓤ω
are-effective sq = {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                   (R : EqRel {𝓤} {𝓥} X)
                   {x y : X}
                 → η/ R x ＝ η/ R y → x ≈[ R ] y
 where
  open general-set-quotients-exist sq

\end{code}
