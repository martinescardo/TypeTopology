Martin Escardo, 15th April 2025

We look at convex bodies (= cancellative, iterative mindpoint objects)
in the ∞-topos of types.

NB. Here the category of sets in a universe 𝓤 can be any 𝟏-topos in models.

These are experimental thoughts while finishing the joirnal version of
the interval objects paper with Alex Simpson.

Euclidean interval objects in categories with finite products
https://arxiv.org/abs/2504.21551

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import Naturals.Addition
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Base

module gist.IntervalObject
        (fe : Fun-Ext)
       where

convex-body-structure : 𝓤 ̇ → 𝓤 ̇
convex-body-structure X = X → X → X

is-convex-body : (X : 𝓤 ̇ ) → convex-body-structure X → 𝓤 ̇
is-convex-body X _⊕_ = Carrier-is-set × Idemp × Comm × Transp × Cancel × Iter
 where
  Carrier-is-set = is-set X
  Idemp  = (x : X) → x ⊕ x ＝ x
  Comm   = (x y : X) → x ⊕ y ＝ y ⊕ x
  Transp = (a b x y : X) → (a ⊕ b) ⊕ (x ⊕ y) ＝ (a ⊕ x) ⊕ (b ⊕ y)
  Cancel = (a x y : X) → a ⊕ x ＝ a ⊕ y → x ＝ y
  Iter   = Σ ⨁ ꞉ ((ℕ → X) → X) , Unfolding ⨁ × Canonicity ⨁
   where
    Unfolding =  ⨁ ↦ ((x : ℕ → X) → ⨁ x ＝ x 0 ⊕ ⨁ (x ∘ succ))

    Canonicity = ⨁ ↦ ((x y : ℕ → X)
                      → ((i : ℕ) → y i ＝ x i ⊕ y (succ i))
                      → y 0 ＝ ⨁ x)
\end{code}

NB. We are adopting the formulation of iteration that uses unfolding
an canonicity, which is possible as we have a natural numbers type.

NB. The iteration axiom is property, and hence so is
is-convex-body. (TODO in due course.)

\begin{code}

Convex-Body : (𝓤 : Universe) → 𝓤 ⁺ ̇
Convex-Body 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ convex-body-structure A , is-convex-body A s

⟨_⟩ : Convex-Body 𝓤 → 𝓤 ̇
⟨ A , _ ⟩ = A

is-hom : (𝓐 : Convex-Body 𝓤) (𝓑 : Convex-Body 𝓥)
       → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-hom (A , _⊕_ , _) (_ , _⊞_ , _) f = (x y : A) → f (x ⊕ y) ＝ f x ⊞ f y

is-Hom : (𝓐 : Convex-Body 𝓤) (𝓑 : Convex-Body 𝓥)
       → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-Hom (A , _ , _ , _ , _ , _ , _ , ⨁ᵃ , _)
       (_ , _ , _ , _ , _ , _ , _ , ⨁ᵇ , _) f
 = (x : ℕ → A) → f (⨁ᵃ x) ＝ ⨁ᵇ (f ∘ x)

homs-are-Homs : (𝓐 : Convex-Body 𝓤) (𝓑 : Convex-Body 𝓥)
                (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
              → is-hom 𝓐 𝓑 f
              → is-Hom 𝓐 𝓑 f
homs-are-Homs (_ , _⊕ᵃ_ , _ , _ , _ , _ , _ , ⨁ᵃ , unfoldingᵃ , _)
              (_ , _⊕ᵇ_ , _ , _ , _ , _ , _ , ⨁ᵇ , _          , canonicityᵇ)
              f f-is-hom x
 = II
 where
  I : (i : ℕ) → f (⨁ᵃ (j ↦ x (j + i))) ＝ (f (x i) ⊕ᵇ f (⨁ᵃ (j ↦ x (j + succ i))))
  I i = f (⨁ᵃ (j ↦ x (j + i)))                       ＝⟨ ap f (unfoldingᵃ _) ⟩
        f (x (0 + i) ⊕ᵃ ⨁ᵃ (j ↦ x (succ j + i)))     ＝⟨ f-is-hom _ _ ⟩
        f (x (0 + i)) ⊕ᵇ f (⨁ᵃ (j ↦ x (succ j + i))) ＝⟨ I₁ ⟩
        (f (x i) ⊕ᵇ f (⨁ᵃ (j ↦ x (j + succ i))))     ∎
    where
     I₀ = j ↦ (succ j + i   ＝⟨ addition-commutativity (succ j) i ⟩
               i + succ j   ＝⟨refl⟩
               succ (i + j) ＝⟨ ap succ (addition-commutativity i j) ⟩
               succ (j + i) ＝⟨refl⟩
               j + succ i   ∎)

     I₁ = ap₂ _⊕ᵇ_
           (ap (f ∘ x) (addition-commutativity 0 i))
           (ap (f ∘ ⨁ᵃ) (dfunext fe (j ↦ ap x (I₀ j))))

  II : f (⨁ᵃ x) ＝ ⨁ᵇ (f ∘ x)
  II = canonicityᵇ (f ∘ x) (i ↦ f (⨁ᵃ (j ↦ x (j + i)))) I


\end{code}

TODO. Add a proof Homs-are-homs of the converse (not needed for our
current purposes).

\begin{code}

id-is-hom : (𝓐 : Convex-Body 𝓤)
          → is-hom 𝓐 𝓐 id
id-is-hom 𝓐 a₀ a₁ = refl

const-is-hom : (𝓐 : Convex-Body 𝓤) (𝓑 : Convex-Body 𝓥)
               (b : ⟨ 𝓑 ⟩)
             → is-hom 𝓐 𝓑 (_ ↦ b)
const-is-hom 𝓐 𝓑@(_ , _⊕_ , _ , idemp , _) b a₀ a₁ = (idemp b)⁻¹

module _ (𝓐@(A , _⊕_ , _ , idemp , _ , transp , _) : Convex-Body 𝓤) where

 ⊕-is-left-hom : (x : A)
               → is-hom 𝓐 𝓐 (_⊕ x)
 ⊕-is-left-hom x y z =
  (y ⊕ z) ⊕ x       ＝⟨ ap ((y ⊕ z) ⊕_) ((idemp x)⁻¹) ⟩
  (y ⊕ z) ⊕ (x ⊕ x) ＝⟨ transp y z x x ⟩
  (y ⊕ x) ⊕ (z ⊕ x) ∎

 ⊕-is-right-hom : (x : A)
                → is-hom 𝓐 𝓐 (x ⊕_)
 ⊕-is-right-hom x y z =
  x ⊕ (y ⊕ z)       ＝⟨ ap (_⊕ (y ⊕ z)) ((idemp x)⁻¹) ⟩
  (x ⊕ x) ⊕ (y ⊕ z) ＝⟨ transp x x y z ⟩
  (x ⊕ y) ⊕ (x ⊕ z) ∎

∘-is-hom : (𝓐 : Convex-Body 𝓤) (𝓑 : Convex-Body 𝓥) (𝓒 : Convex-Body 𝓦)
           (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) (g : ⟨ 𝓑 ⟩ → ⟨ 𝓒 ⟩)
         → is-hom 𝓐 𝓑 f
         → is-hom 𝓑 𝓒 g
         → is-hom 𝓐 𝓒 (g ∘ f)
∘-is-hom 𝓐@(A , _⊕ᵃ_ , _) 𝓑@(B , _⊕ᵇ_ , _) 𝓒@(C , _⊕ᶜ_ , _)
         f g f-is-hom g-is-hom a₀ a₁ =
 g (f (a₀ ⊕ᵃ a₁))           ＝⟨ ap g (f-is-hom a₀ a₁) ⟩
 g (f a₀ ⊕ᵇ f a₁)           ＝⟨ g-is-hom (f a₀) (f a₁) ⟩
 ((g ∘ f) a₀ ⊕ᶜ (g ∘ f) a₁) ∎

is-interval-object : (𝓐 : Convex-Body 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → 𝓤ω
is-interval-object 𝓐 a₀ a₁ =
  {𝓥 : Universe} (𝓑 : Convex-Body 𝓥) (b₀ b₁ : ⟨ 𝓑 ⟩)
 → ∃! h ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) , is-hom 𝓐 𝓑 h
                           × (h a₀ ＝ b₀)
                           × (h a₁ ＝ b₁)

module _ (𝓧@(X ,
             _⊞_ ,
             X-is-set ,
             ⊞-idemp ,
             ⊞-comm ,
             ⊞-transp ,
             ⊞-cancel ,
             ⊞-iter@(M , ⊞-unfolding , ⊞-canonicity))
           : Convex-Body 𝓥)
       where

 append : X → (ℕ → X) → (ℕ → X)
 append x s 0        = x
 append x s (succ i) = s i

 constant-sequence : X → (ℕ → X)
 constant-sequence x i = x

 ⊞-fix : (a x : X) → a ＝ x ⊞ a → a ＝ x
 ⊞-fix a x e = ⊞-cancel a a x
                (a ⊞ a ＝⟨ ⊞-idemp a ⟩
                 a     ＝⟨ e  ⟩
                 x ⊞ a ＝⟨ ⊞-comm x a ⟩
                 a ⊞ x ∎)

 constant-iteration : (x : X) → M (constant-sequence x) ＝ x
 constant-iteration x = ⊞-fix (M (constant-sequence x)) x I
  where
   I : M (constant-sequence x) ＝ x ⊞ M (constant-sequence x)
   I = ⊞-unfolding (constant-sequence x)

 binary-from-infinitary : (x y : X) → M (append x (constant-sequence y)) ＝ x ⊞ y
 binary-from-infinitary x y = I
  where
   I = M (append x (constant-sequence y)) ＝⟨ I₀ ⟩
       x ⊞ M (constant-sequence y)        ＝⟨ I₁ ⟩
       x ⊞ y                     ∎
        where
         I₀ = ⊞-unfolding (append x (constant-sequence y))
         I₁ = ap (x ⊞_) (constant-iteration y)

module _ (𝓤 : Universe)
         (𝓘@([𝟎,𝟏] ,
          _⊕_ ,
          [𝟎,𝟏]-is-set ,
          ⊕-idemp ,
          ⊕-comm ,
          ⊕-transp ,
          ⊕-cancel ,
          ⊕-iter@(⨁ , ⊕-unfolding , ⊕-canonicity)) : Convex-Body 𝓤)
         (𝟎 𝟏 : [𝟎,𝟏])
         ([𝟎,𝟏]-is-interval-object : is-interval-object 𝓘 𝟎 𝟏)
       where

 module standard-definitions
         (𝓐@(A , _⊞_ , A-is-set , ⊞-idemp , ⊞-comm , ⊞-transp , ⊞-cancel , ⊞-iter)
           : Convex-Body 𝓥)
        where

\end{code}

We think of α a₀ a₁ defined below as the line from a₀ to a₁ in A, or
as the unique affine function that maps 𝟎 to a₀ and 𝟏 to a₁. We also
think of α a₀ a₁ r as the weighted average of a₀ and a₁ with left
weight r and right weight 1 - r, often termed a convex combination of
a₀ and a₁.

\begin{code}

  α : A → A → [𝟎,𝟏] → A
  α a₀ a₁ = ∃!-witness ([𝟎,𝟏]-is-interval-object 𝓐 a₀ a₁)

  module _ (a₀ a₁ : A) where

   α-property : is-hom 𝓘 𝓐 (α a₀ a₁)
              × (α a₀ a₁ 𝟎 ＝ a₀)
              × (α a₀ a₁ 𝟏 ＝ a₁)
   α-property = ∃!-is-witness ([𝟎,𝟏]-is-interval-object 𝓐 a₀ a₁)

   α-is-hom : is-hom 𝓘 𝓐 (α a₀ a₁)
   α-is-hom = pr₁ α-property

   α-law₀ : α a₀ a₁ 𝟎 ＝ a₀
   α-law₀ = pr₁ (pr₂ α-property)

   α-law₁ : α a₀ a₁ 𝟏 ＝ a₁
   α-law₁ = pr₂ (pr₂ α-property)

   at-most-one-hom : (h k : ⟨ 𝓘 ⟩ → A)
                   → is-hom 𝓘 𝓐 h × (h 𝟎 ＝ a₀) × (h 𝟏 ＝ a₁)
                   → is-hom 𝓘 𝓐 k × (k 𝟎 ＝ a₀) × (k 𝟏 ＝ a₁)
                   → h ∼ k
   at-most-one-hom h k u v =
    happly (witness-uniqueness _ ([𝟎,𝟏]-is-interval-object 𝓐 a₀ a₁) h k u v)

   α-uniqueness : (h : [𝟎,𝟏] → A)
                → is-hom 𝓘 𝓐 h × (h 𝟎 ＝ a₀) × (h 𝟏 ＝ a₁)
                → h ∼ α a₀ a₁
   α-uniqueness h h-property = at-most-one-hom h (α a₀ a₁) h-property α-property

   α-uniqueness⁻¹ : (h : [𝟎,𝟏] → A)
                  → is-hom 𝓘 𝓐 h × (h 𝟎 ＝ a₀) × (h 𝟏 ＝ a₁)
                  → α a₀ a₁ ∼ h
   α-uniqueness⁻¹ h h-property r = (α-uniqueness h h-property r)⁻¹

  homs-charac : (h : [𝟎,𝟏] → A) → is-hom 𝓘 𝓐 h → h ∼ α (h 𝟎) (h 𝟏)
  homs-charac h h-is-hom = α-uniqueness (h 𝟎) (h 𝟏) h (h-is-hom , refl , refl)

  homs-charac⁻¹ : (h : [𝟎,𝟏] → A) → is-hom 𝓘 𝓐 h → α (h 𝟎) (h 𝟏) ∼ h
  homs-charac⁻¹ h h-is-hom r = (homs-charac h h-is-hom r)⁻¹

  α-law₂ : (r : [𝟎,𝟏]) (x : A) → α x x r ＝ x
  α-law₂ r x = homs-charac⁻¹ (_ ↦ x) (const-is-hom 𝓘 𝓐 x) r

\end{code}

End of module standard-definitions, and still in anonymous module
assumming an interval [𝟎,𝟏].

Observation (17th April 2025). If we don't assume commutativity in the
definition of interval object, but only that 𝟎 ⊕ 𝟏 ＝ 𝟏 ⊕ 𝟎, then we
get commutativity automatically. The advantage of a definition
replacing commutativity by commutativity at 𝟎 and 𝟏 only is that we
have a more general class of convex bodies in the universal
property. However, we will keep working with the less general
definition in this file, leaving the generalization to future work (of
the author or any interested reader).

\begin{code}

 module observation where

  open standard-definitions 𝓘

  comm-automatic₀ : (x : [𝟎,𝟏])
                  → 𝟎 ⊕ 𝟏 ＝ 𝟏 ⊕ 𝟎
                  → 𝟎 ⊕ x ＝ x ⊕ 𝟎
  comm-automatic₀ x e = at-most-one-hom (𝟎 ⊕ 𝟎) (𝟎 ⊕ 𝟏) (𝟎 ⊕_) (_⊕ 𝟎)
                         (⊕-is-right-hom 𝓘 𝟎 , refl , refl)
                         (⊕-is-left-hom  𝓘 𝟎 , refl , (e ⁻¹))
                         x

  comm-automatic₁ : (x : [𝟎,𝟏])
                  → 𝟎 ⊕ 𝟏 ＝ 𝟏 ⊕ 𝟎
                  → 𝟏 ⊕ x ＝ x ⊕ 𝟏
  comm-automatic₁ x e = at-most-one-hom (𝟏 ⊕ 𝟎) (𝟏 ⊕ 𝟏) (𝟏 ⊕_) (_⊕ 𝟏)
                         (⊕-is-right-hom 𝓘 𝟏 , refl , refl)
                         (⊕-is-left-hom  𝓘 𝟏 , e , refl)
                         x

  comm-automatic : (x y : [𝟎,𝟏])
                 → 𝟎 ⊕ 𝟏 ＝ 𝟏 ⊕ 𝟎
                 → x ⊕ y ＝ y ⊕ x
  comm-automatic x y e =
   at-most-one-hom (x ⊕ 𝟎) (x ⊕ 𝟏) (x ⊕_) (_⊕ x)
    (⊕-is-right-hom 𝓘 x , refl , refl)
    (⊕-is-left-hom 𝓘 x , comm-automatic₀ x e , comm-automatic₁ x e)
    y

\end{code}

End of module observation and still in the anonymous module assuming
an interval object [𝟎,𝟏].

\begin{code}

 open standard-definitions

 private
  α̲ : [𝟎,𝟏] → [𝟎,𝟏] → [𝟎,𝟏] → [𝟎,𝟏]
  α̲ = α 𝓘

 line-from-𝟎-to-𝟏-is-id : α̲ 𝟎 𝟏 ∼ id
 line-from-𝟎-to-𝟏-is-id = homs-charac⁻¹ 𝓘 id (id-is-hom 𝓘)

\end{code}

Induction on [𝟎,𝟏]. (Added 28th April 2025.)

This requires more than just a category with finite
products. Everything else in this file should work in a category with
finite products.

TODO. There should be a variation that doesn't assume that P is prop-valued.

\begin{code}

 is-closed-under-midpoint : ([𝟎,𝟏] → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 is-closed-under-midpoint P = (r s : [𝟎,𝟏]) → P r → P s → P (r ⊕ s)

 is-closed-under-big-midpoint : ([𝟎,𝟏] → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 is-closed-under-big-midpoint P = (x : ℕ → [𝟎,𝟏]) → ((i : ℕ) → P (x i)) → P (⨁ x)

 closure-under-big-midpoint-gives-closure-under-midpoint
  : (P : [𝟎,𝟏] → 𝓥 ̇ )
  → is-closed-under-big-midpoint P
  → is-closed-under-midpoint P
 closure-under-big-midpoint-gives-closure-under-midpoint
  P P⨁ r s pr ps
  = transport P
     (binary-from-infinitary 𝓘 r s)
     (P⨁ (append 𝓘 r (constant-sequence 𝓘 s)) I)
    where
     I : (i : ℕ) → P (append 𝓘 r (constant-sequence 𝓘 s) i)
     I 0        = pr
     I (succ i) = ps

 [𝟎,𝟏]-induction
  : (P : [𝟎,𝟏] → 𝓥 ̇ )
  → ((r : [𝟎,𝟏]) → is-prop (P r))
  → P 𝟎
  → P 𝟏
  → is-closed-under-big-midpoint P
  → (r : [𝟎,𝟏]) → P r
 [𝟎,𝟏]-induction {𝓥} P P-is-prop-valued P₀ P₁ P⨁ = VI
  where
   X : 𝓤 ⊔ 𝓥 ̇
   X = Σ r ꞉ [𝟎,𝟏] , P r

   X-is-set : is-set X
   X-is-set = subtypes-of-sets-are-sets' pr₁
               (pr₁-lc (P-is-prop-valued _))
               [𝟎,𝟏]-is-set

   P⊕ : (r s : [𝟎,𝟏]) → P r → P s → P (r ⊕ s)
   P⊕ = closure-under-big-midpoint-gives-closure-under-midpoint P P⨁

   _⊞_ : X → X → X
   (r , pr) ⊞ (s , ps) = r ⊕ s , P⊕ r s pr ps

   ⊞-idemp : (x : X) → x ⊞ x ＝ x
   ⊞-idemp (r , _) = to-subtype-＝ P-is-prop-valued (⊕-idemp r)

   ⊞-comm : (x y : X) → x ⊞ y ＝ y ⊞ x
   ⊞-comm (r , _) (s , _) = to-subtype-＝ P-is-prop-valued (⊕-comm r s)

   ⊞-transp : (a b x y : X) → (a ⊞ b) ⊞ (x ⊞ y) ＝ (a ⊞ x) ⊞ (b ⊞ y)
   ⊞-transp (u , _) (v , _) (r , _) (s , _) =
    to-subtype-＝ P-is-prop-valued (⊕-transp u v r s)

   ⊞-cancel : (a x y : X) → a ⊞ x ＝ a ⊞ y → x ＝ y
   ⊞-cancel (u , _) (r , _) (s , _) e =
    to-subtype-＝ P-is-prop-valued (⊕-cancel u r s (ap pr₁ e))

   M : (ℕ → X) → X
   M x = (⨁ (pr₁ ∘ x)) ,
         P⨁ (pr₁ ∘ x) (pr₂ ∘ x)

   ⊞-unfolding : (x : ℕ → X) → M x ＝ x 0 ⊞ M (x ∘ succ)
   ⊞-unfolding x = to-subtype-＝ P-is-prop-valued (⊕-unfolding (pr₁ ∘ x))

   ⊞-canonicity : (x y : ℕ → X)
                → ((i : ℕ) → y i ＝ x i ⊞ y (succ i))
                → y 0 ＝ M x
   ⊞-canonicity x y a = to-subtype-＝ P-is-prop-valued
                         (⊕-canonicity (pr₁ ∘ x) (pr₁ ∘ y) (λ i → ap pr₁ (a i)))

   ⊞-iter = M , ⊞-unfolding , ⊞-canonicity

   𝓧 : Convex-Body (𝓤 ⊔ 𝓥)
   𝓧 = X , _⊞_ , X-is-set , ⊞-idemp , ⊞-comm , ⊞-transp , ⊞-cancel , ⊞-iter

   x₀ x₁ : X
   x₀ = 𝟎 , P₀
   x₁ = 𝟏 , P₁

   h : [𝟎,𝟏] → X
   h = α 𝓧 x₀ x₁

   pr₁-is-hom : is-hom 𝓧 𝓘 pr₁
   pr₁-is-hom x y = refl

   I : is-hom 𝓘 𝓘 (pr₁ ∘ h)
   I = ∘-is-hom 𝓘 𝓧 𝓘 h pr₁ (α-is-hom 𝓧 x₀ x₁) pr₁-is-hom

   II₀ : pr₁ (h 𝟎) ＝ 𝟎
   II₀ = ap pr₁ (α-law₀ 𝓧 x₀ x₁)

   II₁ : pr₁ (h 𝟏) ＝ 𝟏
   II₁ = ap pr₁ (α-law₁ 𝓧 x₀ x₁)

   III : pr₁ ∘ h ∼ α̲ 𝟎 𝟏
   III = α-uniqueness 𝓘 𝟎 𝟏 (pr₁ ∘ h) (I , II₀ , II₁)

   IV : pr₁ ∘ h ∼ id
   IV r = III r ∙ line-from-𝟎-to-𝟏-is-id r

   V : (r : [𝟎,𝟏]) → P (pr₁ (h r))
   V r = pr₂ (h r )

   VI : (r : [𝟎,𝟏]) → P r
   VI r = transport P (IV r) (V r)

\end{code}

Notice, however, that a number of operations can be defined and their
properties can be easily established without induction, using only the
universal property of [𝟎,𝟏].

Complement and multiplication.

\begin{code}

 𝟏- : [𝟎,𝟏] → [𝟎,𝟏]
 𝟏- r = α̲ 𝟏 𝟎 r

 𝟏-𝟎-is-𝟏 : 𝟏- 𝟎 ＝ 𝟏
 𝟏-𝟎-is-𝟏 = α-law₀ 𝓘 𝟏 𝟎

 𝟏-𝟏-is-𝟎 : 𝟏- 𝟏 ＝ 𝟎
 𝟏-𝟏-is-𝟎 = α-law₁ 𝓘 𝟏 𝟎

 𝟏-is-hom : (r s : [𝟎,𝟏]) → 𝟏- (r ⊕ s) ＝ (𝟏- r) ⊕ (𝟏- s)
 𝟏-is-hom = α-is-hom 𝓘 𝟏 𝟎

 𝟏-involution : (r : [𝟎,𝟏]) → 𝟏- (𝟏- r) ＝ r
 𝟏-involution =
  at-most-one-hom 𝓘 𝟎 𝟏 (𝟏- ∘ 𝟏-) id
   (∘-is-hom 𝓘 𝓘 𝓘 𝟏- 𝟏- 𝟏-is-hom 𝟏-is-hom ,
   (𝟏- (𝟏- 𝟎) ＝⟨ ap 𝟏- 𝟏-𝟎-is-𝟏 ⟩
    𝟏- 𝟏      ＝⟨ 𝟏-𝟏-is-𝟎 ⟩
    𝟎         ∎) ,
   (𝟏- (𝟏- 𝟏) ＝⟨ ap 𝟏- 𝟏-𝟏-is-𝟎 ⟩
    𝟏- 𝟎      ＝⟨ 𝟏-𝟎-is-𝟏 ⟩
    𝟏         ∎))
    (id-is-hom 𝓘 , refl , refl)

 ½ : [𝟎,𝟏]
 ½ = 𝟎 ⊕ 𝟏

 ½-is-𝟏-fix : 𝟏- ½ ＝ ½
 ½-is-𝟏-fix =
  𝟏- ½            ＝⟨ 𝟏-is-hom 𝟎 𝟏 ⟩
  (𝟏- 𝟎) ⊕ (𝟏- 𝟏) ＝⟨ ap₂ _⊕_ 𝟏-𝟎-is-𝟏 𝟏-𝟏-is-𝟎 ⟩
  𝟏 ⊕ 𝟎           ＝⟨ ⊕-comm 𝟏 𝟎 ⟩
  𝟎 ⊕ 𝟏           ∎

 ⊕-𝟏-½-property : (r : [𝟎,𝟏]) → r ⊕ (𝟏- r) ＝ ½
 ⊕-𝟏-½-property =
  at-most-one-hom 𝓘 ½ ½ h (_ ↦ ½)
   (h-is-hom , ap (𝟎 ⊕_) 𝟏-𝟎-is-𝟏 , (ap (𝟏 ⊕_) 𝟏-𝟏-is-𝟎 ∙ ⊕-comm 𝟏 𝟎))
   (const-is-hom 𝓘 𝓘 ½ , refl , refl)
  where
   h : [𝟎,𝟏] → [𝟎,𝟏]
   h r = r ⊕ (𝟏- r)

   h-is-hom : is-hom 𝓘 𝓘 h
   h-is-hom r s =
    (r ⊕ s) ⊕ (𝟏- (r ⊕ s))      ＝⟨ ap ((r ⊕ s) ⊕_) (𝟏-is-hom r s) ⟩
    (r ⊕ s) ⊕ ((𝟏- r) ⊕ (𝟏- s)) ＝⟨ ⊕-transp r s (𝟏- r) (𝟏- s) ⟩
    (r ⊕ (𝟏- r)) ⊕ (s ⊕ (𝟏- s)) ∎

 _·_ : [𝟎,𝟏] → [𝟎,𝟏] → [𝟎,𝟏]
 r · s = α̲ 𝟎 s r

 𝟎-left : (s : [𝟎,𝟏]) → 𝟎 · s ＝ 𝟎
 𝟎-left = α-law₀ 𝓘 𝟎

 𝟏-left : (s : [𝟎,𝟏]) → 𝟏 · s ＝ s
 𝟏-left = α-law₁ 𝓘 𝟎

 mult-is-left-hom : (s : [𝟎,𝟏]) → is-hom 𝓘 𝓘 (_· s)
 mult-is-left-hom = α-is-hom 𝓘 𝟎

 mult-mid-left-distr : (r s t : [𝟎,𝟏]) → (r ⊕ s) · t ＝ (r · t) ⊕ (s · t)
 mult-mid-left-distr r s t = mult-is-left-hom t r s

 mult-is-assoc : (r s t : [𝟎,𝟏]) → r · (s · t) ＝ (r · s) · t
 mult-is-assoc r s t = γ
  where
   I : is-hom 𝓘 𝓘 (r ↦ (r · s) · t)
   I r₀ r₁ =
    ((r₀ ⊕ r₁) · s) · t             ＝⟨ ap (_· t) (mult-is-left-hom s r₀ r₁) ⟩
    ((r₀ · s) ⊕ (r₁ · s)) · t       ＝⟨ mult-is-left-hom t (r₀ · s) (r₁ · s) ⟩
    ((r₀ · s) · t) ⊕ ((r₁ · s) · t) ∎

   II₀ = (𝟎 · s) · t ＝⟨ ap (_· t) (𝟎-left s) ⟩
         𝟎 · t       ＝⟨ 𝟎-left t ⟩
         𝟎           ∎

   II₁ = (𝟏 · s) · t ＝⟨ ap (_· t) (𝟏-left s) ⟩
         s · t       ∎

   γ : r · (s · t) ＝ (r · s) · t
   γ = α-uniqueness⁻¹ 𝓘 𝟎 (s · t) (r ↦ (r · s) · t) (I , II₀ , II₁) r

 𝟎-right : (r : [𝟎,𝟏]) → r · 𝟎 ＝ 𝟎
 𝟎-right r = α-law₂ 𝓘 r 𝟎

 𝟏-right : (r : [𝟎,𝟏]) → r · 𝟏 ＝ r
 𝟏-right = line-from-𝟎-to-𝟏-is-id

 mult-is-right-hom : (r : [𝟎,𝟏]) → is-hom 𝓘 𝓘 (r ·_)
 mult-is-right-hom r s t = γ
  where
   f g : [𝟎,𝟏] → [𝟎,𝟏]
   f r = r · (s ⊕ t)
   g r = (r · s) ⊕ (r · t)

   f-is-hom : is-hom 𝓘 𝓘 f
   f-is-hom = mult-is-left-hom (s ⊕ t)

   g-is-hom : is-hom 𝓘 𝓘 g
   g-is-hom r₀ r₁ =
    ((r₀ ⊕ r₁) · s) ⊕ ((r₀ ⊕ r₁) · t)             ＝⟨ I ⟩
    ((r₀ · s) ⊕ (r₁ · s)) ⊕ ((r₀ · t) ⊕ (r₁ · t)) ＝⟨ II ⟩
    ((r₀ · s) ⊕ (r₀ · t)) ⊕ ((r₁ · s) ⊕ (r₁ · t)) ∎
     where
      I  = ap₂ _⊕_ (mult-is-left-hom s r₀ r₁) (mult-is-left-hom t r₀ r₁)
      II = ⊕-transp (r₀ · s) (r₁ · s) (r₀ · t) (r₁ · t)

   f₀ : f 𝟎 ＝ 𝟎
   f₀ = 𝟎-left (s ⊕ t)

   f₁ : f 𝟏 ＝ s ⊕ t
   f₁ = 𝟏-left (s ⊕ t)

   g₀ : g 𝟎 ＝ 𝟎
   g₀ =  (𝟎 · s) ⊕ (𝟎 · t) ＝⟨ ap₂ _⊕_ (𝟎-left s) (𝟎-left t) ⟩
         𝟎 ⊕ 𝟎             ＝⟨ ⊕-idemp 𝟎 ⟩
         𝟎                 ∎

   g₁ : g 𝟏 ＝ s ⊕ t
   g₁ = ap₂ _⊕_ (𝟏-left s) (𝟏-left t)

   γ : f r ＝ g r
   γ = at-most-one-hom 𝓘 𝟎 (s ⊕ t) f g
        (f-is-hom , f₀ , f₁)
        (g-is-hom , g₀ , g₁)
        r

 mult-is-comm : (r s : [𝟎,𝟏]) → r · s ＝ s · r
 mult-is-comm r s = α-uniqueness⁻¹ 𝓘 𝟎 s (s ·_)
                     (mult-is-right-hom s , 𝟎-right s , 𝟏-right s)
                     r
 mult-mid-right-distr : (r s t : [𝟎,𝟏]) → r · (s ⊕ t) ＝ (r · s) ⊕ (r · t)
 mult-mid-right-distr = mult-is-right-hom

\end{code}

TODO. r · s ＝ 𝟏 → r ＝ 𝟏.

In an interval object [𝟎,𝟏] in a cartesian closed category, we cannot
prove that 𝟎 ≠ 𝟏, because a terminal category is cartesian closed and
any of its (terminal) objects is an interval objects, but terminal
objects have only one global point by definition. But we can prove the
following in any ccc with interval object.

\begin{code}

 [𝟎,𝟏]-triviality : 𝟎 ＝ 𝟏 → (r s : [𝟎,𝟏]) → r ＝ s
 [𝟎,𝟏]-triviality e r s =
   r       ＝⟨ (α-law₀ 𝓘 r s)⁻¹ ⟩
   α̲ r s 𝟎 ＝⟨ ap (α̲ r s) e ⟩
   α̲ r s 𝟏 ＝⟨ α-law₁ 𝓘 r s ⟩
   s       ∎

\end{code}

Homomorphisms automatically preserve convex combinations.

\begin{code}

 homs-preserve-ccs : (𝓐 : Convex-Body 𝓤) (𝓑 : Convex-Body 𝓥)
                   → (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
                   → is-hom 𝓐 𝓑 h
                   → (x₀ x₁ : ⟨ 𝓐 ⟩) (r : [𝟎,𝟏])
                   → h (α 𝓐 x₀ x₁ r) ＝ α 𝓑 (h x₀) (h x₁) r
 homs-preserve-ccs 𝓐@(A , _⊕ᵃ_ , _) 𝓑@(_ , _⊕ᵇ_ , _) h h-is-hom x₀ x₁ =
  f-and-g-agreement
  where
   f : [𝟎,𝟏] → ⟨ 𝓑 ⟩
   f r = h (α 𝓐 x₀ x₁ r)

   f-is-hom : is-hom 𝓘 𝓑 f
   f-is-hom = ∘-is-hom 𝓘 𝓐 𝓑 (α 𝓐 x₀ x₁) h (α-is-hom 𝓐 x₀ x₁) h-is-hom

   𝟎-agreement : f 𝟎 ＝ h x₀
   𝟎-agreement = ap h (α-law₀ 𝓐 x₀ x₁)

   𝟏-agreement : f 𝟏 ＝ h x₁
   𝟏-agreement = ap h (α-law₁ 𝓐 x₀ x₁)

   f-and-g-agreement : f ∼ α 𝓑 (h x₀) (h x₁)
   f-and-g-agreement = α-uniqueness 𝓑 (h x₀) (h x₁) f
                        (f-is-hom , 𝟎-agreement , 𝟏-agreement)

 module _ (𝓧@(X , _⊞_ , X-is-set , ⊞-idemp , ⊞-comm , ⊞-transp , ⊞-cancel , ⊞-iter)
             : Convex-Body 𝓥)
        where

  α̅ : X → X → [𝟎,𝟏] → X
  α̅ = α 𝓧

  c : [𝟎,𝟏] → X → X → X
  c r x y = α̅ x y r

  c̅ : [𝟎,𝟏] → [𝟎,𝟏] → [𝟎,𝟏] → [𝟎,𝟏]
  c̅ r x y = α̲ x y r

  ½-combination : (x₀ x₁ : X) → c ½ x₀ x₁ ＝ x₀ ⊞ x₁
  ½-combination x₀ x₁ =
   c ½ x₀ x₁             ＝⟨refl⟩
   α̅ x₀ x₁ (𝟎 ⊕ 𝟏)       ＝⟨ α-is-hom 𝓧 x₀ x₁ 𝟎 𝟏 ⟩
   α̅ x₀ x₁ 𝟎 ⊞ α̅ x₀ x₁ 𝟏 ＝⟨ ap₂ _⊞_ (α-law₀ 𝓧 x₀ x₁) (α-law₁ 𝓧 x₀ x₁) ⟩
   x₀ ⊞ x₁               ∎

  α-self-hom : (x₀ x₁ : X) (s₀ s₁ r : [𝟎,𝟏])
             → α̅ x₀ x₁ (α̲ s₀ s₁ r) ＝ α̅ (α̅ x₀ x₁ s₀) (α̅ x₀ x₁ s₁) r
  α-self-hom x₀ x₁ = homs-preserve-ccs 𝓘 𝓧 (α̅ x₀ x₁) (α-is-hom 𝓧 x₀ x₁)

  c-self-hom : (r s₀ s₁ : [𝟎,𝟏]) (x₀ x₁ : X)
             → c (c̅ r s₀ s₁) x₀ x₁ ＝ c r (c s₀ x₀ x₁) (c s₁ x₀ x₁)
  c-self-hom r s₀ s₁ x₀ x₁ = α-self-hom x₀ x₁ s₀ s₁ r

  c-self-hom-special : (r s : [𝟎,𝟏]) (x₀ x₁ : X)
                     → c (r · s) x₀ x₁ ＝ c r x₀ (c s x₀ x₁)
  c-self-hom-special r s x₀ x₁ =
   c (r · s) x₀ x₁             ＝⟨ I ⟩
   c r (c 𝟎 x₀ x₁) (c s x₀ x₁) ＝⟨ II ⟩
   c r x₀ (c s x₀ x₁)          ∎
    where
     I  = c-self-hom r 𝟎 s x₀ x₁
     II = ap (- ↦ c r - (c s x₀ x₁)) (α-law₀ 𝓧 x₀ x₁)

  α-is-hom₀₁ : (x₀ x₁ y₀ y₁ : X) (r : [𝟎,𝟏])
            → α̅ (x₀ ⊞ x₁) (y₀ ⊞ y₁) r ＝ α̅ x₀ y₀ r ⊞ α̅ x₁ y₁ r
  α-is-hom₀₁ x₀ x₁ y₀ y₁ =
   α-uniqueness⁻¹ 𝓧 (x₀ ⊞ x₁) (y₀ ⊞ y₁) f (f-is-hom , 𝟎-agreement , 𝟏-agreement)
   where
    f : [𝟎,𝟏] → X
    f r = α̅ x₀ y₀ r ⊞ α̅ x₁ y₁ r

    f-is-hom : is-hom 𝓘 𝓧 f
    f-is-hom r s =
     (α̅ x₀ y₀ (r ⊕ s) ⊞ α̅ x₁ y₁ (r ⊕ s))               ＝⟨ I ⟩
     (α̅ x₀ y₀ r ⊞ α̅ x₀ y₀ s) ⊞ (α̅ x₁ y₁ r ⊞ α̅ x₁ y₁ s) ＝⟨ II ⟩
     (α̅ x₀ y₀ r ⊞ α̅ x₁ y₁ r) ⊞ (α̅ x₀ y₀ s ⊞ α̅ x₁ y₁ s) ∎
      where
       I = ap₂
            _⊞_
            (α-is-hom 𝓧 x₀ y₀ r s)
            (α-is-hom 𝓧 x₁ y₁ r s)

       II = ⊞-transp (α̅ x₀ y₀ r) (α̅ x₀ y₀ s) (α̅ x₁ y₁ r) (α̅ x₁ y₁ s)

    𝟎-agreement : f 𝟎 ＝ x₀ ⊞ x₁
    𝟎-agreement =
     f 𝟎                 ＝⟨refl⟩
     α̅ x₀ y₀ 𝟎 ⊞ α̅ x₁ y₁ 𝟎 ＝⟨ I ⟩
     x₀ ⊞ x₁             ∎
      where
       I = ap₂ _⊞_ (α-law₀ 𝓧 x₀ y₀) (α-law₀ 𝓧 x₁ y₁)

    𝟏-agreement : f 𝟏 ＝ y₀ ⊞ y₁
    𝟏-agreement =
     f 𝟏                   ＝⟨refl⟩
     α̅ x₀ y₀ 𝟏 ⊞ α̅ x₁ y₁ 𝟏 ＝⟨ I ⟩
     y₀ ⊞ y₁               ∎
      where
       I = ap₂ _⊞_ (α-law₁ 𝓧 x₀ y₀) (α-law₁ 𝓧 x₁ y₁)

  α-is-hom₀ : (x₀ x₁ y : X) (r : [𝟎,𝟏])
            → α̅ (x₀ ⊞ x₁) y r ＝ α̅ x₀ y r ⊞ α̅ x₁ y r
  α-is-hom₀ x₀ x₁ y r =
   α̅ (x₀ ⊞ x₁) y r       ＝⟨ ap (- ↦ α̅ (x₀ ⊞ x₁) - r) ((⊞-idemp y)⁻¹) ⟩
   α̅ (x₀ ⊞ x₁) (y ⊞ y) r ＝⟨ α-is-hom₀₁ x₀ x₁ y y r ⟩
   α̅ x₀ y r ⊞ α̅ x₁ y r   ∎

  α-is-hom₁ : (x y₀ y₁ : X) (r : [𝟎,𝟏])
            → α̅ x (y₀ ⊞ y₁) r ＝ α̅ x y₀ r ⊞ α̅ x y₁ r
  α-is-hom₁ x y₀ y₁ r =
   α̅ x (y₀ ⊞ y₁) r       ＝⟨ ap (- ↦ α̅ - (y₀ ⊞ y₁) r) ((⊞-idemp x)⁻¹) ⟩
   α̅ (x ⊞ x) (y₀ ⊞ y₁) r ＝⟨ α-is-hom₀₁ x x y₀ y₁ r ⟩
   α̅ x y₀ r ⊞ α̅ x y₁ r   ∎

  α-law₃ : (r : [𝟎,𝟏]) (x y : X) → c r x y ＝ c (𝟏- r) y x
  α-law₃ r x y = III
   where
    I : is-hom 𝓘 𝓧 (- ↦ c (𝟏- -) y x)
    I = ∘-is-hom 𝓘 𝓘 𝓧 𝟏- (- ↦ c - y x) (α-is-hom 𝓘 𝟏 𝟎) (α-is-hom 𝓧 y x)

    II₀ = c (𝟏- 𝟎) y x    ＝⟨refl⟩
          α̅ y x (α̲ 𝟏 𝟎 𝟎) ＝⟨ ap (α̅ y x) (α-law₀ 𝓘 𝟏 𝟎) ⟩
          α̅ y x 𝟏         ＝⟨ α-law₁ 𝓧 y x ⟩
          x               ∎

    II₁ = c (𝟏- 𝟏) y x    ＝⟨refl⟩
          α̅ y x (α̲ 𝟏 𝟎 𝟏) ＝⟨ ap (α̅ y x) (α-law₁ 𝓘 𝟏 𝟎) ⟩
          α̅ y x 𝟎         ＝⟨ α-law₀ 𝓧 y x ⟩
          y               ∎

    III : c r x y ＝ c (𝟏- r) y x
    III = α-uniqueness⁻¹ 𝓧 x y (ƛ ↦ c (𝟏- ƛ) y x) (I , II₀ , II₁) r

\end{code}
