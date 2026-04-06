Jon Sterling, started 16th Dec 2022

A deductive system is a category-like structure in that omits the associativity
law; associativity of pre-and-post-composition then begins a *property* of
certain morphisms. This captures the behavior of *effectful* programs, whose
composition is not also associative; this perspective of effectful programs
arises from an analysis of the dynamics of cut elimination in polarized sequent
calculus. For this reason, we denote morphisms by `A ⊢ B` and write `cut` for
the (non-associative) composition operation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Duploids.DeductiveSystem (fe : Fun-Ext) where

open import UF.Equiv

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import deprecated.Categories.Category fe

deductive-system-structure : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
deductive-system-structure 𝓤 𝓥 = category-structure 𝓤 𝓥

module deductive-system-structure (𝓓 : deductive-system-structure 𝓤 𝓥) where
 ob : 𝓤 ̇
 ob = pr₁ 𝓓

 _⊢_ : ob → ob → 𝓥 ̇
 A ⊢ B = pr₁ (pr₂ 𝓓) A B

 idn : (A : ob) → A ⊢ A
 idn A = pr₁ (pr₂ (pr₂ 𝓓)) A

 cut : {A B C : ob} (f : A ⊢ B) (g : B ⊢ C) → A ⊢ C
 cut f g = pr₂ (pr₂ (pr₂ 𝓓)) _ _ _ f g

module _ (𝓓 : deductive-system-structure 𝓤 𝓥) where
 open deductive-system-structure 𝓓
 open category-axiom-statements 𝓓

 deductive-system-axioms : 𝓤 ⊔ 𝓥 ̇
 deductive-system-axioms =
  statement-hom-is-set
  × statement-idn-L
  × statement-idn-R

 module deductive-system-axioms (ax : deductive-system-axioms) where
  ⊢-is-set : statement-hom-is-set
  ⊢-is-set = pr₁ ax

  idn-L : statement-idn-L
  idn-L = pr₁ (pr₂ ax)

  idn-R : statement-idn-R
  idn-R = pr₂ (pr₂ ax)

record deductive-system (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇ where
 constructor make
 field
  str : deductive-system-structure 𝓤 𝓥
  ax : deductive-system-axioms str
 open deductive-system-structure str public
 open deductive-system-axioms str ax public

module deductive-system-as-sum {𝓤 𝓥 : Universe} where
 to-sum
  : deductive-system 𝓤 𝓥
  → Σ str ꞉ deductive-system-structure 𝓤 𝓥 , deductive-system-axioms str
 to-sum 𝓓 = let open deductive-system 𝓓 in str , ax

 from-sum
  : (Σ str ꞉ deductive-system-structure 𝓤 𝓥 , deductive-system-axioms str)
  → deductive-system 𝓤 𝓥
 from-sum 𝓓 = make (pr₁ 𝓓) (pr₂ 𝓓)

 to-sum-is-equiv : is-equiv to-sum
 pr₁ (pr₁ to-sum-is-equiv) = from-sum
 pr₂ (pr₁ to-sum-is-equiv) _ = refl
 pr₁ (pr₂ to-sum-is-equiv) = from-sum
 pr₂ (pr₂ to-sum-is-equiv) _ = refl

 equiv
  : deductive-system 𝓤 𝓥
  ≃ (Σ str ꞉ deductive-system-structure 𝓤 𝓥 , deductive-system-axioms str)
 equiv = to-sum , to-sum-is-equiv
\end{code}

We now begin to state the associativity properties that hold of certain
morphisms. A morphism `f` is "thunkable" when precomposing by it is associative
in the sense that `f; (g; h) ＝ (f; g); h`; such morphisms correspond to
"values" in programming languages. On the other hand, a morphism `f` is "linear"
when postcomposing by it is associative; such morphisms correspond to "stacks" in
programming languages.

\begin{code}
module ⊢-properties (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓

 module _ {A B : ob} (f : A ⊢ B) where
  is-thunkable : 𝓤 ⊔ 𝓥 ̇
  is-thunkable =
   (C D : ob) (g : B ⊢ C) (h : C ⊢ D)
   → cut (cut f g) h ＝ cut f (cut g h)

  is-linear : 𝓤 ⊔ 𝓥 ̇
  is-linear =
   (U V : ob) (g : V ⊢ A) (h : U ⊢ V)
   → cut (cut h g) f ＝ (cut h (cut g f))
\end{code}

Just as in a category, we can speak of a map being inverse to another map. Note
however that without additional assumptions, inverses do not seem to be unique.

\begin{code}
  is-inverse : (g : B ⊢ A) → 𝓥 ̇
  is-inverse g =
   (cut f g ＝ idn _)
   × (cut g f ＝ idn _)

  being-inverse-is-prop
   : {g : B ⊢ A}
   → is-prop (is-inverse g)
  being-inverse-is-prop =
   ×-is-prop
    (⊢-is-set _ _)
    (⊢-is-set _ _)


\end{code}

Because the identity laws hold, identity morphisms are both linear and
thunkable. Furthermore, the composition of (linear, thunkable) morphisms is
(linear, thunkable).

\begin{code}
 module _ (A : ob) where
  abstract
   idn-linear : is-linear (idn A)
   idn-linear U V g h =
    cut (cut h g) (idn A) ＝⟨ idn-R _ _ _ ⟩
    cut h g ＝⟨ ap (cut h) (idn-R _ _ _ ⁻¹) ⟩
    cut h (cut g (idn A)) ∎

   idn-thunkable : is-thunkable (idn A)
   idn-thunkable C D g h =
     cut (cut (idn A) g) h ＝⟨ ap (λ x → cut x h) (idn-L A C g) ⟩
     cut g h ＝⟨ idn-L A D (cut g h) ⁻¹ ⟩
     cut (idn A) (cut g h) ∎

 module _ {A B C : ob} (f : A ⊢ B) (g : B ⊢ C) where
  abstract
   cut-linear
    : is-linear f
    → is-linear g
    → is-linear (cut f g)
   cut-linear f-lin g-lin U V h k =
    cut (cut k h) (cut f g) ＝⟨ g-lin U A f (cut k h) ⁻¹ ⟩
    cut (cut (cut k h) f) g ＝⟨ ap (λ x → cut x g) (f-lin U V h k) ⟩
    cut (cut k (cut h f)) g ＝⟨ g-lin U V (cut h f) k ⟩
    cut k (cut (cut h f) g) ＝⟨ ap (cut k) (g-lin V A f h) ⟩
    cut k (cut h (cut f g)) ∎

   cut-thunkable
    : is-thunkable f
    → is-thunkable g
    → is-thunkable (cut f g)
   cut-thunkable f-th g-th D E h k =
    cut (cut (cut f g) h) k ＝⟨ ap (λ x → cut x k) (f-th C D g h) ⟩
    cut (cut f (cut g h)) k ＝⟨ f-th D E (cut g h) k ⟩
    cut f (cut (cut g h) k) ＝⟨ ap (cut f) (g-th D E h k) ⟩
    cut f (cut g (cut h k)) ＝⟨ f-th C E g (cut h k) ⁻¹ ⟩
    cut (cut f g) (cut h k) ∎

 module _ {A B} {f : A ⊢ B} where
  being-thunkable-is-prop : is-prop (is-thunkable f)
  being-thunkable-is-prop =
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   ⊢-is-set _ _

  being-linear-is-prop : is-prop (is-linear f)
  being-linear-is-prop =
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   ⊢-is-set _ _
\end{code}

Although inverses need not in general be unique, an inverse *is* unique if it is
either linear or thunkable.

\begin{code}
 module _ {A B} {f : A ⊢ B} {g g'} (fg : is-inverse f g) (fg' : is-inverse f g') where
  linear-inverse-is-unique
   : is-linear g
   → g' ＝ g
  linear-inverse-is-unique g-lin =
   g' ＝⟨ idn-R B A _ ⁻¹ ⟩
   cut _ (idn _) ＝⟨ ap (cut _) (pr₁ fg ⁻¹) ⟩
   cut _ (cut f _) ＝⟨ g-lin B A f _ ⁻¹ ⟩
   cut (cut _ f) _ ＝⟨ ap (λ x → cut x g) (pr₂ fg') ⟩
   cut (idn _) g ＝⟨ idn-L B A g ⟩
   g ∎

  thunkable-inverse-is-unique
   : is-thunkable g
   → g' ＝ g
  thunkable-inverse-is-unique g-th =
   g' ＝⟨ idn-L B A g' ⁻¹ ⟩
   cut (idn _) g' ＝⟨ ap (λ x → cut x g') (pr₂ fg ⁻¹) ⟩
   cut (cut g f) g' ＝⟨ g-th B A f g' ⟩
   cut g (cut f g') ＝⟨ ap (cut g) (pr₁ fg') ⟩
   cut g (idn _) ＝⟨ idn-R B A g ⟩
   g ∎
\end{code}

An object `A` in a deductive system such that every morphism out of `A` is
linear is called "positive"; conversely, when every morphism into `A` is
thunkable we call `A` "negative". This is an extensional / objective account of
the syntactical phenomenon of polarity in structural proof theory.

\begin{code}
module polarities (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓
 open ⊢-properties 𝓓

 module _ (A : ob) where
  is-positive : 𝓤 ⊔ 𝓥 ̇
  is-positive =
   (B : ob) (f : A ⊢ B)
   → is-linear f

  is-negative : 𝓤 ⊔ 𝓥 ̇
  is-negative =
   (B : ob) (f : B ⊢ A)
   → is-thunkable f

 module _ {A} where
  being-positive-is-prop : is-prop (is-positive A)
  being-positive-is-prop =
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   being-linear-is-prop

  being-negative-is-prop : is-prop (is-negative A)
  being-negative-is-prop =
   Π-is-prop fe λ _ →
   Π-is-prop fe λ _ →
   being-thunkable-is-prop

\end{code}
