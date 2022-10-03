--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

Begun on July 2022. Reworked starting on September 2022.
--------------------------------------------------------------------------------

Basic facts about 2-groups, or categorical groups, or gr-categories, in another parlance.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Groupoids

module 2Groups.Type where

\end{code}

Underlying type of the structure

\begin{code}

open import Groups.Type using (⟨_⟩)

\end{code}

The mathematical structure of a 2-Group, or categorical group. The
main structure is of course an operation X → X → X as usual, but since
in categorical algebra the underlying carrier is a category, the
structure also affects morphisms. The most important property of the
structure on morphisms is functoriality, which in categorical algebra
is a reflection of the fact that the operation is overall a functor.

In our case, there should be a companion structure defined on identity
types.  More precisely, given a specific tensor structure on X, we
postulate there exists a lift to the identity types, and we require
that the companion structure satisfy an interchange law with respect
to the underlying structure.

\begin{code}

⊗-structure : 𝓤 ̇ → 𝓤 ̇
⊗-structure X = X → X → X

⊗-structure-Id : (X : 𝓤 ̇) → ⊗-structure X → 𝓤 ̇
⊗-structure-Id X _●_ = ∀ {x x' y y'} → x ＝ x' → y ＝ y'
                      → x ● y ＝ x' ● y'

⊗-structure-Id-interchange : (X : 𝓤 ̇) → (_●_ : ⊗-structure X) → ⊗-structure-Id X _●_ → 𝓤 ̇
⊗-structure-Id-interchange X _●_ _✶_ = {x x' x'' y y' y'' : X}
                                      → (p : x ＝ x') (p' : x' ＝ x'')
                                      → (q : y ＝ y') (q' : y' ＝ y'')
                                      → ((p ✶ q) ∙ (p' ✶ q')) ＝ ((p ∙ p') ✶ (q ∙ q'))

\end{code}

It turns out a lifted structure can be obtained from a given
⊗-structure using ap. In fact, this can be done in several ways.

\begin{code}


⊗-structure-ap-left : {X : 𝓤 ̇ } → (_●_ : ⊗-structure X)
                    → {x y : X} → (p : x ＝ y) → (z : X)
                    → x ● z ＝ y ● z
⊗-structure-ap-left _●_ p z = ap (λ v → v ● z) p

⊗-structure-ap-right : {X : 𝓤 ̇} → (_●_ : ⊗-structure X)
                     → (z : X) → {x y : X} → (p : x ＝ y)
                     →  z ● x ＝ z ● y
⊗-structure-ap-right _●_ z p = ap (λ v → z ● v) p

⊗-structure-to-Id : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                   → ⊗-structure-Id X _●_
⊗-structure-to-Id X _●_ {_} {x'} {y} p q =
                    (⊗-structure-ap-left _●_ p y) ∙ (⊗-structure-ap-right _●_ x' q) 

⊗-structure-to-Id' : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                    → ⊗-structure-Id X _●_
⊗-structure-to-Id' X _●_ {x} {x'} {y} {y'} p q =
                   (⊗-structure-ap-right _●_ x q) ∙ (⊗-structure-ap-left _●_ p y')

⊗-structure-to-Id₂ : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                    → ⊗-structure-Id X _●_
⊗-structure-to-Id₂ X _●_ = ap₂ _●_


\end{code}

The lifts are compatible. We do this by first expressing the
compatibility via a type, and then, second, showing that this type is
inhabited.

\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X) where

  ⊗-structure-has-compatible-lifts : 𝓤 ̇
  ⊗-structure-has-compatible-lifts = {x x' y y' : X}
                                    → (p : x ＝ x')
                                    → (q : y ＝ y')
                                    → ⊗-structure-to-Id X _●_ {_} {x'} {y} p q 
                                       ＝ ⊗-structure-to-Id' X _●_ {x} {x'} {y} {y'} p q

  ⊗-structure-lifts-compatible : ⊗-structure-has-compatible-lifts
  ⊗-structure-lifts-compatible {x} {.x} {y} {y'} refl q = 
                               ⊗-structure-to-Id X _●_ refl q        ＝⟨ refl ⟩
                               refl ∙ (⊗-structure-ap-right _●_ x q) ＝⟨ refl-left-neutral ⟩
                               ⊗-structure-ap-right _●_ x q          ＝⟨ refl ⁻¹ ⟩
                               (⊗-structure-ap-right _●_ x q) ∙ refl ＝⟨ refl ⟩
                               ⊗-structure-to-Id' X _●_ refl q ∎

  ⊗-structure-has-compatible-lifts₂ : 𝓤 ̇
  ⊗-structure-has-compatible-lifts₂ = {x x' y y' : X}
                                    → (p : x ＝ x')
                                    → (q : y ＝ y')
                                    → ⊗-structure-to-Id₂ X _●_ p q ＝
                                         ⊗-structure-to-Id X _●_ p q

  ⊗-structure-lifts-compatible₂ : ⊗-structure-has-compatible-lifts₂
  ⊗-structure-lifts-compatible₂ refl refl = refl

\end{code}

The interchange law holds for the lifts we have introduced. We prove it for one of them.

\begin{code}

  ⊗-structure-to-Id-has-interchange : ⊗-structure-Id-interchange X _●_ (⊗-structure-to-Id X _●_)
  ⊗-structure-to-Id-has-interchange {x} {x'} {.x'} {y} {.y} {y''} p refl refl q' =
       ⊗-structure-to-Id X _●_ p refl ∙ ⊗-structure-to-Id X _●_ refl q'         ＝⟨ refl ⟩
       ⊗-structure-to-Id X _●_ p refl ∙ (refl ∙ ⊗-structure-ap-right _●_ x' q') ＝⟨ refl ⟩
       (⊗-structure-ap-left _●_ p y)  ∙ (refl ∙ ⊗-structure-ap-right _●_ x' q') ＝⟨ i ⟩
       (⊗-structure-ap-left _●_ p y)  ∙ (⊗-structure-ap-right _●_ x' q')        ＝⟨ refl ⟩
       ⊗-structure-to-Id X _●_ p  q'                                             ＝⟨ refl ⟩
       ⊗-structure-to-Id X _●_ (p ∙ refl) q'                                     ＝⟨ ii ⟩
       ⊗-structure-to-Id X _●_ (p ∙ refl) (refl ∙ q') ∎
         where
           i = ap (λ v → (⊗-structure-ap-left _●_ p y) ∙ v) (refl-left-neutral {p = ⊗-structure-ap-right _●_ x' q'})
           ii = ap (⊗-structure-to-Id X _●_ (p ∙ refl)) (refl-left-neutral {p = q'}) ⁻¹ 
         
\end{code}

If the operation is associative and it admits a neutral element, we
consider the following two axioms. One is the pentagon, that is the
equality

((xy)z)t → (x(yz))t → x((yz)t) → x(y(zt)) ＝ ((xy)z)t → (xy)(zt) → x(y(zt))

The other, which holds in the presence of a neutral term I is that

(xI)y → x(Iy) → xy ＝ (xI)y → xy

\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X) where

  ⊗-assoc-pentagon : associative _●_ → 𝓤 ̇
  ⊗-assoc-pentagon α = ∀ {x y z t} → p x y z t ＝ q x y z t
    where
      p q : (x y z t : X) → ((x ● y) ● z) ● t ＝  x ● (y ● (z ● t))
      p x y z t = ((x ● y) ● z) ● t ＝⟨ ⊗-structure-ap-left _●_ (α x y z) t ⟩
                  (x ● (y ● z)) ● t ＝⟨ α _ _ _ ⟩
                  x ● ((y ● z) ● t) ＝⟨ ⊗-structure-ap-right _●_ x (α y z t) ⟩
                  x ● (y ● (z ● t)) ∎
      q x y z t = ((x ● y) ● z) ● t ＝⟨ α _ _ _ ⟩
                  (x ● y) ● (z ● t) ＝⟨ α _ _ _ ⟩
                  x ● (y ● (z ● t)) ∎

  ⊗-assoc-neutral : associative _●_
                  → (e : X) → left-neutral e _●_ → right-neutral e _●_
                  → 𝓤 ̇ 
  ⊗-assoc-neutral α e l r = ∀ {x y} → p x y ＝ q x y 
    where
      p q : (x y : X) → (x ● e) ● y ＝ x ● y
      p x y = (x ● e) ● y ＝⟨ α _ _ _ ⟩
              x ● (e ● y) ＝⟨ ⊗-structure-ap-right _●_ x (l y) ⟩
              x ● y ∎
      q x y = (x ● e) ● y ＝⟨ ⊗-structure-ap-left _●_ (r x) y ⟩
              x ● y ∎             

\end{code}

Inveritibility of the structure operation (duality, in another
parlance) stipulates that for each object X there are two "duality"
morphisms

ε : x  xᵛ → I
η : I → xᵛ x

corresponding to the usual notion of "inverse" elements, such that the
compositions

x → x I → x (xᵛ x) → (x xᵛ) x → I x → x

xᵛ → I xᵛ → (xᵛ x) xᵛ → xᵛ (x xᵛ) → xᵛ I → xᵛ

are the identity, that is, refl in our case.

\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X) where

  ⊗-inv-structure : (e : X)
                   → left-neutral e _●_
                   → right-neutral e _●_
                   → 𝓤 ̇
  ⊗-inv-structure e l r = (x : X) → Σ xᵛ ꞉ X , (x ● xᵛ ＝ e) × (e ＝ xᵛ ● x)

  ⊗-inv-compatible : associative _●_
                   → (e : X) (l : left-neutral e _●_) (r : right-neutral e _●_)
                   → ⊗-inv-structure e l r
                   → 𝓤 ̇
  ⊗-inv-compatible α e l r inv = (x : X) → (p x ＝ refl) × (q x ＝ refl)
    where
      p : (x : X) → x ＝ x
      p x = x            ＝⟨ (r x) ⁻¹ ⟩
            x ● e        ＝⟨ ⊗-structure-ap-right _●_ x (pr₂ (pr₂ (inv x)))  ⟩
            x ● (xᵛ ● x) ＝⟨ (α _ _ _) ⁻¹ ⟩
            (x ● xᵛ) ● x ＝⟨ ⊗-structure-ap-left _●_ (pr₁ (pr₂ (inv x))) x ⟩
            e ● x        ＝⟨ l x ⟩
            x ∎
            where
              xᵛ : X
              xᵛ = pr₁ (inv x)
      q : (x : X) → pr₁ (inv x) ＝ pr₁ (inv x)
      q x = xᵛ            ＝⟨ (l xᵛ) ⁻¹ ⟩
            e ● xᵛ        ＝⟨ ⊗-structure-ap-left _●_ (pr₂ (pr₂ (inv x))) xᵛ ⟩
            (xᵛ ● x) ● xᵛ ＝⟨ α _ _ _ ⟩
            xᵛ ● (x ● xᵛ) ＝⟨ ⊗-structure-ap-right _●_ xᵛ (pr₁ (pr₂ (inv x))) ⟩
            xᵛ ● e        ＝⟨ r xᵛ ⟩
            xᵛ ∎
            where
              xᵛ : X
              xᵛ = pr₁ (inv x)
\end{code}

Given a type X, have a structure consisting of a multiplication map
_●_ : X → X → X and a unit e : X on X. We collect its axioms in a
record.

\begin{code}

record monoidal-grpd-axioms (X : 𝓤 ̇)
                            (_●_ : ⊗-structure X)
                            (e : X) : 𝓤 ̇
                              where
  field
    is-grpd : is-groupoid X
    is-assoc : associative _●_
    has-pentagon : ⊗-assoc-pentagon X _●_ is-assoc

    unit-left : left-neutral e _●_
    unit-right : right-neutral e _●_

    left-right : unit-left e ＝ unit-right e
    
    has-assoc-neutral : ⊗-assoc-neutral X _●_
                                        is-assoc
                                        e unit-left unit-right

-- open monoidal-grpd-axioms public

\end{code}

From another point of view a "monoidal groupoid structure" on the type
X can be viewed as the the data (_●_ , e) together with the axioms.

\begin{code}

record Monoidal-grpd-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  field
    _⊗_ : ⊗-structure X
    e : X
    is-monoidal-grpd : monoidal-grpd-axioms X _⊗_ e

  open monoidal-grpd-axioms is-monoidal-grpd public -- do I need this?

\end{code}


The type of monoidal groupoids.

\begin{code}

Monoidal-Grpd : (𝓤 : Universe) → 𝓤 ⁺ ̇
Monoidal-Grpd 𝓤 = Σ X ꞉ 𝓤 ̇ , Monoidal-grpd-structure X

\end{code}

Synonyms and References: the following terms all denote the same
thing, namely a monoidal group-like groupoid.

1. Categorical Group: abbreviated as Cat-Group

   1. Joyal and Street
   1. Brown, Higgins, Porter
   1. Bullejos, Carrasco, Cegarra, Garzón, del Río, …

1. 2-Group

   1. Baez, Baez-Dolan, and followers

1. Gr-Category (= gr-catégorie)

   1. The french Algebraic Geometry school: Breen, Grothendieck, Sinh

The "group-like" refers to the inverse structure in the sense
specified above, that every term x : X possesses a rigid dual xᵛ.

Thus a categorical group, or 2-group, or gr-category is a type
equipped with a monoidal groupoid structure satisfying group-like
axioms.

\begin{code}

record gr-like-axioms (X : 𝓤 ̇)
                      (m : Monoidal-grpd-structure X) : 𝓤 ̇
                        where
  open Monoidal-grpd-structure 

  field
    ⊗-inv : ⊗-inv-structure X (m ._⊗_)
            (m .e) (m .unit-left) (m .unit-right)

    ⊗-inv-axioms : ⊗-inv-compatible X (m ._⊗_) (m .is-assoc)
                   (m .e) (m .unit-left) (m .unit-right) ⊗-inv


record gr-like-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  field
    m : Monoidal-grpd-structure X
    gr : gr-like-axioms X m

  open Monoidal-grpd-structure m public
  open gr-like-axioms gr public

group-like-structure = gr-like-structure -- for convenience


2-Group Cat-Group Gr-Cat : (𝓤 : Universe) → 𝓤 ⁺ ̇
2-Group 𝓤 = Σ X ꞉ 𝓤 ̇ , gr-like-structure X
Cat-Group = 2-Group
Gr-Cat = 2-Group

\end{code}

Forgetting the group-like structure gives a monoidal groupoid

\begin{code}

gr-like-structure-is-monoidal-grpd-structure : (X : 𝓤 ̇)
                                             → gr-like-structure X
                                             → Monoidal-grpd-structure X
gr-like-structure-is-monoidal-grpd-structure X s = s .gr-like-structure.m

2-groups-are-monoidal-groupoids : 2-Group 𝓤 → Monoidal-Grpd 𝓤
2-groups-are-monoidal-groupoids (X , s) = X , gr-like-structure-is-monoidal-grpd-structure X s


\end{code}
