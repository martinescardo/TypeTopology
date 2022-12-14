--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

Begun on July 2022. Reworked starting on September 2022.
--------------------------------------------------------------------------------

Basic facts about 2-groups, or categorical groups, or gr-categories,
in another parlance.

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
⊗-structure using ap. In fact, this can be done in several ways, but
usign ap₂ is the preferred one, because it simultaneously lifts to
both sides of the ⊗-structure.

\begin{code}

⊗-structure-to-Id₂ : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                    → ⊗-structure-Id X _●_
⊗-structure-to-Id₂ X _●_ = ap₂ _●_

⊗-structure-to-Id₂-∙ : {X : 𝓤 ̇} → (_●_ : ⊗-structure X)
                     → {x x' x'' y y' y'' : X}
                     → (p : x ＝ x') (p' : x' ＝ x'')
                     → (q : y ＝ y') (q' : y' ＝ y'')
                     → (⊗-structure-to-Id₂ X _●_ p q) ∙ (⊗-structure-to-Id₂ X _●_ p' q')
                       ＝ ⊗-structure-to-Id₂ X _●_ (p ∙ p') (q ∙ q')
⊗-structure-to-Id₂-∙ _●_ refl refl refl refl = refl

\end{code}


Variants of the lifts. These encapsulate the idea that the ⊗-structure
at the level of identity paths can be decomposed by inserting identity
maps, as explained by the following diagram.

% https://q.uiver.app/?q=WzAsNCxbMCwwLCJ4XFxvdGltZXMgeSJdLFsyLDAsIngnXFxvdGltZXMgeSJdLFsyLDIsIngnXFxvdGltZXMgeSciXSxbMCwyLCJ4XFxvdGltZXMgeSciXSxbMCwyLCJmIFxcb3RpbWVzIGciLDFdLFswLDEsImZcXG90aW1lcyBpZF95Il0sWzEsMiwiaWRfe3gnfVxcb3RpbWVzIGciLDAseyJvZmZzZXQiOi0xfV0sWzAsMywiaWRfeFxcb3RpbWVzIGciLDJdLFszLDIsImZcXG90aW1lcyBpZF97eSd9IiwyXV0=
\[\begin{tikzcd}
	{x\otimes y} && {x'\otimes y} \\
	\\
	{x\otimes y'} && {x'\otimes y'}
	\arrow["{f \otimes g}"{description}, from=1-1, to=3-3]
	\arrow["{f\otimes id_y}", from=1-1, to=1-3]
	\arrow["{id_{x'}\otimes g}", shift left=1, from=1-3, to=3-3]
	\arrow["{id_x\otimes g}"', from=1-1, to=3-1]
	\arrow["{f\otimes id_{y'}}"', from=3-1, to=3-3]
\end{tikzcd}\]

\begin{code}

⊗-structure-ap-left : {X : 𝓤 ̇ } → (_●_ : ⊗-structure X)
                    → {x y : X} → (p : x ＝ y) → (z : X)
                    → x ● z ＝ y ● z
⊗-structure-ap-left _●_ p z = ap (λ v → v ● z) p


⊗-structure-ap-left-∙ : {X : 𝓤 ̇ } → (_●_ : ⊗-structure X)
                      → {x y z : X} (p : x ＝ y) (q : y ＝ z) (t : X)
                      → (⊗-structure-ap-left _●_ p t) ∙ (⊗-structure-ap-left _●_ q t)
                        ＝ ⊗-structure-ap-left _●_ (p ∙ q) t
⊗-structure-ap-left-∙ _●_ p refl t = refl

⊗-structure-ap-right : {X : 𝓤 ̇} → (_●_ : ⊗-structure X)
                     → (z : X) → {x y : X} → (p : x ＝ y)
                     →  z ● x ＝ z ● y
⊗-structure-ap-right _●_ z p = ap (λ v → z ● v) p

⊗-structure-ap-right-∙ : {X : 𝓤 ̇} → (_●_ : ⊗-structure X)
                       → (t : X) {x y z : X} (p : x ＝ y) (q : y ＝ z)
                       → (⊗-structure-ap-right _●_ t p) ∙ (⊗-structure-ap-right _●_ t q)
                         ＝ ⊗-structure-ap-right _●_ t (p ∙ q)
⊗-structure-ap-right-∙ _●_ t p refl = refl

⊗-structure-to-Id : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                   → ⊗-structure-Id X _●_
⊗-structure-to-Id X _●_ {_} {x'} {y} p q =
                    (⊗-structure-ap-left _●_ p y) ∙ (⊗-structure-ap-right _●_ x' q) 

⊗-structure-to-Id' : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                    → ⊗-structure-Id X _●_
⊗-structure-to-Id' X _●_ {x} {x'} {y} {y'} p q =
                   (⊗-structure-ap-right _●_ x q) ∙ (⊗-structure-ap-left _●_ p y')


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

The interchange law holds for the lifts we have introduced. For
⊗-structure-to-Id₂ this is immediate and it is just the compatibility
with path composition.

\begin{code}

  ⊗-structure-to-Id₂-has-interchange : ⊗-structure-Id-interchange X _●_ (⊗-structure-to-Id₂ X _●_)
  ⊗-structure-to-Id₂-has-interchange = ⊗-structure-to-Id₂-∙ _●_

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

We need to consider the following axioms for the associativity. One is
the pentagon, that is the equality

((xy)z)t → (x(yz))t → x((yz)t) → x(y(zt)) ＝ ((xy)z)t → (xy)(zt) → x(y(zt))

It is also supposed that the associativity term behaves in a
compatible way relative to identity types, that is

(xy)x → x(yz) → x'(y'z') ＝ (xy)x → (x'y')z' → x'(y'z')

\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X) where

  ⊗-assoc-pentagon : associative _●_ → 𝓤 ̇
  ⊗-assoc-pentagon α = ∀ {x y z t} →
                       ( ((x ● y) ● z) ● t ＝⟨ ⊗-structure-to-Id₂ X _●_ (α x y z) refl ⟩
                         (x ● (y ● z)) ● t ＝⟨ α x (y ● z) t ⟩ 
                         x ● ((y ● z) ● t) ＝⟨ ⊗-structure-to-Id₂ X _●_ refl (α y z t) ⟩
                         x ● (y ● (z ● t)) ∎ )
                        ＝
                       ( ((x ● y) ● z) ● t ＝⟨ α _ _ _ ⟩
                         (x ● y) ● (z ● t) ＝⟨ α _ _ _ ⟩
                         x ● (y ● (z ● t)) ∎ )

  ⊗-assoc-compatible-with-＝ : associative _●_ → 𝓤 ̇
  ⊗-assoc-compatible-with-＝ α =
    ∀ {x y z x' y' z'}
    → (p : x ＝ x')
    → (q : y ＝ y')
    → (r : z ＝ z')
    → ( (x ● y) ● z   ＝⟨ α x y z ⟩
        x ● (y ● z)   ＝⟨ ⊗-structure-to-Id₂ X _●_ p (⊗-structure-to-Id₂ X _●_ q r) ⟩
        x' ● (y' ● z') ∎ )
       ＝
      ( (x ● y) ● z    ＝⟨ ⊗-structure-to-Id₂ X _●_ (⊗-structure-to-Id₂ X _●_ p q) r ⟩
        (x' ● y') ● z' ＝⟨ α x' y' z' ⟩
        x' ● (y' ● z') ∎ )

\end{code}

If there is a neutral element e, we require the following axioms.

1. Compatibility with the associativity

   (ex)y → e(xy) → xy ＝ (ex)y → xy

   (xe)y → x(ey) → xy ＝ (xe)y → xy

   (xy)e → x(ye) → xy ＝ (xy)e → xy

2. Compatibility with the identity types

   ex → ex' → x' ＝ ex → x → x'

   xe → x'e → x' ＝ xe → x → x'


\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X) where

  ⊗-assoc-neutral-l : associative _●_
                    → (e : X) → left-neutral e _●_ → right-neutral e _●_
                    → 𝓤 ̇
  ⊗-assoc-neutral-l α e l r = ∀ { x y } →
             ((e ● x) ● y ＝⟨ α e x y ⟩
              e ● (x ● y) ＝⟨ l (x ● y) ⟩
              x ● y       ∎)
              ＝
             ((e ● x) ● y ＝⟨ ⊗-structure-to-Id₂ X _●_ (l x) refl ⟩
              x ● y       ∎)

  ⊗-assoc-neutral : associative _●_
                  → (e : X) → left-neutral e _●_ → right-neutral e _●_
                  → 𝓤 ̇
  ⊗-assoc-neutral α e l r = ∀ {x y} →
              ((x ● e) ● y ＝⟨ α _ _ _ ⟩
               x ● (e ● y) ＝⟨ ⊗-structure-to-Id₂ X _●_ refl (l y) ⟩
               x ● y       ∎)
               ＝
              ((x ● e) ● y ＝⟨ ⊗-structure-to-Id₂ X _●_ (r x) refl ⟩
               x ● y       ∎)

  ⊗-assoc-neutral-r : associative _●_
                    → (e : X) → left-neutral e _●_ → right-neutral e _●_
                    → 𝓤 ̇
  ⊗-assoc-neutral-r α e l r = ∀ {x y} →
                    ((x ● y) ● e ＝⟨ α x y e ⟩
                      x ● (y ● e) ＝⟨ ⊗-structure-to-Id₂ X _●_ refl (r y) ⟩
                      x ● y       ∎)
                      ＝
                    ((x ● y) ● e ＝⟨ r (x ● y) ⟩
                      x ● y       ∎)

  left-neutral-compatible-with-＝ : (e : X)
                                  → left-neutral e _●_
                                  → right-neutral e _●_
                                  → 𝓤 ̇
  left-neutral-compatible-with-＝ e l r = ∀ {x x'} → (p : x ＝ x')
                                          → (e ● x  ＝⟨ ⊗-structure-to-Id₂ X _●_ refl p ⟩
                                             e ● x' ＝⟨ l x' ⟩
                                             x'     ∎ ) ＝ (l x) ∙ p

  right-neutral-compatible-with-＝ : (e : X)
                                   → left-neutral e _●_
                                   → right-neutral e _●_
                                   → 𝓤 ̇
  right-neutral-compatible-with-＝ e l r = ∀ {x x'} → (p : x ＝ x')
                                           → ( x ● e   ＝⟨ ⊗-structure-to-Id₂ X _●_ p refl ⟩ 
                                               x' ● e  ＝⟨ r x' ⟩
                                               x'      ∎ ) ＝ (r x) ∙ p


  left-right-neutral-compatibility : (e : X)
                                   → (l : left-neutral e _●_)
                                   → (r : right-neutral e _●_)
                                   → 𝓤 ̇
  left-right-neutral-compatibility e l r = l e ＝ r e
  
\end{code}

It is known that the axioms are not all independent. In particular,
`⊗-assoc-neutral-l`, `⊗-assoc-neutral-r`,
`left-right-neutral-compatibility` follow from the rest. The classical
argument, given below, is in:

1. Joyal, Street: Braided Tensor Categories.
2. Mac Lane: Categories for the Working Mathematician.

\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X)
         (α : associative _●_)
         (π : ⊗-assoc-pentagon X _●_ α)
         (φₐₛ : ⊗-assoc-compatible-with-＝ X _●_ α)
         (e : X) (𝓵 : left-neutral e _●_) (𝓻 : right-neutral e _●_)
         (φᵢ : ⊗-assoc-neutral X _●_ α e 𝓵 𝓻)
         (φₗ : left-neutral-compatible-with-＝ X _●_ e 𝓵 𝓻)
         (φᵣ : right-neutral-compatible-with-＝ X _●_ e 𝓵 𝓻)
           where

  private
    _✶_ = ⊗-structure-to-Id₂ X _●_ 

\end{code}

This shows how to get ⊗-assoc-neutral-l from ⊗-assoc-neutral plus the naturality axioms.

The two diagrams analyzed in the code below are:

% https://q.uiver.app/?q=WzAsNyxbMCwwLCIoKGUgZSl4KXkiXSxbNCwwLCIoZShleCkpeSJdLFsyLDEsIihleCl5Il0sWzIsMywiZSh4eSkiXSxbNCwyLCJlKChleCl5KSJdLFs0LDQsImUoZSh4eSkpIl0sWzAsNCwiKGVlKSh4eSkiXSxbMCwxLCJwIl0sWzEsMiwidCciLDFdLFsyLDMsInEnIl0sWzEsNCwicSJdLFs0LDMsInQiLDFdLFs0LDUsInIiXSxbNSwzLCJzIiwxXSxbNiw1LCJ2Il0sWzAsNiwidSIsMV0sWzAsMiwidyciLDFdLFs2LDMsInciLDFdLFsxMSwxMywiPyIsMSx7Im9mZnNldCI6LTIsInNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sImxldmVsIjoxLCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJub25lIn0sImhlYWQiOnsibmFtZSI6Im5vbmUifX19XV0=
\[\begin{tikzcd}
	{((e e)x)y} &&&& {(e(ex))y} \\
	&& {(ex)y} \\
	&&&& {e((ex)y)} \\
	&& {e(xy)} \\
	{(ee)(xy)} &&&& {e(e(xy))}
	\arrow["p", from=1-1, to=1-5]
	\arrow["{t'}"{description}, from=1-5, to=2-3]
	\arrow["{q'}", from=2-3, to=4-3]
	\arrow["q", from=1-5, to=3-5]
	\arrow[""{name=0, anchor=center, inner sep=0}, "t"{description}, from=3-5, to=4-3]
	\arrow["r", from=3-5, to=5-5]
	\arrow[""{name=1, anchor=center, inner sep=0}, "s"{description}, from=5-5, to=4-3]
	\arrow["v", from=5-1, to=5-5]
	\arrow["u"{description}, from=1-1, to=5-1]
	\arrow["{w'}"{description}, from=1-1, to=2-3]
	\arrow["w"{description}, from=5-1, to=4-3]
	\arrow["{?}"{description}, shift left=2, draw=none, from=0, to=1]
\end{tikzcd}\]

and:

% https://q.uiver.app/?q=WzAsNixbMCwyLCJlKHh5KSJdLFsxLDIsInh5Il0sWzIsMSwiKGV4KXkiXSxbMiwzLCJlKHh5KSJdLFszLDAsImUoKGV4KXkpIl0sWzMsNCwiZShlKHh5KSkiXSxbMCwxXSxbMiwxLCJ0XzEiLDJdLFsyLDMsInJfMSJdLFszLDEsInNfMSJdLFs0LDJdLFs0LDAsInQiLDEseyJjdXJ2ZSI6M31dLFs0LDUsInIiXSxbNSwzXSxbNSwwLCJzIiwxLHsiY3VydmUiOi0zfV1d
\[\begin{tikzcd}
	&&& {e((ex)y)} \\
	&& {(ex)y} \\
	{e(xy)} & xy \\
	&& {e(xy)} \\
	&&& {e(e(xy))}
	\arrow[from=3-1, to=3-2]
	\arrow["{t_1}"', from=2-3, to=3-2]
	\arrow["{r_1}", from=2-3, to=4-3]
	\arrow["{s_1}", from=4-3, to=3-2]
	\arrow[from=1-4, to=2-3]
	\arrow["t"{description}, curve={height=18pt}, from=1-4, to=3-1]
	\arrow["r", from=1-4, to=5-4]
	\arrow[from=5-4, to=4-3]
	\arrow["s"{description}, curve={height=-18pt}, from=5-4, to=3-1]
\end{tikzcd}\]

\begin{code}
  have-⊗-assoc-neutral-l : ⊗-assoc-neutral-l X _●_ α e 𝓵 𝓻
  have-⊗-assoc-neutral-l {x} {y} = l-4
    where
      p : ((e ● e) ● x) ● y ＝ (e ● (e ● x)) ● y
      p = (α e e x) ✶ refl

      q : (e ● (e ● x)) ● y ＝ e ● ((e ● x) ● y)
      q = α e (e ● x) y

      r : e ● ((e ● x) ● y) ＝ e ● (e ● (x ● y))
      r = refl ✶ (α e x y)

      s : e ● (e ● (x ● y)) ＝ e ● (x ● y)
      s = refl ✶ 𝓵 (x ● y)

      t : e ● ((e ● x) ● y) ＝ e ● (x ● y)
      t = refl ✶ ((𝓵 x) ✶ refl)

      u : ((e ● e) ● x) ● y ＝ (e ● e) ● (x ● y)
      u = α (e ● e) x y

      v : (e ● e) ● (x ● y) ＝ e ● (e ● (x ● y))
      v = α e e (x ● y)

      w : (e ● e) ● (x ● y) ＝ e ● (x ● y)
      w = (𝓻 e) ✶ refl

      w' : ((e ● e) ● x) ● y ＝ (e ● x) ● y
      w' = ((𝓻 e) ✶ refl) ✶ refl

      t' : (e ● (e ● x)) ● y ＝ (e ● x) ● y
      t' = (refl ✶ (𝓵 x)) ✶ refl

      γ : ((e ● e) ● x) ● y ＝ e ● (x ● y)
      γ = ((e ● e) ● x) ● y ＝⟨ p ⟩
          (e ● (e ● x)) ● y ＝⟨ q ⟩
          e ● ((e ● x) ● y) ＝⟨ r ⟩
          e ● (e ● (x ● y)) ＝⟨ s ⟩
          e ● (x ● y)       ∎

      δ : ((e ● e) ● x) ● y ＝ e ● (x ● y)
      δ = ((e ● e) ● x) ● y ＝⟨ p ⟩
          (e ● (e ● x)) ● y ＝⟨ q ⟩
          e ● ((e ● x) ● y) ＝⟨ t ⟩
          e ● (x ● y)       ∎

      l-1 : γ ＝ δ
      l-1 = γ                   ＝⟨ refl ⟩
            p ∙ (q ∙ (r ∙ s))   ＝⟨ ap (p ∙_) (∙assoc q r s ⁻¹) ⟩
            p ∙ ((q ∙ r) ∙ s)   ＝⟨ (∙assoc p (q ∙ r) s) ⁻¹ ⟩
            (p ∙ (q ∙ r)) ∙ s   ＝⟨ ap (_∙ s) π ⟩
            (u ∙ v) ∙ s         ＝⟨ ∙assoc u v s ⟩
            u ∙ (v ∙ s)         ＝⟨ ap (λ v₁ → u ∙ v₁) φᵢ ⟩
            u ∙ w               ＝⟨ φₐₛ (𝓻 e) refl refl ⟩
            w' ∙ α e x y        ＝⟨ ap (_∙ α e x y) (i ⁻¹) ⟩
            (p ∙ t') ∙ α e x y  ＝⟨ ∙assoc p t' (α e x y) ⟩
            p ∙ (t' ∙ α e x y)  ＝⟨ ap (p ∙_) ii ⁻¹ ⟩
            p ∙ (q ∙ t)         ∎ 
              where
                i : p ∙ t' ＝ w'
                i = p ∙ t' ＝⟨ ⊗-structure-to-Id₂-∙ _●_ (α e e x) (refl ✶ (𝓵 x)) refl refl ⟩
                    (α e e x ∙ (refl ✶ (𝓵 x))) ✶ refl
                           ＝⟨ ap (λ 𝓼 → 𝓼 ✶ refl) φᵢ ⟩
                    w'     ∎

                ii : q ∙ t ＝ t' ∙ α e x y
                ii = φₐₛ refl (𝓵 x) refl

      l-2 : r ∙ s ＝ t
      l-2 = cancel-left (cancel-left l-1)

      γ₁ : e ● ((e ● x) ● y) ＝ x ● y
      γ₁ = e ● ((e ● x) ● y) ＝⟨ 𝓵 ((e ● x) ● y) ⟩
           (e ● x) ● y       ＝⟨ α e x y ⟩
           e ● (x ● y)       ＝⟨ 𝓵 (x ● y) ⟩
           x ● y             ∎

      δ₁ : e ● ((e ● x) ● y) ＝ x ● y
      δ₁ = e ● ((e ● x) ● y) ＝⟨ 𝓵 ((e ● x) ● y) ⟩
           (e ● x) ● y       ＝⟨ (𝓵 x) ✶ refl ⟩
           x ● y             ∎

      l-3 : γ₁ ＝ δ₁
      l-3 = γ₁                                      ＝⟨ ∙assoc (𝓵 ((e ● x) ● y)) (α e x y) (𝓵 (x ● y)) ⁻¹ ⟩
            𝓵 ((e ● x) ● y) ∙ (α e x y) ∙ 𝓵 (x ● y) ＝⟨ ap (_∙ (𝓵 (x ● y))) (φₗ (α e x y) ⁻¹) ⟩
            r ∙ 𝓵 (e ● (x ● y)) ∙ 𝓵 (x ● y)         ＝⟨ ∙assoc r _ (𝓵 (x ● y)) ⟩
            r ∙ (𝓵 (e ● (x ● y)) ∙ 𝓵 (x ● y))       ＝⟨ ap (r ∙_) (φₗ (𝓵 (x ● y)) ⁻¹) ⟩
            r ∙ (s ∙ 𝓵 (x ● y))                     ＝⟨ ∙assoc r s (𝓵 (x ● y)) ⁻¹ ⟩
            (r ∙ s) ∙ 𝓵 (x ● y)                     ＝⟨ ap (_∙ (𝓵 (x ● y))) l-2 ⟩
            t ∙ 𝓵 (x ● y)                           ＝⟨ φₗ (ap₂ _●_ (𝓵 x) refl) ⟩
            δ₁ ∎

      l-4 : (α e x y) ∙ 𝓵 (x ● y) ＝ (𝓵 x) ✶ refl
      l-4 = cancel-left l-3

\end{code}

Also ⊗-assoc-neutral-r is a consequence of ⊗-assoc-neutral and the
naturality axioms. We prove the commutativity of the following two
diagrams:

% https://q.uiver.app/?q=WzAsNyxbMCwwLCIoKHh5KWUpZSJdLFsyLDAsIih4KHllKSllIl0sWzQsMCwieCgoeWUpZSkiXSxbNCwyLCJ4KHkoZWUpKSJdLFswLDIsIih4eSkoZWUpIl0sWzEsMSwiKHh5KWUiXSxbMywxLCJ4KHllKSJdLFswLDEsInAiXSxbMSwyLCJxIl0sWzIsMywiciJdLFswLDQsInUiLDJdLFs0LDMsInYiLDJdLFswLDUsInMnJyIsMl0sWzUsNiwicSciLDIseyJsYWJlbF9wb3NpdGlvbiI6NjB9XSxbMSw1LCJ0JyJdLFsyLDYsInQiXSxbMyw2LCJzIiwyXSxbNCw1LCJzJyIsMl1d
\[\begin{tikzcd}
	{((xy)e)e} && {(x(ye))e} && {x((ye)e)} \\
	& {(xy)e} && {x(ye)} \\
	{(xy)(ee)} &&&& {x(y(ee))}
	\arrow["p", from=1-1, to=1-3]
	\arrow["q", from=1-3, to=1-5]
	\arrow["r", from=1-5, to=3-5]
	\arrow["u"', from=1-1, to=3-1]
	\arrow["v"', from=3-1, to=3-5]
	\arrow["{s''}"', from=1-1, to=2-2]
	\arrow["{q'}"'{pos=0.6}, from=2-2, to=2-4]
	\arrow["{t'}", from=1-3, to=2-2]
	\arrow["t", from=1-5, to=2-4]
	\arrow["s"', from=3-5, to=2-4]
	\arrow["{s'}"', from=3-1, to=2-2]
\end{tikzcd}\]

% https://q.uiver.app/?q=WzAsOCxbMiwyLCIoeHkpZSIsWzI0NCw4Niw2MCwxXV0sWzQsMiwieCh5ZSkiLFsyNDQsODYsNjAsMV1dLFswLDBdLFs2LDBdLFsxLDEsIigoeHkpZSllIl0sWzUsMSwiKHgoeWUpKWUiXSxbMyw1LCIoeHkpZSJdLFszLDMsInh5IixbMjQ0LDg2LDYwLDFdXSxbMCwxLCJcXGFscGhhIiwwLHsiY29sb3VyIjpbMjQ0LDg2LDYwXX0sWzI0NCw4Niw2MCwxXV0sWzQsNSwicCJdLFs0LDYsInMnJyIsMix7ImN1cnZlIjoyfV0sWzUsNiwidCciLDAseyJjdXJ2ZSI6LTJ9XSxbNSwxLCJyX3t4KHllKX0iLDIseyJsYWJlbF9wb3NpdGlvbiI6NzB9XSxbNCwwLCJyX3soeHkpZX0iLDAseyJsYWJlbF9wb3NpdGlvbiI6NzB9XSxbMCw3LCJyX3t4eX0iLDIseyJsYWJlbF9wb3NpdGlvbiI6MzAsImNvbG91ciI6WzI0NCw4Niw2MF19LFsyNDQsODYsNjAsMV1dLFsxLDcsInggcl95IiwwLHsibGFiZWxfcG9zaXRpb24iOjIwLCJjb2xvdXIiOlsyNDQsODYsNjBdfSxbMjQ0LDg2LDYwLDFdXSxbNiw3LCJyX3t4eX0iLDFdXQ==
\[\begin{tikzcd}
	{} &&&&&& {} \\
	& {((xy)e)e} &&&& {(x(ye))e} \\
	&& \textcolor{rgb,255:red,77;green,65;blue,241}{(xy)e} && \textcolor{rgb,255:red,77;green,65;blue,241}{x(ye)} \\
	&&& \textcolor{rgb,255:red,77;green,65;blue,241}{xy} \\
	\\
	&&& {(xy)e}
	\arrow["\alpha", color={rgb,255:red,77;green,65;blue,241}, from=3-3, to=3-5]
	\arrow["p", from=2-2, to=2-6]
	\arrow["{s''}"', curve={height=12pt}, from=2-2, to=6-4]
	\arrow["{t'}", curve={height=-12pt}, from=2-6, to=6-4]
	\arrow["{r_{x(ye)}}"'{pos=0.7}, from=2-6, to=3-5]
	\arrow["{r_{(xy)e}}"{pos=0.7}, from=2-2, to=3-3]
	\arrow["{r_{xy}}"'{pos=0.3}, color={rgb,255:red,77;green,65;blue,241}, from=3-3, to=4-4]
	\arrow["{x r_y}"{pos=0.2}, color={rgb,255:red,77;green,65;blue,241}, from=3-5, to=4-4]
	\arrow["{r_{xy}}"{description}, from=6-4, to=4-4]
\end{tikzcd}\]

\begin{code}

  have-⊗-assoc-neutral-r : ⊗-assoc-neutral-r X _●_ α e 𝓵 𝓻
  have-⊗-assoc-neutral-r {x} {y} = cancel-left lemma-2
    where
      p : ((x ● y) ● e) ● e ＝ (x ● (y ● e)) ● e
      p = (α x y e) ✶ refl
      q : (x ● (y ● e)) ● e ＝ x ● ((y ● e) ● e)
      q = α x (y ● e) e
      q' : (x ● y) ● e ＝ x ● (y ● e)
      q' = α _ _ _
      r : x ● ((y ● e) ● e) ＝ x ● (y ● (e ● e))
      r = refl ✶ (α y e e)
      s : x ● (y ● (e ● e)) ＝ x ● (y ● e)
      s = refl ✶ (refl ✶ 𝓵 e)
      s' : (x ● y) ● (e ● e) ＝ (x ● y) ● e
      s' = refl ✶ (𝓵 e)
      s'' : ((x ● y) ● e) ● e ＝ (x ● y) ● e
      s'' = 𝓻 (x ● y) ✶ refl
      t : x ● ((y ● e) ● e) ＝ x ● (y ● e)
      t = refl ✶ ((𝓻 y) ✶ refl)
      t' : (x ● (y ● e)) ● e ＝ (x ● y) ● e
      t' = ((refl ✶ 𝓻 y)) ✶ refl
      u : ((x ● y) ● e) ● e ＝ (x ● y) ● (e ● e)
      u = α (x ● y) e e
      v : (x ● y) ● (e ● e) ＝ x ● (y ● (e ● e))
      v = α _ _ _

      γ δ ε η : ((x ● y) ● e) ● e ＝ x ● (y ● e)
      γ = p ∙ q ∙ r ∙ s
      δ = p ∙ t' ∙ q'
      ε = u ∙ v ∙ s
      η = s'' ∙ q'

      i : γ ＝ δ
      i = ((p ∙ q) ∙ r) ∙ s     ＝⟨ ∙assoc (p ∙ q) r s ⟩
          (p ∙ q) ∙ (r ∙ s)     ＝⟨ ap ((p ∙ q) ∙_) (⊗-structure-to-Id₂-∙ _●_ refl refl (α y e e) (refl ✶ (𝓵 e))) ⟩
          (p ∙ q) ∙ (refl ✶ (α y e e ∙ (refl ✶ 𝓵 e)))
                                 ＝⟨ ap ((p ∙ q) ∙_) (ap (refl ✶_) φᵢ) ⟩
          p ∙ q ∙ t             ＝⟨ ∙assoc p q t ⟩
          p ∙ (q ∙ t)           ＝⟨ ap (p ∙_) (φₐₛ refl (𝓻 y) refl) ⟩
          p ∙ (t' ∙ q')         ＝⟨ (∙assoc p t' q') ⁻¹ ⟩
          p ∙ t' ∙ q'            ∎

      ii : γ ＝ ε
      ii = p ∙ q ∙ r ∙ s        ＝⟨ ap (_∙ s) (∙assoc p q r) ⟩
           (p ∙ (q ∙ r)) ∙ s    ＝⟨ ap (_∙ s) π ⟩
           u ∙ v ∙ s            ∎

      iii : ε ＝ η
      iii = u ∙ v ∙ s           ＝⟨ ∙assoc u v s ⟩
            u ∙ (v ∙ s)         ＝⟨ ap (u ∙_) (φₐₛ refl refl (𝓵 e)) ⟩
            u ∙ (s' ∙ q')       ＝⟨ (∙assoc u s' q') ⁻¹ ⟩
            (u ∙ s') ∙ q'       ＝⟨ ap (_∙ q') φᵢ ⟩
            s'' ∙ q'            ∎

      iv : δ ＝ η
      iv = i ⁻¹ ∙ ii ∙ iii

      lemma : p ∙ t' ＝ s''
      lemma = p ∙ t'                    ＝⟨ ap ((p ∙ t') ∙_) (right-inverse q') ⟩
              (p ∙ t') ∙ (q' ∙ q' ⁻¹)   ＝⟨ ∙assoc (p ∙ t') q' (q' ⁻¹) ⁻¹ ⟩
              (p ∙ t' ∙ q') ∙ q' ⁻¹     ＝⟨ ap (_∙ q' ⁻¹) iv ⟩
              (s'' ∙ q') ∙ q' ⁻¹        ＝⟨ ∙assoc s'' q' (q' ⁻¹) ⟩
              s'' ∙ (q' ∙ q' ⁻¹)        ＝⟨ ap (s'' ∙_) (right-inverse q' ⁻¹) ⟩
              s''                       ∎

      μ ν : ((x ● y) ● e) ● e ＝ x ● y
      μ = ((x ● y) ● e) ● e  ＝⟨ 𝓻 ((x ● y) ● e) ⟩
           (x ● y) ● e       ＝⟨ α x y e ⟩
           x ● (y ● e)       ＝⟨ refl ✶ 𝓻 y ⟩
           x ● y             ∎

      ν = ((x ● y) ● e) ● e ＝⟨ 𝓻 ((x ● y) ● e) ⟩
          (x ● y) ● e       ＝⟨ 𝓻 (x ● y) ⟩
          x ● y             ∎

      lemma-2 : μ ＝ ν
      lemma-2 = 𝓻 ((x ● y) ● e) ∙ (α x y e ∙ refl ✶ 𝓻 y) ＝⟨ (∙assoc (𝓻 ((x ● y) ● e)) (α x y e) (refl ✶ 𝓻 y)) ⁻¹ ⟩
                (𝓻 ((x ● y) ● e) ∙ α x y e) ∙ refl ✶ 𝓻 y ＝⟨ ap (_∙ refl ✶ 𝓻 y) (φᵣ (α x y e) ⁻¹) ⟩
                (p ∙ 𝓻 (x ● (y ● e))) ∙ refl ✶ 𝓻 y       ＝⟨ ∙assoc p (𝓻 (x ● (y ● e))) (refl ✶ (𝓻 y)) ⟩
                p ∙ (𝓻 (x ● (y ● e)) ∙ refl ✶ 𝓻 y)       ＝⟨ ap (p ∙_) (φᵣ (refl ✶ (𝓻 y)) ⁻¹) ⟩
                p ∙ (t' ∙ 𝓻 (x ● y))                      ＝⟨ ∙assoc p t' (𝓻 (x ● y)) ⁻¹ ⟩
                (p ∙ t') ∙ 𝓻 (x ● y)                      ＝⟨ ap (_∙ 𝓻 (x ● y)) lemma ⟩
                s'' ∙ 𝓻 (x ● y)                           ＝⟨ φᵣ (𝓻 (x ● y)) ⟩
                ν                                          ∎

\end{code}

\begin{code}

  have-left-right-neutral-compat : left-right-neutral-compatibility X _●_ e 𝓵 𝓻
  have-left-right-neutral-compat = cancel-left (lemma-4 ⁻¹)
    where
      lemma-1 : (𝓻 e) ✶ refl ＝ 𝓻 (e ● e)
      lemma-1 = (𝓻 e) ✶ refl                         ＝⟨ ap (((𝓻 e) ✶ refl) ∙_) (right-inverse (𝓻 e)) ⟩
                ((𝓻 e) ✶ refl) ∙ ((𝓻 e) ∙ (𝓻 e) ⁻¹) ＝⟨ ∙assoc ((𝓻 e) ✶ refl) (𝓻 e) ((𝓻 e) ⁻¹) ⁻¹ ⟩
                (((𝓻 e) ✶ refl) ∙ (𝓻 e)) ∙ (𝓻 e) ⁻¹ ＝⟨ ap (_∙ (𝓻 e) ⁻¹) (φᵣ (𝓻 e)) ⟩
                (𝓻 (e ● e) ∙ (𝓻 e)) ∙ (𝓻 e) ⁻¹      ＝⟨ ∙assoc (𝓻 (e ● e)) (𝓻 e) ((𝓻 e) ⁻¹) ⟩
                𝓻 (e ● e) ∙ ((𝓻 e) ∙ (𝓻 e) ⁻¹)      ＝⟨ ap (𝓻 (e ● e) ∙_) (( right-inverse (𝓻 e) ) ⁻¹) ⟩
                𝓻 (e ● e)      ∎

      lemma-2 : refl ✶ (𝓵 e) ＝ 𝓵 (e ● e)
      lemma-2 = refl ✶ (𝓵 e)                        ＝⟨ ap ((refl ✶ (𝓵 e)) ∙_) (right-inverse (𝓵 e)) ⟩
                (refl ✶ (𝓵 e)) ∙ ((𝓵 e) ∙ (𝓵 e) ⁻¹) ＝⟨ ∙assoc (refl ✶ (𝓵 e)) (𝓵 e) ((𝓵 e) ⁻¹) ⁻¹ ⟩
                ((refl ✶ (𝓵 e)) ∙ (𝓵 e)) ∙ (𝓵 e) ⁻¹ ＝⟨ ap (_∙ (𝓵 e) ⁻¹) (φₗ (𝓵 e)) ⟩
                (𝓵 (e ● e) ∙ (𝓵 e)) ∙ (𝓵 e) ⁻¹      ＝⟨ ∙assoc (𝓵 (e ● e)) (𝓵 e) (𝓵 e ⁻¹) ⟩
                𝓵 (e ● e) ∙ ((𝓵 e) ∙ (𝓵 e) ⁻¹)      ＝⟨ ap (𝓵 (e ● e) ∙_) (right-inverse (𝓵 e) ⁻¹) ⟩
                𝓵 (e ● e)                           ∎

      lemma-3 : (𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e) ＝ (𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e)
      lemma-3 = (𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e)           ＝⟨ φᵢ ⁻¹ ⟩
                (α e e e) ∙ (refl ✶ (𝓵 e)) ＝⟨ ap ((α e e e) ∙_) lemma-2 ⟩
                (α e e e) ∙ (𝓵 (e ● e))    ＝⟨ have-⊗-assoc-neutral-l ⟩
                (𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e) ∎

      lemma-4 : 𝓻 (e ● e) ∙ (𝓻 e) ＝ 𝓻 (e ● e) ∙ (𝓵 e)
      lemma-4 = 𝓻 (e ● e) ∙ (𝓻 e)      ＝⟨ φᵣ (𝓻 e) ⁻¹ ⟩
                ((𝓻 e) ✶ refl) ∙ (𝓻 e) ＝⟨ ap (_∙ (𝓻 e)) lemma-3 ⟩
                ((𝓵 e) ✶ refl) ∙ (𝓻 e) ＝⟨ φᵣ (𝓵 e) ⟩
                𝓻 (e ● e) ∙ (𝓵 e)       ∎

\end{code}

Invertibility of the structure operation (duality, in another
parlance) stipulates that for each object X there are two "duality"
morphisms

ε : x  xᵛ → I
η : I → xᵛ x

corresponding to the usual notion of "inverse" elements, such that the
compositions

x → x I → x (xᵛ x) → (x xᵛ) x → I x → x

xᵛ → I xᵛ → (xᵛ x) xᵛ → xᵛ (x xᵛ) → xᵛ I → xᵛ

are the identity.

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
            x ● e        ＝⟨ ⊗-structure-to-Id₂ X _●_ refl (pr₂ (pr₂ (inv x))) ⟩
            x ● (xᵛ ● x) ＝⟨ (α _ _ _) ⁻¹ ⟩
            (x ● xᵛ) ● x ＝⟨ ⊗-structure-to-Id₂ X _●_ (pr₁ (pr₂ (inv x))) refl ⟩
            e ● x        ＝⟨ l x ⟩
            x ∎
            where
              xᵛ : X
              xᵛ = pr₁ (inv x)
      q : (x : X) → pr₁ (inv x) ＝ pr₁ (inv x)
      q x = xᵛ            ＝⟨ (l xᵛ) ⁻¹ ⟩
            e ● xᵛ        ＝⟨ ⊗-structure-to-Id₂ X _●_ (pr₂ (pr₂ (inv x))) refl ⟩
            (xᵛ ● x) ● xᵛ ＝⟨ α _ _ _ ⟩
            xᵛ ● (x ● xᵛ) ＝⟨ ⊗-structure-to-Id₂ X _●_ refl (pr₁ (pr₂ (inv x))) ⟩
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

    has-assoc-neutral : ⊗-assoc-neutral X _●_
                                        is-assoc
                                        e unit-left unit-right


\end{code}

From another point of view a "monoidal groupoid structure" on the type
X can be viewed as the the data (_●_ , e) together with the axioms.

\begin{code}

record Monoidal-grpd-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  field
    _⊗_ : ⊗-structure X
    e : X
    is-monoidal-grpd : monoidal-grpd-axioms X _⊗_ e
  open monoidal-grpd-axioms is-monoidal-grpd public

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

record cat-group-axioms (X : 𝓤 ̇)
                        (m : Monoidal-grpd-structure X) : 𝓤 ̇
                          where
  open Monoidal-grpd-structure
  field
    ⊗-inv : ⊗-inv-structure X (m ._⊗_)
            (m .e) (m .unit-left) (m .unit-right)

    ⊗-inv-axioms : ⊗-inv-compatible X (m ._⊗_) (m .is-assoc)
                   (m .e) (m .unit-left) (m .unit-right) ⊗-inv


record Cat-Group-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  open Monoidal-grpd-structure public
  open cat-group-axioms public
  field
    isMonoidalGrpd : Monoidal-grpd-structure X
    isCatGroup : cat-group-axioms X isMonoidalGrpd


2-Group Cat-Group Gr-Cat : (𝓤 : Universe) → 𝓤 ⁺ ̇
2-Group 𝓤 = Σ X ꞉ 𝓤 ̇ , Cat-Group-structure X
Cat-Group = 2-Group
Gr-Cat = 2-Group

\end{code}

Forgetting the group-like structure gives a monoidal groupoid

\begin{code}

cat-group-structure-is-monoidal-grpd-structure : (X : 𝓤 ̇)
                                             → Cat-Group-structure X
                                             → Monoidal-grpd-structure X
cat-group-structure-is-monoidal-grpd-structure X s = s .Cat-Group-structure.isMonoidalGrpd

2-groups-are-monoidal-groupoids : 2-Group 𝓤 → Monoidal-Grpd 𝓤
2-groups-are-monoidal-groupoids (X , s) = X , cat-group-structure-is-monoidal-grpd-structure X s


\end{code}

