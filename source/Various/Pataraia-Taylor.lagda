Martin Escardo, Tom de Jong, 16 & 22 Feb 2023

In this module Various.Pataraia-Taylor we implement a predicative
version of Pataraia's fixed point theorem:

  Every monotone endomap of a dcpo (directed complete poset) with a
  least element has a least fixed point.

The original impredicative version is implemented in the module
Various.Pataraia.

Pataraia [1] was the first to give a constructive proof of this in
topos logic. A version of his proof is published in [2] by Escardo,
with Pataraia's permission. Pataraia himself didn't publish the
result. An earlier, less general, theorem was proved by Coquand [6]
for *bounded complete* dcpos, with an easier proof.

See the module Various.Pataraia for an implementation of the
impredicative proof given [2].

Pataraia's proof has two steps, the first of which is directly
predicative and coded in the module lemma₂·₁ in the file
Various.Pataraia.

The second step (theorem-₂·₂ in the file Various.Pataraia) is
impredicative, because it considers the intersection of all subsets of
the dcpo that contain the least element, are closed under the monotone
map, and are closed under directed suprema. This is impredicative in
the sense that it requires propositional resizing axioms so that we
can form this intersection.

We instead consider a direct, explicit, elegant, predicative
construction of this subset, due to Paul Taylor [3], in our
alternative second step here, coded in the module `Taylor` below.

This version of the theorem probably deserves to be called the
Pataraia-Taylor fixed-point theorem, not only because the proof
involves a new ingredient, but also because it holds in a more general
predicative setting (here MLTT with function extensionality and
existence of propositional truncations).

There is a catch, though. In a predicative setting, there is no
non-trivial dcpo to apply the theorem [4]. More precisely, dcpos are
parametrized by three universes (𝓤,𝓥,𝓦) where the carrier lives in 𝓤,
the truth values of the order relation live in 𝓥, and the index types
for directed families live in 𝓦. In practice, for instance for the
Scott model of PCF, or Scott's D∞-model of the untyped
lambda-calculus, the parameter is of the form (𝓤⁺,𝓤,𝓤), and we refer
to such dcpos as "large, locally small, small directed-complete", and
if the parameter is (𝓤,𝓤,𝓤), we could refer to the dcpo as "small and
small directed-complete". The Pataraia-Taylor fixed point theorem
presented here applies to small, small directed-complete dcpos, and
the trouble is that there are no non-trivial examples of such dcpos in
our predicative world [4]. The only way to produce nontrivial such
dcpos to apply the theorem is to assume propositional resizing axioms
(which e.g. the UniMath project [5] does).

[1] Dito Pataraia. A constructive proof of Tarski’s fixed-point
    theorem for dcpo’s. Presented at the 65th Peripatetic Seminar on
    Sheaves and Logic, Aarhus, Denmark, November 1997.

[2] Martin Escardo. Joins in the frame of nuclei.
    Applied Categorical Structures 11: 117–124, 2003.
    https://doi.org/10.1023/A:1023555514029

[3] Paul Taylor. Two recent talks at Birmingham.
    Slides and papers available at
    https://paultaylor.eu/ordinals/
    https://web.archive.org/web/20240222103315/https://paultaylor.eu/ordinals/
    (22 Feb 2024 snapshot)

[4] Tom de Jong. Domain theory in constructive and predicative
    univalent foundations.
    PhD thesis at the University of Birmingham, UK, 2023.
    https://arxiv.org/abs/2301.12405

[5] Vladimir Voevodky, Benedikt Ahrens, Dan Grayson and others.
    Unimath --- a computer-checked library of univalent mathematics.
    https://unimath.github.io/UniMath/
    https://doi.org/10.5281/zenodo.8427604

[6] Thierry Coquand. A topos theoretic fix point theorem.
    Unpublished manuscript, June 1995.
    https://web.archive.org/web/20110822085930/https://www.cse.chalmers.se/~coquand/fix.pdf

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

\end{code}

We assume that propositional truncations exist, that function
extensionality holds, and work in a fixed universe 𝓤.

\begin{code}

module Various.Pataraia-Taylor
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓤
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Various.Pataraia pt fe 𝓤

\end{code}

We prove the following theorem, which says that every monotone endomap
of a dcpo with a least element has a least fixed point. As discussed
above, dcpos require three universes to be fully specified. For the
formulation of the theorem, we need the three universes to be the
same, namely 𝓤. (Notice that we mention 𝓤 only twice in the statement
of the theorem. This is because when we opened the domain theory
modules above, we already passed the universe 𝓤 once as a parameter.)

\begin{code}

Theorem : (𝓓 : DCPO {𝓤} {𝓤})
        → has-bottom 𝓓
        → (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
        → is-monotone 𝓓 𝓓 f
        → Σ x ꞉ ⟨ 𝓓 ⟩
              , (f x ＝ x)
              × ((y : ⟨ 𝓓 ⟩) → f y ＝ y → x ⊑⟨ 𝓓 ⟩ y)
\end{code}

Before proving this theorem, we first need to prove a number of
lemmas, in two modules, lemma₂·₁ in Various.Pataraia, and `taylor`
here.

The second part of Pataraia's proof (theorem₂·₂ of the module
Various.Pataraia) considers the intersection of all subsets of 𝓓 that
have ⊥ as a member, are closed under f, and are closed under directed
suprema. This is impredicative in the sense that it requires
propositional resizing axioms to compute the intersection. We instead
consider the subset of 𝓓 consisting of the elements that satisfy
Taylor's condition (TC) below, which is defined predicatively.

\begin{code}

module Taylor
        (𝓓 : DCPO {𝓤} {𝓤})
        ((⊥ , ⊥-is-least) : has-bottom 𝓓)
        (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
        (fm : is-monotone 𝓓 𝓓 f)
       where

 private
  D   = ⟨ 𝓓 ⟩
  _⊑_ = underlying-order 𝓓

 TC : D → 𝓤 ̇
 TC x = (x ⊑ f x) × ((u : D) → f u ⊑ u → x ⊑ u)

 TC₁ : (x : D) → TC x → x ⊑ f x
 TC₁ x = pr₁

 TC₂ : (x : D) → TC x → (u : D) → f u ⊑ u → x ⊑ u
 TC₂ x = pr₂

 TC-is-prop-valued : (x : D) → is-prop (TC x)
 TC-is-prop-valued x =  ×-is-prop
                         (prop-valuedness 𝓓 _ _)
                         (Π₂-is-prop fe λ _ _ → prop-valuedness 𝓓 _ _)

 TC-is-closed-under-directed-sups : is-closed-under-directed-sups 𝓓 TC
 TC-is-closed-under-directed-sups {A} α δ TC-preservation = c₁ , c₂
  where
   TC-preservation₁ : (a : A) → α a ⊑ f (α a)
   TC-preservation₁ a = TC₁ (α a) (TC-preservation a)

   TC-preservation₂ : (a : A) (u : D) → f u ⊑ u → α a ⊑ u
   TC-preservation₂ a = TC₂ (α a) (TC-preservation a)

   I : (a : A) → α a ⊑ f (∐ 𝓓 δ)
   I a = α a        ⊑⟨ 𝓓 ⟩[ TC-preservation₁ a ]
         f (α a)    ⊑⟨ 𝓓 ⟩[ fm (α a) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ a) ]
         f (∐ 𝓓 δ) ∎⟨ 𝓓 ⟩

   c₁ : ∐ 𝓓 δ ⊑ f (∐ 𝓓 δ)
   c₁ = ∐-is-lowerbound-of-upperbounds 𝓓 δ (f (∐ 𝓓 δ)) I

   c₂ : (u : D) → f u ⊑ u → ∐ 𝓓 δ ⊑ u
   c₂ u l = ∐-is-lowerbound-of-upperbounds 𝓓 δ u II
    where
     II : (a : A) → α a ⊑ u
     II a = TC-preservation₂ a u l

 TC-holds-at-⊥ : TC ⊥
 TC-holds-at-⊥ = ⊥-is-least (f ⊥) , (λ (u : D) _ → ⊥-is-least u)

\end{code}

Now the rest of Taylor is essentially the original one by Pataraia. We
apply lemma₂·₁ of the module Various.Pataraia to the subdcpo 𝓔 of 𝓓
consisting of the elements that satisfy Taylor's condition.

\begin{code}

 𝓔 : DCPO
 𝓔 = subdcpo 𝓓 TC TC-is-prop-valued TC-is-closed-under-directed-sups

 private
  E = ⟨ 𝓔 ⟩
  _≤_ : E → E → 𝓤 ̇
  s ≤ t = s ⊑⟨ 𝓔 ⟩ t

  NB-E : E ＝ (Σ x ꞉ D , TC x)
  NB-E = by-definition

  NB-≤ : (x x' : D) (c : TC x) (c' : TC x')
       → ((x , c) ≤ (x' , c')) ＝ (x ⊑ x')
  NB-≤ x x' c c' = by-definition

 ι : E → D
 ι (x , c) = x

 τ : (t : E) → TC (ι t)
 τ (x , c) = c

 ⊥𝓔 : E
 ⊥𝓔 =  ⊥ , TC-holds-at-⊥

\end{code}

The monotone function f : D → D restricts to a monotone inflationary
function 𝓯 : E → E.

\begin{code}

 𝓯 : E → E
 𝓯 (x , c₁ , c₂) = f x ,
                   fm x (f x) c₁ ,
                   (λ u (l : f u ⊑ u) → f x ⊑⟨ 𝓓 ⟩[ fm x u (c₂ u l) ]
                                        f u ⊑⟨ 𝓓 ⟩[ l ]
                                        u   ∎⟨ 𝓓 ⟩)

 𝓯-is-monotone : (s t : E) → s ≤ t → 𝓯 s ≤ 𝓯 t
 𝓯-is-monotone (x , _) (y , _) = fm x y

 𝓯-is-inflationary : (t : E) → t ≤ 𝓯 t
 𝓯-is-inflationary (x , c₁ , c₂) = c₁

 TC-𝓯 : (s : E) → TC (f (ι s))
 TC-𝓯 s = pr₂ (𝓯 s)

\end{code}

So now we can apply lemma₂·₁ proved in Various.Pataraia.

\begin{code}

 open lemma₂·₁ 𝓔

 𝕗 : MI
 𝕗 = (𝓯 , 𝓯-is-monotone , 𝓯-is-inflationary)

 t₀ : E
 t₀ = γ ⊥𝓔

 t₀-is-fp : 𝓯 t₀ ＝ t₀
 t₀-is-fp = γ-is-fixed-point 𝕗 ⊥𝓔

 x₀ : D
 x₀ = ι t₀

 x₀-is-fp : f x₀ ＝ x₀
 x₀-is-fp = ap ι t₀-is-fp

\end{code}

x₀ is the least pre-fixed point.

\begin{code}

 x₀-is-lpfp : (x : D) → f x ⊑ x → x₀ ⊑ x
 x₀-is-lpfp = TC₂ x₀ (τ t₀)

\end{code}

And so it is the least fixed point.

\begin{code}

 x₀-is-lfp : (x : D) → f x ＝ x → x₀ ⊑ x
 x₀-is-lfp x p = x₀-is-lpfp x (＝-to-⊑ 𝓓 p)

\end{code}

This concludes the proof of the theorem.

\begin{code}

Theorem 𝓓 hb f fm = x₀ , x₀-is-fp , x₀-is-lfp
 where
  open Taylor 𝓓 hb f fm

\end{code}

This theorem can be strengthened as follows, which says that any
endofunctor f has an initial algebra, when the dcpo is viewed as a
category.

\begin{code}

initial-algebra : (𝓓 : DCPO {𝓤} {𝓤})
                → has-bottom 𝓓
                → (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
                → is-monotone 𝓓 𝓓 f
                → Σ x ꞉ ⟨ 𝓓 ⟩
                      , (f x ＝ x)
                      × ((y : ⟨ 𝓓 ⟩) → f y ⊑⟨ 𝓓 ⟩ y → x ⊑⟨ 𝓓 ⟩ y)
initial-algebra 𝓓 hb f fm = x₀ , x₀-is-fp , x₀-is-lpfp
 where
  open Taylor 𝓓 hb f fm

\end{code}

NB. We could have formulated and proved this more categorically as

  (𝓓 : DCPO {𝓤} {𝓤})
 → has-bottom 𝓓
 → (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
 → is-monotone 𝓓 𝓓 f
 → Σ x ꞉ ⟨ 𝓓 ⟩
       , (f x ⊑⟨ 𝓓 ⟩ x)
       × ((y : ⟨ 𝓓 ⟩) → f y ⊑⟨ 𝓓 ⟩ y → x ⊑⟨ 𝓓 ⟩ y)

and then conclude that actually f x ＝ x by Lambek's Lemma. But we
already know that the initial algebra is a fixed point in our case,
and so there is no point in doing this.

For later reference we repackage the theorem as follows:

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓤})
        ((⊥ , ⊥-is-least) : has-bottom 𝓓)
        (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
        (fm : is-monotone 𝓓 𝓓 f)
       where

 lfp : ⟨ 𝓓 ⟩
 lfp = pr₁ (Theorem 𝓓 (⊥ , ⊥-is-least) f fm)

 lfp-is-fixed-point : f lfp ＝ lfp
 lfp-is-fixed-point = pr₁ (pr₂ (Theorem 𝓓 (⊥ , ⊥-is-least) f fm))

 lfp-is-least : (y : ⟨ 𝓓 ⟩) → f y ＝ y → lfp ⊑⟨ 𝓓 ⟩ y
 lfp-is-least = pr₂ (pr₂ (Theorem 𝓓 (⊥ , ⊥-is-least) f fm))

\end{code}

Added 22 February 2024.

It follows directly from Pataraia's original proof [2] that if P is a
property that holds for ⊥, is closed under directed suprema, and is
closed under f, then P holds for the least fixed point of f. We refer
to this as the fixed-point induction principle. Although this
principle doesn't follow directly from the above argument, we can
prove it as follows, using the above module Taylor again.

\begin{code}

 lfp-induction :
    (P : ⟨ 𝓓 ⟩ → 𝓤 ̇  )
  → ((x : ⟨ 𝓓 ⟩) → is-prop (P x))
  → P ⊥
  → is-closed-under-directed-sups 𝓓 P
  → ((x : ⟨ 𝓓 ⟩) → P x → P (f x))
  → P lfp

 module fixed-point-induction
         (P : ⟨ 𝓓 ⟩ → 𝓤 ̇  )
         (P-is-prop-valued : (x : ⟨ 𝓓 ⟩) → is-prop (P x))
         (P-holds-at-⊥ : P ⊥)
         (P-is-closed-under-directed-sups : is-closed-under-directed-sups 𝓓 P)
         (P-is-closed-under-f : (x : ⟨ 𝓓 ⟩) → P x → P (f x))
        where

  private
   D = ⟨ 𝓓 ⟩
   _⊑_ = underlying-order 𝓓

  open Taylor 𝓓 (⊥ , ⊥-is-least) f fm
   using (TC ;
          TC₂ ;
          TC-𝓯 ;
          TC-is-prop-valued ;
          TC-is-closed-under-directed-sups ;
          TC-holds-at-⊥)
   renaming (𝓯 to 𝓯')

  TC' : D → 𝓤 ̇
  TC' x = TC x × P x

  TC'-⊆-TC : (x : ⟨ 𝓓 ⟩) → TC' x → TC x
  TC'-⊆-TC x = pr₁

  TC'-⊆-P : (x : ⟨ 𝓓 ⟩) → TC' x → P x
  TC'-⊆-P x = pr₂

  TC'-is-prop-valued : (x : D) → is-prop (TC' x)
  TC'-is-prop-valued x = ×-is-prop
                          (TC-is-prop-valued x)
                          (P-is-prop-valued x)

  TC'-is-closed-under-directed-sups : is-closed-under-directed-sups 𝓓 TC'
  TC'-is-closed-under-directed-sups α δ TC'-preservation = c₁ , c₂
   where
    c₁ : TC (∐ 𝓓 δ)
    c₁ = TC-is-closed-under-directed-sups α δ
          (λ a → TC'-⊆-TC (α a) (TC'-preservation a))

    c₂ : P (∐ 𝓓 δ)
    c₂ = P-is-closed-under-directed-sups α δ
          (λ a → TC'-⊆-P (α a) (TC'-preservation a))

  𝓔 : DCPO
  𝓔 = subdcpo 𝓓 TC' TC'-is-prop-valued TC'-is-closed-under-directed-sups

  private
   E = ⟨ 𝓔 ⟩
   _≤_ : E → E → 𝓤 ̇
   s ≤ t = s ⊑⟨ 𝓔 ⟩ t

  ι : E → D
  ι (x , c) = x

  τ' : (t : E) → TC' (ι t)
  τ' (x , c) = c

  τ : (t : E) → TC (ι t)
  τ t = TC'-⊆-TC (ι t) (τ' t)

  ⊥𝓔 : E
  ⊥𝓔 = ⊥ , TC-holds-at-⊥ , P-holds-at-⊥

  𝓯 : E → E
  𝓯 (x , tc , p) = f x , TC-𝓯 (x , tc) , P-is-closed-under-f x p

  𝓯-is-monotone : (s t : E) → s ≤ t → 𝓯 s ≤ 𝓯 t
  𝓯-is-monotone (x , _) (y , _) = fm x y

  𝓯-is-inflationary : (t : E) → t ≤ 𝓯 t
  𝓯-is-inflationary (x , (c₁ , c₂) , _) = c₁

  open lemma₂·₁ 𝓔

  𝕗 : MI
  𝕗 = (𝓯 , 𝓯-is-monotone , 𝓯-is-inflationary)

  t₀ : E
  t₀ = γ ⊥𝓔

  t₀-is-fp : 𝓯 t₀ ＝ t₀
  t₀-is-fp = γ-is-fixed-point 𝕗 ⊥𝓔

  x₀ : D
  x₀ = ι t₀

  x₀-is-fp : f x₀ ＝ x₀
  x₀-is-fp = ap ι t₀-is-fp

  x₀-is-lpfp : (x : D) → f x ⊑ x → x₀ ⊑ x
  x₀-is-lpfp = TC₂ x₀ (τ t₀)

  x₀-is-lfp : (x : D) → f x ＝ x → x₀ ⊑ x
  x₀-is-lfp x p = x₀-is-lpfp x (＝-to-⊑ 𝓓 p)

  x₀-satisfies-P : P x₀
  x₀-satisfies-P = TC'-⊆-P (ι t₀) (τ' t₀)

\end{code}

Now we are ready to prove the least fixed point induction theorem.

\begin{code}

 lfp-induction
  P
  P-is-prop-valued
  P-holds-at-⊥
  P-is-closed-under-directed-sups
  P-is-closed-under-f = transport P e x₀-satisfies-P
   where
    open fixed-point-induction
          P
          P-is-prop-valued
          P-holds-at-⊥
          P-is-closed-under-directed-sups
          P-is-closed-under-f
    e : x₀ ＝ lfp
    e = antisymmetry 𝓓
         x₀ lfp
         (x₀-is-lfp lfp lfp-is-fixed-point)
         (lfp-is-least x₀ x₀-is-fp)

\end{code}
