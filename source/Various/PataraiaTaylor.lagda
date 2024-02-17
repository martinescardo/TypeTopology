Martin Escardo, 16 Feb 2023

We present a predicative version of Pataraia's fixed point theorem
that every monotone endomap of a dcpo with a least element has a least
fixed point. I benefitted from discussions by Tom de Jong.

Pataraia [1] was the first to give a constructive proof of this in
topos logic.  A version of his proof is published in [2] by the
author, with Pataraia's permission.

The proof has two steps, the first of which is directly predicative
and coded in the module step₁.

The second step is impredicative, because it consideres the
intersection of all subsets of the dcpo that contain the least
element, are closed under the monotone map, and are closed under
suprema. This is impredicative in the sense that it requires
propositional resizing axioms so that we can form this intersection.

We instead consider a direct, explicit, predicative construction of
this subset, due to Paul Taylor [3], in our second step, coded in the
module step₂.

This version of the theorem would probably deserve to be called the
Pataraia-Taylor theorem, not only because the proof involves a new
ingredient, but also because it holds in a more general predicative
setting (here MLTT with function extensionality and existence of
propositional truncations). Therefore we decided to name this module
PataraiaTaylor.

There is a catch, though. In a predicative setting, there is no
non-trivial dcpo to apply the theorem [4]. More precisely, dcpos are
parametrized by three universes (𝓤,𝓥,𝓦) where the carrier lives in 𝓤,
the truth values of the order relation live in 𝓥, the index types for
directed families live in 𝓦. In practice, for example for the Scott
model of PCF, or Scott's D∞, the parameter is of the form (𝓤⁺,𝓤,𝓤),
and we refer to such dcpos as "large, locally small, small complete",
and if the parameter is (𝓤,𝓤,𝓤), we could refer to the dcpo as "small
and small complete".  The Pataraia-Taylor theorem presented here
applies to small, small complete dcpos, and the trouble is that there
are no non-trivial examples of such dcpos in our predicative world
[4].  The only way to produce small, small complete dcpos to apply the
theorem is to assume propositional resizing axioms (which e.g. the
UniMath project [5] does).


[1] Ditto Pataraia. A constructive proof of Tarski’s fixed-point
    theorem for dcpo’s. Presented at the 65th Peripatetic Seminar on
    Sheaves and Logic, Aarhus, Denmark, November 1997.

[2] Martin Escardo. Joins in the frame of nuclei.
    Applied Categorical Structures 11: 117–124, 2003.
    https://doi.org/10.1023/A:1023555514029

[3] Paul Taylor. Two recent talks at Birmingham.
    Slides and papers available at https://paultaylor.eu/ordinals/

[4] Tom de Jong. Domain theory in constructive and predicative
    univalent foundations.
    https://arxiv.org/abs/2301.12405

[5] Vladimir Voevodky, Benedikt Ahrens, Dan Grayson and others.
    Unimath --- a computer-checked library of univalent mathematics.
    https://unimath.github.io/UniMath/
    https://doi.org/10.5281/zenodo.8427604

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc

module Various.PataraiaTaylor
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓤
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Sets
open import UF.Sets-Properties

\end{code}

We prove the following.

\begin{code}

Theorem : (𝓓 : DCPO {𝓤} {𝓤})
        → has-bottom 𝓓
        → (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
        → is-monotone 𝓓 𝓓 f
        → Σ x ꞉ ⟨ 𝓓 ⟩
              , (f x ＝ x)
              × ((y : ⟨ 𝓓 ⟩) → f y ＝ y → x ⊑⟨ 𝓓 ⟩ y)
\end{code}

We prove this at the very end of the file. We first need to prove a
number of lemmas.

\begin{code}

module step₁ (𝓔 : DCPO {𝓤} {𝓤}) where

 private
  E   = ⟨ 𝓔 ⟩
  _⊑_ = underlying-order 𝓔

\end{code}

The pointed type MI of monotone inflationary endo maps of E. Notice that E is allowed to be empty.

\begin{code}

 MI : 𝓤 ̇
 MI = Σ f ꞉ (E → E) , is-monotone 𝓔 𝓔 f × is-inflationary 𝓔 f

 𝕚𝕕 : MI
 𝕚𝕕 = id , id-is-monotone 𝓔 , id-is-inflationary 𝓔

\end{code}

We use the following auxiliary function Γ : E → MI → E to define a
function γ : E → E with suitable properties. For each x : E we get a
directed family Γ x : MI → E, and we define γ x to be the supremum of
this family.

Notice that it is as this point that we assume that our dcpo is small
and small complete, because MI lives in the universe 𝓤, which is also
where the carrier of 𝓔 lives.

\begin{code}

 Γ : E → MI → E
 Γ x (f , _) = f x

 Γ-is-semidirected : (x : E) → is-semidirected _⊑_ (Γ x)
 Γ-is-semidirected x 𝕗@(f , fm , fi) 𝕘@(g , gm , gi) = ∣ 𝕙 , f-le-h , g-le-h ∣
  where
   h = g ∘ f

   𝕙 : MI
   𝕙 = (g ∘ f , ∘-is-monotone 𝓔 𝓔 𝓔 f g fm gm , ∘-is-inflationary 𝓔 f g fi gi)

   f-le-h : f x ⊑ h x
   f-le-h = gi (f x)

   g-le-h : g x ⊑ h x
   g-le-h = gm x (f x) (fi x)

 Γ-is-directed : (x : E) → is-directed _⊑_ (Γ x)
 Γ-is-directed x = ∣ 𝕚𝕕 ∣ , Γ-is-semidirected x

 γ : E → E
 γ x = ∐ 𝓔 (Γ-is-directed x)

\end{code}

So the function γ is the pointwise supremum of the monotone
inflationary endomaps of E.

\begin{code}

 γ-is-monotone : is-monotone 𝓔 𝓔 γ
 γ-is-monotone x y l = ∐-is-monotone 𝓔 (Γ-is-directed x) (Γ-is-directed y) l'
  where
   l' : (𝕗 : MI) → Γ x 𝕗 ⊑ Γ y 𝕗
   l' (f , fm , fi) = fm x y l

\end{code}

From this it is easy to conclude that γ is the largest monotone
inflationary map.

\begin{code}

 γ-is-largest-mi-map : ((f , fm , fi) : MI) (x : E) → f x ⊑ γ x
 γ-is-largest-mi-map 𝕗 x = ∐-is-upperbound 𝓔 (Γ-is-directed x) 𝕗

 γ-is-inflationary : is-inflationary 𝓔 γ
 γ-is-inflationary = γ-is-largest-mi-map 𝕚𝕕

\end{code}

And, in turn, from this we conclude that γ x is a fixed point of any
monotone inflationary map f : E → E.

\begin{code}

 γ-is-fixed-point : ((f , fm , fi) : MI) (x : E) → f (γ x) ＝ γ x
 γ-is-fixed-point (f , fm , fi) x = antisymmetry 𝓔 _ _ I II
  where
   I : f (γ x) ⊑ γ x
   I = γ-is-largest-mi-map
        (f ∘ γ ,
         ∘-is-monotone 𝓔 𝓔 𝓔 γ f γ-is-monotone fm ,
         ∘-is-inflationary 𝓔 γ f γ-is-inflationary fi)
       x

   II : γ x ⊑ f (γ x)
   II = ∐-is-lowerbound-of-upperbounds 𝓔 (Γ-is-directed x) (f (γ x))
         (λ 𝕘@(g , gm , gi)  →
             g x     ⊑⟨ 𝓔 ⟩[ fi (g x) ]
             f (g x) ⊑⟨ 𝓔 ⟩[ fm (g x) (γ x) (γ-is-largest-mi-map 𝕘 x) ]
             f (γ x) ∎⟨ 𝓔 ⟩)

\end{code}

The second part of Pataraia's proof considers the intersection of all
subsets of 𝓓 that contain ⊥, are closed under f, and are closed under
suprema. This is impredicative in the sense that it requires
propositional resizing axioms to compute the intersection. We instead
consider the subset of 𝓓 consisting of the elements that satisfy
Taylor's condition below, which is defined predicatively.

\begin{code}

module step₂
        (𝓓 : DCPO {𝓤} {𝓤})
        ((⊥ , ⊥-is-least) : has-bottom 𝓓)
        (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
        (fm : is-monotone 𝓓 𝓓 f)
       where

 private
  D   = ⟨ 𝓓 ⟩
  _⊑_ = underlying-order 𝓓

 taylors-condition : D → 𝓤 ̇
 taylors-condition x = (x ⊑ f x) × ((u : D) → f u ⊑ u → x ⊑ u)

 tc-is-closed-under-directed-sups
  : {A : 𝓤 ̇ }
    (α : A → D)
  → (δ : is-Directed 𝓓 α)
  → ((a : A) → taylors-condition (α a))
  → taylors-condition (∐ 𝓓 δ)
 tc-is-closed-under-directed-sups {A} α δ tc-preservation = I , II
  where
   tc-preservation₁ : (a : A) → α a ⊑ f (α a)
   tc-preservation₁ a = pr₁ (tc-preservation a)

   tc-preservation₂ : (a : A) (u : D) → f u ⊑ u → α a ⊑ u
   tc-preservation₂ a = pr₂ (tc-preservation a)

   I' : (a : A) → α a ⊑ f (∐ 𝓓 δ)
   I' a = α a        ⊑⟨ 𝓓 ⟩[ tc-preservation₁ a ]
          f (α a)    ⊑⟨ 𝓓 ⟩[ fm (α a) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ a) ]
          f (∐ 𝓓 δ) ∎⟨ 𝓓 ⟩

   I : ∐ 𝓓 δ ⊑ f (∐ 𝓓 δ)
   I = ∐-is-lowerbound-of-upperbounds 𝓓 δ (f (∐ 𝓓 δ)) I'

   II : (u : D) → f u ⊑ u → ∐ 𝓓 δ ⊑ u
   II u l = ∐-is-lowerbound-of-upperbounds 𝓓 δ u II'
    where
     II' : (a : A) → α a ⊑ u
     II' a = tc-preservation₂ a u l

 E = Σ x ꞉ D , taylors-condition x

 ι : E → D
 ι = pr₁

 τ : (t : E) → taylors-condition (ι t)
 τ = pr₂

 _≤_ : E → E → 𝓤 ̇
 (x , _) ≤ (y , _) = x ⊑ y

 tc-is-prop-valued : (x : D) → is-prop (taylors-condition x)
 tc-is-prop-valued x =  ×-is-prop
                         (prop-valuedness 𝓓 _ _)
                         (Π₂-is-prop fe λ _ _ → prop-valuedness 𝓓 _ _)

 E-is-set : is-set E
 E-is-set = subsets-of-sets-are-sets D
             taylors-condition
             (sethood 𝓓)
             (tc-is-prop-valued _)

\end{code}

We now build a dcpo 𝓔 to be able to apply step₁. It is simply the
subdcpo E of 𝓓 and the rest of the argument is essentially the
original one by Pataraia.

TODO. Develop the construction of subdcpos in full generality else
where in the domain theory modules.

\begin{code}

 𝓔 : DCPO
 𝓔 = E ,
     _≤_ ,
     (E-is-set ,
      (λ _ _ → prop-valuedness 𝓓 _ _) ,
      (λ _ → reflexivity 𝓓 _) ,
      (λ (x , _) (y , _) (z , _) → transitivity 𝓓 x y z) ,
      (λ (x , _) (y , _) l m → to-subtype-＝
                                tc-is-prop-valued
                                (antisymmetry 𝓓 x y l m))) ,
     (λ I α δ@(inh , s) → (∐ 𝓓 {I} {ι ∘ α} δ ,
                           tc-is-closed-under-directed-sups (ι ∘ α) δ (τ ∘ α) ) ,
                          (∐-is-upperbound 𝓓 δ) ,
                           (λ t → ∐-is-lowerbound-of-upperbounds 𝓓 δ (ι t)))

 ⊥𝓔 : E
 ⊥𝓔 =  ⊥ , ⊥-is-least (f ⊥) , (λ (u : D) _ → ⊥-is-least u)

 ⊥𝓔-is-least : is-least _≤_ ⊥𝓔
 ⊥𝓔-is-least (x , c₁ , c₂) = ⊥-is-least x

\end{code}

The monotone function f : D → D restricts to a monotone inflationary
function 𝓯 : E → E.

\begin{code}

 𝓯 : E → E
 𝓯 (x , c₁ , c₂) = f x ,
                   fm x (f x) c₁ ,
                   (λ u (l : f u ⊑ u) →
                       f x ⊑⟨ 𝓓 ⟩[ fm x u (c₂ u l) ]
                       f u ⊑⟨ 𝓓 ⟩[ l ]
                       u   ∎⟨ 𝓓 ⟩)

 𝓯-is-inflationary : (t : E) → t ≤ 𝓯 t
 𝓯-is-inflationary (x , c₁ , c₂) = c₁

 𝓯-is-monotone : (s t : E) → s ≤ t → 𝓯 s ≤ 𝓯 t
 𝓯-is-monotone (x , c₁ , c₂) (y , d₁ , d₂) = fm x y

 open step₁ 𝓔

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
 x₀-is-lpfp = pr₂ (pr₂ t₀)

 x₀-is-lfp : (x : D) → f x ＝ x → x₀ ⊑ x
 x₀-is-lfp x p = x₀-is-lpfp x l
  where
   l : f x ⊑ x
   l = transport (f x ⊑_) p (reflexivity 𝓓 (f x))

\end{code}

Putting the above together, the proof of the theorem is concluded.

\begin{code}

Theorem 𝓓 hb f fm = x₀ , x₀-is-fp , x₀-is-lfp
 where
  open step₂ 𝓓 hb f fm

\end{code}

The theorem can be strengthened as follows, which says that any
endofunctor f has an initial algebra, when the dcpo is viewed as a
category.

\begin{code}

initial-algebras : (𝓓 : DCPO {𝓤} {𝓤})
                 → has-bottom 𝓓
                 → (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
                 → is-monotone 𝓓 𝓓 f
                 → Σ x ꞉ ⟨ 𝓓 ⟩
                       , (f x ＝ x)
                       × ((y : ⟨ 𝓓 ⟩) → f y ⊑⟨ 𝓓 ⟩ y → x ⊑⟨ 𝓓 ⟩ y)
initial-algebras 𝓓 hb f fm = x₀ , x₀-is-fp , x₀-is-lpfp
 where
  open step₂ 𝓓 hb f fm

\end{code}

NB. We could have formulated this version as

  (𝓓 : DCPO {𝓤} {𝓤})
 → has-bottom 𝓓
 → (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
 → is-monotone 𝓓 𝓓 f
 → Σ x ꞉ ⟨ 𝓓 ⟩
       , (f x ⊑⟨ 𝓓 ⟩ x)
       × ((y : ⟨ 𝓓 ⟩) → f y ⊑⟨ 𝓓 ⟩ y → x ⊑⟨ 𝓓 ⟩ y)

and then conclude that actually f x = x by Lambek's Lemma.
