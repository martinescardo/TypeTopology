Ian Ray. 1st October 2025.

Minor changes and merged into TypeToplogy in May 2026.

We present the notion of a reflexive graph lens which was introduced by
Sterling in "Reflexive graph lenses in univalent foundations" (see index for
link).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.Lenses where

open import MLTT.Spartan
open import ReflexiveGraphs.Displayed
open import ReflexiveGraphs.DisplayedUnivalent
open import ReflexiveGraphs.Type
open import ReflexiveGraphs.Univalent

\end{code}

Given a reflexive graph (A , ≈) it is useful to consider 'transport' along
edges, that is, terms of the form

                   push : (x ≈ y) → P(x) → P(y)

where P is a type family (but in full generality we wish P to be a reflexive
graph family). For example, we have the following term 

                   _ : (X ≃ Y) → is-set X → is-set Y

on the reflexive graph (𝓤 , ≃). In fact, such a term is recorded in
Sets-Properties.lagda, albeit contravariantly, as the term equiv-to-set. Of
course, many notions of transport arise in the contravariant form as well.
For this reason we wish to also consider terms of the form

                  pull : (x ≈ y) → P(y) → P(x).

A lens on a reflexive graph can be thought of as such a generic notion of
transport. They will manifest in both the covariant and contravariant forms.
Lenses allow for a deeper characterization of many structures that use a
personalized notion of transport (which under univalence are equivalent up to
homotopy). This fact about uniqueness of transport has been dubbed the
fundamental lemma of transport along equivalences by Martin Escardo
(see UF/FundamentalLemmaOfTransportAlongEquivalences).
TODO. Add the ReflexiveGraphs.Examples file which provides a generalization
of this theorem. Just as in the statement of this transport theorem one needs
data that details behavior at refl, this data must also be included in the
definition of a lens.

We present the structure of an oplax covariant lens as a record and then
collect the type of oplax covariant lenses as a sigma type.

NOTE ON TERMINOLOGY: We follow Sterling's terminological conventions, but we
make an attempt to explain them here. The term "lens" has a long history of use
in computer science and category theory which we make no attempt to recount
here. Sterling borrows the term lens from work on a generalization of fibrations
which, rather than satisfying a universal property, are only required to satisfy
a unit law. The "oplax/lax" terminology is borrowed from category theory; more
precisely the notion of a lax (oplax) monoidal functor. Recall, if a monoidal
functor F : C → D is lax then in particular there is a morphism 1_D → F(1_C)
(in addition to many other requirements) and oplax if there is a morphism
F(1_C) → 1_D. It is the direction of these morphisms which motivates Sterling's
use of the terminology. In particular, see the direction of the edges in the
push-refl and pull-refl data below.

\begin{code}

record oplax-covariant-lens-structure
 (𝓤' 𝓥' : Universe) (𝓐 : Refl-Graph 𝓤 𝓥)
 (𝓑 : ⟨ 𝓐 ⟩ → Refl-Graph 𝓤' 𝓥') : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥'  ̇ where
 field
  push : {x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 x ⟩ → ⟨ 𝓑 y ⟩
  push-refl : {x : ⟨ 𝓐 ⟩} (u : ⟨ 𝓑 x ⟩) → push (≈-refl 𝓐 x) u ≈⟨ 𝓑 x ⟩ u

Oplax-Covariant-Lens : (𝓤' 𝓥' : Universe) (𝓐 : Refl-Graph 𝓤 𝓥)
                      → 𝓤 ⊔ 𝓥 ⊔ (𝓤' ⊔ 𝓥')⁺ ̇
Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐
 = Σ 𝓑 ꞉ (⟨ 𝓐 ⟩ → Refl-Graph 𝓤' 𝓥') , oplax-covariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑

\end{code}

We name the components of an oplax covariant lens.

\begin{code}

module _ {𝓤' 𝓥' : Universe} {𝓐 : Refl-Graph 𝓤 𝓥}
         (𝓛@(𝓑 , s) : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐)
       where

 lens-push-graph : ⟨ 𝓐 ⟩ → Refl-Graph 𝓤' 𝓥'
 lens-push-graph = 𝓑

 lens-push-fam : ⟨ 𝓐 ⟩ → 𝓤' ̇
 lens-push-fam x = ⟨ lens-push-graph x ⟩

 lens-push : {x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y)
           → lens-push-fam x
           → lens-push-fam y
 lens-push = oplax-covariant-lens-structure.push s

 lens-push-refl : {x : ⟨ 𝓐 ⟩} (u : lens-push-fam x)
                → lens-push (≈-refl 𝓐 x) u ≈⟨ lens-push-graph x ⟩ u
 lens-push-refl = oplax-covariant-lens-structure.push-refl s

\end{code}

We now present a lax contravariant lens.

\begin{code}

record lax-contravariant-lens-structure
 (𝓤' 𝓥' : Universe) (𝓐 : Refl-Graph 𝓤 𝓥)
 (𝓑 : ⟨ 𝓐 ⟩ → Refl-Graph 𝓤' 𝓥') : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇ where
 field
  pull : {x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 y ⟩ → ⟨ 𝓑 x ⟩
  pull-refl : {x : ⟨ 𝓐 ⟩} (u : ⟨ 𝓑 x ⟩) → u ≈⟨ 𝓑 x ⟩ pull (≈-refl 𝓐 x) u

Lax-Contravariant-Lens : (𝓤' 𝓥' : Universe) (𝓐 : Refl-Graph 𝓤 𝓥)
                       → 𝓤 ⊔ 𝓥 ⊔ (𝓤' ⊔ 𝓥')⁺ ̇
Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐
 = Σ 𝓑 ꞉ (⟨ 𝓐 ⟩ → Refl-Graph 𝓤' 𝓥') , lax-contravariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑

\end{code}

We name the components of an lax contravariant lens.

\begin{code}

module _ {𝓤' 𝓥' : Universe} {𝓐 : Refl-Graph 𝓤 𝓥}
         (𝓛@(𝓑 , s) : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐)
       where

 lens-pull-graph : ⟨ 𝓐 ⟩ → Refl-Graph 𝓤' 𝓥'
 lens-pull-graph = 𝓑

 lens-pull-fam : ⟨ 𝓐 ⟩ → 𝓤' ̇
 lens-pull-fam x = ⟨ lens-pull-graph x ⟩

 lens-pull : {x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y)
           → lens-pull-fam y
           → lens-pull-fam x
 lens-pull = lax-contravariant-lens-structure.pull s

 lens-pull-refl : {x : ⟨ 𝓐 ⟩} (u : lens-pull-fam x)
                → u ≈⟨ lens-pull-graph x ⟩ lens-pull (≈-refl 𝓐 x) u
 lens-pull-refl = lax-contravariant-lens-structure.pull-refl s
  
\end{code}

We say an oplax (lax) covariant (contravariant) lens is univalent just when
each fiber of the underlying family is univalent.

\begin{code}

module _ {𝓤' 𝓥' : Universe} (𝓐 : Refl-Graph 𝓤 𝓥) where

 oplax-covariant-lens-is-univalent : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐
                                   → 𝓤 ⊔ 𝓤' ⊔ 𝓥' ̇
 oplax-covariant-lens-is-univalent 𝓛
  = (x : ⟨ 𝓐 ⟩) → is-univalent-refl-graph (lens-push-graph 𝓛 x)

 lax-contravariant-lens-is-univalent : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐
                                     → 𝓤 ⊔ 𝓤' ⊔ 𝓥' ̇
 lax-contravariant-lens-is-univalent 𝓛
  = (x : ⟨ 𝓐 ⟩) → is-univalent-refl-graph (lens-pull-graph 𝓛 x)

\end{code}

We now define a display of lenses.

\begin{code}

 display-oplax-covariant-lens : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐
                              → Displayed-Refl-Graph 𝓤' 𝓥' 𝓐
 display-oplax-covariant-lens 𝓛 = (lens-push-fam 𝓛 , I , II)
  where
   I : {x y : ⟨ 𝓐 ⟩} → x ≈⟨ 𝓐 ⟩ y → lens-push-fam 𝓛 x → lens-push-fam 𝓛 y → 𝓥' ̇
   I {_} {y} p u v = lens-push 𝓛 p u ≈⟨ lens-push-graph 𝓛 y ⟩ v
   II : {x : ⟨ 𝓐 ⟩} (u : lens-push-fam 𝓛 x) → I (≈-refl 𝓐 x) u u
   II u = lens-push-refl 𝓛 u

 disp⁺ : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐
       → Displayed-Refl-Graph 𝓤' 𝓥' 𝓐
 disp⁺ 𝓛 = display-oplax-covariant-lens 𝓛

 display-lax-contravariant-lens : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐
                                → Displayed-Refl-Graph 𝓤' 𝓥' 𝓐
 display-lax-contravariant-lens 𝓛 = (lens-pull-fam 𝓛 , I , II)
  where
   I : {x y : ⟨ 𝓐 ⟩} → x ≈⟨ 𝓐 ⟩ y → lens-pull-fam 𝓛 x → lens-pull-fam 𝓛 y → 𝓥' ̇
   I {x} p u v = u ≈⟨ lens-pull-graph 𝓛 x ⟩ lens-pull 𝓛 p v
   II : {x : ⟨ 𝓐 ⟩} (u : ⟨ lens-pull-graph 𝓛 x ⟩) → I (≈-refl 𝓐 x) u u
   II u = lens-pull-refl 𝓛 u

 disp⁻ : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐
       → Displayed-Refl-Graph 𝓤' 𝓥' 𝓐
 disp⁻ 𝓛 = display-lax-contravariant-lens 𝓛

\end{code}

We observe the components of the displayed lenses are as we expect.

\begin{code}

 private
  observation
   : (𝓛 : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐)
   → (x : ⟨ 𝓐 ⟩)
   → [ disp⁺ 𝓛 ] x ＝ (⟪ disp⁺ 𝓛 ⟫ x ,
                         (λ u v → u ≈⟨ (disp⁺ 𝓛) ⸴ (≈-refl 𝓐 x) ⟩ v) ,
                         ≈-disp-refl (disp⁺ 𝓛))
  observation 𝓛 x = refl

  observation'
   : (𝓛 : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐)
   → (x : ⟨ 𝓐 ⟩)
   → [ disp⁻ 𝓛 ] x ＝ (⟪ disp⁻ 𝓛 ⟫ x ,
                         (λ u v → u ≈⟨ (disp⁻ 𝓛) ⸴ (≈-refl 𝓐 x) ⟩ v) ,
                         ≈-disp-refl (disp⁻ 𝓛))
  observation' 𝓛 x = refl

\end{code}

Now let's consider the description of fans of displayed lenses.

\begin{code}
 
 compute-fan-of-oplax-covariant-lens
  : (𝓛 : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐)
  → (x : ⟨ 𝓐 ⟩)
  → (u : ⟪ disp⁺ 𝓛 ⟫ x)
  → fan ([ disp⁺ 𝓛 ] x) u
   ＝ fan (lens-push-graph 𝓛 x) (lens-push 𝓛 (≈-refl 𝓐 x) u)
 compute-fan-of-oplax-covariant-lens 𝓛 x u = refl

 compute-cofan-of-lax-contravariant-lens
  : (𝓛 : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐)
  → (x : ⟨ 𝓐 ⟩)
  → (u : ⟪ disp⁻ 𝓛 ⟫ x)
  → cofan ([ disp⁻ 𝓛 ] x) u
   ＝ cofan (lens-pull-graph 𝓛 x) (lens-pull 𝓛 (≈-refl 𝓐 x) u)
 compute-cofan-of-lax-contravariant-lens 𝓛 x u = refl

\end{code}

We now show that if each fiber of a lens is univalent then the displayed
reflexive graph is univalent. The previous observation should provide some
insight into the form of the following proof terms.

\begin{code}

 disp-oplax-covariant-lens-univalent
  : (𝓛 : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐)
  → ((x : ⟨ 𝓐 ⟩) → is-univalent-refl-graph (lens-push-graph 𝓛 x))
  → is-displayed-univalent-refl-graph 𝓐 (disp⁺ 𝓛)
 disp-oplax-covariant-lens-univalent 𝓛 fibers-ua x u 
  = fibers-ua x (lens-push 𝓛 (≈-refl 𝓐 x) u)

 disp-lax-contravariant-lens-univalent
  : (𝓛 : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐)
  → ((x : ⟨ 𝓐 ⟩)
  → is-univalent-refl-graph (lens-pull-graph 𝓛 x))
  → is-displayed-univalent-refl-graph 𝓐 (disp⁻ 𝓛)
 disp-lax-contravariant-lens-univalent 𝓛 fibers-ua x 
  = prop-cofan-to-fan ([ disp⁻ 𝓛 ] x)
     ((λ - → fibers-co-ua (lens-pull 𝓛 (≈-refl 𝓐 x) -))) 
  where
   fibers-co-ua = prop-fan-to-cofan (lens-pull-graph 𝓛 x) (fibers-ua x)
  
\end{code}
