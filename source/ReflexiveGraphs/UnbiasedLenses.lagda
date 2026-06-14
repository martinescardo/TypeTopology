Ian Ray. 4th November 2025.

Minor changes and merged into TypeToplogy in June 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.UnbiasedLenses where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import ReflexiveGraphs.Constructions
open import ReflexiveGraphs.Displayed
open import ReflexiveGraphs.DisplayedUnivalent
open import ReflexiveGraphs.Lenses
open import ReflexiveGraphs.Type
open import ReflexiveGraphs.Univalent

\end{code}

In this file we generalize the two previous notion of lenses, but before diving
into the techincal details we attempt to motivate the notion of an unbiased lens
(see index for link to Jon Sterling's "Reflexive graph lenses in univalent
foundations"). We first note that, not surpisingly, some univalent reflexive
graphs of interest do not arise naturally from the existing notion of lenses.
For example consider an isomorphism of magmas (M , ⊗) ≃ (N , ⊗') which consist
of an equivalence of the underlying types e : M ≃ N that preserves the binary
operation, that is: e (x ⊗ y) ＝ (e x) ⊗' (e y) for all x, y : M. One could
produce the reflexive graph for the type of Magmas from the following displayed
reflexive graph 

          BinOp(M) :≡ M × M → M
          ⊗ ≈⟨ BinOp , e ⟩ ⊗' :≡ (x y : M) → e (x ⊗ y) ＝ (e x) ⊗' (e y)
          ≈-disp-refl BinOp ⊗ :≡ λ x y : M . refl {x ⊗ y}

but notice that this displayed reflexive graph DOES NOT arise from either of
the existing notions of lens. We could consider a similar, albeit assymetric
(or biased!), displayed reflexive graph

          BinOp(M) :≡ M × M → M
          ⊗ ≈⟨ BinOp , e ⟩ ⊗' :≡ (x y : N) → e (e⁻¹ x ⊗  e⁻¹ y) ＝ x ⊗' y
          ≈-disp-refl BinOp ⊗ :≡ λ x y : M . refl {x ⊗ y}

which does arise from an oplax contravariant lens. Aesthetically, the latter
is lacking but more importantly it is awkward to use. What we need is a notion
of lens that allows us to mediate between either side of the edge we are
displaying over. Without further delay we now introduce the notion of an
unbiased lense. (TODO when the examples file is added we should note that the
above Magma example is actually formalized.)

We define the structure of an unbiased lens using a record then collect the
type of unbiased lens as a sigma type.

\begin{code}

record unbiased-lens-structure
 (𝓤' 𝓥' : Universe) (𝓐 : Refl-Graph 𝓤 𝓥)
 (𝓑 : {x y : ⟨ 𝓐 ⟩} → (x ≈⟨ 𝓐 ⟩ y) → Refl-Graph 𝓤' 𝓥') : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
 where
 field
  lext : {x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 p ⟩
  rext : {x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 (≈-refl 𝓐 y) ⟩ → ⟨ 𝓑 p ⟩
  ext-refl : {x : ⟨ 𝓐 ⟩} (u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
           → lext (≈-refl 𝓐 x) u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ rext (≈-refl 𝓐 x) u
  rext-refl : {x : ⟨ 𝓐 ⟩} (u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
            → u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ rext (≈-refl 𝓐 x) u

\end{code}

Although the previous discussion motivating the notion of an unbiased lens
may offer the reader with insight into the first three datum one may have a
moment's pause at the final field rext-refl. You will see below that it is
not necessary for defining a displayed reflexive graph associated to an
unbiased lens, but it will be relevant when showing univalence is inherited.
The reader may wonder why we only include a reflexivity datum for the rext
field? The situation here is similar to that of half-adjoint equivalences
where we must exclude one of the coherences in the interest of ensuring that
being an equivalence is a property (although it is worth noting that the
situation does differ in that the anaglous lext-refl is not derivable from
rext-refl in general).

\begin{code}

Unbiased-Lens : (𝓤' 𝓥' : Universe) (𝓐 : Refl-Graph 𝓤 𝓥)
              → 𝓤 ⊔ 𝓥 ⊔ (𝓤' ⊔ 𝓥')⁺  ̇
Unbiased-Lens 𝓤' 𝓥' 𝓐
 = Σ 𝓑 ꞉ ({x y : ⟨ 𝓐 ⟩} → (x ≈⟨ 𝓐 ⟩ y) → Refl-Graph 𝓤' 𝓥')
    , unbiased-lens-structure 𝓤' 𝓥' 𝓐 𝓑

module _ {𝓤' 𝓥' : Universe} {𝓐 : Refl-Graph 𝓤 𝓥}
         (𝓛@(𝓑 , s) : Unbiased-Lens 𝓤' 𝓥' 𝓐)
       where

 open unbiased-lens-structure s

 unbiased-graph : {x y : ⟨ 𝓐 ⟩} → (x ≈⟨ 𝓐 ⟩ y) → Refl-Graph 𝓤' 𝓥'
 unbiased-graph = 𝓑

 unbiased-fam : {x y : ⟨ 𝓐 ⟩} → (x ≈⟨ 𝓐 ⟩ y) → 𝓤' ̇
 unbiased-fam p = ⟨ unbiased-graph p ⟩

 unbiased-lext : {x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y)
                    → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩
                    → ⟨ 𝓑 p ⟩
 unbiased-lext = lext

 unbiased-rext : {x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y)
                    → ⟨ 𝓑 (≈-refl 𝓐 y) ⟩
                    → ⟨ 𝓑 p ⟩
 unbiased-rext = rext

 unbiased-ext-refl
  : {x : ⟨ 𝓐 ⟩} (u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
  → lext (≈-refl 𝓐 x) u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ rext (≈-refl 𝓐 x) u
 unbiased-ext-refl = ext-refl

 unbiased-rext-refl
  : {x : ⟨ 𝓐 ⟩} (u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
  → u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ rext (≈-refl 𝓐 x) u
 unbiased-rext-refl = rext-refl

\end{code}

Now we define when a unbiased lens is univalent.

\begin{code}

module _ {𝓤' 𝓥' : Universe} (𝓐 : Refl-Graph 𝓤 𝓥) where

 unbiased-lens-is-univalent : Unbiased-Lens 𝓤' 𝓥' 𝓐
                            → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
 unbiased-lens-is-univalent 𝓛 = {x y : ⟨ 𝓐 ⟩} (p : (x ≈⟨ 𝓐 ⟩ y))
                              → is-univalent-refl-graph (unbiased-graph 𝓛 p)

\end{code}

Now we define a display of unbiased lenses.

\begin{code}

 display-unbiased-lens : Unbiased-Lens 𝓤' 𝓥' 𝓐 → Displayed-Refl-Graph 𝓤' 𝓥' 𝓐
 display-unbiased-lens 𝓛 = (I , II , III)
  where
   I : ⟨ 𝓐 ⟩ → 𝓤' ̇
   I x = ⟨ unbiased-graph 𝓛 (≈-refl 𝓐 x) ⟩
   II : {x y : ⟨ 𝓐 ⟩}
      → (x ≈⟨ 𝓐 ⟩ y)
      → ⟨ unbiased-graph 𝓛 (≈-refl 𝓐 x) ⟩
      → ⟨ unbiased-graph 𝓛 (≈-refl 𝓐 y) ⟩
      → 𝓥' ̇
   II p u v = unbiased-lext 𝓛 p u ≈⟨ unbiased-graph 𝓛 p ⟩ unbiased-rext 𝓛 p v
   III : {x : ⟨ 𝓐 ⟩} (u : ⟨ unbiased-graph 𝓛 (≈-refl 𝓐 x) ⟩)
       → II (≈-refl 𝓐 x) u u
   III {x} u = unbiased-ext-refl 𝓛 u

 disp± : Unbiased-Lens 𝓤' 𝓥' 𝓐 → Displayed-Refl-Graph 𝓤' 𝓥' 𝓐
 disp± 𝓛 = display-unbiased-lens 𝓛

 private
  observation
   : (𝓛 : Unbiased-Lens 𝓤' 𝓥' 𝓐)
   → (x : ⟨ 𝓐 ⟩)
   → [ disp± 𝓛 ] x ＝ (⟪ disp± 𝓛 ⟫ x
                       , displayed-edge-rel (disp± 𝓛) (≈-refl 𝓐 x)
                       , ≈-disp-refl (disp± 𝓛))
  observation 𝓛 x = refl

\end{code}

We now look at fans of unbiased lenses.

\begin{code}

 compute-fan-of-unbiased-lens
  : (𝓛 : Unbiased-Lens 𝓤' 𝓥' 𝓐)
  → ((x : ⟨ 𝓐 ⟩)
   → is-univalent-refl-graph (unbiased-graph 𝓛 (≈-refl 𝓐 x)))
  → (x : ⟨ 𝓐 ⟩)
  → (u : ⟪ disp± 𝓛 ⟫ x)
  → fan ([ disp± 𝓛 ] x) u ≃ fan (unbiased-graph 𝓛 (≈-refl 𝓐 x))
                                (unbiased-lext 𝓛 (≈-refl 𝓐 x) u)
 compute-fan-of-unbiased-lens 𝓛@(𝓑 , s) fibers-ua x u = III
  where
   open unbiased-lens-structure s
   I : (v : ⟪ disp± 𝓛 ⟫ x)
     → (rext (≈-refl 𝓐 x) v , rext-refl v) ＝ (v , ≈-refl (𝓑 (≈-refl 𝓐 x)) v)
   I v = fibers-ua x v
          (rext (≈-refl 𝓐 x) v , rext-refl v)
          (v , ≈-refl (𝓑 (≈-refl 𝓐 x)) v)
   II : (v : ⟪ disp± 𝓛 ⟫ x) → rext (≈-refl 𝓐 x) v ＝ v
   II v = ap pr₁ (I v)
   III : (Σ v ꞉ (⟪ disp± 𝓛 ⟫ x) ,
           lext (≈-refl 𝓐 x) u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ rext (≈-refl 𝓐 x) v)
       ≃ (Σ v ꞉ (⟨ 𝓑 (≈-refl 𝓐 x) ⟩) ,
           lext (≈-refl 𝓐 x) u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ v)
   III = Σ-cong (λ v → transport-≃
                        (λ - → lext (≈-refl 𝓐 x) u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ -)
                (II v))

\end{code}

We now show that if each fiber of a unbiased lens is univalent then the
displayed reflexive graph over it is univalent.

\begin{code}

 disp-unbiased-lens-univalent
  : (𝓛 : Unbiased-Lens 𝓤' 𝓥' 𝓐)
  → ((x : ⟨ 𝓐 ⟩)
  → is-univalent-refl-graph (unbiased-graph 𝓛 (≈-refl 𝓐 x)))
  → is-displayed-univalent-refl-graph 𝓐 (disp± 𝓛)
 disp-unbiased-lens-univalent 𝓛 fibers-ua x u 
  = equiv-to-prop
     (compute-fan-of-unbiased-lens 𝓛 fibers-ua x u)
     (fibers-ua x (unbiased-lext 𝓛 (≈-refl 𝓐 x) u))

\end{code}

We can construct unbiased lenses from an oplax covariant lenses.

\begin{code}

 oplax-covariant-to-unbiased-lens : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐
                                  → Unbiased-Lens 𝓤' 𝓥' 𝓐
 oplax-covariant-to-unbiased-lens 𝓛@(𝓑 , s) = (𝓑' , s')
  where
   open oplax-covariant-lens-structure s
   𝓑' : {x y : ⟨ 𝓐 ⟩} → (x ≈⟨ 𝓐 ⟩ y) → Refl-Graph 𝓤' 𝓥'
   𝓑' {x} {y} p = 𝓑 y
   s' : unbiased-lens-structure 𝓤' 𝓥' 𝓐 (λ {x} {y} p → 𝓑 y)
   s' = record
        { lext = λ {x} {y} p u → push p u
        ; rext = λ {x} {y} p u → u 
        ; ext-refl = λ {x} u → push-refl u
        ; rext-refl = λ {x} u → ≈-refl (𝓑 x) u
        }

 disp±̂⁺ : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐 → Unbiased-Lens 𝓤' 𝓥' 𝓐
 disp±̂⁺ 𝓛 = oplax-covariant-to-unbiased-lens 𝓛

\end{code}

We open a new module so we can make the carriers in the arguments of the
induced displayed reflexive graphs explicit in the following observation.

\begin{code}

module _ {𝓤' 𝓥' : Universe} (𝓐 : Refl-Graph 𝓤 𝓥) where

 private
  observation' : (𝓛 : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐)
               → disp⁺ 𝓐 𝓛 ＝ disp± 𝓐 (disp±̂⁺ 𝓐 𝓛)
  observation' 𝓛 = refl

\end{code}

We now construct an unbiased lense from lax contravariant lenses.

\begin{code}

 lax-contravariant-to-unbiased-lens : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐
                                    → Unbiased-Lens 𝓤' 𝓥' 𝓐
 lax-contravariant-to-unbiased-lens 𝓛@(𝓑 , s) = (𝓑' , s')
  where
   open lax-contravariant-lens-structure s
   𝓑' : {x y : ⟨ 𝓐 ⟩} → (x ≈⟨ 𝓐 ⟩ y) → Refl-Graph 𝓤' 𝓥'
   𝓑' {x} {y} p = 𝓑 x
   s' : unbiased-lens-structure 𝓤' 𝓥' 𝓐 (λ {x} {y} p → 𝓑 x)
   s' = record
        { lext = λ {x} {y} p u → u
        ; rext = λ {x} {y} p u → pull p u
        ; ext-refl = λ {x} u → pull-refl u
        ; rext-refl = λ {x} u → pull-refl u
        }

 disp±⁻ : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐 → Unbiased-Lens 𝓤' 𝓥' 𝓐
 disp±⁻ 𝓛 = lax-contravariant-to-unbiased-lens 𝓛

module _ {𝓤' 𝓥' : Universe} (𝓐 : Refl-Graph 𝓤 𝓥) where

 private
  observation'' : (𝓛 : Lax-Contravariant-Lens 𝓤' 𝓥' 𝓐)
                → disp⁻ 𝓐 𝓛 ＝ disp± 𝓐 (disp±⁻ 𝓐 𝓛)
  observation'' 𝓛 = refl

\end{code}
