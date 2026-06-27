Ian Ray. 4th November 2025.

Minor changes and merged into TypeToplogy in June 2026.

We provide some applications of (displayed) univalent reflexive graphs to
existing identity characterization results. This provides evidence that DURGs
provide a unified framework for developing structured identity principles (SIP).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.Examples where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Pullback
open import UF.Sets
open import UF.Sets-Properties
open import UF.SIP
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.Univalence
open import UF.UA-FunExt
open import ReflexiveGraphs.Constructions
open import ReflexiveGraphs.Displayed
open import ReflexiveGraphs.DisplayedUnivalent
open import ReflexiveGraphs.Lenses
open import ReflexiveGraphs.Properties
open import ReflexiveGraphs.Type
open import ReflexiveGraphs.UnbiasedLenses
open import ReflexiveGraphs.Univalent
open import ReflexiveGraphs.UnivalentClosureProperties
open import ReflexiveGraphs.UnivalentFamilies

\end{code}

We can recover the standard characterization of the identity type of products
using discrete reflexive graphs.

\begin{code}

product-characterization-from-univalent-refl-graphs
 : {A : 𝓤 ̇} {B : 𝓥 ̇} {a a' : A} {b b' : B}
 → ((a , b) ＝ (a' , b')) ≃ (a ＝ a') × (b ＝ b')
product-characterization-from-univalent-refl-graphs
 {_} {_} {A} {B} {a} {a'} {b} {b'}
 = id-equiv-edge ((Δ A) ⊗ (Δ B) , I) (a , b) (a' , b')
 where
  I : is-univalent-refl-graph ((Δ A) ⊗ (Δ B))
  I = univalence-closed-under-× (Δ A) (Δ B)
       (discrete-refl-graph-is-univalent A) (discrete-refl-graph-is-univalent B)

\end{code}

Similarly for Sigma types.

\begin{code}

sigma-characterization-from-univalent-refl-graphs
 : {A : 𝓤 ̇} {B : A → 𝓥 ̇} {a a' : A} {b : B a} {b' : B a'}
 → ((a , b) ＝ (a' , b')) ≃ (Σ p ꞉ (a ＝ a') , transport B p b ＝ b')
sigma-characterization-from-univalent-refl-graphs
 {𝓤} {𝓥} {A} {B} {a} {a'} {b} {b'}
 = id-equiv-edge ((∐ a ˸ A , (Δ (B a))) , I) (a , b) (a' , b')
 where
  I : is-univalent-refl-graph (∐ a ˸ A , (Δ (B a)))
  I = univalence-closed-under-Σ A (λ a → Δ (B a))
       (λ a → discrete-refl-graph-is-univalent (B a))

\end{code}

This is simply a sanity check for the theory we have developed. We now
wish to move towards a more unified approach to SIP, by working through
some illustrative examples.

Example 1:

We give a detailed characaterization of the identity type of cones over a
cospan using reflexive graphs. This illustration is not intended to be brief.

Two cones with commutative graphs witnessed by 

               q                                  q'
        A ─────────→ X                      A ─────────→ X       
        │            │                      │            │
  H : p │            │ g            H' : p' │            │ g
        │            │                      │            │
        ↓            ↓                      ↓            ↓
        Y ─────────→ Z                      Y ─────────→ Z
                f                                 f

are the same when we have homotopies α : p ∼ p' and β : q ∼ q' and a natural
coherence

                           H
                 f ∘ p  ───────→ g ∘ q
                   |               |
               α*  |               |  β*
                   |               |
                   ↓               ↓
                 f ∘ p' ───────→ g ∘ q'
                           H'
between the homotopies.

\begin{code}

module _ (fe : Fun-Ext) {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
         (f : X → Z) (g : Y → Z)
       where

 open pullback f g

\end{code}

We define reflexive graph structure on the base of cone whose underlying type
must be (A → X) × (A → Y) with edges corresponding to the pair of homotopes
p ∼ p' and q ∼ q'.

\begin{code}

 cone-base-refl-graph : (A : 𝓣 ̇) → Refl-Graph (𝓤 ⊔ 𝓥 ⊔ 𝓣) (𝓤 ⊔ 𝓥 ⊔ 𝓣)
 cone-base-refl-graph {𝓣} A
  = (((A → X) × (A → Y)) , I , II)
  where
   I : ((A → X) × (A → Y))
     → ((A → X) × (A → Y))
     → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
   I (p , q) (p' , q') = (p ∼ p') × (q ∼ q')
   II : ((p , q) : (A → X) × (A → Y)) → (p ∼ p) × (q ∼ q) 
   II (p , q) = (∼-refl , ∼-refl)

\end{code}

That this reflexive graph is univalent is automatic as univalence is closed
under products, functions and the discrete reflexive graph.

\begin{code}
     
 cone-base-is-univalent : (A : 𝓣 ̇)
                        → is-univalent-refl-graph (cone-base-refl-graph A)
 cone-base-is-univalent A = univalence-closed-under-×
                             (A ➙ (Δ X)) (A ➙ (Δ Y))
                             (univalence-closed-under-cotensor fe A (Δ X)
                              (discrete-refl-graph-is-univalent X))
                             (univalence-closed-under-cotensor fe A (Δ Y)
                              (discrete-refl-graph-is-univalent Y))

\end{code}

We now give the structure of a displayed reflexive graph over the base
whose type family takes pairs of maps and returns commutative squares. The
edges correspond to the natural coherence condition mentioned above.

\begin{code}
                              
 cone-displayed-refl-graph
  : (A : 𝓣 ̇)
  → Displayed-Refl-Graph (𝓦 ⊔ 𝓣) (𝓦 ⊔ 𝓣) (cone-base-refl-graph A)
 cone-displayed-refl-graph {𝓣} A
  = (commutative-square , I , II)
  where
   I : {(p , q) (p' , q') : (A → X) × (A → Y)}
       ((α , β) : (p ∼ p') × (q ∼ q'))
     → commutative-square (p , q)
     → commutative-square (p' , q')
     → 𝓦 ⊔ 𝓣 ̇
   I (α , β) H H' = ∼-trans H (∼-ap-∘ g β) ∼ ∼-trans (∼-ap-∘ f α) H'
   II : {(p , q) : (A → X) × (A → Y)}
        (H : commutative-square (p , q))
      → ∼-trans H ∼-refl ∼ ∼-trans ∼-refl H
   II H x = refl-left-neutral ⁻¹

\end{code}

To see that the displayed reflexive graph is univalent we only have to look
at the fibers. The luxury here is that the base edges are taken to be the
reflexive data. The fan of interest here is equivalent to a fan over what is
essentially the discrete reflexive graph of f ∘ p ∼ g ∘ q (which is manifestly
univalent).

\begin{code}

 cone-display-is-univalent
  : (A : 𝓣 ̇)
  → is-displayed-univalent-refl-graph (cone-base-refl-graph A)
     (cone-displayed-refl-graph A) 
 cone-display-is-univalent A (p , q) H
  = equiv-to-prop I
     (univalence-closed-under-Π fe A (λ - → Δ (f (p -) ＝ g (q -)))
      (λ - → discrete-refl-graph-is-univalent (f (p -) ＝ g (q -))) H)
  where
   I : fan ([ cone-displayed-refl-graph A ] (p , q)) H
     ≃ fan (∏ x ˸ A , (Δ (f (p x) ＝ g (q x)))) H
   I = (Σ H' ꞉ commutative-square (p , q) ,
        ∼-trans H ∼-refl ∼ ∼-trans ∼-refl H')
                                                           ≃⟨ II ⟩
       (Σ H' ꞉ commutative-square (p , q) , H ∼ H')        ■
    where
     II = Σ-cong (λ - → transport-≃ (λ - → H ∼ -)
          (dfunext fe (λ x → refl-left-neutral)))

\end{code}

The hard work is done. Since we have a displayed univalent reflexive graph
over a univalent reflexive graph the total reflexive graph is also univalent.
The carrier of this total reflexive graph corresponds to the type of cones.

\begin{code}

 cone-total-refl-graph : (A : 𝓣 ̇) → Refl-Graph (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣)
 cone-total-refl-graph A
  = (cone-base-refl-graph A ﹐ cone-displayed-refl-graph A)

 private
  observation : (A : 𝓣 ̇)
              → ⟨ cone-total-refl-graph A ⟩ ＝ cone A
  observation A = refl

 cone-total-is-univalent : (A : 𝓣 ̇)
                         → is-univalent-refl-graph (cone-total-refl-graph A)
 cone-total-is-univalent A
  = univalence-closed-under-total
     (cone-base-refl-graph A)
     (cone-displayed-refl-graph A)
     (cone-base-is-univalent A)
     (cone-display-is-univalent A)

 cone-＝-characterization
  : {A : 𝓣 ̇ } {p p' : A → X} {q q' : A → Y}
    {H : f ∘ p ∼ g ∘ q} {H' : f ∘ p' ∼ g ∘ q'}
  → (((p , q) , H) ＝ ((p' , q') , H'))
  ≃ (Σ (α , β) ꞉ (p ∼ p') × (q ∼ q') ,
     ∼-trans H (∼-ap-∘ g β) ∼ ∼-trans (∼-ap-∘ f α) H')
 cone-＝-characterization {𝓣} {A} {p} {p'} {q} {q'} {H} {H'}
  = id-equiv-edge (cone-total-refl-graph A , cone-total-is-univalent A)
     ((p , q) , H) ((p' , q') , H')

\end{code}

Example 2:

We now use lenses to generalize an existing characterization of transport (see
file UF.FundamentalLemmaOfTransportAlongEquivalences). We start by defining
transport along an edge.

\begin{code}

module _ (𝓐 : Refl-Graph 𝓤 𝓥) (ua-𝓐 : is-univalent-refl-graph 𝓐)
       where

 transport-along-≈ : (P : ⟨ 𝓐 ⟩ → 𝓣 ̇) {x y : ⟨ 𝓐 ⟩}
                   → x ≈⟨ 𝓐 ⟩ y
                   → P x → P y
 transport-along-≈ P e = transport P (edge-to-id (𝓐 , ua-𝓐) e)

 transport-along-≈-comp : (P : ⟨ 𝓐 ⟩ → 𝓣 ̇) {x : ⟨ 𝓐 ⟩}
                        → (u : P x)
                        → transport-along-≈ P (≈-refl 𝓐 x) u ＝ u
 transport-along-≈-comp P u
  = transport (λ - → transport P - u ＝ u)
     (edge-to-id-preserves-refl (𝓐 , ua-𝓐) ⁻¹) refl

\end{code}

We now show that if a univalent reflexive graph has an oplax covariant lens
structure on it then push and transport share an edge.

\begin{code}

module _ {𝓤' 𝓥' : Universe}
         (𝓐 : Refl-Graph 𝓤 𝓥) (ua-𝓐 : is-univalent-refl-graph 𝓐)
         (𝓛@(𝓑 , s) : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐)
       where

 open oplax-covariant-lens-structure s

 fundamental-theorem-of-transport-for-edges
  : {x y : ⟨ 𝓐 ⟩}
  → (e : x ≈⟨ 𝓐 ⟩ y)
  → (u : ⟨ 𝓑 x ⟩)
  → push e u ≈⟨ 𝓑 y ⟩ transport-along-≈ 𝓐 ua-𝓐 (lens-push-fam 𝓛) e u
 fundamental-theorem-of-transport-for-edges {x} {y} = I II IV x y
  where
   I : edge-induction 𝓐
   I = univalence-implies-edge-induction 𝓐 ua-𝓐
   II : (x y : ⟨ 𝓐 ⟩) → x ≈⟨ 𝓐 ⟩ y → 𝓤' ⊔ 𝓥' ̇
   II x y e = (u : ⟨ 𝓑 x ⟩)
            → push e u ≈⟨ 𝓑 y ⟩ transport-along-≈ 𝓐 ua-𝓐 (lens-push-fam 𝓛) e u
   III : (x : ⟨ 𝓐 ⟩) (u : ⟨ 𝓑 x ⟩)
       → u ＝ transport-along-≈ 𝓐 ua-𝓐 (lens-push-fam 𝓛) (≈-refl 𝓐 x) u
   III x u = transport-along-≈-comp 𝓐 ua-𝓐 (lens-push-fam 𝓛) u ⁻¹
   IV : (x : ⟨ 𝓐 ⟩) (u : ⟨ 𝓑 x ⟩)
      → push (≈-refl 𝓐 x) u
      ≈⟨ 𝓑 x ⟩ transport-along-≈ 𝓐 ua-𝓐 (lens-push-fam 𝓛) (≈-refl 𝓐 x) u
   IV x u = transport (λ - → push (≈-refl 𝓐 x) u ≈⟨ 𝓑 x ⟩ -) (III x u)
             (push-refl u)

\end{code}

If the oplax lens is itself univalent then we can upgrade the edge to an
identity.

\begin{code}

module _ {𝓤' 𝓥' : Universe}
         (𝓐 : Refl-Graph 𝓤 𝓥) (ua-𝓐 : is-univalent-refl-graph 𝓐)
         (𝓛@(𝓑 , s) : Oplax-Covariant-Lens 𝓤' 𝓥' 𝓐)
         (ua-𝓛 : oplax-covariant-lens-is-univalent 𝓐 𝓛)
       where

 open oplax-covariant-lens-structure s

 fundamental-theorem-of-transport
  : {x y : ⟨ 𝓐 ⟩}
  → (e : x ≈⟨ 𝓐 ⟩ y)
  → push e ∼ transport-along-≈ 𝓐 ua-𝓐 (lens-push-fam 𝓛) e
 fundamental-theorem-of-transport {x} {y} e u
  = edge-to-id (𝓑 y , ua-𝓛 y)
     (fundamental-theorem-of-transport-for-edges 𝓐 ua-𝓐 𝓛 e u)

\end{code}

It is worth noting that this result follows immediatly from the fact that
oplax structure is in fact a property, but this avenue requires function
extensionality.

\begin{code}

 private
  transport-along-≈-is-oplax-structure
   : oplax-covariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑
  transport-along-≈-is-oplax-structure
   = record {push = I ; push-refl = II}
   where
    I : {x y : ⟨ 𝓐 ⟩} → (x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 x ⟩ → ⟨ 𝓑 y ⟩
    I {x} {y} = transport-along-≈ 𝓐 ua-𝓐 (lens-push-fam 𝓛)
    II : {x : ⟨ 𝓐 ⟩} (u : ⟨ 𝓑 x ⟩)
       → (I (≈-refl 𝓐 x) u) ≈⟨ 𝓑 x ⟩ u
    II {x} u = id-to-edge (𝓑 x)
                (transport-along-≈-comp 𝓐 ua-𝓐 (lens-push-fam 𝓛) u)

  oplax-＝-transport-structure
   : Fun-Ext
   → s ＝ transport-along-≈-is-oplax-structure
  oplax-＝-transport-structure fe
   = oplax-lens-structure-is-a-property fe 𝓤' 𝓥' 𝓐 𝓑 ua-𝓐 ua-𝓛
      s transport-along-≈-is-oplax-structure

  unique-transport-observation
   : Fun-Ext
   → {x y : ⟨ 𝓐 ⟩}
   → (e : x ≈⟨ 𝓐 ⟩ y)
   → push e ∼ transport-along-≈ 𝓐 ua-𝓐 (lens-push-fam 𝓛) e
  unique-transport-observation fe e u
   = ap (λ - → lens-push (𝓑 , -) e u) (oplax-＝-transport-structure fe)

\end{code}

If one instantiates the previous theorem with the reflexive graph on a univalent
universe the previous theorem reduces to what is observed in the previously
mentioned file UF.FundamentalLemmaOfTransportAlongEquivalences. In fact, before
moving to the next example we observe that univalent universes form a univalent
family (which is a specific form of univalent reflexive graph), although we wont
explicitly record the previously mentioned observation.

\begin{code}

universe-refl-graph : (𝓤 : Universe)
                    → Refl-Graph (𝓤 ⁺) 𝓤
universe-refl-graph 𝓤 = refl-graph-image (𝓤  ̇) id

univalent-universe-is-univalent-family : is-univalent 𝓤
                                       → funext (𝓤 ⁺) 𝓤
                                       → is-univalent-family ((𝓤  ̇) , id)
univalent-universe-is-univalent-family {𝓤} ua fe
 = id-to-edge-equiv-implies-prop-fans (universe-refl-graph 𝓤)
    (λ X Y → transport is-equiv (II X Y) (ua X Y))
 where
  I : (X Y : 𝓤  ̇)
    → idtoeq X Y ∼ id-to-edge (universe-refl-graph 𝓤) {X} {Y}
  I X Y refl = refl
  II : (X Y : 𝓤  ̇)
     → idtoeq X Y ＝ id-to-edge (universe-refl-graph 𝓤) {X} {Y}
  II X Y = dfunext fe (I X Y)

universe-univalent-refl-graph : is-univalent 𝓤
                              → funext (𝓤 ⁺) 𝓤
                              → Univalent-Refl-Graph (𝓤 ⁺) 𝓤
universe-univalent-refl-graph {𝓤} ua fe
 = (universe-refl-graph 𝓤 , univalent-universe-is-univalent-family ua fe)

\end{code}

TODO: Consider how to prove the universe reflexive graph is univalent without
function extensionality.

Example 3:

We record the logical equivalence between displayed univalent reflexive graphs
over the reflexive graph on a univalent universe and the standard notion of
structure (SNS) (see UF.SIP) already present in the TypeTopology library.

\begin{code}

open sip hiding (⟨_⟩)

displayed-univalent-refl-graph-to-SNS
 : {𝓤 𝓣 𝓦 : Universe}
 → Fun-Ext
 → (((B , _ , _) , _) : Displayed-Univalent-Refl-Graph 𝓣 𝓦
                         (universe-refl-graph 𝓤))
 → SNS B 𝓦
displayed-univalent-refl-graph-to-SNS {𝓤} {𝓣} {𝓦} fe (𝓑@(B , R , r) , ua)
 = (I , II , III)
 where
  I : ((X , _) (Y , _) : Σ B) → X ≃ Y → 𝓦 ̇
  I X Y e = structure X ≈⟨ 𝓑 ⸴ e ⟩ structure Y
  II : ((X , _) : Σ B) → I (X , _) (X , _) (≃-refl X)
  II X = r (structure X)
  obs : {X : 𝓤 ̇} (s t : B X)
      → id-to-edge ([ 𝓑 ] X) {s} {t} ＝ canonical-map I II s t
  obs {X} s t = dfunext fe obs'
   where
    obs'
     : id-to-edge (component-refl-graph (B , R , r) X) ∼ canonical-map I II s t 
    obs' refl = refl
  III : {X : 𝓤 ̇} (s t : B X)
      → is-equiv (canonical-map I II s t)
  III {X} s t = transport is-equiv (obs s t)
                 (prop-fans-implies-id-to-edge-equiv ([ 𝓑 ] X) (ua X) s t)

SNS-to-displayed-univalent-refl-graph
 : {𝓤 𝓣 𝓦 : Universe}
 → Fun-Ext
 → (B : 𝓤 ̇ → 𝓣 ̇)
 → SNS B 𝓦 
 → Displayed-Univalent-Refl-Graph 𝓣 𝓦 (universe-refl-graph 𝓤)
SNS-to-displayed-univalent-refl-graph {𝓤} {𝓣} {𝓦} fe B (ι , ρ , θ)
 = ((B , I , II) , III)
 where
  I : {X Y : ⟨ universe-refl-graph 𝓤 ⟩}
    → edge-rel (universe-refl-graph 𝓤) X Y
    → B X
    → B Y
    → 𝓦 ̇
  I {X} {Y} e s t = ι (X , s) (Y , t) e
  II : {X : ⟨ universe-refl-graph 𝓤 ⟩} (u : B X)
     → ι (X , u) (X , u) (≈-refl (universe-refl-graph 𝓤) X)
  II {X} u = ρ (X , u)
  obs : {X : 𝓤 ̇} (s t : B X)
      → canonical-map ι ρ s t ＝ id-to-edge ([ (B , I , II) ] X)
  obs {X} s t = dfunext fe obs'
   where
    obs'
     : canonical-map ι ρ s t ∼ id-to-edge (component-refl-graph (B , I , II) X)
    obs' refl = refl
  III : is-displayed-univalent-refl-graph (universe-refl-graph 𝓤)
         (B , I , II)
  III X u = id-to-edge-equiv-implies-prop-fans ([ (B , I , II) ] X)
             (λ s t → transport is-equiv (obs s t) (θ s t)) u

\end{code}

TODO characterize ＝ of displayed refl graphs and finish the proof of
equivalence stated below.

displayed-univalent-refl-graph-≃-SNS
 : {𝓤 𝓣 𝓦 : Universe}
 → Fun-Ext
 → (displayed-univalent-refl-graph 𝓣 𝓦 (universe-refl-graph 𝓤))
 ≃ (Σ B ꞉ (𝓤 ̇ → 𝓣 ̇) , SNS B 𝓦)
displayed-univalent-refl-graph-≃-SNS fe
 = (I , qinvs-are-equivs I (II , III , IV))
 where
  I : (displayed-univalent-refl-graph 𝓣 𝓦 (universe-refl-graph 𝓤))
    → (Σ B ꞉ (𝓤 ̇ → 𝓣 ̇) , SNS B 𝓦)
  I (𝓑@((B , _ , _) , _)) = (B , displayed-univalent-refl-graph-to-SNS fe 𝓑)
  II : (Σ B ꞉ (𝓤 ̇ → 𝓣 ̇) , SNS B 𝓦)
     → (displayed-univalent-refl-graph 𝓣 𝓦 (universe-refl-graph 𝓤))
  II (B , sns) = SNS-to-displayed-univalent-refl-graph fe B sns
  III : II ∘ I ∼ id
  III ((B , R , r) , ua) = ?
  IV : I ∘ II ∼ id
  IV (B , (ι , ρ , θ)) = ?

Example 4:

We conclude this example file (for now) with a comparison of characterizations
of the identity type of ∞-magmas. The former characterization directly via
displayed reflexive graphs (but by the above observation this is equivalent to
a characterization via SNS) and the latter via unbiased lenses. 

\begin{code}

∞-Magma : (𝓤 : Universe) → (𝓤 ⁺) ̇
∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X)

\end{code}

We now define a displayed reflexive graph over 𝓤 of binary operations.

\begin{code}

bin-op-displayed-refl-graph
 : (𝓤 : Universe)
 → Displayed-Refl-Graph 𝓤 𝓤 (universe-refl-graph 𝓤)
bin-op-displayed-refl-graph 𝓤
 = ((λ X → (X → X → X)) , I , II)
 where
  I : {X Y : 𝓤 ̇}
    → (X ≃ Y)
    → (X → X → X)
    → (Y → Y → Y)
    → 𝓤 ̇
  I {X} {_} e _·X_ _·Y_ = (x y : X) → ⌜ e ⌝ (x ·X y) ＝ (⌜ e ⌝ x ·Y ⌜ e ⌝ y)
  II : {X : 𝓤 ̇}
     → (_·X_ : X → X → X)
     → (x y : X)
     → (x ·X y) ＝ (x ·X y)
  II _·X_ x y = refl

bin-op-disp-is-univalent
 : (fe : Fun-Ext) (𝓤 : Universe)
 → is-displayed-univalent-refl-graph (universe-refl-graph 𝓤)
    (bin-op-displayed-refl-graph 𝓤)
bin-op-disp-is-univalent fe 𝓤 X _·X_
 = equiv-to-prop I
    (Π-is-prop fe (λ x → Π-is-prop fe λ y
      → singletons-are-props (singleton-types-are-singletons (x ·X y))))
 where
  I : fan ([ bin-op-displayed-refl-graph 𝓤 ] X) _·X_
    ≃ ((x y : X) → Σ z ꞉ X , x ·X y ＝ z)
  I = (Σ _·X'_ ꞉ (X → X → X) , ((x y : X) → x ·X y ＝ x ·X' y)) ≃⟨ II ⟩
      ((x y : X) → Σ z ꞉ X , x ·X y ＝ z)                       ■
   where
    II = ≃-sym (≃-comp (Π-cong fe fe (λ x → ΠΣ-distr-≃)) ΠΣ-distr-≃)

\end{code}

Now we can give the total univalent reflexive graph whose carrier is the type
of ∞-magmas and then characterize the type of identifications of them.

\begin{code}

∞-Magma-total-refl-graph : (𝓤 : Universe)
                         → Refl-Graph (𝓤 ⁺) 𝓤
∞-Magma-total-refl-graph 𝓤
 = (universe-refl-graph 𝓤 ﹐ bin-op-displayed-refl-graph 𝓤)

private
 observation : (𝓤 : Universe)
              → ⟨ ∞-Magma-total-refl-graph 𝓤 ⟩ ＝ ∞-Magma 𝓤
 observation 𝓤 = refl

∞-Magma-total-univalent-refl-graph
 : (𝓤 : Universe)
 → is-univalent 𝓤
 → Fun-Ext
 → is-univalent-refl-graph (∞-Magma-total-refl-graph 𝓤)
∞-Magma-total-univalent-refl-graph 𝓤 ua fe
 = univalence-closed-under-total
    (universe-refl-graph 𝓤)
    (bin-op-displayed-refl-graph 𝓤)
    (univalent-universe-is-univalent-family ua fe)
    (bin-op-disp-is-univalent fe 𝓤)

∞-Magma-＝-char
 : {𝓤 : Universe} 
 → Fun-Ext
 → is-univalent 𝓤
 → ((X , _·X_) (Y , _·Y_) : ∞-Magma 𝓤) 
 → ((X , _·X_) ＝ (Y , _·Y_))
  ≃ (Σ e ꞉ X ≃ Y , ((x y : X) → ⌜ e ⌝ (x ·X y) ＝ (⌜ e ⌝ x ·Y ⌜ e ⌝ y)))
∞-Magma-＝-char {𝓤} fe ua (X , _·X_) (Y , _·Y_)
 = id-equiv-edge
    (∞-Magma-total-refl-graph 𝓤 , ∞-Magma-total-univalent-refl-graph 𝓤 ua fe)
    (X , _·X_) (Y , _·Y_)

\end{code}

We may instead utilize the unbiased lense machinary, which allows us to
characterize structures that have 'mixed variance'.

\begin{code}

∞-Magma-unbiased-lens
 : (𝓤 : Universe)
 → Unbiased-Lens 𝓤 𝓤 (universe-refl-graph 𝓤)
∞-Magma-unbiased-lens 𝓤 =
 (I , record
       { lext = λ e u → λ x x' → ⌜ e ⌝ (u x x')
       ; rext = λ e u → λ x x' → u (⌜ e ⌝ x) (⌜ e ⌝ x')
       ; ext-refl = λ u x x' → refl
       ; rext-refl = λ u x x' → refl
       })
 where
  I : {x y : ⟨ universe-refl-graph 𝓤 ⟩}
    → x ≈⟨ universe-refl-graph 𝓤 ⟩ y
    → Refl-Graph 𝓤 𝓤
  I {X} {Y} e = X ➙ (X ➙ (Δ Y))

∞-Magma-unbiased-lens-is-univalent
 : (𝓤 : Universe)
 → Fun-Ext
 → unbiased-lens-is-univalent (universe-refl-graph 𝓤)
    (∞-Magma-unbiased-lens 𝓤)
∞-Magma-unbiased-lens-is-univalent 𝓤 fe {X} {Y} p
 = univalence-closed-under-cotensor fe X (X ➙ (Δ Y))
    (univalence-closed-under-cotensor fe X (Δ Y)
     (discrete-refl-graph-is-univalent Y))

∞-Magma-unbiased-lens-display
 : (𝓤 : Universe)
 → Displayed-Refl-Graph 𝓤 𝓤 (universe-refl-graph 𝓤)
∞-Magma-unbiased-lens-display 𝓤
 = disp± (universe-refl-graph 𝓤) (∞-Magma-unbiased-lens 𝓤)

∞-Magma-unbiased-lens-display-univalent
 : (𝓤 : Universe)
 → Fun-Ext
 → is-displayed-univalent-refl-graph (universe-refl-graph 𝓤)
    (∞-Magma-unbiased-lens-display 𝓤)
∞-Magma-unbiased-lens-display-univalent 𝓤 fe
 = disp-unbiased-lens-univalent (universe-refl-graph 𝓤)
    (∞-Magma-unbiased-lens 𝓤)
     (λ x → ∞-Magma-unbiased-lens-is-univalent 𝓤 fe
            (≃-refl x))

∞-Magma-unbiased-lens-total
 : (𝓤 : Universe)
 → Refl-Graph (𝓤 ⁺) 𝓤
∞-Magma-unbiased-lens-total 𝓤 
 = universe-refl-graph 𝓤 ﹐ ∞-Magma-unbiased-lens-display 𝓤

private
 obs1 : (𝓤 : Universe)
      → ⟨ ∞-Magma-unbiased-lens-total 𝓤 ⟩ ＝ ∞-Magma 𝓤
 obs1 𝓤 = refl

∞-Magma-unbiased-lens-total-univalent
 : (𝓤 : Universe)
 → is-univalent 𝓤
 → Fun-Ext
 → is-univalent-refl-graph (∞-Magma-unbiased-lens-total 𝓤)
∞-Magma-unbiased-lens-total-univalent 𝓤 ua fe
 = univalence-closed-under-total
    (universe-refl-graph 𝓤)
    (∞-Magma-unbiased-lens-display 𝓤)
    (univalent-universe-is-univalent-family ua fe)
    (∞-Magma-unbiased-lens-display-univalent 𝓤 fe)

∞-Magma-unbiased-lens-＝-char
 : {𝓤 : Universe}  
 → Fun-Ext
 → is-univalent 𝓤
 → ((X , _·X_) (Y , _·Y_) : ∞-Magma 𝓤) 
 → ((X , _·X_) ＝ (Y , _·Y_))
  ≃ (Σ e ꞉ X ≃ Y , ((x y : X) → ⌜ e ⌝ (x ·X y) ＝ (⌜ e ⌝ x ·Y ⌜ e ⌝ y)))
∞-Magma-unbiased-lens-＝-char {𝓤} fe ua (X , _·X_) (Y , _·Y_)
 = id-equiv-edge
    (∞-Magma-unbiased-lens-total 𝓤
     , ∞-Magma-unbiased-lens-total-univalent 𝓤 ua fe)
    (X , _·X_) (Y , _·Y_)

\end{code}

Appealing simply to line counting one could not justify the latter approach to
characterizing the identity type of ∞-Magma. But we would like to point out a
few advantages. We get the displayed reflexive graph (and its univalence) for
free just by identifying what we want the left and right hand side of the
equation relating the mixed variance data to be. This offers a blueprint for
characterizing mixed variance structures of increasingly complicated nature
where "guessing" (or maybe it is more apt to say "being clever") is not
feasible.

The following should probably be deleted or heavily improved...

We show that propositional valued families on univalent reflexive graphs induce
displayed univalent reflexive graphs such that the resulting total univalent
reflexive graph contains no new edge information.

\begin{code}

discrete-displayed-reflexive-graph : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥)
                                   → (⟨ 𝓐 ⟩ᵤ → 𝓣 ̇)
                                   → Displayed-Refl-Graph 𝓣 𝓣 (𝓐 /ᵤ)
discrete-displayed-reflexive-graph {_} {_} {𝓣} 𝓐 B = (B , I , II)
 where
  I : {x y : ⟨ 𝓐 ⟩ᵤ} → x ≈ᵤ⟨ 𝓐 ⟩ y → B x → B y → 𝓣 ̇
  I e u v = transport B (edge-to-id 𝓐 e) u ＝ v
  II : {x : ⟨ 𝓐 ⟩ᵤ} (u : B x)
     → I (≈-refl (𝓐 /ᵤ) x) u u
  II u = transport (λ - → transport B - u ＝ u)
          (edge-to-id-preserves-refl 𝓐 ⁻¹) refl

syntax discrete-displayed-reflexive-graph 𝓐 B = 𝓐 Δ B

prop-display-univalent
 : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥)
 → (B : ⟨ 𝓐 ⟩ᵤ → 𝓣 ̇)
 → ((x : ⟨ 𝓐 ⟩ᵤ) → is-prop (B x))
 → is-displayed-univalent-refl-graph (𝓐 /ᵤ) (𝓐 Δ B)
prop-display-univalent 𝓐 B B-prop x u = Σ-is-prop (B-prop x) I
 where
  I : (v : B x) → is-prop (u ≈⟨ 𝓐 Δ B ⸴ ≈-refl (𝓐 /ᵤ) x ⟩ v)
  I v = props-are-sets (B-prop x)

prop-display-total-univalent : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥)
                             → (B : ⟨ 𝓐 ⟩ᵤ → 𝓣 ̇)
                             → ((x : ⟨ 𝓐 ⟩ᵤ) → is-prop (B x))
                             → is-univalent-refl-graph ((𝓐 /ᵤ) ﹐ (𝓐 Δ B))
prop-display-total-univalent 𝓐 B B-prop
 = univalence-closed-under-total (𝓐 /ᵤ) (𝓐 Δ B)
    (underlying-refl-graph-is-univalent 𝓐)
    (prop-display-univalent 𝓐 B B-prop)

prop-display-total-edge-char
 : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥)
 → (B : ⟨ 𝓐 ⟩ᵤ → 𝓣 ̇)
 → ((x : ⟨ 𝓐 ⟩ᵤ) → is-prop (B x))
 → (x y : ⟨ 𝓐 ⟩ᵤ) (u : B x) (v : B y)
 → (x , u) ≈⟨ (𝓐 /ᵤ) ﹐ (𝓐 Δ B) ⟩ (y , v) ≃ x ≈ᵤ⟨ 𝓐 ⟩ y
prop-display-total-edge-char 𝓐 B B-prop x y u v
 = (x , u) ≈⟨ (𝓐 /ᵤ) ﹐ (𝓐 Δ B) ⟩ (y , v)                     ≃⟨by-definition⟩
   (Σ e ꞉ x ≈ᵤ⟨ 𝓐 ⟩ y , transport B (edge-to-id 𝓐 e) u ＝ v) ≃⟨ I ⟩ 
   x ≈ᵤ⟨ 𝓐 ⟩ y                                               ■
    where
     I = pr₁-≃ (x ≈ᵤ⟨ 𝓐 ⟩ y) (λ - → transport B (edge-to-id 𝓐 -) u ＝ v)
          (λ - → pointed-props-are-singletons
                  (B-prop y (transport B (edge-to-id 𝓐 -) u) v)
                  (props-are-sets (B-prop y)))

\end{code}

We use this fact to give a characterization of the identity type of hSets
(although this is by no means better than existing characterizations).

\begin{code}

hSet-refl-graph : is-univalent 𝓤
                → funext (𝓤 ⁺) 𝓤
                → Refl-Graph (𝓤 ⁺) 𝓤
hSet-refl-graph {𝓤} ua fe
 = universe-refl-graph 𝓤 ﹐ (universe-univalent-refl-graph ua fe Δ is-set)

private
  observation-I : (ua : is-univalent 𝓤) (fe : funext (𝓤 ⁺) 𝓤)
                → ⟨ hSet-refl-graph ua fe ⟩ ＝ hSet 𝓤
  observation-I = λ ua fe → refl

hSet-refl-graph-is-univalent : (ua : is-univalent 𝓤)
                             → funext 𝓤 𝓤
                             → (fe' : funext (𝓤 ⁺) 𝓤)
                             → is-univalent-refl-graph (hSet-refl-graph ua fe')
hSet-refl-graph-is-univalent {𝓤} ua fe fe'
 = prop-display-total-univalent I is-set II
 where
  I = universe-univalent-refl-graph ua fe'
  II = λ - → being-set-is-prop fe

hSet-univalent-refl-graph : is-univalent 𝓤
                          → funext 𝓤 𝓤
                          → funext (𝓤 ⁺) 𝓤
                          → Univalent-Refl-Graph (𝓤 ⁺) 𝓤
hSet-univalent-refl-graph ua fe fe'
 = (hSet-refl-graph ua fe' , hSet-refl-graph-is-univalent ua fe fe')

hSet-＝-char : is-univalent 𝓤
             → funext 𝓤 𝓤
             → funext (𝓤 ⁺) 𝓤
             → (X Y : hSet 𝓤)
             → (X ＝ Y) ≃ (underlying-set X ≃ underlying-set Y)
hSet-＝-char {𝓤} ua fe fe' 𝓧@(X , X-is-set) 𝓨@(Y , Y-is-set)
 = (𝓧 ＝ 𝓨)                               ≃⟨ II ⟩
   (𝓧 ≈⟨ hSet-refl-graph ua fe' ⟩ 𝓨)      ≃⟨ III ⟩
   (X ≃ Y)                                ■
 where
  I = universe-univalent-refl-graph ua fe'
  II = id-equiv-edge
        (hSet-refl-graph ua fe' , prop-display-total-univalent I is-set
                                   (λ - → being-set-is-prop fe))
        𝓧 𝓨
  III = prop-display-total-edge-char I is-set (λ - → being-set-is-prop fe)
         X Y X-is-set Y-is-set

\end{code}
