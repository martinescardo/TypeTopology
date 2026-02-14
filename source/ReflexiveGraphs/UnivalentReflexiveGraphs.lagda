Ian Ray. 2nd September 2025.

Minor changes and merged into TypeToplogy in February 2026.

We give some properties about fans (terminology borrowed from Sterling),
which are analogous to singletons up to the edge relation. Then we provide
some equivalent characterizations of univalent reflexive graphs. It is worth
noting that, although Sterling makes no choice for the defintion in his paper,
we are required to. There is good reason to go with the 'propositional fans'
definition as it simplifies many proofs later on, but all the definitions
are useful.

We provide some equivalent descriptions of univalent reflexive graphs (see
index for references to Sterling, Buchholtz, etc.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.UnivalentReflexiveGraphs where

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import ReflexiveGraphs.Type

module _ (𝓐 : Refl-Graph 𝓤 𝓥) where

 fan : ⟨ 𝓐 ⟩
     → 𝓤 ⊔ 𝓥 ̇ 
 fan x = Σ y ꞉ ⟨ 𝓐 ⟩ , x ≈⟨ 𝓐 ⟩ y

 cofan : ⟨ 𝓐 ⟩
       → 𝓤 ⊔ 𝓥 ̇ 
 cofan x = Σ y ꞉ ⟨ 𝓐 ⟩ , y ≈⟨ 𝓐 ⟩ x

 prop-fan-to-cofan : ((x : ⟨ 𝓐 ⟩) → is-prop (fan x))
                   → ((x : ⟨ 𝓐 ⟩) → is-prop (cofan x))
 prop-fan-to-cofan fan-prop = I ∼-refl
  where
   I = ((x : ⟨ 𝓐 ⟩) → is-prop (cofan x))
         suffices-to-show⟨ id ⟩
       ((x : ⟨ 𝓐 ⟩) → ((y , s) (y' , t) : cofan x) → (y , s) ＝ (y' , t))
         suffices-to-show⟨ (λ f x (y , s) (y' , t) → f x y s y' t) ⟩ 
       ((x y : ⟨ 𝓐 ⟩) (s : y ≈⟨ 𝓐 ⟩ x) (y' : ⟨ 𝓐 ⟩) (t : y' ≈⟨ 𝓐 ⟩ x)
         → (y , s) ＝ (y' , t))
         suffices-to-show⟨ (λ f x y → f y x) ⟩
       ((y x : ⟨ 𝓐 ⟩) (s : y ≈⟨ 𝓐 ⟩ x) (y' : ⟨ 𝓐 ⟩) (t : y' ≈⟨ 𝓐 ⟩ x)
         → (y , s) ＝ (y' , t))
         suffices-to-show⟨ (λ f y x s y' t → f y (x , s) y' t) ⟩
       ((y : ⟨ 𝓐 ⟩) ((x , s) : fan y) (y' : ⟨ 𝓐 ⟩) (t : y' ≈⟨ 𝓐 ⟩ x)
         → (y , s) ＝ (y' , t))
         suffices-to-show⟨
          (λ f y → Π-proj⁻¹ (y , ≈-refl 𝓐 y) (fan-prop y) (f y)) ⟩
       ((y y' : ⟨ 𝓐 ⟩) (t : y' ≈⟨ 𝓐 ⟩ y) → (y , ≈-refl 𝓐 y) ＝ (y' , t))
         suffices-to-show⟨ (λ f y' y → f y y') ⟩
       ((y' y : ⟨ 𝓐 ⟩) (t : y' ≈⟨ 𝓐 ⟩ y) → (y , ≈-refl 𝓐 y) ＝ (y' , t))
         suffices-to-show⟨ (λ f y' y t → f y' (y , t)) ⟩
       ((y' : ⟨ 𝓐 ⟩) ((y , t) : fan y') → (y , ≈-refl 𝓐 y) ＝ (y' , t))
         suffices-to-show⟨
          (λ _ y' → Π-proj⁻¹ (y' , ≈-refl 𝓐 y') (fan-prop y') refl) ⟩
       ((y' : ⟨ 𝓐 ⟩) → (y' , ≈-refl 𝓐 y') ＝[ fan y' ] (y' , ≈-refl 𝓐 y'))  ▢

 prop-cofan-to-fan : ((x : ⟨ 𝓐 ⟩) → is-prop (cofan x))
                   → ((x : ⟨ 𝓐 ⟩) → is-prop (fan x))
 prop-cofan-to-fan co-prop = I ∼-refl
  where
   I = ((x : ⟨ 𝓐 ⟩) → is-prop (fan x))
         suffices-to-show⟨ id ⟩
       ((x : ⟨ 𝓐 ⟩) → ((y , s) (y' , t) : fan x) → (y , s) ＝ (y' , t))
         suffices-to-show⟨ (λ f x (y , s) (y' , t) → f x y s y' t) ⟩ 
       ((x y : ⟨ 𝓐 ⟩) (s : x ≈⟨ 𝓐 ⟩ y) (y' : ⟨ 𝓐 ⟩) (t : x ≈⟨ 𝓐 ⟩ y')
         → (y , s) ＝ (y' , t))
         suffices-to-show⟨ (λ f x y → f y x) ⟩
       ((y x : ⟨ 𝓐 ⟩) (s : x ≈⟨ 𝓐 ⟩ y) (y' : ⟨ 𝓐 ⟩) (t : x ≈⟨ 𝓐 ⟩ y')
         → (y , s) ＝ (y' , t))
         suffices-to-show⟨ (λ f y x s y' t → f y (x , s) y' t) ⟩
       ((y : ⟨ 𝓐 ⟩) ((x , s) : cofan y) (y' : ⟨ 𝓐 ⟩) (t : x ≈⟨ 𝓐 ⟩ y')
         → (y , s) ＝ (y' , t))
         suffices-to-show⟨
          (λ f y → Π-proj⁻¹ (y , ≈-refl 𝓐 y) (co-prop y) (f y)) ⟩
       ((y y' : ⟨ 𝓐 ⟩) (t : y ≈⟨ 𝓐 ⟩ y') → (y , ≈-refl 𝓐 y) ＝ (y' , t))
         suffices-to-show⟨ (λ f y y' → f y' y) ⟩
       ((y' y : ⟨ 𝓐 ⟩) (t : y ≈⟨ 𝓐 ⟩ y') → (y , ≈-refl 𝓐 y) ＝ (y' , t))
         suffices-to-show⟨ (λ f y' y t → f y' (y , t)) ⟩
       ((y' : ⟨ 𝓐 ⟩) ((y , t) : cofan y') → (y , ≈-refl 𝓐 y) ＝ (y' , t))
         suffices-to-show⟨
          (λ _ y' → Π-proj⁻¹ (y' , ≈-refl 𝓐 y') (co-prop y') refl) ⟩
       ((y' : ⟨ 𝓐 ⟩) → (y' , ≈-refl 𝓐 y') ＝[ fan y' ] (y' , ≈-refl 𝓐 y'))  ▢

 contr-fan-to-prop : ((x : ⟨ 𝓐 ⟩) → is-contr (fan x))
                   → ((x : ⟨ 𝓐 ⟩) → is-prop (fan x))
 contr-fan-to-prop fan-contr x = singletons-are-props (fan-contr x)

 prop-fan-to-contr : ((x : ⟨ 𝓐 ⟩) → is-prop (fan x))
                   → ((x : ⟨ 𝓐 ⟩) → is-contr (fan x))
 prop-fan-to-contr fan-prop x
  = pointed-props-are-singletons (x , ≈-refl 𝓐 x) (fan-prop x)

 contr-fan-to-cofan : ((x : ⟨ 𝓐 ⟩) → is-contr (fan x))
                    → ((x : ⟨ 𝓐 ⟩) → is-contr (cofan x))
 contr-fan-to-cofan contr-fan x
  = pointed-props-are-singletons (x , ≈-refl 𝓐 x)
     (prop-fan-to-cofan (λ - → singletons-are-props (contr-fan -)) x)

 prop-fan-to-contr-cofan : ((x : ⟨ 𝓐 ⟩) → is-prop (fan x))
                         → ((x : ⟨ 𝓐 ⟩) → is-contr (cofan x))
 prop-fan-to-contr-cofan fan-prop x
  = contr-fan-to-cofan (prop-fan-to-contr fan-prop) x

 contr-cofan-to-fan : ((x : ⟨ 𝓐 ⟩) → is-contr (cofan x))
                    → ((x : ⟨ 𝓐 ⟩) → is-contr (fan x))
 contr-cofan-to-fan contr-cofan x
  = pointed-props-are-singletons (x , ≈-refl 𝓐 x)
     (prop-cofan-to-fan (λ - → singletons-are-props (contr-cofan -)) x)

\end{code}

We give the canonical function from an identification to an edge.

\begin{code}

 id-to-edge : {x y : ⟨ 𝓐 ⟩}
            → x ＝ y
            → x ≈⟨ 𝓐 ⟩ y
 id-to-edge {x} {x} refl = ≈-refl 𝓐 x

\end{code}

If each fan is propositional then id-to-edge is an equivalence.

\begin{code}

 private
  helper-edge-to-id : (x y : ⟨ 𝓐 ⟩)
                    → (p : x ≈⟨ 𝓐 ⟩ y)
                    → (x , ≈-refl 𝓐 x) ＝ (y , p)
                    → x ＝ y
  helper-edge-to-id x .x .(≈-refl 𝓐 x) refl = refl

 module _ (prop-fans : ((x : ⟨ 𝓐 ⟩) → is-prop (fan x))) where

  prop-fans-edge-to-id : (x y : ⟨ 𝓐 ⟩)
                       → x ≈⟨ 𝓐 ⟩ y
                       → x ＝ y
  prop-fans-edge-to-id x y p
   = helper-edge-to-id x y p (prop-fans x (x , ≈-refl 𝓐 x) (y , p))

  prop-fans-gives-retraction : (x y : ⟨ 𝓐 ⟩)
                             → has-retraction id-to-edge
  prop-fans-gives-retraction x y
   = (prop-fans-edge-to-id x y , II x y)
   where
    I : (x : ⟨ 𝓐 ⟩) → prop-fans x (x , ≈-refl 𝓐 x) (x , ≈-refl 𝓐 x) ＝ refl
    I x = props-are-sets (prop-fans x)
           (prop-fans x (x , ≈-refl 𝓐 x) (x , ≈-refl 𝓐 x)) refl
    II : (x y : ⟨ 𝓐 ⟩) (p : x ＝ y)
       → (prop-fans-edge-to-id x y)
          (id-to-edge p) ＝ p
    II x .x refl = ap (helper-edge-to-id x x (≈-refl 𝓐 x)) (I x)

  id-are-retracts-of-edges : (x y : ⟨ 𝓐 ⟩)
                           → retract (x ＝ y) of (x ≈⟨ 𝓐 ⟩ y)
  id-are-retracts-of-edges x y
   = (prop-fans-edge-to-id x y , id-to-edge ,
      retraction-equation (id-to-edge) (prop-fans-gives-retraction x y))

  prop-fans-gives-section : (x y : ⟨ 𝓐 ⟩)
                          → has-section id-to-edge
  prop-fans-gives-section x y
   = (prop-fans-edge-to-id x y , II)
   where
    I : (p : x ≈⟨ 𝓐 ⟩ y) (ϕ : (x , ≈-refl 𝓐 x) ＝ (y , p))
      → id-to-edge (helper-edge-to-id x y p ϕ) ＝ p
    I p refl = refl
    II : (p : x ≈⟨ 𝓐 ⟩ y)
       → id-to-edge (prop-fans-edge-to-id x y p) ＝ p
    II p = I p (prop-fans x (x , ≈-refl 𝓐 x) (y , p))

  edges-are-retracts-of-id : (x y : ⟨ 𝓐 ⟩)
                           → retract (x ≈⟨ 𝓐 ⟩ y) of (x ＝ y)
  edges-are-retracts-of-id x y
   = (id-to-edge , prop-fans-gives-section x y)

\end{code}

Now we show that id-to-edge is an equiv iff all fans are propositional.

\begin{code}

 id-to-edge-equiv-implies-prop-fans : ((x y : ⟨ 𝓐 ⟩) → is-equiv id-to-edge)
                                    → ((x : ⟨ 𝓐 ⟩) → is-prop (fan x))
 id-to-edge-equiv-implies-prop-fans e
  = contr-fan-to-prop fan-is-contr
  where
   fan-is-contr : (x : ⟨ 𝓐 ⟩) → is-contr (fan x)
   fan-is-contr x = equiv-to-singleton' (Σ-cong (λ y → id-to-edge , e x y))
                     (singleton-types-are-singletons x)

 prop-fans-implies-id-to-edge-equiv
  : ((x : ⟨ 𝓐 ⟩) → is-prop (fan x))
  → ((x y : ⟨ 𝓐 ⟩) → is-equiv id-to-edge)
 prop-fans-implies-id-to-edge-equiv prop-fans x y
  = (prop-fans-gives-section prop-fans x y ,
      prop-fans-gives-retraction prop-fans x y) 

\end{code}

We now define univalent reflexive graphs in terms of propositional fans, but
one could use any of the equivalent characterizations.

\begin{code}

is-univalent-refl-graph : (𝓐 : Refl-Graph 𝓤 𝓥) → 𝓤 ⊔ 𝓥 ̇ 
is-univalent-refl-graph 𝓐 = (x : ⟨ 𝓐 ⟩) → is-prop (fan 𝓐 x)

Univalent-Refl-Graph : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Univalent-Refl-Graph 𝓤 𝓥 = Σ 𝓐 ꞉ (Refl-Graph 𝓤 𝓥) , is-univalent-refl-graph 𝓐

\end{code}

We will now record some boiler plate code for univalent reflexive graphs.

\begin{code}

⟨_⟩ᵤ : Univalent-Refl-Graph 𝓤 𝓥 → 𝓤 ̇
⟨ (𝓐 , _) ⟩ᵤ = ⟨ 𝓐 ⟩

edge-relᵤ : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥) → ⟨ 𝓐 ⟩ᵤ → ⟨ 𝓐 ⟩ᵤ → 𝓥 ̇
edge-relᵤ (𝓐 , _) = edge-rel 𝓐

syntax edge-relᵤ 𝓐 x y = x ≈ᵤ⟨ 𝓐 ⟩ y

≈-reflᵤ : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥) → (x : ⟨ 𝓐 ⟩ᵤ) → x ≈ᵤ⟨ 𝓐 ⟩ x
≈-reflᵤ (𝓐 , _) x = ≈-refl 𝓐 x

underlying-refl-graph : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥)
                      → Refl-Graph 𝓤 𝓥
underlying-refl-graph (𝓐 , _) = 𝓐

syntax underlying-refl-graph 𝓐 = 𝓐 /ᵤ 

underlying-refl-graph-is-univalent : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥)
                                   → is-univalent-refl-graph (𝓐 /ᵤ)
underlying-refl-graph-is-univalent (𝓐 , is-ua) = is-ua

id-equiv-edge : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥)
              → (x y : ⟨ 𝓐 ⟩ᵤ)
              → (x ＝ y) ≃ (x ≈ᵤ⟨ 𝓐 ⟩ y)
id-equiv-edge 𝓐 x y
 = (id-to-edge (𝓐 /ᵤ)
   , prop-fans-implies-id-to-edge-equiv (underlying-refl-graph 𝓐)
      (underlying-refl-graph-is-univalent 𝓐) x y)

edge-to-id : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥) {x y : ⟨ 𝓐 ⟩ᵤ}
           → x ≈ᵤ⟨ 𝓐 ⟩ y
           → x ＝ y
edge-to-id 𝓐 {x} {y} = ⌜ id-equiv-edge 𝓐 x y ⌝⁻¹

edge-to-id-preserves-refl : (𝓐 : Univalent-Refl-Graph 𝓤 𝓥) {x : ⟨ 𝓐 ⟩ᵤ}
                          → edge-to-id 𝓐 (≈-refl (𝓐 /ᵤ) x) ＝ refl
edge-to-id-preserves-refl 𝓐 {x}
 = inverses-are-retractions (id-to-edge (𝓐 /ᵤ))
    (prop-fans-implies-id-to-edge-equiv (underlying-refl-graph 𝓐)
     (underlying-refl-graph-is-univalent 𝓐) x x) refl

\end{code}

We show univalence implies edge induction.

TODO: show they are also equivalent.

\begin{code}

univalence-implies-edge-induction : {𝓐 : Refl-Graph 𝓤 𝓥}
                                  → is-univalent-refl-graph 𝓐
                                  → (P : (x y : ⟨ 𝓐 ⟩) → (x ≈⟨ 𝓐 ⟩ y) → 𝓣 ̇)
                                  → ((x : ⟨ 𝓐 ⟩) → P x x (≈-refl 𝓐 x))
                                  → (x y : ⟨ 𝓐 ⟩)
                                  → (p : x ≈⟨ 𝓐 ⟩ y)
                                  → P x y p
univalence-implies-edge-induction {𝓤} {𝓥} {𝓣} {𝓐} ua P R x y p
 = I (ua x (x , ≈-refl 𝓐 x) (y , p))
 where
  I : (x , ≈-refl 𝓐 x) ＝ (y , p) → P x y p
  I refl = R x  

\end{code}
