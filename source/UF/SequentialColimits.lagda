Ian Ray, 21st Jun 2025.

We will prove some results about sequential colimits. This formalization will follow
section 26 of Introduction to Homotopy Type Theory by Egbert Rijke (HoTTest summer
school version:
https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/HoTT/hott-intro.pdf).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.SequentialColimits (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Powerset-MultiUniverse
open import UF.PropIndexedPiSigma
open import UF.Pushouts fe
open import UF.Subsingletons
open import UF.Yoneda

\end{code}

A diagram of the following form

          a₀      a₁      a₂
     A₀ ----> A₁ ----> A₂ ----> ...

is a type sequence. We can give a formal specification as follows.

\begin{code}

type-sequence : (𝓤 : Universe) → (𝓤 ⁺) ̇
type-sequence 𝓤 = Σ A ꞉ (ℕ → 𝓤 ̇) , ((n : ℕ) → A n → A (succ n))

\end{code}

A sequential cocone over a type sequence consists of maps to a vertex

          a₀      a₁      a₂
     A₀ ----> A₁ ----> A₂ ----> ...
      \       |        /
       \      |       /
    b₀  \     | b₁   / b₂
         \    |     /
          \   |    /
           v  v   v
              B

such that everything commuts. Formally we can define this as follows.

\begin{code}

sequential-cocone : {𝓤 𝓥 : Universe}
                  → type-sequence 𝓤
                  → 𝓥 ̇
                  → 𝓤 ⊔ 𝓥 ̇ 
sequential-cocone (A , a) B
 = Σ b ꞉ ((n : ℕ) → A n → B) , ((n : ℕ) → b n ∼ b (succ n) ∘ a n)

\end{code}

TODO. Characterize equality of sequential cocones.

\begin{code}

module _ (𝓐@(A , a) : type-sequence 𝓤)
         (B : 𝓥 ̇)
          where

 sequential-cocone-family : sequential-cocone 𝓐 B
                          → sequential-cocone 𝓐 B
                          → 𝓤 ⊔ 𝓥 ̇
 sequential-cocone-family (s , S) (r , R)
  = Σ H ꞉ ((n : ℕ) → s n ∼ r n) ,
    ((n : ℕ) → ∼-trans (S n) (H (succ n) ∘ a n) ∼ ∼-trans (H n) (R n))

 id-to-sequential-cocone-family : (𝓑 𝓑' : sequential-cocone 𝓐 B)
                                → 𝓑 ＝ 𝓑'
                                → sequential-cocone-family 𝓑 𝓑'
 id-to-sequential-cocone-family 𝓑 .𝓑 refl
  = ((λ - → ∼-refl) , λ - → λ -' → refl-left-neutral ⁻¹)

 sequential-cocone-family-is-identity-system
  : (𝓑 : sequential-cocone 𝓐 B)
  → is-contr (Σ 𝓑' ꞉ (sequential-cocone 𝓐 B) , sequential-cocone-family 𝓑 𝓑')
 sequential-cocone-family-is-identity-system (b , G)
  = equiv-to-singleton e 𝟙-is-singleton
  where
   e : (Σ 𝓑' ꞉ (sequential-cocone 𝓐 B) , sequential-cocone-family (b , G) 𝓑') ≃ 𝟙 {𝓤 ⊔ 𝓥}
   e = (Σ 𝓑' ꞉ (sequential-cocone 𝓐 B) , sequential-cocone-family (b , G) 𝓑')
                                                                                ≃⟨ I ⟩
       (Σ b' ꞉ ((n : ℕ) → A n → B) ,
        (Σ G' ꞉ ((n : ℕ) → b' n ∼ b' (succ n) ∘ a n) ,
         Σ H ꞉ ((n : ℕ) → b n ∼ b' n) ,
          ((n : ℕ) → ∼-trans (G n) (H (succ n) ∘ a n) ∼ ∼-trans (H n) (G' n))))
                                                                                ≃⟨ {!!} ⟩
       {!!}
    where
     I = Σ-assoc

 sequential-cocone-identity-characterization : (𝓑 𝓑' : sequential-cocone 𝓐 B)
                                             → (𝓑 ＝ 𝓑') ≃ (sequential-cocone-family 𝓑 𝓑')
 sequential-cocone-identity-characterization 𝓑 𝓑' =
  (id-to-sequential-cocone-family 𝓑 𝓑' ,
    Yoneda-Theorem-forth 𝓑 (id-to-sequential-cocone-family 𝓑)
     (sequential-cocone-family-is-identity-system 𝓑) 𝓑')

 sequential-cocone-family-to-id : (𝓑 𝓑' : sequential-cocone 𝓐 B)
                                → (sequential-cocone-family 𝓑 𝓑')
                                → 𝓑 ＝ 𝓑'
 sequential-cocone-family-to-id 𝓑 𝓑'
  = ⌜ sequential-cocone-identity-characterization 𝓑 𝓑' ⌝⁻¹

\end{code}

Given a sequential cocone over B and a map B → C there is a canonical assignment to
a sequential cocone over C.

\begin{code}

module _ (𝓐@(A , a) : type-sequence 𝓤)
         (B : 𝓥 ̇) (C : 𝓣 ̇)
          where

 canonical-map-to-sequential-cocone : sequential-cocone 𝓐 B
                                    → (B → C)
                                    → sequential-cocone 𝓐 C
 canonical-map-to-sequential-cocone (b , H) u =
  ((λ n → u ∘ b n) , λ n → ∼-ap-∘ u (H n))

\end{code}

A sequential cocone over B is universal if the above map is an equivalence for any C.
Such a sequential cocone is said to be the sequential colimit of a type sequence.

\begin{code}

 Seqential-Colimit-Universal-Property : (𝓑 : sequential-cocone 𝓐 B)
                                      → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 Seqential-Colimit-Universal-Property 𝓑 =
  is-equiv (canonical-map-to-sequential-cocone 𝓑)

\end{code}

We will now give a construction of the sequential colimit in terms of the pushout.
This construction follows 26.2 in Introduction to Homotopy Type Theory (link above).

The sequential colimit A∞ can be constructed as the pushout of the following diagram

                     [id , σ]
          Σ A + Σ A ------------> Σ A
              |                    |
   [id , id]  |                    | inrr
              |                    |
             Σ A ----------------> A∞
                       inll

where σ (n , x) = (n + 1 , a n x).

\begin{code}

module _ (X : 𝓣 ̇)
         (𝓐@(A , a) : type-sequence 𝓤)
          where

 σ : Σ A → Σ A
 σ (n , x) = (succ n , a n x)

 f : Σ A + Σ A → Σ A
 f (inl -) = -
 f (inr -) = -

 g : Σ A + Σ A → Σ A
 g (inl -) = -
 g (inr -) = σ -

 module _ (push-ex : pushouts-exist f g)
           where

  open pushouts-exist push-ex

  sequential-colimit : 𝓤 ̇
  sequential-colimit = pushout

\end{code}

We give the sequential cocone structure for the sequential colimt.

\begin{code}

  ι : (n : ℕ) → A n → sequential-colimit
  ι n x = inrr (n , x)

  K : (n : ℕ) → ι n ∼ ι (succ n) ∘ a n
  K n x = glue (inl (n , x)) ⁻¹ ∙ glue (inr (n , x))

  sequential-colimit-is-cocone : sequential-cocone 𝓐 sequential-colimit
  sequential-colimit-is-cocone = (ι , K)

\end{code}

We prove the universal property for the sequential colimit.

\begin{code}

  sequential-colimit-universal-property
   : Seqential-Colimit-Universal-Property 𝓐 sequential-colimit X
      sequential-colimit-is-cocone  
  sequential-colimit-universal-property
   = qinvs-are-equivs
      (canonical-map-to-sequential-cocone 𝓐 sequential-colimit X
       sequential-colimit-is-cocone)
      (I , III , IV)
   where
    I : sequential-cocone 𝓐 X → (sequential-colimit → X)
    I (b , H) = pushout-recursion (λ (n , x) → b n x) (λ (n , x) → b n x) II
     where
      II : (c : Σ A + Σ A)
        → b (pr₁ (f c)) (pr₂ (f c)) ＝ b (pr₁ (g c)) (pr₂ (g c))
      II (inl -) = refl
      II (inr (n , x)) = H n x
    III : I ∘ canonical-map-to-sequential-cocone 𝓐 sequential-colimit X
               sequential-colimit-is-cocone
        ∼ id
    III u = {!!}
    IV : canonical-map-to-sequential-cocone 𝓐 sequential-colimit X
          sequential-colimit-is-cocone ∘ I ∼ id
    IV (b , H) = {!!}

  sequential-colimit-universal-property'
   : Seqential-Colimit-Universal-Property 𝓐 sequential-colimit X
      sequential-colimit-is-cocone  
  sequential-colimit-universal-property'
   = vv-equivs-are-equivs
      (canonical-map-to-sequential-cocone 𝓐 sequential-colimit X
       sequential-colimit-is-cocone)
      I
   where
    I : is-vv-equiv (canonical-map-to-sequential-cocone 𝓐 sequential-colimit X
         sequential-colimit-is-cocone)
    I (b , H) = {!!}
    
    

\end{code}
