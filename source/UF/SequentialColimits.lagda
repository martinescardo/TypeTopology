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
open import UF.CoconesofSpans fe
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Powerset-MultiUniverse
open import UF.PropIndexedPiSigma
open import UF.Pushouts fe
open import UF.Retracts
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
        Σ G' ꞉ ((n : ℕ) → b' n ∼ b' (succ n) ∘ a n) ,
         Σ H ꞉ ((n : ℕ) → b n ∼ b' n) ,
          ((n : ℕ) → ∼-trans (G n) (H (succ n) ∘ a n) ∼ ∼-trans (H n) (G' n)))
                                                                                ≃⟨ II ⟩
       (Σ b' ꞉ ((n : ℕ) → A n → B) ,
        Σ H ꞉ ((n : ℕ) → b n ∼ b' n) ,
         Σ G' ꞉ ((n : ℕ) → b' n ∼ b' (succ n) ∘ a n) ,
          ((n : ℕ) → ∼-trans (G n) (H (succ n) ∘ a n) ∼ ∼-trans (H n) (G' n)))
                                                                                ≃⟨ III ⟩
       (Σ G' ꞉ ((n : ℕ) → b n ∼ b (succ n) ∘ a n) ,
        ((n : ℕ) → G n ∼ G' n))
                                                                                ≃⟨ IV ⟩
       𝟙                                                                        ■
    where
     I = Σ-assoc
     II = Σ-cong (λ - → Σ-flip)
     III : (Σ b' ꞉ ((n : ℕ) → A n → B) ,
            Σ H ꞉ ((n : ℕ) → b n ∼ b' n) ,
             Σ G' ꞉ ((n : ℕ) → b' n ∼ b' (succ n) ∘ a n) ,
              ((n : ℕ) → ∼-trans (G n) (H (succ n) ∘ a n) ∼ ∼-trans (H n) (G' n)))
         ≃ (Σ G' ꞉ ((n : ℕ) → b n ∼ b (succ n) ∘ a n) , ((n : ℕ) → G n ∼ G' n))
     III = (Σ b' ꞉ ((n : ℕ) → A n → B) ,
            Σ H ꞉ ((n : ℕ) → b n ∼ b' n) ,
             Σ G' ꞉ ((n : ℕ) → b' n ∼ b' (succ n) ∘ a n) ,
              ((n : ℕ) → ∼-trans (G n) (H (succ n) ∘ a n) ∼ ∼-trans (H n) (G' n)))
                                                                               ≃⟨ V ⟩
           (Σ (b' , H) ꞉ (Σ b' ꞉ ((n : ℕ) → A n → B) , ((n : ℕ) → b n ∼ b' n)) ,
            (Σ G' ꞉ ((n : ℕ) → b' n ∼ b' (succ n) ∘ a n) ,
              ((n : ℕ) → ∼-trans (G n) (H (succ n) ∘ a n) ∼ ∼-trans (H n) (G' n))))
                                                                               ≃⟨ VII ⟩
           (Σ G' ꞉ ((n : ℕ) → b n ∼ b (succ n) ∘ a n) ,
            ((n : ℕ) → ∼-trans (G n) ∼-refl ∼ ∼-trans ∼-refl (G' n)))
                                                                               ≃⟨ VIII ⟩
           (Σ G' ꞉ ((n : ℕ) → b n ∼ b (succ n) ∘ a n) , ((n : ℕ) → G n ∼ G' n))■
      where
       V = ≃-sym Σ-assoc
       VI : (Σ b' ꞉ ((n : ℕ) → A n → B) , ((n : ℕ) → b n ∼ b' n)) ≃ 𝟙 {𝓤 ⊔ 𝓥}
       VI = (Σ b' ꞉ ((n : ℕ) → A n → B) , ((n : ℕ) → b n ∼ b' n))
                                                                  ≃⟨ Σ-cong IX ⟩
            (Σ b' ꞉ ((n : ℕ) → A n → B) , b ＝ b')
                                                                  ≃⟨ X ⟩
            𝟙                                                     ■
        where
         IX : (b' : (n : ℕ) → A n → B)
            → ((n : ℕ) → b n ∼ b' n) ≃ (b ＝ b')
         IX b' = ((n : ℕ) → b n ∼ b' n)
                                         ≃⟨ Π-cong fe fe
                                             (λ n → ≃-sym (≃-funext fe (b n) (b' n))) ⟩
                 ((n : ℕ) → b n ＝ b' n)
                                         ≃⟨ ≃-sym (≃-funext fe b b') ⟩
                 (b ＝ b')               ■
         X = singleton-≃-𝟙 (singleton-types-are-singletons b)
       VII = prop-indexed-sum (b , (λ n → ∼-refl)) (equiv-to-prop VI 𝟙-is-prop)
       VIII = Σ-cong (λ G' → Π-cong fe fe
               (λ n → Π-cong fe fe
                (λ x → ＝-cong (G n x) (∼-trans (λ - → refl) (G' n) x)
                 refl refl-left-neutral)))
     IV : (Σ G' ꞉ ((n : ℕ) → b n ∼ b (succ n) ∘ a n) , ((n : ℕ) → G n ∼ G' n)) ≃ 𝟙
     IV = (Σ G' ꞉ ((n : ℕ) → b n ∼ b (succ n) ∘ a n) , ((n : ℕ) → G n ∼ G' n))
                                                                               ≃⟨ VI ⟩
          (Σ G' ꞉ ((n : ℕ) → b n ∼ b (succ n) ∘ a n) , G ＝ G')
                                                                               ≃⟨ VII ⟩
          𝟙                                                                    ■
      where
       V : (G' : ((n : ℕ) → b n ∼ b (succ n) ∘ a n))
         → ((n : ℕ) → G n ∼ G' n) ≃ (G ＝ G')
       V G' = ((n : ℕ) → G n ∼ G' n)
                                      ≃⟨ Π-cong fe fe
                                          (λ n → ≃-sym (≃-funext fe (G n) (G' n))) ⟩
              ((n : ℕ) → G n ＝ G' n)
                                      ≃⟨ ≃-sym (≃-funext fe G G') ⟩
              (G ＝ G')               ■
       VI = Σ-cong V
       VII = singleton-≃-𝟙 (singleton-types-are-singletons G)

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

module _ (𝓐 : type-sequence 𝓤)
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

module _ (𝓐@(A , a) : type-sequence 𝓤)
         (X : 𝓣 ̇)
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

We will define our inverse map before showing the universal property of sequential
colimits.

\begin{code}

  gluing-from-sequential-cocone : ((b , H) : sequential-cocone 𝓐 X)
                                → (c : Σ A + Σ A)
                                → b (pr₁ (f c)) (pr₂ (f c)) ＝ b (pr₁ (g c)) (pr₂ (g c))
  gluing-from-sequential-cocone (b , H) (inl -) = refl
  gluing-from-sequential-cocone (b , H) (inr (n , x)) = H n x

  map-from-sequential-cocone : sequential-cocone 𝓐 X → (sequential-colimit → X)
  map-from-sequential-cocone (b , H)
   = pushout-recursion (uncurry b) (uncurry b) (gluing-from-sequential-cocone (b , H))

\end{code}

We will now show cocones over the above pushout diagram are equivalent to a sequential
cocones over the above type sequence.

\begin{code}

  pushout-cocone-to-seq-cocone : cocone f g X → sequential-cocone 𝓐 X
  pushout-cocone-to-seq-cocone (i , j , H) = (curry j , I)
   where
    I : (n : ℕ) → (curry j n) ∼ (λ - → j (succ n , a n -))
    I n x = H (inl (n , x)) ⁻¹ ∙ H (inr (n , x))

  seq-cocone-to-pushout-cocone : sequential-cocone 𝓐 X → cocone f g X
  seq-cocone-to-pushout-cocone (b , H)
   = (uncurry b , uncurry b , gluing-from-sequential-cocone (b , H))

  pushout-cocone-to-seq-cocone-is-retraction
   : pushout-cocone-to-seq-cocone ∘ seq-cocone-to-pushout-cocone ∼ id
  pushout-cocone-to-seq-cocone-is-retraction (b , H)
   = sequential-cocone-family-to-id 𝓐 X
      (pushout-cocone-to-seq-cocone (seq-cocone-to-pushout-cocone (b , H)))
      (b , H) ((λ n → λ x → refl) , (λ n → λ x → refl))

  pushout-cocone-to-seq-cocone-is-section
   : seq-cocone-to-pushout-cocone ∘ pushout-cocone-to-seq-cocone ∼ id
  pushout-cocone-to-seq-cocone-is-section (i , j , H)
   = inverse-cocone-map f g X
      (seq-cocone-to-pushout-cocone (pushout-cocone-to-seq-cocone (i , j , H)))
      (i , j , H) ((λ (n , x) → H (inl (n , x)) ⁻¹) , ∼-refl , I)
   where
    I : (z : Σ A + Σ A)
      → H (inl (pr₁ (f z) , pr₂ (f z))) ⁻¹ ∙ H z
      ＝ gluing-from-sequential-cocone
         (curry j , λ n → λ x → H (inl (n , x)) ⁻¹ ∙ H (inr (n , x))) z
    I (inl -) = left-inverse (H (inl -))
    I (inr -) = refl

  pushout-to-seq-cocone-is-equiv : is-equiv pushout-cocone-to-seq-cocone
  pushout-to-seq-cocone-is-equiv
   = qinvs-are-equivs pushout-cocone-to-seq-cocone
      (seq-cocone-to-pushout-cocone ,
       pushout-cocone-to-seq-cocone-is-section ,
        pushout-cocone-to-seq-cocone-is-retraction)

  canonical-maps-commute
   : canonical-map-to-sequential-cocone 𝓐 sequential-colimit X
      sequential-colimit-is-cocone
   ∼ pushout-cocone-to-seq-cocone
    ∘ canonical-map-to-cocone sequential-colimit f g pushout-cocone X
  canonical-maps-commute u
   = sequential-cocone-family-to-id 𝓐 X
      (canonical-map-to-sequential-cocone 𝓐 sequential-colimit X
       sequential-colimit-is-cocone u)
      (pushout-cocone-to-seq-cocone (canonical-map-to-cocone sequential-colimit f g
       pushout-cocone X u))
      (I , II)
    where
     I : (n : ℕ) → u ∘ ι n ∼ curry (u ∘ inrr) n
     I n x = refl
     II : (n : ℕ) (x : A n)
        → ap u (K n x)
        ＝ refl ∙ (ap u (glue (inl (n , x))) ⁻¹ ∙ ap u (glue (inr (n , x))))
     II n x = ap-∙ u (glue (inl (n , x)) ⁻¹) (glue (inr (n , x)))
             ∙ (ap (_∙ ap u (glue (inr (n , x)))) (ap-sym u (glue (inl (n , x))) ⁻¹)
             ∙ refl-left-neutral ⁻¹)

\end{code}

Using the above we prove the universal property for the sequential colimit.

\begin{code}

  sequential-colimit-universal-property
   : Seqential-Colimit-Universal-Property 𝓐 sequential-colimit X
      sequential-colimit-is-cocone  
  sequential-colimit-universal-property
   = transport is-equiv (dfunext fe (∼-sym canonical-maps-commute))
      (∘-is-equiv pushout-universal-property pushout-to-seq-cocone-is-equiv)

\end{code}

We unpack the equivalence obtained from the universal property.

\begin{code}

  module _ (𝓧@(h , H) : sequential-cocone 𝓐 X)
            where

   canonical-map-seq-cocone-fiber-contr
    : is-contr (fiber (canonical-map-to-sequential-cocone 𝓐 sequential-colimit X
       sequential-colimit-is-cocone) 𝓧)
   canonical-map-seq-cocone-fiber-contr
    = equivs-are-vv-equivs (canonical-map-to-sequential-cocone 𝓐 sequential-colimit X
       sequential-colimit-is-cocone) sequential-colimit-universal-property 𝓧

   canonical-map-seq-cocone-fiber-contr'
    : is-contr (Σ u ꞉ (sequential-colimit → X) ,
       sequential-cocone-family 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧)
   canonical-map-seq-cocone-fiber-contr' =
    equiv-to-singleton'
     (Σ-cong (λ - → sequential-cocone-identity-characterization 𝓐 X
      ((λ n → - ∘ ι n) , λ n → ∼-ap-∘ - (K n)) 𝓧)) (canonical-map-seq-cocone-fiber-contr)

   sequential-colimit-fiber-center
    : Σ u ꞉ (sequential-colimit → X) ,
       sequential-cocone-family 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧
   sequential-colimit-fiber-center = center (canonical-map-seq-cocone-fiber-contr')

   sequential-colimit-fiber-centrality
    : is-central
       (Σ u ꞉ (sequential-colimit → X) ,
        sequential-cocone-family 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧)
       (sequential-colimit-fiber-center)
   sequential-colimit-fiber-centrality
    = centrality (canonical-map-seq-cocone-fiber-contr')

   sequential-colimit-unique-map
    : Σ u ꞉ (sequential-colimit → X) ,
       sequential-cocone-family 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧
    → sequential-colimit → X
   sequential-colimit-unique-map (u , _ , _) = u

   sequential-colimit-homotopy
    : (z : Σ u ꞉ (sequential-colimit → X) ,
       sequential-cocone-family 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧)
    → (n : ℕ) → sequential-colimit-unique-map z ∘ ι n ∼ h n
   sequential-colimit-homotopy (_ , G , _) = G

   sequential-colimit-glue
    : ((u , G , M) : Σ u ꞉ (sequential-colimit → X) ,
       sequential-cocone-family 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧)
    → (n : ℕ) → ∼-trans (∼-ap-∘ u (K n)) (λ x → G (succ n) (a n x))
              ∼ ∼-trans (G n) (H n)
   sequential-colimit-glue (_ , _ , M) = M

\end{code}

From the universal property we will derived the recursion principle and computation rules
for sequential colimits.

\begin{code}

  sequential-colimit-recursion : sequential-cocone 𝓐 X
                               → sequential-colimit → X
  sequential-colimit-recursion 𝓧
   = sequential-colimit-unique-map 𝓧 (sequential-colimit-fiber-center 𝓧)

  sequential-colimit-recursion-computation
   : ((h , H) : sequential-cocone 𝓐 X)
   → (n : ℕ)
   → (x : A n)
   → sequential-colimit-recursion (h , H) (ι n x) ＝ h n x
  sequential-colimit-recursion-computation 𝓧
   = sequential-colimit-homotopy 𝓧 (sequential-colimit-fiber-center 𝓧)

  sequential-colimit-recursion-glue
   : ((h , H) : sequential-cocone 𝓐 X)
   → (n : ℕ)
   → (x : A n)
   → ap (sequential-colimit-recursion (h , H)) (K n x)
     ∙ sequential-colimit-recursion-computation (h , H) (succ n) (a n x)
   ＝ sequential-colimit-recursion-computation (h , H) n x ∙ H n x
  sequential-colimit-recursion-glue 𝓧
   = sequential-colimit-glue 𝓧 (sequential-colimit-fiber-center 𝓧)

\end{code}

We will now prove the uniqueness principle for sequential colimits.

\begin{code}

  sequential-colimit-uniqueness
   : (u u' : sequential-colimit → X)
   → (G : (n : ℕ)
        → u ∘ (ι n) ∼ u' ∘ (ι n))
   → (M : (n : ℕ) (x : A n)
        → ap u (K n x) ∙ G (succ n) (a n x) ＝ G n x ∙ ap u' (K n x))
   → u ∼ u'
  sequential-colimit-uniqueness u u' G M
   = pushout-uniqueness u u'
      (λ (n , x) → ap u (glue (inl (n , x))) ∙ (G n x ∙ ap u' (glue (inl (n , x)) ⁻¹)))
       (λ z → G (pr₁ (f (inl z))) (pr₂ (f (inl z))))
        (λ c → {!!})

\end{code}

TODO. Derive the dependent universal property and induction principle for sequential
colimits.
