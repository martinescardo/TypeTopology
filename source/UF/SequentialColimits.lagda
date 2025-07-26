Ian Ray, 21st Jun 2025.

We develop sequential colimits in HoTT/UF. This formalization follows Section 26 of
Introduction to Homotopy Type Theory by Egbert Rijke (HoTTEST summer school version:
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

A sequential cocone over a type sequence consists of a sequence of maps to a specified
type

          a₀      a₁      a₂
     A₀ ----> A₁ ----> A₂ ----> ...
      \       |        /
       \      |       /
    b₀  \     | b₁   / b₂ ...
         \    |     /
          \   |    /
           v  v   v
              B

such that every composable triangle commutes. Formally we can define this as follows.

\begin{code}

sequential-cocone : {𝓤 𝓥 : Universe}
                  → type-sequence 𝓤
                  → 𝓥 ̇
                  → 𝓤 ⊔ 𝓥 ̇ 
sequential-cocone (A , a) B
 = Σ b ꞉ ((n : ℕ) → A n → B) , ((n : ℕ) → b n ∼ b (succ n) ∘ a n)

\end{code}

We now characterize the identity type of sequential cocones.

\begin{code}

module _ (𝓐@(A , a) : type-sequence 𝓤)
         (B : 𝓥 ̇)
       where

 sequential-cocone-identity : sequential-cocone 𝓐 B
                            → sequential-cocone 𝓐 B
                            → 𝓤 ⊔ 𝓥 ̇
 sequential-cocone-identity (s , S) (r , R)
  = Σ H ꞉ ((n : ℕ) → s n ∼ r n) ,
    ((n : ℕ) → ∼-trans (S n) (H (succ n) ∘ a n) ∼ ∼-trans (H n) (R n))

 id-to-sequential-cocone-family : (𝓑 𝓑' : sequential-cocone 𝓐 B)
                                → 𝓑 ＝ 𝓑'
                                → sequential-cocone-identity 𝓑 𝓑'
 id-to-sequential-cocone-family 𝓑 𝓑 refl
  = ((λ - → ∼-refl) , λ - → λ -' → refl-left-neutral ⁻¹)

 sequential-cocone-family-is-identity-system
  : (𝓑 : sequential-cocone 𝓐 B)
  → is-contr (Σ 𝓑' ꞉ (sequential-cocone 𝓐 B) , sequential-cocone-identity 𝓑 𝓑')
 sequential-cocone-family-is-identity-system (b , G)
  = equiv-to-singleton e 𝟙-is-singleton
  where
   e : (Σ 𝓑' ꞉ (sequential-cocone 𝓐 B) , sequential-cocone-identity (b , G) 𝓑')
     ≃ 𝟙 {𝓤 ⊔ 𝓥}
   e = (Σ 𝓑' ꞉ (sequential-cocone 𝓐 B) , sequential-cocone-identity (b , G) 𝓑') ≃⟨ I ⟩
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
       VI = (Σ b' ꞉ ((n : ℕ) → A n → B) , ((n : ℕ) → b n ∼ b' n)) ≃⟨ Σ-cong IX ⟩
            (Σ b' ꞉ ((n : ℕ) → A n → B) , b ＝ b')                ≃⟨ X ⟩
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
         X = singleton-≃-𝟙 {𝓤 ⊔ 𝓥} {𝓥} (singleton-types-are-singletons b)
       VII = prop-indexed-sum (b , (λ n → ∼-refl)) (equiv-to-prop VI 𝟙-is-prop)
       VIII = Σ-cong (λ G' → Π-cong fe fe
               (λ n → Π-cong fe fe
                (λ x → ＝-cong (G n x) (∼-trans (λ - → refl) (G' n) x)
                 refl refl-left-neutral)))
     IV = (Σ G' ꞉ ((n : ℕ) → b n ∼ b (succ n) ∘ a n) , ((n : ℕ) → G n ∼ G' n)) ≃⟨ VI ⟩
          (Σ G' ꞉ ((n : ℕ) → b n ∼ b (succ n) ∘ a n) , G ＝ G')                ≃⟨ VII ⟩
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

 sequential-cocone-identity-characterization
  : (𝓑 𝓑' : sequential-cocone 𝓐 B)
  → (𝓑 ＝ 𝓑') ≃ (sequential-cocone-identity 𝓑 𝓑')
 sequential-cocone-identity-characterization 𝓑 𝓑' =
  (id-to-sequential-cocone-family 𝓑 𝓑' ,
    Yoneda-Theorem-forth 𝓑 (id-to-sequential-cocone-family 𝓑)
     (sequential-cocone-family-is-identity-system 𝓑) 𝓑')

 sequential-cocone-family-to-id : (𝓑 𝓑' : sequential-cocone 𝓐 B)
                                → (sequential-cocone-identity 𝓑 𝓑')
                                → 𝓑 ＝ 𝓑'
 sequential-cocone-family-to-id 𝓑 𝓑'
  = ⌜ sequential-cocone-identity-characterization 𝓑 𝓑' ⌝⁻¹

\end{code}

Given a sequential cocone over X and a map X → Y there is a canonical assignment to
a sequential cocone over Y.

\begin{code}

module _ (𝓐 : type-sequence 𝓤)
         (X : 𝓥 ̇) (Y : 𝓣 ̇)
       where

 canonical-map-to-sequential-cocone : sequential-cocone 𝓐 X
                                    → (X → Y)
                                    → sequential-cocone 𝓐 Y
 canonical-map-to-sequential-cocone (h , H) u =
  ((λ n → u ∘ h n) , λ n → ∼-ap-∘ u (H n))

\end{code}

A sequential cocone over X is universal if the above map is an equivalence for any Y.
Such a sequential cocone is said to be the sequential colimit of a type sequence.

\begin{code}

 Sequential-Colimit-Universal-Property : (𝓧 : sequential-cocone 𝓐 X)
                                       → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 Sequential-Colimit-Universal-Property 𝓧 =
  is-equiv (canonical-map-to-sequential-cocone 𝓧)

\end{code}

We now give a construction of the sequential colimit in terms of the pushout.
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
 f = cases id id

 g : Σ A + Σ A → Σ A
 g = cases id σ

 private
  index : Σ A → ℕ
  index = pr₁

  element-at : ((n , x) : Σ A) → A n
  element-at = pr₂

 module _ (push-ex : pushouts-exist f g)
           where

  open pushouts-exist push-ex

  sequential-colimit : 𝓤 ̇
  sequential-colimit = pushout

\end{code}

We provide the sequential cocone structure for the sequential colimit. Notice since the
pushout is formed on a coproduct we get two equations from the canonical pushout gluing.
These equations will prove useful throughout the development.

\begin{code}

  ι : (n : ℕ) → A n → sequential-colimit
  ι n x = inrr (n , x)

  glue-inl : ((n , x) : Σ A) → inll (n , x) ＝ inrr (n , x)
  glue-inl (n , x) = glue (inl (n , x))

  glue-inr : ((n , x) : Σ A) → inll (n , x) ＝ inrr (succ n , a n x)
  glue-inr (n , x) = glue (inr (n , x))

  K : (n : ℕ) → ι n ∼ ι (succ n) ∘ a n
  K n x = glue-inl (n , x) ⁻¹ ∙ glue-inr (n , x)

  sequential-colimit-is-cocone : sequential-cocone 𝓐 sequential-colimit
  sequential-colimit-is-cocone = (ι , K)

\end{code}

We will quickly record a technical lemma that will prove useful later.

\begin{code}

  ap-on-glue : (u : sequential-colimit → X)
             → (n : ℕ)
             → (x : A n)
             → ap u (K n x) ＝ ap u (glue-inl (n , x)) ⁻¹ ∙ ap u (glue-inr (n , x))
  ap-on-glue u n x = ap u (K n x)                                          ＝⟨ I ⟩
                     ap u (glue-inl (n , x) ⁻¹) ∙ ap u (glue-inr (n , x))  ＝⟨ II ⟩
                     ap u (glue-inl (n , x)) ⁻¹ ∙ ap u (glue-inr (n , x))  ∎
   where
    I = ap-∙ u (glue-inl (n , x) ⁻¹) (glue-inr (n , x))
    II = ap (_∙ ap u (glue-inr (n , x))) (ap-sym u (glue-inl (n , x))) ⁻¹

\end{code}

We show that cocones over the above pushout diagram are equivalent to sequential
cocones over the above type sequence. 

\begin{code}

  gluing-from-sequential-cocone
   : ((b , H) : sequential-cocone 𝓐 X)
   → (c : Σ A + Σ A)
   → b (index (f c)) (element-at (f c)) ＝ b (index (g c)) (element-at (g c))
  gluing-from-sequential-cocone (b , H) (inl -) = refl
  gluing-from-sequential-cocone (b , H) (inr (n , x)) = H n x

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
      → H (inl (index (f z) , element-at (f z))) ⁻¹ ∙ H z
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

\end{code}

Additionally, we show that the canonical map to sequential cocones factors through the
canonical map to pushout cocones and the above map that translates between them.

\begin{code}

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
        ＝ refl ∙ (ap u (glue-inl (n , x)) ⁻¹ ∙ ap u (glue-inr (n , x)))
     II n x = ap u (K n x)                                                   ＝⟨ III ⟩
              ap u (glue-inl (n , x) ⁻¹) ∙ ap u (glue-inr (n , x))           ＝⟨ IV ⟩
              ap u (glue-inl (n , x)) ⁻¹ ∙ ap u (glue-inr (n , x))           ＝⟨ V ⟩
              refl ∙ (ap u (glue-inl (n , x)) ⁻¹ ∙ ap u (glue-inr (n , x)))  ∎
      where
       III = ap-∙ u (glue-inl (n , x) ⁻¹) (glue-inr (n , x))
       IV = ap (_∙ ap u (glue-inr (n , x))) (ap-sym u (glue-inl (n , x)) ⁻¹)
       V = refl-left-neutral ⁻¹

\end{code}

Using the above results we prove that the pushout constructed above satisfies the
universal property of the sequential colimit.

\begin{code}

  sequential-colimit-universal-property
   : Sequential-Colimit-Universal-Property 𝓐 sequential-colimit X
      sequential-colimit-is-cocone  
  sequential-colimit-universal-property
   = transport is-equiv (dfunext fe (∼-sym canonical-maps-commute))
      (∘-is-equiv pushout-universal-property pushout-to-seq-cocone-is-equiv)

\end{code}

We unpack useful results from the equivalence obtained from the universal property.

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
       sequential-cocone-identity 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧)
   canonical-map-seq-cocone-fiber-contr' =
    equiv-to-singleton'
     (Σ-cong (λ - → sequential-cocone-identity-characterization 𝓐 X
      ((λ n → - ∘ ι n) , λ n → ∼-ap-∘ - (K n)) 𝓧)) (canonical-map-seq-cocone-fiber-contr)

   sequential-colimit-unique-map
    : Σ u ꞉ (sequential-colimit → X) ,
       sequential-cocone-identity 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧
    → sequential-colimit → X
   sequential-colimit-unique-map (u , _ , _) = u

   sequential-colimit-homotopy
    : (z : Σ u ꞉ (sequential-colimit → X) ,
       sequential-cocone-identity 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧)
    → (n : ℕ) → sequential-colimit-unique-map z ∘ ι n ∼ h n
   sequential-colimit-homotopy (_ , G , _) = G

   sequential-colimit-glue
    : ((u , G , M) : Σ u ꞉ (sequential-colimit → X) ,
       sequential-cocone-identity 𝓐 X ((λ n → u ∘ ι n) , λ n → ∼-ap-∘ u (K n)) 𝓧)
    → (n : ℕ) → ∼-trans (∼-ap-∘ u (K n)) (λ x → G (succ n) (a n x))
              ∼ ∼-trans (G n) (H n)
   sequential-colimit-glue (_ , _ , M) = M

\end{code}

From the universal property we derive the recursion principle and computation rules for
sequential colimits.

\begin{code}

  sequential-colimit-recursion : sequential-cocone 𝓐 X
                               → sequential-colimit → X
  sequential-colimit-recursion 𝓧
   = sequential-colimit-unique-map 𝓧 (center (canonical-map-seq-cocone-fiber-contr' 𝓧))

  sequential-colimit-recursion-computation
   : ((h , H) : sequential-cocone 𝓐 X)
   → (n : ℕ)
   → (x : A n)
   → sequential-colimit-recursion (h , H) (ι n x) ＝ h n x
  sequential-colimit-recursion-computation 𝓧
   = sequential-colimit-homotopy 𝓧 (center (canonical-map-seq-cocone-fiber-contr' 𝓧))

  sequential-colimit-recursion-glue
   : ((h , H) : sequential-cocone 𝓐 X)
   → (n : ℕ)
   → (x : A n)
   → ap (sequential-colimit-recursion (h , H)) (K n x)
     ∙ sequential-colimit-recursion-computation (h , H) (succ n) (a n x)
   ＝ sequential-colimit-recursion-computation (h , H) n x ∙ H n x
  sequential-colimit-recursion-glue 𝓧
   = sequential-colimit-glue 𝓧 (center (canonical-map-seq-cocone-fiber-contr' 𝓧))

\end{code}

Finally, we prove the uniqueness principle for sequential colimits.

\begin{code}

  sequential-colimit-uniqueness
   : (u u' : sequential-colimit → X)
   → (G : (n : ℕ) → u ∘ (ι n) ∼ u' ∘ (ι n))
   → (M : (n : ℕ) (x : A n) → ap u (K n x) ∙ G (succ n) (a n x) ＝ G n x ∙ ap u' (K n x))
   → u ∼ u'
  sequential-colimit-uniqueness u u' G M = pushout-uniqueness u u' I II III
   where
    ap-glue-inl : ((n , x) : Σ A) → u (inll (n , x)) ＝ u (inrr (n , x))
    ap-glue-inl (n , x) = ap u (glue-inl (n , x))
    ap-glue-inr : ((n , x) : Σ A) → u (inll (n , x)) ＝ u (inrr (succ n , a n x))
    ap-glue-inr (n , x) = ap u (glue-inr (n , x))
    ap-glue-inl' : ((n , x) : Σ A) → u' (inll (n , x)) ＝ u' (inrr (n , x))
    ap-glue-inl' (n , x) = ap u' (glue-inl (n , x))
    ap-glue-inr' : ((n , x) : Σ A) → u' (inll (n , x)) ＝ u' (inrr (succ n , a n x))
    ap-glue-inr' (n , x) = ap u' (glue-inr (n , x))
    I : (z : Σ A) → u (inll z) ＝ u' (inll z)
    I (n , x) = ap-glue-inl (n , x) ∙ G n x ∙ ap-glue-inl' (n , x) ⁻¹
    II : (z : Σ A) → u (inrr z) ＝ u' (inrr z)
    II (n , x) = G n x
    III : (c : Σ A + Σ A)
        → ap u (glue c) ∙ II (g c) ＝ I (f c) ∙ ap u' (glue c)
    III (inl (n , x)) = ap-glue-inl (n , x) ∙ G n x                        ＝⟨ IV ⟩
                        ap-glue-inl (n , x) ∙ G n x
                        ∙ (ap-glue-inl' (n , x) ⁻¹ ∙ ap-glue-inl' (n , x)) ＝⟨ V ⟩
                        I (n , x) ∙ ap-glue-inl' (n , x)                   ∎
     where
      IV = ap (ap-glue-inl (n , x) ∙ G n x ∙_) (sym-is-inverse (ap-glue-inl' (n , x)))
      V = ∙assoc (ap-glue-inl (n , x) ∙ G n x)
           (ap-glue-inl' (n , x) ⁻¹)
           (ap-glue-inl' (n , x)) ⁻¹
    III (inr (n , x)) = ap-glue-inr (n , x) ∙ G (succ n) (a n x)         ＝⟨ IV ⟩
                        (ap-glue-inl (n , x) ∙ ap-glue-inl (n , x) ⁻¹)
                        ∙ (ap-glue-inr (n , x) ∙ G (succ n) (a n x))     ＝⟨ V ⟩
                        ap-glue-inl (n , x) ∙ (ap-glue-inl (n , x) ⁻¹
                        ∙ (ap-glue-inr (n , x) ∙ G (succ n) (a n x)))    ＝⟨ VI ⟩
                        ap-glue-inl (n , x) ∙ ((ap-glue-inl (n , x) ⁻¹
                        ∙ ap-glue-inr (n , x)) ∙ G (succ n) (a n x))     ＝⟨ VII ⟩
                        ap-glue-inl (n , x)
                        ∙ (ap u (K n x) ∙ G (succ n) (a n x))            ＝⟨ VIII ⟩
                        ap-glue-inl (n , x) ∙ (G n x ∙ ap u' (K n x))    ＝⟨ IX ⟩
                        ap-glue-inl (n , x) ∙ G n x ∙ ap u' (K n x)      ＝⟨ X' ⟩
                        I (n , x) ∙ ap-glue-inr' (n , x)                 ∎
     where
      IV = refl-left-neutral ⁻¹ ∙ ap (_∙ (ap u (glue-inr (n , x)) ∙ G (succ n) (a n x)))
                                   (sym-is-inverse' (ap u (glue-inl (n , x))))
      V = ∙assoc (ap-glue-inl (n , x)) (ap-glue-inl (n , x) ⁻¹)
           (ap-glue-inr (n , x) ∙ G (succ n) (a n x))
      VI = ap (ap-glue-inl (n , x) ∙_)
            (∙assoc (ap-glue-inl (n , x) ⁻¹) (ap-glue-inr (n , x)) (G (succ n) (a n x)) ⁻¹)
      VII = ap (ap-glue-inl (n , x) ∙_) (ap (_∙ G (succ n) (a n x)) (ap-on-glue u n x ⁻¹))
      VIII = ap (ap-glue-inl (n , x) ∙_) (M n x)
      IX = ∙assoc (ap-glue-inl (n , x)) (G n x) (ap u' (K n x)) ⁻¹
      X' = ap (ap-glue-inl (n , x) ∙ G n x ∙_ ) (ap-on-glue u' n x)
           ∙ (∙assoc (ap-glue-inl (n , x) ∙ G n x) (ap-glue-inl' (n , x) ⁻¹)
              (ap-glue-inr' (n , x))) ⁻¹

\end{code}

TODO. Derive the dependent universal property and induction principle for sequential
colimits.
