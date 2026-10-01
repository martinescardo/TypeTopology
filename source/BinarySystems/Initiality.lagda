Martin Escardo, 30th September 2026.

We show that 𝓜, the initial binary system of BinarySystems.Type, is
initial in the strong sense that the type of homomorphisms from it to
any binary system is a singleton. For this to be possible we have to
consider coherent homomorphisms, defined below.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module BinarySystems.Initiality (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Retracts
open import UF.SIP
open sip
open import UF.Subsingletons hiding (center)

open import BinarySystems.Type

\end{code}

Because the type of binary systems doesn't require the underlying type
to be a set, we would like to prove unique existence as the singleton
property of a Σ type, written ∃! here, as done e.g. for natural number
objects in MGS.Unique-Existence (and with a dependent version in
Naturals.UniversalProperty).

But the notion of homomorphism of BinarySystems.Type will not do for
this, because it doesn't mention the binary system equations, and so
the type

   Σ h ꞉ (𝕄 → ⟨ 𝓐 ⟩) , is-hom 𝓜 𝓐 h

is not a singleton in general. Indeed, l L is L by definition, and
therefore the third component of is-hom 𝓜 𝓐 h, applied to L, is an
identification h L ＝ f (h L). Once h L is identified with the point a
using the first component, this becomes an element of the identity
type a ＝ f a, which is the first axiom of 𝓐, and hence is data unless
the underlying type of 𝓐 is a set. For the circle with the points a
and b both chosen to be the base point, and the functions f and g both
chosen to be the identity, for instance, the constant map at the base
point has a whole loop space of homomorphism structures.

What is missing is that a homomorphism between structures presented by
equations should also say how it respects the equations. We add this as
three squares, one for each axiom.

The axiom a ＝ f a of 𝓐 and the axiom a' ＝ f' a' of 𝓑 give the two
routes

                    ap h ι₁ ∙ hl a
          h a ------------------------> f' (h a)
           |                              |
        hL |                              | ap f' hL
           |                              |
           v                              v
           a' ------------------------> f' a'
                         ι₁'

and the axioms b ＝ g b and b' ＝ g' b' give the two routes

                    ap h ι₃ ∙ hr b
          h b ------------------------> g' (h b)
           |                              |
        hR |                              | ap g' hR
           |                              |
           v                              v
           b' ------------------------> g' b'
                         ι₃'

whereas the axioms f b ＝ g a and f' b' ＝ g' a', which relate the two
descriptions of the midpoint, give the two routes

                   hl b             ap f' hR         ι₂'
         h (f b) --------> f' (h b) --------> f' b' -----> g' a'
            |                                               ^
   ap h ι₂  |                                               |
            |                                               |
            v                                               |
         h (g a) --------> g' (h a) -------------------------
                   hr a             ap g' hL

We define the notion of coherent homomorphism by requiring that the
two routes are identified in each of these three cases. It turns out
that higher coherences are not needed for the initiality result.

\begin{code}

is-coherent-hom : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-coherent-hom 𝓐@(A , (a , b , f , g) , (ι₁ , ι₂ , ι₃))
                𝓑@(B , (a' , b' , f' , g') , (ι₁' , ι₂' , ι₃')) h =
 Σ (hL , hR , hl , hr) ꞉ is-hom 𝓐 𝓑 h ,
   (ap h ι₁ ∙ hl a ∙ ap f' hL ＝ hL ∙ ι₁')
 × (ap h ι₂ ∙ hr a ∙ ap g' hL ＝ hl b ∙ ap f' hR ∙ ι₂')
 × (ap h ι₃ ∙ hr b ∙ ap g' hR ＝ hR ∙ ι₃')

\end{code}

For any binary system 𝓐, the homomorphism 𝓜-rec 𝓐 recursively defined
in BinarySystems.Type is coherent, and, moreover, the three squares
hold by reflexivity, because the axioms of 𝓜 do, and because the
homomorphism equations of 𝓜-rec at L, R and l R are the axioms of 𝓐
and reflexivities respectively.

\begin{code}

𝓜-rec-is-coherent-hom : (𝓐 : BS 𝓤) → is-coherent-hom 𝓜 𝓐 (𝓜-rec 𝓐)
𝓜-rec-is-coherent-hom 𝓐@(A , (a , b , f , g) , ι) =
 𝓜-rec-is-hom 𝓐 , refl , refl , refl

\end{code}

The type 𝔹 defined in BinarySystems.Type has no axioms, and so it is
initial for a point and two endomaps with no equations, which we prove
following the strategy of ℕ-is-nno in the module MGS.Unique-Existence.

\begin{code}

module _ (A : 𝓤 ̇ ) (c : A) (f g : A → A) where

 𝔹-rec : 𝔹 → A
 𝔹-rec center    = c
 𝔹-rec (left x)  = f (𝔹-rec x)
 𝔹-rec (right x) = g (𝔹-rec x)

 𝔹-recursive : (𝔹 → A) → 𝓤 ̇
 𝔹-recursive w = (w center ＝ c) × (w ∘ left ∼ f ∘ w) × (w ∘ right ∼ g ∘ w)

 𝔹-recursive-retract : (w : 𝔹 → A) → 𝔹-recursive w ◁ (w ∼ 𝔹-rec)
 𝔹-recursive-retract w = ρ , σ , ρσ
  where
   ρ : (w ∼ 𝔹-rec) → 𝔹-recursive w
   ρ H = H center ,
         (λ x → H (left x) ∙ (ap f (H x))⁻¹) ,
         (λ x → H (right x) ∙ (ap g (H x))⁻¹)

   σ : 𝔹-recursive w → w ∼ 𝔹-rec
   σ z@(p , K , Λ) center    = p
   σ z@(p , K , Λ) (left x)  = K x ∙ ap f (σ z x)
   σ z@(p , K , Λ) (right x) = Λ x ∙ ap g (σ z x)

   cancel : {x y z : A} (k : x ＝ y) (q : y ＝ z) → (k ∙ q) ∙ q ⁻¹ ＝ k
   cancel k q = (k ∙ q) ∙ q ⁻¹ ＝⟨ ∙assoc k q (q ⁻¹) ⟩
                k ∙ (q ∙ q ⁻¹) ＝⟨ ap (k ∙_) (trans-sym' q) ⟩
                k              ∎

   ρσ : (z : 𝔹-recursive w) → ρ (σ z) ＝ z
   ρσ z@(p , K , Λ) = to-×-＝ refl (to-×-＝ (dfunext fe κ) (dfunext fe κ'))
    where
     κ : (x : 𝔹) → σ z (left x) ∙ (ap f (σ z x))⁻¹ ＝ K x
     κ x = cancel (K x) (ap f (σ z x))

     κ' : (x : 𝔹) → σ z (right x) ∙ (ap g (σ z x))⁻¹ ＝ Λ x
     κ' x = cancel (Λ x) (ap g (σ z x))

 𝔹-is-initial : ∃! w ꞉ (𝔹 → A) , 𝔹-recursive w
 𝔹-is-initial =
  retract-of-singleton
   (Σ-retract _ _
     (λ w → 𝔹-recursive w ◁⟨ 𝔹-recursive-retract w ⟩
            ≃-gives-▷ (≃-funext fe w 𝔹-rec)))
   (singleton-types'-are-singletons 𝔹-rec)

\end{code}

Before proceeding we state and prove the following technical lemma,
which doesn't refer to binary systems.

\begin{code}

private
 contraction-lemma : {X : 𝓥 ̇ } {x y : X} (p : x ＝ y) (Y : 𝓦 ̇ )
                   → (Σ q ꞉ x ＝ y , (refl ∙ q ＝ p) × Y) ≃ Y
 contraction-lemma {_} {_} {X} {x} {y} p Y =
  (Σ q ꞉ x ＝ y , (refl ∙ q ＝ p) × Y) ≃⟨ I ⟩
  (Σ q ꞉ x ＝ y , (q ＝ p) × Y)        ≃⟨ left-Id-equiv p ⟩
  Y                                  ■
   where
    I = Σ-cong (λ q → ×-cong
                       (＝-cong-l (refl ∙ q) p refl-left-neutral)
                       (≃-refl Y))

\end{code}

We now fix a binary system 𝓐 and analyse the type of coherent
homomorphisms from 𝓜 to it.

\begin{code}

module _ (A : 𝓤 ̇ )
         (a b : A)
         (f g : A → A)
         (ι₁ : a ＝ f a)
         (ι₂ : f b ＝ g a)
         (ι₃ : b ＝ g b)
       where

 𝓐 : BS 𝓤
 𝓐 = A , (a , b , f , g) , (ι₁ , ι₂ , ι₃)

 𝓜-coherence : (h : 𝕄 → A) → is-hom 𝓜 𝓐 h → 𝓤 ̇
 𝓜-coherence h (hL , hR , hl , hr) =
    (refl ∙ hl L ∙ ap f hL ＝ hL ∙ ι₁)
  × (refl ∙ hr L ∙ ap g hL ＝ hl R ∙ ap f hR ∙ ι₂)
  × (refl ∙ hr R ∙ ap g hR ＝ hR ∙ ι₃)

 is-coherent-hom-from-𝓜-explicitly : (h : 𝕄 → A)
                                   → is-coherent-hom 𝓜 𝓐 h
                                   ＝ (Σ u ꞉ is-hom 𝓜 𝓐 h , 𝓜-coherence h u)
 is-coherent-hom-from-𝓜-explicitly h = refl

 glue : A × A × (𝔹 → A) → 𝕄 → A
 glue (u , v , w) L     = u
 glue (u , v , w) R     = v
 glue (u , v , w) (η x) = w x

 unglue : (𝕄 → A) → A × A × (𝔹 → A)
 unglue h = h L , h R , h ∘ η

 glue-unglue : glue ∘ unglue ∼ id
 glue-unglue h = dfunext fe ϕ
  where
   ϕ : glue (unglue h) ∼ h
   ϕ L     = refl
   ϕ R     = refl
   ϕ (η x) = refl

 unglue-glue : unglue ∘ glue ∼ id
 unglue-glue _ = refl

 glue-is-equiv : is-equiv glue
 glue-is-equiv = qinvs-are-equivs glue (unglue , unglue-glue , glue-unglue)

\end{code}

We now show that the homomorphism data on glue (u , v , w) is
equivalent to the following data.

\begin{code}

 glue-data : (u v : A) (w : 𝔹 → A) → 𝓤 ̇
 glue-data u v w = (u ＝ a)
                 × (v ＝ b)
                 × ((u ＝ f u) × (w center ＝ f v) × (w ∘ left ∼ f ∘ w))
                 × ((w center ＝ g u) × (v ＝ g v) × (w ∘ right ∼ g ∘ w))

 glue-data-to-glue-hom-data : (u v : A) (w : 𝔹 → A)
                            → glue-data u v w
                            → is-hom 𝓜 𝓐 (glue (u , v , w))
 glue-data-to-glue-hom-data u v w
  (hL , hR , (hlL , hlR , hlη) , (hrL , hrR , hrη)) = hL , hR , hl , hr
  where
   h : 𝕄 → A
   h = glue (u , v , w)

   hl : h ∘ l ∼ f ∘ h
   hl L     = hlL
   hl R     = hlR
   hl (η x) = hlη x

   hr : h ∘ r ∼ g ∘ h
   hr L     = hrL
   hr R     = hrR
   hr (η x) = hrη x

 glue-data-to-glue-hom-data-is-equiv
  : (u v : A) (w : 𝔹 → A)
  → is-equiv (glue-data-to-glue-hom-data u v w)
 glue-data-to-glue-hom-data-is-equiv u v w
  = qinvs-are-equivs (glue-data-to-glue-hom-data u v w) (Δ , ΔΓ , ΓΔ)
  where
   Γ = glue-data-to-glue-hom-data u v w

   Δ : codomain Γ → domain Γ
   Δ (hL , hR , hl , hr) = hL ,
                           hR ,
                           (hl L , hl R , hl ∘ η) ,
                           (hr L , hr R , hr ∘ η)

   ΔΓ : Δ ∘ Γ ∼ id
   ΔΓ s = refl

   ΓΔ : Γ ∘ Δ ∼ id
   ΓΔ i@(hL , hR , hl , hr) =
    to-×-＝ refl (to-×-＝ refl (to-×-＝ (dfunext fe ϕ) (dfunext fe ψ)))
    where
     ϕ : pr₁ (pr₂ (pr₂ (Γ (Δ i)))) ∼ hl
     ϕ L     = refl
     ϕ R     = refl
     ϕ (η x) = refl

     ψ : pr₂ (pr₂ (pr₂ (Γ (Δ i)))) ∼ hr
     ψ L     = refl
     ψ R     = refl
     ψ (η x) = refl

\end{code}

We now reorder the data so that it becomes possible to contract away
portions of it in the equivalence proved in coherent-homs-≃ below.

\begin{code}

 w-data : (u v : A) (hL : u ＝ a) (hR : v ＝ b) (w : 𝔹 → A) → 𝓤 ̇
 w-data u v hL hR w =
  Σ hlR ꞉ w center ＝ f v ,
  Σ hrL ꞉ w center ＝ g u , (refl ∙ hrL ∙ ap g hL ＝ hlR ∙ ap f hR ∙ ι₂)
                          × (w ∘ left ∼ f ∘ w)
                          × (w ∘ right ∼ g ∘ w)

 v-data : (u : A) (hL : u ＝ a) (v : A) → 𝓤 ̇
 v-data u hL v =
  Σ hR  ꞉ v ＝ b ,
  Σ hrR ꞉ v ＝ g v , (refl ∙ hrR ∙ ap g hR ＝ hR ∙ ι₃)
                   × (Σ w ꞉ (𝔹 → A) , w-data u v hL hR w)

 reordered-fiber : (u v : A) (w : 𝔹 → A) → 𝓤 ̇
 reordered-fiber u v w =
  Σ hL  ꞉ u ＝ a ,
  Σ hlL ꞉ u ＝ f u , (refl ∙ hlL ∙ ap f hL ＝ hL ∙ ι₁)
                   × (Σ hR ꞉ v ＝ b ,
                      Σ hrR ꞉ v ＝ g v , (refl ∙ hrR ∙ ap g hR ＝ hR ∙ ι₃)
                                       × w-data u v hL hR w)

 reordered-fiber-≃
  : (u v : A) (w : 𝔹 → A)
  → reordered-fiber u v w
  ≃ (Σ s ꞉ glue-data u v w , 𝓜-coherence
                               (glue (u , v , w))
                               (glue-data-to-glue-hom-data u v w s))
 reordered-fiber-≃ u v w = qinveq Φ (Ψ , ΨΦ , ΦΨ)
  where
   Φ : reordered-fiber u v w
     → Σ s ꞉ glue-data u v w , 𝓜-coherence
                                (glue (u , v , w))
                                (glue-data-to-glue-hom-data u v w s)
   Φ (hL , hlL , sq₁ , hR , hrR , sq₃ , hlR , hrL , sq₂ , hlη , hrη) =
    (hL , hR , (hlL , hlR , hlη) , (hrL , hrR , hrη)) , sq₁ , sq₂ , sq₃

   Ψ : codomain Φ → domain Φ
   Ψ ((hL , hR , (hlL , hlR , hlη) , (hrL , hrR , hrη)) , sq₁ , sq₂ , sq₃) =
    hL , hlL , sq₁ , hR , hrR , sq₃ , hlR , hrL , sq₂ , hlη , hrη

   ΨΦ : Ψ ∘ Φ ∼ id
   ΨΦ t = refl

   ΦΨ : Φ ∘ Ψ ∼ id
   ΦΨ t = refl

 reordered-total-space : 𝓤 ̇
 reordered-total-space =
  Σ u ꞉ A ,
  Σ hL  ꞉ u ＝ a ,
  Σ hlL ꞉ u ＝ f u , (refl ∙ hlL ∙ ap f hL ＝ hL ∙ ι₁)
                   × (Σ v ꞉ A , v-data u hL v)

 reordered-≃ : reordered-total-space
             ≃ (Σ (u , v , w) ꞉ A × A × (𝔹 → A) , reordered-fiber u v w)
 reordered-≃ = qinveq Φ (Ψ , ΨΦ , ΦΨ)
  where
   Φ : reordered-total-space
     → Σ (u , v , w) ꞉ A × A × (𝔹 → A) , reordered-fiber u v w
   Φ (u , hL , hlL , sq₁ , v , hR , hrR , sq₃ , w , d) =
    (u , v , w) , hL , hlL , sq₁ , hR , hrR , sq₃ , d

   Ψ : codomain Φ → domain Φ
   Ψ ((u , v , w) , hL , hlL , sq₁ , hR , hrR , sq₃ , d) =
    u , hL , hlL , sq₁ , v , hR , hrR , sq₃ , w , d

   ΨΦ : Ψ ∘ Φ ∼ id
   ΨΦ t = refl

   ΦΨ : Φ ∘ Ψ ∼ id
   ΦΨ t = refl

\end{code}

We now apply this reordering to prove the following equivalence by
contracting the data step by step.

\begin{code}

 coherent-homs-≃ : (Σ h ꞉ (𝕄 → A) , is-coherent-hom 𝓜 𝓐 h)
                 ≃ (Σ w ꞉ (𝔹 → A) , 𝔹-recursive A (f b) f g w)
 coherent-homs-≃ =

  (Σ h ꞉ (𝕄 → A) , is-coherent-hom 𝓜 𝓐 h)                          ≃⟨ I ⟩
  (Σ t ꞉ A × A × (𝔹 → A) , is-coherent-hom 𝓜 𝓐 (glue t))           ≃⟨ II ⟩
  (Σ (u , v , w) ꞉ A × A × (𝔹 → A) ,
   Σ s ꞉ glue-data u v w , 𝓜-coherence (glue (u , v , w))
                             (glue-data-to-glue-hom-data u v w s)) ≃⟨ III ⟩
  (Σ (u , v , w) ꞉ A × A × (𝔹 → A) , reordered-fiber u v w)        ≃⟨ IV ⟩
  reordered-total-space                                            ≃⟨ V ⟩
  (Σ hlL ꞉ a ＝ f a , (refl ∙ hlL ∙ ap f refl ＝ refl ∙ ι₁)
                    × (Σ v ꞉ A , v-data a refl v))                 ≃⟨ VI ⟩
  (Σ v ꞉ A , v-data a refl v)                                      ≃⟨ VII ⟩
  (Σ hrR ꞉ b ＝ g b , (refl ∙ hrR ∙ ap g refl ＝ refl ∙ ι₃)
                    × (Σ w ꞉ (𝔹 → A) , w-data a b refl refl w))    ≃⟨ VIII ⟩
  (Σ w ꞉ (𝔹 → A) , w-data a b refl refl w)                         ≃⟨ IX ⟩
  (Σ w ꞉ (𝔹 → A) , 𝔹-recursive A (f b) f g w)                      ■

  where
   I = ≃-sym (Σ-change-of-variable
               (λ h → is-coherent-hom 𝓜 𝓐 h) glue glue-is-equiv)

   II = Σ-cong' _ _
         (λ (u , v , w) → ≃-sym (Σ-change-of-variable
                                  (𝓜-coherence (glue (u , v , w)))
                                  (glue-data-to-glue-hom-data u v w)
                                  (glue-data-to-glue-hom-data-is-equiv u v w)))

   III = Σ-cong' _ _ (λ (u , v , w) → ≃-sym (reordered-fiber-≃ u v w))

   IV = ≃-sym reordered-≃

   V = based-contraction
        (λ u hL → Σ hlL ꞉ u ＝ f u ,
                    (refl ∙ hlL ∙ ap f hL ＝ hL ∙ ι₁)
                  × (Σ v ꞉ A , v-data u hL v))

   VI = contraction-lemma (refl ∙ ι₁) (Σ v ꞉ A , v-data a refl v)

   VII = based-contraction
          (λ v hR → Σ hrR ꞉ v ＝ g v ,
                      (refl ∙ hrR ∙ ap g hR ＝ hR ∙ ι₃)
                    × (Σ w ꞉ (𝔹 → A) , w-data a v refl hR w))

   VIII = contraction-lemma (refl ∙ ι₃)
           (Σ w ꞉ (𝔹 → A) , w-data a b refl refl w)

   IX = Σ-cong' _ _
         (λ w → Σ-cong' _ _
                 (λ hlR → contraction-lemma (hlR ∙ ι₂)
                           ((w ∘ left ∼ f ∘ w) × (w ∘ right ∼ g ∘ w))))

\end{code}

So 𝓜 is the initial binary system, in the sense that the type of
coherent homomorphisms from it to any binary system is a singleton.

\begin{code}

𝓜-is-initial : (𝓐 : BS 𝓤) → ∃! h ꞉ (𝕄 → ⟨ 𝓐 ⟩) , is-coherent-hom 𝓜 𝓐 h
𝓜-is-initial (A , (a , b , f , g) , (ι₁ , ι₂ , ι₃)) =
 equiv-to-singleton
  (coherent-homs-≃ A a b f g ι₁ ι₂ ι₃)
  (𝔹-is-initial A (f b) f g)

\end{code}
