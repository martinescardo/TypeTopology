Martin Escardo, 14 Feb 2024.

Generalization of UF.SIP to characterize equality of Σ-types,
suggested by Ian Ray. In UF.SIP, the index type of the Σ-type is a
universe. But the results hold for any index type whatsoever, if they
are slightly modified to replace some equivalences by identities. In
particular we don't use univalence (or function or propositional
extensionality) here, which the file UF.SIP does.

we consider Σ-types of the form Σ x ꞉ X , S x. We think of s : S x as
structure on the point x : X, so that S x is the type of all
structures on x, and Σ x ꞉ X , S x is the type of structured points.

Conventions.

 * x, y range over X.
 * σ, τ range over Σ S.
 * s, t range over S x.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.SigmaIdentity where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Retracts
open import UF.Subsingletons
open import UF.Yoneda

module Σ-identity where

\end{code}

Underlying point and structure of a structured point.

\begin{code}

 module _ {X : 𝓤 ̇ } {S : X → 𝓥 ̇ } where

  ⟨_⟩ : Σ S → X
  ⟨_⟩ = pr₁

  structure : (σ : Σ S) → S ⟨ σ ⟩
  structure = pr₂

\end{code}

The canonical map from an identification of structures on the same
point to a generalized identification ι with reflexivity data ρ of
structured points with the same underlying point:

\begin{code}

  canonical-map : (ι : (σ τ : Σ S) → ⟨ σ ⟩ ＝ ⟨ τ ⟩ → 𝓦 ̇ )
                  (ρ : (σ : Σ S) → ι σ σ refl)
                  {x : X}
                  (s t : S x)
                → s ＝ t → ι (x , s) (x , t) refl
  canonical-map ι ρ {x} s s refl = ρ (x , s)

\end{code}

The type of Sigma notions of identity, ranged over by δ = (ι , ρ , θ).

\begin{code}

 SNI : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
 SNI {𝓤} {𝓥} {X} S 𝓦 =
    Σ ι ꞉ ((σ τ : Σ S) → (⟨ σ ⟩ ＝ ⟨ τ ⟩ → 𝓦 ̇ ))
  , Σ ρ ꞉ ((σ : Σ S) → ι σ σ refl)
  , ({x : X} (s t : S x) → is-equiv (canonical-map ι ρ s t))

 module _ {X : 𝓤 ̇ } {S : X → 𝓥 ̇ } where

  structure-preserving : SNI S 𝓦
                       → (σ τ : Σ S) → ⟨ σ ⟩ ＝ ⟨ τ ⟩ → 𝓦 ̇
  structure-preserving (ι , ρ , θ) = ι

  _≃[_]_ : Σ S → SNI S 𝓦 → Σ S → 𝓤 ⊔ 𝓦 ̇
  σ ≃[ δ ] τ = Σ p ꞉ (⟨ σ ⟩ ＝ ⟨ τ ⟩) , structure-preserving δ σ τ p

  structure-preservation-lemma :
     (δ : SNI S 𝓦)
     (σ τ : Σ S)
     (p : ⟨ σ ⟩ ＝ ⟨ τ ⟩)
   → (transport S p (structure σ) ＝ structure τ) ≃ structure-preserving δ σ τ p
  structure-preservation-lemma (ι , ρ , θ) (x , s) (x , t) (refl {x}) = γ
   where
    γ : (s ＝ t) ≃ ι (x , s) (x , t) refl
    γ = (canonical-map ι ρ s t , θ s t)

  module _ (δ@(ι , ρ , θ) : SNI S 𝓦) where

   characterization-of-＝ : (σ τ : Σ S) → (σ ＝ τ) ≃ (σ ≃[ δ ] τ)
   characterization-of-＝ σ τ =
    (σ ＝ τ)                                                            ≃⟨ i ⟩
    (Σ p ꞉ ⟨ σ ⟩ ＝ ⟨ τ ⟩ , transport S p (structure σ) ＝ structure τ) ≃⟨ ii ⟩
    (Σ p ꞉ ⟨ σ ⟩ ＝ ⟨ τ ⟩ , structure-preserving δ σ τ p)               ≃⟨ iii ⟩
    (σ ≃[ δ ] τ)                                                        ■
    where
     i   = Σ-＝-≃
     ii  = Σ-cong (structure-preservation-lemma δ σ τ)
     iii = ≃-refl _

   ＝-to-≃[] : (σ τ : Σ S) → (σ ＝ τ) → (σ ≃[ δ ] τ)
   ＝-to-≃[] σ σ refl = refl , ρ σ

   characterization-of-characterization-of-＝ :
    (σ τ : Σ S) → ⌜ characterization-of-＝ σ τ ⌝ ∼ ＝-to-≃[] σ τ
   characterization-of-characterization-of-＝ σ σ refl = refl

   ＝-to-≃[]-is-equiv : (σ τ : Σ S) → is-equiv (＝-to-≃[] σ τ)
   ＝-to-≃[]-is-equiv σ τ = equiv-closed-under-∼'
                             (⌜⌝-is-equiv (characterization-of-＝ σ τ))
                             (characterization-of-characterization-of-＝ σ τ)

  module _ (ι : (σ τ : Σ S) → ⟨ σ ⟩ ＝ ⟨ τ ⟩ → 𝓦 ̇ )
           (ρ : (σ : Σ S) → ι σ σ refl)
           {x : X}
         where

   private
    c = canonical-map ι ρ

   canonical-map-charac :
      (s t : S x)
      (p : s ＝ t)
    → c s t p ＝ transport (λ - → ι (x , s) (x , -) refl) p (ρ (x , s))
   canonical-map-charac s t p =
    (yoneda-lemma s (λ t → ι (x , s) (x , t) refl) (c s) t p)⁻¹

   when-canonical-map-is-equiv : ((s t : S x) → is-equiv (c s t))
                               ↔ ((s : S x) → ∃! t ꞉ S x , ι (x , s) (x , t) refl)
   when-canonical-map-is-equiv = (λ e s → Yoneda-Theorem-back  s (c s) (e s)) ,
                                 (λ φ s → Yoneda-Theorem-forth s (c s) (φ s))
\end{code}

The canonical map is an equivalence if (and only) if we have some
equivalence.

\begin{code}

   canonical-map-equiv-criterion :
     ((s t : S x) → (s ＝ t) ≃ ι (x , s) (x , t) refl)
    → (s t : S x) → is-equiv (c s t)
   canonical-map-equiv-criterion φ s = fiberwise-equiv-criterion'
                                        (λ t → ι (x , s) (x , t) refl)
                                        s (φ s) (c s)
\end{code}

But a retraction suffices for the canonical map to be an equivalence.

\begin{code}

   canonical-map-equiv-criterion' :
     ((s t : S x) → ι (x , s) (x , t) refl ◁ (s ＝ t))
    → (s t : S x) → is-equiv (c s t)
   canonical-map-equiv-criterion' φ s = fiberwise-equiv-criterion
                                         (λ t → ι (x , s) (x , t) refl)
                                         s (φ s) (c s)
\end{code}

TODO. The type SNI X 𝓥 should be contractible, with the
following center of contraction, using univalence. Notice that we are
currently not using univalence (or even function or propositional
extensionality) in this file.

\begin{code}

 canonical-SNI : {X : 𝓤 ̇ } (S : X → 𝓥 ̇ ) → SNI S 𝓥
 canonical-SNI {𝓤} {𝓥} {X} S = ι , ρ , canonical-map-is-equiv
  where
   ι : (σ τ : Σ S) → (⟨ σ ⟩ ＝ ⟨ τ ⟩ → 𝓥 ̇ )
   ι (x , s) (y , t) p = transport S p s ＝ t

   ρ : (σ : Σ S) → ι σ σ refl
   ρ (x , s) = refl

   canonical-map-is-equiv : {x : X} (s t : S x) → is-equiv (canonical-map ι ρ s t)
   canonical-map-is-equiv {x} s t = (canonical-map⁻¹ , η) ,
                                    (canonical-map⁻¹ , ε)
    where
     canonical-map⁻¹ : ι (x , s) (x , t) refl → s ＝ t
     canonical-map⁻¹ refl = refl

     η : canonical-map ι ρ s t ∘ canonical-map⁻¹ ∼ id
     η refl = refl

     ε : canonical-map⁻¹ ∘ canonical-map ι ρ s t ∼ id
     ε refl = refl

module Σ-identity-with-axioms where

 open Σ-identity

 module _ {X : 𝓤 ̇ }
          {S : X → 𝓥 ̇ }
          (axioms : (x : X) → S x → 𝓦 ̇ )
        where

  [_] : (Σ x ꞉ X , Σ s ꞉ S x , axioms x s) → Σ S
  [ x , s , _ ] = (x , s)

  ⟪_⟫ : (Σ x ꞉ X , Σ s ꞉ S x , axioms x s) → X
  ⟪ X , _ , _ ⟫ = X

  module _ (axioms-are-prop : (x : X) (s : S x) → is-prop (axioms x s)) where

   add-axioms : SNI S 𝓣
              → SNI (λ x → Σ s ꞉ S x , axioms x s) 𝓣
   add-axioms {𝓣} (ι , ρ , θ) = ι' , ρ' , θ'
    where
     S' : X → 𝓥 ⊔ 𝓦  ̇
     S' x = Σ s ꞉ S x , axioms x s

     ι' : (σ τ : Σ S') → ⟨ σ ⟩ ＝ ⟨ τ ⟩ → 𝓣 ̇
     ι' σ τ = ι [ σ ] [ τ ]

     ρ' : (σ : Σ S') → ι' σ σ refl
     ρ' σ = ρ [ σ ]

     θ' : {x : X} (s' t' : S' x) → is-equiv (canonical-map ι' ρ' s' t')
     θ' {x} (s , a) (t , b) = γ
      where
       π : S' x → S x
       π (s , _) = s

       π-is-embedding : is-embedding π
       π-is-embedding = pr₁-is-embedding (axioms-are-prop x)

       k : {s' t' : S' x} → is-equiv (ap π {s'} {t'})
       k {s'} {t'} = embedding-gives-embedding' π π-is-embedding s' t'

       l : canonical-map ι' ρ' (s , a) (t , b)
         ∼ canonical-map ι ρ s t ∘ ap π {s , a} {t , b}
       l (refl {s , a}) = 𝓻𝓮𝒻𝓵 (ρ (x , s))

       e : is-equiv (canonical-map ι ρ s t ∘ ap π {s , a} {t , b})
       e = ∘-is-equiv k (θ s t)

       γ : is-equiv (canonical-map ι' ρ' (s , a) (t , b))
       γ = equiv-closed-under-∼ _ _ e l

\end{code}

As expected, the axioms don't contribute to the characterization of
equality.

\begin{code}

   characterization-of-＝-with-axioms : (δ : SNI S 𝓣)
                                      → (σ τ : Σ x ꞉ X , Σ s ꞉ S x , axioms x s)
                                      → (σ ＝ τ) ≃ ([ σ ] ≃[ δ ] [ τ ])
   characterization-of-＝-with-axioms δ = characterization-of-＝ (add-axioms δ)

\end{code}

We now put together two structures on the same type of points.

\begin{code}

module Σ-identity-join where

 technical-lemma :
     {X : 𝓤 ̇ } {σ : X → X → 𝓥 ̇ }
     {Y : 𝓦 ̇ } {τ : Y → Y → 𝓣 ̇ }
     (f : (x₀ x₁ : X) → x₀ ＝ x₁ → σ x₀ x₁)
     (g : (y₀ y₁ : Y) → y₀ ＝ y₁ → τ y₀ y₁)
   → ((x₀ x₁ : X) → is-equiv (f x₀ x₁))
   → ((y₀ y₁ : Y) → is-equiv (g y₀ y₁))
   → ((x₀ , y₀) (x₁ , y₁) : X × Y)
          → is-equiv (λ (p : (x₀ , y₀) ＝ (x₁ , y₁)) → f x₀ x₁ (ap pr₁ p) ,
                                                       g y₀ y₁ (ap pr₂ p))
 technical-lemma {𝓤} {𝓥} {𝓦} {𝓣} {X} {σ} {Y} {τ} f g i j (x₀ , y₀) = γ
  where
   module _ ((x₁ , y₁) : X × Y) where
    r : (x₀ , y₀) ＝ (x₁ , y₁) → σ x₀ x₁ × τ y₀ y₁
    r p = f x₀ x₁ (ap pr₁ p) , g y₀ y₁ (ap pr₂ p)

    f' : (a : σ x₀ x₁) → x₀ ＝ x₁
    f' = inverse (f x₀ x₁) (i x₀ x₁)

    g' : (b : τ y₀ y₁) → y₀ ＝ y₁
    g' = inverse (g y₀ y₁) (j y₀ y₁)

    s : σ x₀ x₁ × τ y₀ y₁ → (x₀ , y₀) ＝ (x₁ , y₁)
    s (a , b) = to-×-＝ (f' a) (g' b)

    η : (c : σ x₀ x₁ × τ y₀ y₁) → r (s c) ＝ c
    η (a , b) =
      r (s (a , b))                               ＝⟨ refl ⟩
      r (to-×-＝  (f' a) (g' b))                  ＝⟨ refl ⟩
      (f x₀ x₁ (ap pr₁ (to-×-＝ (f' a) (g' b))) ,
       g y₀ y₁ (ap pr₂ (to-×-＝ (f' a) (g' b))))  ＝⟨ ii ⟩
      (f x₀ x₁ (f' a) , g y₀ y₁ (g' b))           ＝⟨ iii ⟩
      a , b                                       ∎
     where
      ii  = ap₂ (λ p q → f x₀ x₁ p , g y₀ y₁ q)
                (ap-pr₁-to-×-＝ (f' a) (g' b))
                (ap-pr₂-to-×-＝ (f' a) (g' b))
      iii = to-×-＝ (inverses-are-sections (f x₀ x₁) (i x₀ x₁) a)
                   (inverses-are-sections (g y₀ y₁) (j y₀ y₁) b)

   γ : (z : X × Y) → is-equiv (r z)
   γ = nats-with-sections-are-equivs (x₀ , y₀) r (λ z → (s z , η z))

 variable
  𝓥₀ 𝓥₁ 𝓦₀ 𝓦₁ : Universe

 open Σ-identity

 module _ {X : 𝓤 ̇ }
          {S₀ : X → 𝓥₀ ̇ }
          {S₁ : X → 𝓥₁ ̇ }
        where

  ⟪_⟫ : (Σ x ꞉ X , S₀ x × S₁ x) → X
  ⟪ x , s₀ , s₁ ⟫ = x

  [_]₀ : (Σ x ꞉ X , S₀ x × S₁ x) → Σ S₀
  [ x , s₀ , s₁ ]₀ = (x , s₀)

  [_]₁ : (Σ x ꞉ X , S₀ x × S₁ x) → Σ S₁
  [ x , s₀ , s₁ ]₁ = (x , s₁)

  join : SNI S₀ 𝓦₀
       → SNI S₁ 𝓦₁
       → SNI (λ x → S₀ x × S₁ x) (𝓦₀ ⊔ 𝓦₁)
  join {𝓦₀} {𝓦₁} (ι₀ , ρ₀ , θ₀) (ι₁ , ρ₁ , θ₁) = ι , ρ , θ
   where
    S : X → 𝓥₀ ⊔ 𝓥₁ ̇
    S x = S₀ x × S₁ x

    ι : (σ τ : Σ S) → ⟨ σ ⟩ ＝ ⟨ τ ⟩ → 𝓦₀ ⊔ 𝓦₁ ̇
    ι σ τ e = ι₀ [ σ ]₀ [ τ ]₀ e  ×  ι₁ [ σ ]₁ [ τ ]₁ e

    ρ : (σ : Σ S) → ι σ σ refl
    ρ σ = (ρ₀ [ σ ]₀ , ρ₁ [ σ ]₁)

    θ : {x : X} (s t : S x) → is-equiv (canonical-map ι ρ s t)
    θ {x} s@(s₀ , s₁) t@(t₀ , t₁) = γ
     where
      c : (p : s₀ , s₁ ＝ t₀ , t₁) → ι₀ (x , s₀) (x , t₀) refl
                                   × ι₁ (x , s₁) (x , t₁) refl

      c p = (canonical-map ι₀ ρ₀ s₀ t₀ (ap pr₁ p) ,
             canonical-map ι₁ ρ₁ s₁ t₁ (ap pr₂ p))

      i : is-equiv c
      i = technical-lemma
           (canonical-map ι₀ ρ₀)
           (canonical-map ι₁ ρ₁)
           θ₀ θ₁ s t

      e : canonical-map ι ρ s t ∼ c
      e (refl {s}) = 𝓻𝓮𝒻𝓵 (ρ₀ (x , s₀) , ρ₁ (x , s₁))

      γ : is-equiv (canonical-map ι ρ s t)
      γ = equiv-closed-under-∼ _ _ i e

  _≃⟦_,_⟧_ : (Σ x ꞉ X , S₀ x × S₁ x)
           → SNI S₀ 𝓦₀
           → SNI S₁ 𝓦₁
           → (Σ x ꞉ X , S₀ x × S₁ x)
           → 𝓤 ⊔ 𝓦₀ ⊔ 𝓦₁ ̇
  σ ≃⟦ δ₀ , δ₁ ⟧ τ = Σ p ꞉ (⟪ σ ⟫ ＝ ⟪ τ ⟫)
                         , structure-preserving δ₀ [ σ ]₀ [ τ ]₀ p
                         × structure-preserving δ₁ [ σ ]₁ [ τ ]₁ p

  characterization-of-join-＝ : (δ₀ : SNI S₀ 𝓦₀)
                                (δ₁ : SNI S₁ 𝓦₁)
                                (σ τ : Σ x ꞉ X , S₀ x × S₁ x)
                              → (σ ＝ τ) ≃ (σ ≃⟦ δ₀ , δ₁ ⟧ τ)
  characterization-of-join-＝ δ₀ δ₁ = characterization-of-＝ (join δ₀ δ₁)

\end{code}
