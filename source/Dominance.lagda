Martin Escardo, January 2018

Based on joint work with Cory Knapp.
http://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf

\begin{code}

open import UF hiding (𝟙) hiding (𝟙-isProp) hiding (⊤)

module Dominance (U : Universe) (fe : ∀ U V → FunExt U V) where

U' = U ′

data 𝟙 : U ̇ where
 ⋆ : 𝟙

𝟙-isProp : isProp 𝟙
𝟙-isProp ⋆ ⋆ = refl

D2 : (U ̇ → U ̇) → U' ̇
D2 d = (X : U ̇) → isProp(d X)

D3 : (U ̇ → U ̇) → U' ̇
D3 d = (X : U ̇) → d X → isProp X

D4 : (U ̇ → U ̇) → U ̇
D4 d = d 𝟙

D5 : (U ̇ → U ̇) → U' ̇
D5 d = (P : U ̇) (Q : P → U ̇) → d P → ((p : P) → d(Q p)) → d(Σ Q)

isDominance : (U ̇ → U ̇) → U' ̇
isDominance d = D2 d × D3 d × D4 d × D5 d

Dominance : U' ̇
Dominance = Σ isDominance

isDominant : (D : Dominance) → U ̇ → U ̇
isDominant (d , _) = d

being-dominant-isProp : (D : Dominance) → (X : U ̇) → isProp (isDominant D X)
being-dominant-isProp (_ , (isp , _)) = isp

dominant-type-isProp : (D : Dominance) → (X : U ̇) → isDominant D X → isProp X
dominant-type-isProp (_ , (_ , (disp , _))) = disp

𝟙-isDominant : (D : Dominance) → isDominant D 𝟙
𝟙-isDominant (_ , (_ , (_ , (oisd , _)))) = oisd

dominant-closed-under-Σ : (D : Dominance) → (P : U ̇) (Q : P → U ̇)
                        → isDominant D P → ((p : P) → isDominant D (Q p)) → isDominant D (Σ Q)
dominant-closed-under-Σ (_ , (_ , (_ , (_ , cus)))) = cus

isDominance-isProp : (d : U ̇ → U ̇) → isProp (isDominance d)
isDominance-isProp d = ip-is-p lemma
 where
  lemma : isDominance d → isProp (isDominance d)
  lemma isd = isProp-closed-under-Σ
               (isProp-exponential-ideal (fe U' U) λ _ → isProp-isProp (fe U U))
               λ _ → isProp-closed-under-Σ
                       (isProp-exponential-ideal (fe U' U)
                          λ _ → isProp-exponential-ideal (fe U U)
                                   λ _ → isProp-isProp (fe U U))
                       λ _ → isProp-closed-under-Σ
                               (being-dominant-isProp (d , isd) 𝟙)
                               λ _ → isProp-exponential-ideal (fe U' U')
                                        λ _ → isProp-exponential-ideal (fe U' U)
                                                 λ Q → isProp-exponential-ideal (fe U U)
                                                          λ _ → isProp-exponential-ideal (fe U U)
                                                                   λ _ → being-dominant-isProp (d , isd) (Σ Q)


\end{code}

Example: the decidable propositions form a dominance.

\begin{code}

module DecidableDominance where

 open import DecidableAndDetachable

 decidable-dominance : Dominance
 decidable-dominance = (λ P → isProp P × decidable P) ,
                       (λ P → isProp-closed-under-Σ 
                                 (isProp-isProp (fe U U))
                                 (decidable-isProp (fe U U₀))) ,
                       (λ X → pr₁) ,
                       (𝟙-isProp , inl ⋆) ,
                       λ P Q dP dQ → isProp-closed-under-Σ (pr₁ dP) (λ p → pr₁(dQ p)) ,
                                      decidable-closed-under-Σ (pr₁ dP) (pr₂ dP) λ p → pr₂ (dQ p)

module lift (d : U ̇ → U ̇) (isd : isDominance d) where

 D : Dominance
 D = (d , isd)

 L : ∀ {V} (X : V ̇) → U' ⊔ V ̇
 L X = Σ \(P : U ̇) → d P × (P → X)

 LL : ∀ {V} (X : V ̇) → U' ⊔ V ̇
 LL X = L(L X) 

 _⇀_ : ∀ {V W} → V ̇ → W ̇ → U' ⊔ V ⊔ W ̇
 X ⇀ Y = X → L Y

 isDefined : ∀ {V} {X : V ̇} → L X → U ̇
 isDefined (P , (isdp , φ)) = P

 isDominantisDefined : ∀ {V} {X : V ̇} → (x̃ : L X) → isDominant D (isDefined x̃)
 isDominantisDefined (P , (isdp , φ)) = isdp

 value : ∀ {V} {X : V ̇} → (x̃ : L X) → isDefined x̃ → X
 value (P , (isdp , φ)) = φ

 η : ∀ {V} {X : V ̇} → X → L X
 η x = 𝟙 , 𝟙-isDominant D , λ _ → x

 extension : ∀ {V W} {X : V ̇} {Y : W ̇} → (X ⇀ Y) → (L X → L Y)
 extension {V} {W} {X} {Y} f (P , (isdp , φ)) = (Q , (isdq , γ))
  where
   Q : U ̇
   Q = Σ \(p : P) → isDefined(f(φ p))
   
   isdq : isDominant D Q
   isdq = dominant-closed-under-Σ D
            P
            (λ p → isDefined(f(φ p)))
            isdp
            (λ p → isDominantisDefined (f (φ p)))
            
   γ : Q → Y
   γ (p , def) = value(f (φ p)) def

 _♯ : ∀ {V W} {X : V ̇} {Y : W ̇} → (X ⇀ Y) → (L X → L Y)
 f ♯ = extension f

 _◌_ : ∀ {V W T} {X : V ̇} {Y : W ̇} {Z : T ̇}
     → (Y ⇀ Z) → (X ⇀ Y) → (X ⇀ Z)
 g ◌ f = g ♯ ∘ f

 μ : ∀ {V} {X : V ̇} → L(L X) → L X
 μ = extension id

 {- TODO:
 kleisli-law₀ : ∀ {V} {X : V ̇} → extension (η {V} {X}) ∼ id
 kleisli-law₀ {V} {X} (P , (isdp , φ)) = {!!}

 kleisli-law₁ : ∀ {V W} {X : V ̇} {Y : W ̇} (f : X ⇀ Y) → extension f ∘ η ∼ f
 kleisli-law₁ {V} {W} {X} {Y} f x = {!!}


 kleisli-law₂ : ∀ {V W T} {X : V ̇} {Y : W ̇} {Z : T ̇} (f : X ⇀ Y) (g : Y ⇀ Z)
              → (g ♯ ∘ f)♯ ∼ g ♯ ∘ f ♯
 kleisli-law₂ {V} {W} {T} {X} {Y} {Z} f g (P , (isdp , φ)) = {!!}
 -}


\end{code}

The following is based on http://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf

\begin{code}


module SyntheticTopology (isOpenProp : U ̇ → U ̇)
                         (isd : isDominance isOpenProp)
                         (pt : PropTrunc) where
                         
 open PropositionalTruncation (pt)
 
 𝕊 : U' ̇
 𝕊 = Σ \(G : U ̇) → isOpenProp G

 ⊤ : 𝕊
 ⊤ = (𝟙 , 𝟙-isDominant (isOpenProp , isd))

 OpenSubset : U ̇ → U' ̇
 OpenSubset X = X → 𝕊

 _∈_ : {X : U ̇} → X → OpenSubset X → U ̇
 x ∈ G = pr₁(G x)

 isCompact : U ̇ → U' ̇
 isCompact X = (G : OpenSubset X) → isOpenProp(∀ (x : X) → x ∈ G)

 isOvert : U ̇ → U' ̇
 isOvert X = (G : OpenSubset X) → isOpenProp (∃ \(x : X) → x ∈ G)

 isClosedProp : U ̇ → U' ̇
 isClosedProp F = ∀ G → isOpenProp G → isOpenProp(F → G)

 isClosedSubset : {X : U ̇} → (X → U ̇) → U' ̇
 isClosedSubset A = ∀ x → isClosedProp(A x)

 isDiscrete : U ̇ → U ̇
 isDiscrete X = (x y : X) → isOpenProp(x ≡ y)

 isHausdorff : U ̇ → U' ̇
 isHausdorff X = (x y : X) → isClosedProp(x ≡ y)


\end{code}

TODO. Prove the theorems of loc. cit.
