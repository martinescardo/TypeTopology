Martin Escardo, January 2018

Based on joint work with Cory Knapp.
http://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf

\begin{code}

-- open import UF -- hiding (𝟙) hiding (𝟙-is-prop) hiding (⊤)

open import SpartanMLTT
open import UF-Subsingletons hiding (⊤)
open import UF-Subsingletons-FunExt
open import UF-FunExt

module Dominance (U : Universe) (fe : ∀ U V → funext U V) where

U⁺ = U ⁺

D2 : (U ̇ → U ̇) → U⁺ ̇
D2 d = (X : U ̇) → is-prop(d X)

D3 : (U ̇ → U ̇) → U⁺ ̇
D3 d = (X : U ̇) → d X → is-prop X

D4 : (U ̇ → U ̇) → U ̇
D4 d = d 𝟙

D5 : (U ̇ → U ̇) → U⁺ ̇
D5 d = (P : U ̇) (Q : P → U ̇) → d P → ((p : P) → d(Q p)) → d(Σ Q)

is-dominance : (U ̇ → U ̇) → U⁺ ̇
is-dominance d = D2 d × D3 d × D4 d × D5 d

Dominance : U⁺ ̇
Dominance = Σ is-dominance

is-dominant : (D : Dominance) → U ̇ → U ̇
is-dominant (d , _) = d

being-dominant-is-a-prop : (D : Dominance) → (X : U ̇) → is-prop (is-dominant D X)
being-dominant-is-a-prop (_ , (isp , _)) = isp

dominant-types-are-props : (D : Dominance) → (X : U ̇) → is-dominant D X → is-prop X
dominant-types-are-props (_ , (_ , (disp , _))) = disp

𝟙-is-dominant : (D : Dominance) → is-dominant D 𝟙
𝟙-is-dominant (_ , (_ , (_ , (oisd , _)))) = oisd

dominant-closed-under-Σ : (D : Dominance) → (P : U ̇) (Q : P → U ̇)
                        → is-dominant D P → ((p : P) → is-dominant D (Q p)) → is-dominant D (Σ Q)
dominant-closed-under-Σ (_ , (_ , (_ , (_ , cus)))) = cus

being-a-dominance-is-a-prop : (d : U ̇ → U ̇) → is-prop (is-dominance d)
being-a-dominance-is-a-prop d = iprops-are-propositions lemma
 where
  lemma : is-dominance d → is-prop (is-dominance d)
  lemma isd = Σ-is-prop
               (Π-is-prop (fe U⁺ U) λ _ → is-prop-is-a-prop (fe U U))
               λ _ → Σ-is-prop
                       (Π-is-prop (fe U⁺ U)
                          λ _ → Π-is-prop (fe U U)
                                   λ _ → is-prop-is-a-prop (fe U U))
                       λ _ → Σ-is-prop
                               (being-dominant-is-a-prop (d , isd) 𝟙)
                               λ _ → Π-is-prop (fe U⁺ U⁺)
                                        λ _ → Π-is-prop (fe U⁺ U)
                                                 λ Q → Π-is-prop (fe U U)
                                                          λ _ → Π-is-prop (fe U U)
                                                                   λ _ → being-dominant-is-a-prop (d , isd) (Σ Q)


\end{code}

Example: the decidable propositions form a dominance.

\begin{code}

module DecidableDominance where

 open import DecidableAndDetachable

 decidable-dominance : Dominance
 decidable-dominance = (λ P → is-prop P × decidable P) ,
                       (λ P → Σ-is-prop
                                 (is-prop-is-a-prop (fe U U))
                                 (decidable-types-are-props (fe U U₀))) ,
                       (λ X → pr₁) ,
                       (𝟙-is-prop , inl *) ,
                       λ P Q dP dQ → Σ-is-prop (pr₁ dP) (λ p → pr₁(dQ p)) ,
                                      decidable-closed-under-Σ (pr₁ dP) (pr₂ dP) λ p → pr₂ (dQ p)

module lift (d : U ̇ → U ̇) (isd : is-dominance d) where

 D : Dominance
 D = (d , isd)

 L : ∀ {V} (X : V ̇) → U⁺ ⊔ V ̇
 L X = Σ \(P : U ̇) → d P × (P → X)

 LL : ∀ {V} (X : V ̇) → U⁺ ⊔ V ̇
 LL X = L(L X)

 _⇀_ : ∀ {V W} → V ̇ → W ̇ → U⁺ ⊔ V ⊔ W ̇
 X ⇀ Y = X → L Y

 isDefined : ∀ {V} {X : V ̇} → L X → U ̇
 isDefined (P , (isdp , φ)) = P

 is-dominantisDefined : ∀ {V} {X : V ̇} → (x̃ : L X) → is-dominant D (isDefined x̃)
 is-dominantisDefined (P , (isdp , φ)) = isdp

 value : ∀ {V} {X : V ̇} → (x̃ : L X) → isDefined x̃ → X
 value (P , (isdp , φ)) = φ

 η : ∀ {V} {X : V ̇} → X → L X
 η x = 𝟙 , 𝟙-is-dominant D , λ _ → x

 extension : ∀ {V W} {X : V ̇} {Y : W ̇} → (X ⇀ Y) → (L X → L Y)
 extension {V} {W} {X} {Y} f (P , (isdp , φ)) = (Q , (isdq , γ))
  where
   Q : U ̇
   Q = Σ \(p : P) → isDefined(f(φ p))

   isdq : is-dominant D Q
   isdq = dominant-closed-under-Σ D
            P
            (λ p → isDefined(f(φ p)))
            isdp
            (λ p → is-dominantisDefined (f (φ p)))

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
