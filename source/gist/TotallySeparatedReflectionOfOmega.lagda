Martin Escardo, June 2025.

The totally separated reflection of the type Ω 𝓤 of propositions.

We show, assuming propositional resizing, that the type

    T = WEM → 𝟚

has the universal property of the totally separated reflection of Ω 𝓤,
where

    WEM := (p : Ω 𝓤) → ¬ (p holds) + ¬¬ (p holds)

is the principle of weak excluded middle.

The unit η : Ω 𝓤 → T of the reflection sends a proposition p to the
function that, given a witness of WEM, gives ₀ or ₁ according to
whether ¬ p holds or ¬¬ p holds.

The universal property says that, for every totally separated type Y,
precomposition with η is an equivalence

    (T → Y) ≃ (Ω 𝓤 → Y).

Resizing is used to define a section s : T → Ω 𝓤 of η by
s t = "the proposition that t is the constant function ₁".

TODO. Can this be shown without assuming propositional resizing?

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.Subsingletons

module gist.TotallySeparatedReflectionOfOmega
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import TypeTopology.TotallySeparated
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Sets
open import UF.Size
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt

\end{code}

We work with a fixed universe 𝓤 and assume resizing of 𝓤⁺-valued
propositions down to 𝓤.

\begin{code}

module _ {𝓤 : Universe} (r : propositional-resizing (𝓤 ⁺) 𝓤) where

 WEM : 𝓤 ⁺ ̇
 WEM = (p : Ω 𝓤) → is-decidable (¬ (p holds))

 WEM-is-prop : is-prop WEM
 WEM-is-prop = Π-is-prop fe
                (λ p → decidability-of-prop-is-prop fe
                        (negations-are-props fe))

\end{code}

The carrier T of the candidate reflection.

\begin{code}

 T : 𝓤 ⁺ ̇
 T = WEM → 𝟚

 T-is-totally-separated : is-totally-separated T
 T-is-totally-separated = Π-is-totally-separated fe
                           (λ _ → 𝟚-is-totally-separated)

 T-is-set : is-set T
 T-is-set = totally-separated-types-are-sets fe T
             T-is-totally-separated

 τ : 𝟚 → T
 τ b = λ _ → b

 τ₀ τ₁ : T
 τ₀ = τ ₀
 τ₁ = τ ₁

\end{code}

The unit.

\begin{code}

 δ : {A B : 𝓤 ̇ } → A + B → 𝟚
 δ (inl _) = ₀
 δ (inr _) = ₁

 η : Ω 𝓤 → T
 η Q w = δ (w Q)

 η₀ : (Q : Ω 𝓤) (w : WEM) → ¬ (Q holds) → η Q w ＝ ₀
 η₀ Q w ν = I (w Q)
  where
   I : (d : is-decidable (¬ (Q holds))) → δ d ＝ ₀
   I (inl _) = refl
   I (inr φ) = 𝟘-elim (φ ν)

 η₁ : (Q : Ω 𝓤) (w : WEM) → ¬¬ (Q holds) → η Q w ＝ ₁
 η₁ Q w n = I (w Q)
  where
   I : (d : is-decidable (¬ (Q holds))) → δ d ＝ ₁
   I (inl ν) = 𝟘-elim (n ν)
   I (inr φ) = refl


\end{code}

Using propositional resizing, the map η has a section s. Its defining
property is that "s t holds" is a small copy of the proposition t ＝
τ₁.

\begin{code}

 equality-with-τ₁-is-prop : (t : T) → is-prop (t ＝ τ₁)
 equality-with-τ₁-is-prop t = T-is-set

 s : T → Ω 𝓤
 s t = resize r (t ＝ τ₁) (equality-with-τ₁-is-prop t) ,
       resize-is-prop r (t ＝ τ₁) (equality-with-τ₁-is-prop t)

 to-s-holds : (t : T) → (t ＝ τ₁) → s t holds
 to-s-holds t = to-resize r (t ＝ τ₁) (equality-with-τ₁-is-prop t)

 from-s-holds : (t : T) → s t holds → (t ＝ τ₁)
 from-s-holds t = from-resize r (t ＝ τ₁) (equality-with-τ₁-is-prop t)

\end{code}

The retraction equation η ∘ s ∼ id.

\begin{code}

 ηs : (t : T) → η (s t) ＝ t
 ηs t = dfunext fe (λ w → 𝟚-equality-cases (I₀ w) (I₁ w))
  where
   I₀ : (w : WEM) → t w ＝ ₀ → η (s t) w ＝ t w
   I₀ w e = η (s t) w ＝⟨ η₀ (s t) w II ⟩
               ₀         ＝⟨ e ⁻¹ ⟩
               t w       ∎
    where
     II : ¬ (s t holds)
     II ν = zero-is-not-one
             (₀    ＝⟨ e ⁻¹ ⟩
              t w  ＝⟨ happly (from-s-holds t ν) w ⟩
              τ₁ w ＝⟨ refl ⟩
              ₁    ∎)

   I₁ : (w : WEM) → t w ＝ ₁ → η (s t) w ＝ t w
   I₁ w e = η (s t) w ＝⟨ η₁ (s t) w IV ⟩
               ₁      ＝⟨ e ⁻¹ ⟩
               t w    ∎
    where
     III : t ＝ τ₁
     III = t       ＝⟨ dfunext fe (λ w' → ap t (WEM-is-prop w' w)) ⟩
           τ (t w) ＝⟨ ap τ e ⟩
           τ₁      ∎

     IV : ¬¬ (s t holds)
     IV n = n (to-s-holds t III)

 lemma-⊥ : (h : Ω 𝓤 → 𝟚) (p : Ω 𝓤) → ¬ (p holds) → h p ＝ h ⊥
 lemma-⊥ h p ν = ap h (fails-gives-equal-⊥ pe fe p ν)

 lemma-⊤ : (h : Ω 𝓤 → 𝟚) (p : Ω 𝓤) → p holds → h p ＝ h ⊤
 lemma-⊤ h p e = ap h (holds-gives-equal-⊤ pe fe p e)

 constancy-lemma : (h : Ω 𝓤 → 𝟚) → h ⊥ ＝ h ⊤ → (p : Ω 𝓤) → h p ＝ h ⊥
 constancy-lemma h e p = ⊥-⊤-density' fe pe 𝟚-is-¬¬-separated h e p ⊥

 to-WEM : (h : Ω 𝓤 → 𝟚) → h ⊥ ≠ h ⊤ → WEM
 to-WEM h d p = I (𝟚-is-discrete (h p) (h ⊤))
  where
   I : is-decidable (h p ＝ h ⊤) → is-decidable (¬ (p holds))
   I (inl e) = inr (λ ν → d (h ⊥ ＝⟨ (lemma-⊥ h p ν) ⁻¹ ⟩
                             h p ＝⟨ e ⟩
                             h ⊤ ∎))
   I (inr ν) = inl (λ e → ν (lemma-⊤ h p e))

\end{code}

Although s is not necessarily a retraction of η, any function Ω 𝓤 → 𝟚
believes it is, assuming WEM. But then this can be used to get the
same conclusion without assuming WEM.

\begin{code}

 sη-with-WEM : WEM → (h : Ω 𝓤 → 𝟚) (p : Ω 𝓤) → h (s (η p)) ＝ h p
 sη-with-WEM w h p = I (w p)
  where
   I : is-decidable (¬ (p holds)) → h (s (η p)) ＝ h p
   I (inr φ) = h (s (η p)) ＝⟨ ap h (holds-gives-equal-⊤ pe fe (s (η p)) III) ⟩
               h ⊤         ＝⟨ IV ⁻¹ ⟩
               h p         ∎
    where
     II : η p ＝ τ₁
     II = dfunext fe (λ w → η₁ p w φ)

     III : s (η p) holds
     III = to-s-holds (η p) II

     IV : h p ＝ h ⊤
     IV = 𝟚-is-¬¬-separated (h p) (h ⊤) (λ k → φ (λ q → k (lemma-⊤ h p q)))

   I (inl ν) = h (s (η p)) ＝⟨ ap h (fails-gives-equal-⊥ pe fe (s (η p)) V) ⟩
               h ⊥         ＝⟨ (lemma-⊥ h p ν) ⁻¹ ⟩
               h p         ∎
    where
     V : ¬ (s (η p) holds)
     V n = zero-is-not-one
             (₀       ＝⟨ (η₀ p w ν)⁻¹ ⟩
              η p w ＝⟨ happly (from-s-holds (η p) n) w ⟩
              τ₁ w  ＝⟨ refl ⟩
              ₁       ∎)

 sη : (h : Ω 𝓤 → 𝟚) (p : Ω 𝓤) → h (s (η p)) ＝ h p
 sη h p = 𝟚-is-¬¬-separated (h (s (η p))) (h p) γ
  where
   γ : ¬¬ (h (s (η p)) ＝ h p)
   γ ν = ν (h (s (η p)) ＝⟨ constancy-lemma h II (s (η p)) ⟩
            h ⊥         ＝⟨ (constancy-lemma h II p) ⁻¹ ⟩
            h p         ∎)
    where
     I : ¬ WEM
     I w = ν (sη-with-WEM w h p)

     II : h ⊥ ＝ h ⊤
     II = 𝟚-is-¬¬-separated (h ⊥) (h ⊤) (λ d → I (to-WEM h d))

\end{code}

The universal property says that for every totally separated type Y,
precomposition with η is an equivalence, with inverse given by
precomposition with s.

\begin{code}

 ρ : {Y : 𝓦 ̇ } → (T → Y) → (Ω 𝓤 → Y)
 ρ g = g ∘ η

 ρ-is-equiv : (Y : 𝓦 ̇ )
            → is-totally-separated Y
            → is-equiv ρ
 ρ-is-equiv Y ts = qinvs-are-equivs ρ (ρ⁻¹ , I , II)
  where
   ρ⁻¹ : (Ω 𝓤 → Y) → (T → Y)
   ρ⁻¹ f = f ∘ s

   I : (g : T → Y) → ρ⁻¹ (ρ g) ＝ g
   I g = dfunext fe (λ t → ap g (ηs t))

   II : (f : Ω 𝓤 → Y) → ρ (ρ⁻¹ f) ＝ f
   II f = dfunext fe IV
    where
     III : (p : Ω 𝓤) (π : Y → 𝟚) → π (f (s (η p))) ＝ π (f p)
     III p π = sη (π ∘ f) p

     IV : (p : Ω 𝓤) → f (s (η p)) ＝ f p
     IV p = ts (III p)

\end{code}
