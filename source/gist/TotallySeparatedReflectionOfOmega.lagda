Martin Escardo, 17-19 June 2025.

The totally separated reflection of the type Ω of propositions.

Any type X has a totally separated reflection, given by the image of
the evaluation map X → ((X → 𝟚) → 𝟚). Here we explore whether the
totally separated reflection of Ω has a more direct description.

We show, assuming propositional resizing, that the type

    T := (WEM → 𝟚)

has the universal property of the totally separated reflection of Ω,
where

    WEM := (p : Ω) → ¬ (p holds) + ¬¬ (p holds)

is the principle of weak excluded middle.

The unit η : Ω → T of the reflection sends a proposition p to the
function that, given a witness of WEM, gives ₀ or ₁ according to
whether ¬ p holds or ¬¬ p holds.

The universal property says that, for every totally separated type Y,
precomposition with η (the restriction map) is an equivalence

    (T → Y) ≃ (Ω → Y).

Resizing is used to define a section s : T → Ω of η by
s t = "the resized proposition that t is the constant function ₁".

Can this equivalence be established without assuming propositional
resizing? We don't know, but we explore this a bit here. In particular,
we establish the equivalence, without resizing, for types Y that are
retracts of powers of 𝟚.

TODO. Is every totally separated type a retract of a power of 𝟚,
without assuming resizing? No, because this excludes the empty type
(as pointed out to us by Jason Carr). But what can we say in this
direction?

A side-conclusion of this technical development is that we have an
equivalence

  (Ω → 𝟚) ≃ (𝟚 + WEM × 𝟚).

There are always two maps Ω → 𝟚, namely the constant ones, plus two
when WEM holds.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Subsingletons

open import MLTT.Spartan

module gist.TotallySeparatedReflectionOfOmega
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (𝓤 : Universe)
       where

open import MLTT.Two-Properties
open import TypeTopology.CompactTypes
open import TypeTopology.MicroTychonoff
open import TypeTopology.TotallySeparated
open import TypeTopology.SigmaTotallySeparated
open import UF.Base
open import UF.ClassicalLogic
             using (EM ; LEM ; EM-gives-LEM ; double-negation-of-decision)
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.Size
open import UF.SubtypeClassifier renaming (Ω to Ω-of)
open import UF.Subsingletons-FunExt

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

 𝓤⁺ = 𝓤 ⁺

 Ω : 𝓤⁺ ̇
 Ω = Ω-of 𝓤

 WEM : 𝓤⁺ ̇
 WEM = (p : Ω) → is-decidable (¬ (p holds))

 WEM-is-prop : is-prop WEM
 WEM-is-prop = Π-is-prop fe
                (λ p → decidability-of-prop-is-prop fe (negations-are-props fe))

T : 𝓤⁺ ̇
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

NB. The function δ needs --lossy-unification to avoid unsolved constraints.

\begin{code}

δ : {p : Ω} → is-decidable (¬ (p holds)) → 𝟚
δ (inl _) = ₀
δ (inr _) = ₁

\end{code}

The unit of the reflection and its non-definitional "computation" rules.

\begin{code}

η : Ω → T
η p w = δ (w p)

η₀ : (p : Ω) (w : WEM) → ¬ (p holds) → η p w ＝ ₀
η₀ p w ν = I (w p)
 where
  I : (d : is-decidable (¬ (p holds))) → δ d ＝ ₀
  I (inl _) = refl
  I (inr φ) = 𝟘-elim (φ ν)

η₁ : (p : Ω) (w : WEM) → ¬¬ (p holds) → η p w ＝ ₁
η₁ p w νν = I (w p)
 where
  I : (d : is-decidable (¬ (p holds))) → δ d ＝ ₁
  I (inl ν) = 𝟘-elim (νν ν)
  I (inr _) = refl

η⊥ : η ⊥ ＝ τ₀
η⊥ = dfunext fe (λ w → η₀ ⊥ w ⊥-doesnt-hold)

η⊤ : η ⊤ ＝ τ₁
η⊤ = dfunext fe (λ w → η₁ ⊤ w (¬¬-intro ⊤-holds))

τ-lemma : (t : T) (w : WEM) → t ＝ τ (t w)
τ-lemma t w = dfunext fe (λ w' → ap t (WEM-is-prop w' w))

\end{code}

Sufficient condition for boolean-valued maps on Ω being constant.

\begin{code}

lemma-⊥ : (h : Ω → 𝟚) (p : Ω) → ¬ (p holds) → h p ＝ h ⊥
lemma-⊥ h p ν = ap h (fails-gives-equal-⊥ pe fe p ν)

lemma-⊤ : (h : Ω → 𝟚) (p : Ω) → p holds → h p ＝ h ⊤
lemma-⊤ h p e = ap h (holds-gives-equal-⊤ pe fe p e)

\end{code}

Given h : Ω → 𝟚, we can decide whether h ⊥ ＝ h ⊤ or not.

 * If so, then h is constant.
 * Otherwise, WEM follows.

\begin{code}

constancy-lemma : (h : Ω → 𝟚) → h ⊥ ＝ h ⊤ → (p : Ω) → h p ＝ h ⊥
constancy-lemma h e p = 𝟚-is-¬¬-separated (h p) (h ⊥) I
 where
  I : ¬¬ (h p ＝ h ⊥)
  I νν = III II
   where
    II : ¬ (p holds)
    II ν = νν (h p ＝⟨ lemma-⊤ h p ν ⟩
                 h ⊤ ＝⟨ e ⁻¹ ⟩
                 h ⊥ ∎)
    III : ¬¬ (p holds)
    III ν = νν (lemma-⊥ h p ν)

to-WEM : (h : Ω → 𝟚) → h ⊥ ≠ h ⊤ → WEM
to-WEM h d p = I (𝟚-is-discrete (h p) (h ⊤))
 where
  I : is-decidable (h p ＝ h ⊤) → is-decidable (¬ (p holds))
  I (inl e) = inr (λ ν → d (h ⊥ ＝⟨ (lemma-⊥ h p ν) ⁻¹ ⟩
                            h p ＝⟨ e ⟩
                            h ⊤ ∎))
  I (inr ν) = inl (λ e → ν (lemma-⊤ h p e))

\end{code}

Restriction along η:

\begin{code}

ρ : (Z : 𝓦 ̇ ) → (T → Z) → (Ω → Z)
ρ Z g = g ∘ η

\end{code}

We now show that T is the totally separated reflection of Ω assuming
resizing, and after that we record everything we know about the
universal property of T without assuming resizing.

\begin{code}

module T-is-ts-reflection-of-Ω-assuming-resizing
        (r : propositional-resizing 𝓤⁺ 𝓤)
       where

 being-equal-to-τ₁-is-prop : (t : T) → is-prop (t ＝ τ₁)
 being-equal-to-τ₁-is-prop t = T-is-set

\end{code}

We apply resizing to the proposition (t ＝ τ₁).

\begin{code}

 s : T → Ω
 s t = resize r (t ＝ τ₁) (being-equal-to-τ₁-is-prop t) ,
       resize-is-prop r (t ＝ τ₁) (being-equal-to-τ₁-is-prop t)

 to-s-holds : (t : T) → (t ＝ τ₁) → s t holds
 to-s-holds t = to-resize r (t ＝ τ₁) (being-equal-to-τ₁-is-prop t)

 from-s-holds : (t : T) → s t holds → (t ＝ τ₁)
 from-s-holds t = from-resize r (t ＝ τ₁) (being-equal-to-τ₁-is-prop t)

 ηs : (t : T) → η (s t) ＝ t
 ηs t = dfunext fe (λ w → 𝟚-equality-cases (I w) (II w))
  where
   I : (w : WEM) → t w ＝ ₀ → η (s t) w ＝ t w
   I w e₀ = η (s t) w ＝⟨ η₀ (s t) w III ⟩
            ₀         ＝⟨ e₀ ⁻¹ ⟩
            t w        ∎
    where
     III : ¬ (s t holds)
     III ν = zero-is-not-one (₀     ＝⟨ e₀ ⁻¹ ⟩
                              t  w  ＝⟨ happly (from-s-holds t ν) w ⟩
                              τ₁ w  ＝⟨ refl ⟩
                              ₁     ∎)
   II : (w : WEM) → t w ＝ ₁ → η (s t) w ＝ t w
   II w e = η (s t) w ＝⟨ η₁ (s t) w V ⟩
             ₁         ＝⟨ e ⁻¹ ⟩
             t w       ∎
    where
     IV : t ＝ τ₁
     IV = t       ＝⟨ τ-lemma t w ⟩
          τ (t w) ＝⟨ ap τ e ⟩
          τ₁      ∎
     V : ¬¬ (s t holds)
     V νν = νν (to-s-holds t IV)

\end{code}

Although s is not necessarily a retraction of η, any function Ω → 𝟚
believes it is, assuming WEM. But then this can be used to get the
same conclusion without assuming WEM.

\begin{code}

 sη-with-WEM : (h : Ω → 𝟚) (p : Ω) → WEM → h (s (η p)) ＝ h p
 sη-with-WEM h p w = I (w p)
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
     IV = 𝟚-is-¬¬-separated (h p) (h ⊤)
           (λ k → φ (λ (ph : p holds) → k (lemma-⊤ h p ph)))
   I (inl ν) = h (s (η p)) ＝⟨ ap h (fails-gives-equal-⊥ pe fe (s (η p)) II) ⟩
               h ⊥         ＝⟨ (lemma-⊥ h p ν) ⁻¹ ⟩
               h p         ∎
    where
     II : ¬ (s (η p) holds)
     II sh = zero-is-not-one
              (₀      ＝⟨ (η₀ p w ν) ⁻¹ ⟩
               η p w  ＝⟨ happly (from-s-holds (η p) sh) w ⟩
               τ₁ w   ＝⟨ refl ⟩
               ₁      ∎)

 sη : (h : Ω → 𝟚) (p : Ω) → h (s (η p)) ＝ h p
 sη h p = 𝟚-is-¬¬-separated (h (s (η p))) (h p) I
  where
   I : ¬¬ (h (s (η p)) ＝ h p)
   I k = k (h (s (η p)) ＝⟨ constancy-lemma h III (s (η p)) ⟩
            h ⊥         ＝⟨ (constancy-lemma h III p) ⁻¹ ⟩
            h p         ∎)
    where
     II : ¬ WEM
     II w = k (sη-with-WEM h p w)

     III : h ⊥ ＝ h ⊤
     III = 𝟚-is-¬¬-separated (h ⊥) (h ⊤) (λ ν → II (to-WEM h ν))

 ρ-is-equiv : (Y : 𝓦 ̇ )
            → is-totally-separated Y
            → is-equiv (ρ Y)
 ρ-is-equiv Y ts = qinvs-are-equivs (ρ Y) (ρ⁻¹ , I , II)
  where
   ρ⁻¹ : (Ω → Y) → (T → Y)
   ρ⁻¹ f = f ∘ s

   I : (g : T → Y) → ρ⁻¹ (ρ Y g) ＝ g
   I g = dfunext fe (λ t → ap g (ηs t))

   II : (f : Ω → Y) → ρ Y (ρ⁻¹ f) ＝ f
   II f = dfunext fe (λ p → ts (λ h → sη (λ q → h (f q)) p))

 reflection : (Y : 𝓦 ̇ )
            → is-totally-separated Y
            → (T → Y) ≃ (Ω → Y)
 reflection Y ts = ρ Y , ρ-is-equiv Y ts

 module _ (pt : propositional-truncations-exist) where

  open import UF.ImageAndSurjection pt
  open PropositionalTruncation pt

  resizing-gives-ηsurjection : is-surjection η
  resizing-gives-ηsurjection t = ∣ s t , ηs t ∣

\end{code}

This is the end of the above module assuming resizing, and we now
record everything we know about the universal property of T without
assuming resizing.

We first show that the universal property holds when 𝟚 is the target type.

\begin{code}

extension₂'-along-η : (f : Ω → 𝟚) → is-decidable (f ⊥ ＝ f ⊤) → T → 𝟚
extension₂'-along-η f (inl _) t = f ⊥
extension₂'-along-η f (inr ν) t = 𝟚-cases (f ⊥) (f ⊤) (t (to-WEM f ν))

extension₂-along-η : (Ω → 𝟚) → (T → 𝟚)
extension₂-along-η f = extension₂'-along-η f (𝟚-is-discrete (f ⊥) (f ⊤))

extension₂'-property : (f : Ω → 𝟚) (d : is-decidable (f ⊥ ＝ f ⊤)) (p : Ω)
                     → extension₂'-along-η f d (η p) ＝ f p
extension₂'-property f (inl e)  p = (constancy-lemma f e p) ⁻¹
extension₂'-property f (inr ne) p = I (to-WEM f ne p)
 where
  I : (d : is-decidable (¬ (p holds))) → 𝟚-cases (f ⊥) (f ⊤) (δ d) ＝ f p
  I (inl ν) = (lemma-⊥ f p ν) ⁻¹
  I (inr φ) = (𝟚-is-¬¬-separated (f p) (f ⊤)
                (λ ν → φ (λ ph → ν (lemma-⊤ f p ph)))) ⁻¹

extension₂-property : (f : Ω → 𝟚) (p : Ω) → extension₂-along-η f (η p) ＝ f p
extension₂-property f p = extension₂'-property f (𝟚-is-discrete (f ⊥) (f ⊤)) p

ρ₂ : (T → 𝟚) → Ω → 𝟚
ρ₂ = ρ 𝟚

restriction-of-extension₂ : (f : Ω → 𝟚) → ρ₂ (extension₂-along-η f) ＝ f
restriction-of-extension₂ f = dfunext fe (λ p → extension₂-property f p)

\end{code}

The points τ₀ and τ₁ are ¬¬-dense in T, which gives
left-cancellability of ρ₂.

\begin{code}

τ₀₁-density : (t : T) → ¬¬ ((t ＝ τ₀) + (t ＝ τ₁))
τ₀₁-density t νν = II (λ d → νν (I d))
 where
  I : is-decidable WEM → (t ＝ τ₀) + (t ＝ τ₁)
  I (inl w) = 𝟚-equality-cases
               (λ e → inl (t        ＝⟨ τ-lemma t w ⟩
                           τ (t w) ＝⟨ ap τ e ⟩
                           τ₀       ∎))
               (λ e → inr (t        ＝⟨ τ-lemma t w ⟩
                           τ (t w) ＝⟨ ap τ e ⟩
                           τ₁       ∎))
  I (inr nw) = inl (dfunext fe (λ w → 𝟘-elim (nw w)))

  II : ¬¬ (is-decidable WEM)
  II  = double-negation-of-decision

ρ₂-lc : (g g' : T → 𝟚) → ρ₂ g ＝ ρ₂ g' → g ＝ g'
ρ₂-lc g g' e = dfunext fe (λ t → 𝟚-is-¬¬-separated (g t) (g' t) (III t))
 where
  I : g τ₀ ＝ g' τ₀
  I = g τ₀     ＝⟨ ap g (η⊥ ⁻¹) ⟩
      g (η ⊥)  ＝⟨ happly e ⊥ ⟩
      g' (η ⊥) ＝⟨ ap g' η⊥ ⟩
      g' τ₀    ∎

  II : g τ₁ ＝ g' τ₁
  II = g τ₁     ＝⟨ ap g (η⊤ ⁻¹) ⟩
       g (η ⊤)  ＝⟨ happly e ⊤ ⟩
       g' (η ⊤) ＝⟨ ap g' η⊤ ⟩
       g' τ₁    ∎

  III : (t : T) → ¬¬ (g t ＝ g' t)
  III t νν = τ₀₁-density t IV
   where
    IV : ¬ ((t ＝ τ₀) + (t ＝ τ₁))
    IV (inl l) = νν (g  t  ＝⟨ ap g l ⟩
                     g  τ₀ ＝⟨ I ⟩
                     g' τ₀ ＝⟨ ap g' (l ⁻¹) ⟩
                     g' t  ∎)

    IV (inr r) = νν (g  t  ＝⟨ ap g r ⟩
                     g  τ₁ ＝⟨ II ⟩
                     g' τ₁ ＝⟨ ap g' (r ⁻¹) ⟩
                     g' t  ∎)

extension₂-of-restriction : (g : T → 𝟚) → extension₂-along-η (ρ₂ g) ＝ g
extension₂-of-restriction g = ρ₂-lc (extension₂-along-η (ρ₂ g)) g
                               (restriction-of-extension₂ (ρ₂ g))

ρ₂-is-equiv : is-equiv ρ₂
ρ₂-is-equiv = qinvs-are-equivs ρ₂
               (extension₂-along-η ,
                extension₂-of-restriction ,
                restriction-of-extension₂)

\end{code}

We now prove the universal property when the target type is a power of 𝟚, coordinatewise.

\begin{code}

extension-power-of-𝟚-along-η : {𝓘 : Universe} {J : 𝓘 ̇ }
                             → (Ω → (J → 𝟚)) → (T → (J → 𝟚))
extension-power-of-𝟚-along-η f t j = extension₂-along-η (λ p → f p j) t

ρ-of-power-of-𝟚-is-equiv : {𝓘 : Universe} {J : 𝓘 ̇ } → is-equiv (ρ (J → 𝟚))
ρ-of-power-of-𝟚-is-equiv {𝓘} {J} =
 qinvs-are-equivs (ρ (J → 𝟚)) (extension-power-of-𝟚-along-η , I , II)
 where
  I : (g : T → (J → 𝟚)) → extension-power-of-𝟚-along-η (ρ (J → 𝟚) g) ＝ g
  I g = dfunext fe (λ t → dfunext fe (λ j → happly
                                             (extension₂-of-restriction
                                               (λ t' → g t' j))
                                             t))

  II : (f : Ω → (J → 𝟚)) → ρ (J → 𝟚) (extension-power-of-𝟚-along-η f) ＝ f
  II f = dfunext fe (λ p → dfunext fe (λ j → extension₂-property
                                              (λ p' → f p' j)
                                              p))

\end{code}

Retracts of targets that satisfy the universal property also satisfy
the universal property of totally separated reflection.

\begin{code}

ρ-of-retract-is-equiv : {Y : 𝓦 ̇ } {Z : 𝓣 ̇ }
                      → retract Y of Z
                      → is-equiv (ρ Z)
                      → is-equiv (ρ Y)
ρ-of-retract-is-equiv {𝓦} {𝓣} {Y} {Z} (r , s , rs) ez =
 qinvs-are-equivs (ρ Y) (ρY⁻¹ , III , IV)
 where
  ρZ⁻¹ : (Ω → Z) → (T → Z)
  ρZ⁻¹ = inverse (ρ Z) ez

  I : (φ : Ω → Z) → ρ Z (ρZ⁻¹ φ) ＝ φ
  I = inverses-are-sections (ρ Z) ez

  II : (ψ : T → Z) → ρZ⁻¹ (ρ Z ψ) ＝ ψ
  II = inverses-are-retractions (ρ Z) ez

  ρY⁻¹ : (Ω → Y) → (T → Y)
  ρY⁻¹ f = r ∘ ρZ⁻¹ (s ∘ f)

  III : (g : T → Y) → ρY⁻¹ (ρ Y g) ＝ g
  III g = ρY⁻¹ (ρ Y g)  ＝⟨ ap (λ - → r ∘ -) (II (s ∘ g)) ⟩
          r ∘ (s ∘ g)   ＝⟨ dfunext fe (λ t → rs (g t)) ⟩
          g             ∎

  IV : (f : Ω → Y) → ρ Y (ρY⁻¹ f) ＝ f
  IV f = ρ Y (ρY⁻¹ f)  ＝⟨ ap (λ - → r ∘ -) (I (s ∘ f)) ⟩
          r ∘ (s ∘ f)  ＝⟨ dfunext fe (λ p → rs (f p)) ⟩
          f            ∎

\end{code}

The universal property for retracts of powers of 𝟚.

\begin{code}

ρ-of-retract-of-power-of-𝟚-is-equiv
 : {𝓘 : Universe} {Y : 𝓦 ̇ } {J : 𝓘 ̇ }
 → retract Y of (J → 𝟚)
 → is-equiv (ρ Y)
ρ-of-retract-of-power-of-𝟚-is-equiv ret =
 ρ-of-retract-is-equiv ret ρ-of-power-of-𝟚-is-equiv

reflection-for-retract-of-power-of-𝟚
 : {𝓘 : Universe} {Y : 𝓦 ̇ } {J : 𝓘 ̇ }
 → retract Y of (J → 𝟚)
 → (T → Y) ≃ (Ω → Y)
reflection-for-retract-of-power-of-𝟚 r =
 ρ _ , ρ-of-retract-of-power-of-𝟚-is-equiv r

\end{code}

The remainder of this file is just miscelaneous observations.

We first connect this to the investigation of 𝟚-injective types,
inverstigated in gist.2-injective-types.

\begin{code}

open import gist.2-injective-types fe'

T-is-𝟚-injective : {𝓥 𝓦 : Universe} → 𝟚-injective T 𝓥 𝓦
T-is-𝟚-injective = first-dual-is-𝟚-injective

η-is-𝟚-injecting : is-𝟚-injecting η
η-is-𝟚-injecting f = extension₂-along-η f , happly (restriction-of-extension₂ f)

ρ-of-𝟚-injective-is-equiv : {Y : 𝓦 ̇ }
                          → 𝟚-injective Y 𝓦 𝓦
                          → is-equiv (ρ Y)
ρ-of-𝟚-injective-is-equiv i =
 ρ-of-retract-of-power-of-𝟚-is-equiv (𝟚-injectives-are-K-retracts i)

\end{code}

There is at most one extension for a totally separated target. The
following generalizes and uses ρ₂-lc.

\begin{code}

ρ₂-of-ts-is-lc : (Y : 𝓦 ̇ )
               → is-totally-separated Y
               → (g g' : T → Y) → ρ Y g ＝ ρ Y g' → g ＝ g'
ρ₂-of-ts-is-lc Y ts g g' e =
 dfunext fe (λ t → ts (λ q → happly
                              (ρ₂-lc
                                (λ t' → q (g t'))
                                (λ t' → q (g' t'))
                                (ap (λ - → q ∘ -) e)) t))

\end{code}

The notion of compactness is defined in TypeTopology.CompactTypes,
where it is proved that Ω is-compact.

\begin{code}

T-is-compact∙ : is-compact∙ T
T-is-compact∙ = micro-tychonoff fe WEM-is-prop (λ _ → 𝟚-is-compact∙)

\end{code}

Ω is totally separated if and only if excluded middle holds at 𝓤.
The forward direction is already Ω-totally-separated-gives-EM in
TypeTopology.TotallySeparated (through ¬¬-separatedness and DNE), so we
import and reuse it. Here we record the backward direction: EM makes
Ω discrete, and discrete types are totally separated.

\begin{code}

EM-gives-Ω-discrete : EM 𝓤 → is-discrete Ω
EM-gives-Ω-discrete em p q = II (I p) (I q)
 where
  I : LEM 𝓤
  I = EM-gives-LEM em

  II : is-decidable (p holds) → is-decidable (q holds) → is-decidable (p ＝ q)
  II (inl ph) (inl qh)  = inl (p ＝⟨ holds-gives-equal-⊤ pe fe p ph ⟩
                               ⊤ ＝⟨ (holds-gives-equal-⊤ pe fe q qh) ⁻¹ ⟩
                               q ∎)

  II (inl ph) (inr nq) = inr (λ e → nq (transport _holds e ph))
  II (inr np) (inl qh) = inr (λ e → np (transport _holds (e ⁻¹) qh))
  II (inr np) (inr nq) = inl (p ＝⟨ fails-gives-equal-⊥ pe fe p np ⟩
                              ⊥ ＝⟨ (fails-gives-equal-⊥ pe fe q nq) ⁻¹ ⟩
                              q ∎)

EM-gives-Ω-totally-separated : EM 𝓤 → is-totally-separated Ω
EM-gives-Ω-totally-separated em =
 discrete-types-are-totally-separated (EM-gives-Ω-discrete em)

extension₂-along-η-under-WEM : (h : Ω → 𝟚) (w : WEM) (t : T)
                             → extension₂-along-η h t ＝ 𝟚-cases (h ⊥) (h ⊤)(t w)
extension₂-along-η-under-WEM h w t = I (𝟚-is-discrete (h ⊥) (h ⊤))
 where
  I : (d : is-decidable (h ⊥ ＝ h ⊤))
    → extension₂'-along-η h d t ＝ 𝟚-cases (h ⊥) (h ⊤) (t w)
  I (inl e)  = 𝟚-equality-cases
                (λ e' → h ⊥                       ＝⟨ I₀ e' ⟩
                        𝟚-cases (h ⊥) (h ⊤) (t w) ∎)
                (λ e' → h ⊥                       ＝⟨ e ⟩
                        h ⊤                       ＝⟨ I₁ e' ⟩
                        𝟚-cases (h ⊥) (h ⊤) (t w) ∎)
               where
                I₀ = λ e' → ap (𝟚-cases (h ⊥) (h ⊤)) (e' ⁻¹)
                I₁ = λ e' → ap (𝟚-cases (h ⊥) (h ⊤)) (e' ⁻¹)

  I (inr ν) = ap (𝟚-cases (h ⊥) (h ⊤))
                 (ap t (WEM-is-prop (to-WEM h ν) w))

extension₂-along-η-under-¬WEM : (h : Ω → 𝟚) (t : T)
                              → ¬ WEM
                              → extension₂-along-η h t ＝ h ⊥
extension₂-along-η-under-¬WEM h t nw = I (𝟚-is-discrete (h ⊥) (h ⊤))
 where
  I : (d : is-decidable (h ⊥ ＝ h ⊤)) → extension₂'-along-η h d t ＝ h ⊥
  I (inl e)  = refl
  I (inr ν) = 𝟘-elim (nw (to-WEM h ν))

\end{code}

TODO. The following deserves a better name and some explanation.

\begin{code}

¬¬-extension
 : (Y : 𝓦 ̇ )
 → is-totally-separated Y
 → (f : Ω → Y)
   (t : T)
 → ¬¬ (Σ y ꞉ Y , ((y ＝ f ⊥) + (y ＝ f ⊤))
               × ((q : Y → 𝟚) → q y ＝ extension₂-along-η (q ∘ f) t))
¬¬-extension Y ts f t ν
 = I (λ d → ν (II d))
 where
  I : ¬¬ (is-decidable WEM)
  I = double-negation-of-decision

  II : is-decidable WEM
      → Σ y ꞉ Y , ((y ＝ f ⊥) + (y ＝ f ⊤))
                × ((q : Y → 𝟚) → q y ＝ extension₂-along-η (q ∘ f) t)
  II (inl w) = 𝟚-cases (f ⊥) (f ⊤) (t w) , III , IV
   where
    III : (𝟚-cases (f ⊥) (f ⊤) (t w) ＝ f ⊥) + (𝟚-cases (f ⊥) (f ⊤) (t w) ＝ f ⊤)
    III = 𝟚-equality-cases {b = t w}
            (λ e → inl (ap (𝟚-cases (f ⊥) (f ⊤)) e))
            (λ e → inr (ap (𝟚-cases (f ⊥) (f ⊤)) e))

    IV : (q : Y → 𝟚)
       → q (𝟚-cases (f ⊥) (f ⊤) (t w)) ＝ extension₂-along-η (q ∘ f) t
    IV q = q (𝟚-cases (f ⊥) (f ⊤) (t w))        ＝⟨ IV₀ ⟩
           𝟚-cases (q (f ⊥)) (q (f ⊤)) (t w)    ＝⟨ IV₁ ⟩
           extension₂-along-η (q ∘ f) t         ∎
            where
             IV₀ = 𝟚-cases-lemma q (f ⊥) (f ⊤) (t w)
             IV₁ = (extension₂-along-η-under-WEM (q ∘ f) w t)⁻¹

  II (inr nw) = f ⊥ , inl refl , V
   where
    V : (q : Y → 𝟚) → q (f ⊥) ＝ extension₂-along-η (q ∘ f) t
    V q = (extension₂-along-η-under-¬WEM (q ∘ f) t nw) ⁻¹

\end{code}

We now assume propositional truncations.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open import UF.ImageAndSurjection pt

 ι : image η → T
 ι = restriction η

 ι-emb : is-embedding ι
 ι-emb = restrictions-are-embeddings η

 ι-image-is-ts : is-totally-separated (image η)
 ι-image-is-ts = subtype-is-totally-separated' ι T-is-totally-separated ι-emb

 ηc : Ω → image η
 ηc = corestriction η

 section-of-ι-gives-η-surjection : (𝓼 : T → image η)
                                 → ι ∘ 𝓼 ＝ id
                                 → is-surjection η
 section-of-ι-gives-η-surjection 𝓼 ι𝓼-id =
  ∘-is-surjection
   (corestrictions-are-surjections η)
   (equivs-are-surjections
     (embeddings-with-sections-are-equivs ι ι-emb (𝓼 , happly ι𝓼-id)))

 ρ-equiv-gives-η-surjection
  : ((Y : 𝓤⁺ ̇ ) → is-totally-separated Y → is-equiv (ρ Y))
  → is-surjection η
 ρ-equiv-gives-η-surjection up = section-of-ι-gives-η-surjection 𝓼 III
  where
   I : is-equiv (ρ (image η))
   I = up (image η) ι-image-is-ts

   𝓼 : T → image η
   𝓼 = inverse (ρ (image η)) I ηc

   II : ρ (image η) 𝓼 ＝ ηc
   II = inverses-are-sections (ρ (image η)) I ηc

   III : ι ∘ 𝓼 ＝ id
   III = ρ₂-of-ts-is-lc T T-is-totally-separated (ι ∘ 𝓼) id
          (ap (λ - → ι ∘ -) II)

 𝟚-injective-image-gives-η-surjection : 𝟚-injective (image η) 𝓤⁺ 𝓤⁺
                                      → is-surjection η
 𝟚-injective-image-gives-η-surjection i = section-of-ι-gives-η-surjection 𝓼 III
  where
   I : Σ 𝓼 ꞉ (T → image η) , 𝓼 ∘ η ∼ ηc
   I = i η η-is-𝟚-injecting ηc

   𝓼 : T → image η
   𝓼 = pr₁ I

   II : 𝓼 ∘ η ∼ ηc
   II = pr₂ I

   III : ι ∘ 𝓼 ＝ id
   III = ρ₂-of-ts-is-lc T T-is-totally-separated (ι ∘ 𝓼) id
          (dfunext fe (λ p → ap ι (II p)))

\end{code}

We now relate T to the general construction of the totally separated reflection
of any type X as the image of the evaluation map X → ((X → 𝟚) → 𝟚).

\begin{code}

 open totally-separated-reflection fe' pt

\end{code}

The comparison map 𝓬.

\begin{code}

 𝓬 : 𝕋 Ω → T
 𝓬 = ∃!-witness (totally-separated-reflection T-is-totally-separated η)

 𝓬-triangle : 𝓬 ∘ ηᵀ ＝ η
 𝓬-triangle = ∃!-is-witness
                        (totally-separated-reflection T-is-totally-separated η)

 reflection-gives-𝕋-equivalence
  : ((Y : 𝓤⁺ ̇ ) → is-totally-separated Y → is-equiv (ρ Y))
  → is-equiv 𝓬
 reflection-gives-𝕋-equivalence up
  = qinvs-are-equivs 𝓬 (𝓬⁻¹ , III , IV)
  where
   I : is-equiv (ρ (𝕋 Ω))
   I = up (𝕋 Ω) 𝕋-is-totally-separated

   𝓬⁻¹ : T → 𝕋 Ω
   𝓬⁻¹ = inverse (ρ (𝕋 Ω)) I ηᵀ

   II : ρ (𝕋 Ω) 𝓬⁻¹ ＝ ηᵀ
   II = inverses-are-sections (ρ (𝕋 Ω)) I ηᵀ

   III : 𝓬⁻¹ ∘ 𝓬 ∼ id
   III = happly VI
    where
     V : (𝓬⁻¹ ∘ 𝓬) ∘ ηᵀ ＝ ηᵀ
     V = (𝓬⁻¹ ∘ 𝓬) ∘ ηᵀ ＝⟨ ap (λ - → 𝓬⁻¹ ∘ -) 𝓬-triangle ⟩
         𝓬⁻¹ ∘ η                 ＝⟨ II ⟩
         ηᵀ                    ∎
     VI : 𝓬⁻¹ ∘ 𝓬 ＝ id
     VI = witness-uniqueness _
            (totally-separated-reflection 𝕋-is-totally-separated ηᵀ)
            (𝓬⁻¹ ∘ 𝓬) id V refl

   IV : 𝓬 ∘ 𝓬⁻¹ ∼ id
   IV = happly VII
    where
     VII : 𝓬 ∘ 𝓬⁻¹ ＝ id
     VII = ρ₂-of-ts-is-lc T T-is-totally-separated (𝓬 ∘ 𝓬⁻¹) id
            (ρ T (𝓬 ∘ 𝓬⁻¹) ＝⟨ ap (λ - → 𝓬 ∘ -) II ⟩
             𝓬 ∘ ηᵀ           ＝⟨ 𝓬-triangle ⟩
             η                         ∎)

\end{code}

The above development gives the equivalence

    (Ω → 𝟚) ≃ (𝟚 + WEM × 𝟚)

more or less directly.

\begin{code}

ψ' : (h : Ω → 𝟚) → is-decidable (h ⊥ ＝ h ⊤) → 𝟚 + WEM × 𝟚
ψ' h (inl _) = inl (h ⊥)
ψ' h (inr ν) = inr (to-WEM h ν , h ⊥)

ψ : (Ω → 𝟚) → 𝟚 + WEM × 𝟚
ψ h = ψ' h (𝟚-is-discrete (h ⊥) (h ⊤))

ψ⁻¹ : 𝟚 + WEM × 𝟚 → (Ω → 𝟚)
ψ⁻¹ (inl b)       _ = b
ψ⁻¹ (inr (w , b)) p = 𝟚-cases b (complement b) (δ (w p))

ψη : ψ⁻¹ ∘ ψ ∼ id
ψη h = I (𝟚-is-discrete (h ⊥) (h ⊤))
 where
  I : (d : is-decidable (h ⊥ ＝ h ⊤)) → ψ⁻¹ (ψ' h d) ＝ h
  I (inl e) = dfunext fe (λ p → (constancy-lemma h e p) ⁻¹)
  I (inr ν) = dfunext fe III
   where
    II : WEM
    II = to-WEM h ν

    III : (p : Ω) → 𝟚-cases (h ⊥) (complement (h ⊥)) (δ (II p)) ＝ h p
    III p = IV (II p)
     where
      IV : (d : is-decidable (¬ (p holds)))
         → 𝟚-cases (h ⊥) (complement (h ⊥)) (δ d) ＝ h p
      IV (inl ν)  = (lemma-⊥ h p ν) ⁻¹
      IV (inr νν) = complement (h ⊥) ＝⟨ (complement-of-different-booleans ν) ⁻¹ ⟩
                    h ⊤              ＝⟨ V ⁻¹ ⟩
                    h p              ∎
       where
        V : h p ＝ h ⊤
        V = 𝟚-is-¬¬-separated (h p) (h ⊤)
             (λ ν → νν (λ ph → ν (lemma-⊤ h p ph)))

ψε : ψ ∘ ψ⁻¹ ∼ id
ψε (inl b) = I (𝟚-is-discrete b b)
 where
  I : (d : is-decidable (b ＝ b)) → ψ' (ψ⁻¹ (inl b)) d ＝ inl b
  I (inl _) = refl
  I (inr ν) = 𝟘-elim (ν refl)
ψε (inr (w , b)) = IV (𝟚-is-discrete (h ⊥) (h ⊤))
 where
  h : Ω → 𝟚
  h = ψ⁻¹ (inr (w , b))

  I : h ⊥ ＝ b
  I = ap (𝟚-cases b (complement b)) (η₀ ⊥ w ⊥-doesnt-hold)

  II : h ⊤ ＝ complement b
  II = ap (𝟚-cases b (complement b)) (η₁ ⊤ w (¬¬-intro ⊤-holds))

  III : h ⊥ ≠ h ⊤
  III ν = complement-no-fp b
           (b            ＝⟨ I ⁻¹ ⟩
            h ⊥          ＝⟨ ν ⟩
            h ⊤          ＝⟨ II ⟩
            complement b ∎)

  IV : (d : is-decidable (h ⊥ ＝ h ⊤)) → ψ' h d ＝ inr (w , b)
  IV (inl e) = 𝟘-elim (III e)
  IV (inr ν) = ap inr (to-×-＝ (WEM-is-prop (to-WEM h ν) w) I)

Ψ : (Ω → 𝟚) ≃ (𝟚 + WEM × 𝟚)
Ψ = ψ , qinvs-are-equivs ψ (ψ⁻¹ , ψη , ψε)

\end{code}
