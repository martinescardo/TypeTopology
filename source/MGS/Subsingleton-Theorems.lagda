Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Subsingleton-Theorems where

open import MGS.FunExt-from-Univalence public

Π-is-subsingleton : dfunext 𝓤 𝓥
                  → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  → ((x : X) → is-subsingleton (A x))
                  → is-subsingleton (Π A)

Π-is-subsingleton fe i f g = fe (λ x → i x (f x) (g x))

being-singleton-is-subsingleton : dfunext 𝓤 𝓤
                                → {X : 𝓤 ̇ } → is-subsingleton (is-singleton X)

being-singleton-is-subsingleton fe {X} (x , φ) (y , γ) = p
 where
  i : is-subsingleton X
  i = singletons-are-subsingletons X (y , γ)

  s : is-set X
  s = subsingletons-are-sets X i

  a : (z : X) → is-subsingleton ((t : X) → z ＝ t)
  a z = Π-is-subsingleton fe (s z)

  b : x ＝ y
  b = φ y

  p : (x , φ) ＝ (y , γ)
  p = to-subtype-＝ a b

being-equiv-is-subsingleton : dfunext 𝓥 (𝓤 ⊔ 𝓥)
                            → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-subsingleton (is-equiv f)

being-equiv-is-subsingleton fe fe' f
 = Π-is-subsingleton fe
    (λ x → being-singleton-is-subsingleton fe')

subsingletons-are-retracts-of-logically-equivalent-types : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                                         → is-subsingleton X
                                                         → (X ⇔ Y)
                                                         → X ◁ Y

subsingletons-are-retracts-of-logically-equivalent-types i (f , g) = g , f , η
 where
  η : g ∘ f ∼ id
  η x = i (g (f x)) x

equivalence-property-is-retract-of-invertibility-data
 : dfunext 𝓥 (𝓤 ⊔ 𝓥)
 → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → is-equiv f ◁ invertible f

equivalence-property-is-retract-of-invertibility-data fe fe' f =
  subsingletons-are-retracts-of-logically-equivalent-types
   (being-equiv-is-subsingleton fe fe' f)
   (equivs-are-invertible f , invertibles-are-equivs f)

univalence-is-subsingleton : is-univalent (𝓤 ⁺)
                           → is-subsingleton (is-univalent 𝓤)

univalence-is-subsingleton {𝓤} ua⁺ = subsingleton-criterion' γ
 where
  γ : is-univalent 𝓤 → is-subsingleton (is-univalent 𝓤)
  γ ua = i
   where
    dfe₁ : dfunext  𝓤    (𝓤 ⁺)
    dfe₂ : dfunext (𝓤 ⁺) (𝓤 ⁺)

    dfe₁ = univalence-gives-dfunext' ua ua⁺
    dfe₂ = univalence-gives-dfunext ua⁺

    i : is-subsingleton (is-univalent 𝓤)
    i = Π-is-subsingleton dfe₂
         (λ X → Π-is-subsingleton dfe₂
         (λ Y → being-equiv-is-subsingleton dfe₁ dfe₂ (Id→Eq X Y)))

Univalence : 𝓤ω
Univalence = ∀ 𝓤 → is-univalent 𝓤

univalence-is-subsingletonω : Univalence → is-subsingleton (is-univalent 𝓤)
univalence-is-subsingletonω {𝓤} γ = univalence-is-subsingleton (γ (𝓤 ⁺))

univalence-is-a-singleton : Univalence → is-singleton (is-univalent 𝓤)
univalence-is-a-singleton {𝓤} γ = pointed-subsingletons-are-singletons
                                   (is-univalent 𝓤)
                                   (γ 𝓤)
                                   (univalence-is-subsingletonω γ)

global-dfunext : 𝓤ω
global-dfunext = ∀ {𝓤 𝓥} → dfunext 𝓤 𝓥

univalence-gives-global-dfunext : Univalence → global-dfunext
univalence-gives-global-dfunext ua {𝓤} {𝓥} = univalence-gives-dfunext'
                                               (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

global-hfunext : 𝓤ω
global-hfunext = ∀ {𝓤 𝓥} → hfunext 𝓤 𝓥

univalence-gives-global-hfunext : Univalence → global-hfunext
univalence-gives-global-hfunext ua {𝓤} {𝓥} = univalence-gives-hfunext'
                                               (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

Π-is-subsingleton' : dfunext 𝓤 𝓥
                   → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                   → ((x : X) → is-subsingleton (A x))
                   → is-subsingleton ({x : X} → A x)

Π-is-subsingleton' fe {X} {A} i = γ
 where
  ρ : ({x : X} → A x) ◁ Π A
  ρ = (λ f {x} → f x) , (λ g x → g {x}) , (λ f → refl (λ {x} → f))

  γ : is-subsingleton ({x : X} → A x)
  γ = retract-of-subsingleton ρ (Π-is-subsingleton fe i)

vv-and-hfunext-are-subsingletons-lemma  : dfunext (𝓤 ⁺)       (𝓤 ⊔ (𝓥 ⁺))
                                        → dfunext (𝓤 ⊔ (𝓥 ⁺)) (𝓤 ⊔ 𝓥)
                                        → dfunext (𝓤 ⊔ 𝓥)     (𝓤 ⊔ 𝓥)

                                        → is-subsingleton (vvfunext 𝓤 𝓥)
                                        × is-subsingleton (hfunext  𝓤 𝓥)

vv-and-hfunext-are-subsingletons-lemma {𝓤} {𝓥} dfe dfe' dfe'' = φ , γ
 where
  φ : is-subsingleton (vvfunext 𝓤 𝓥)
  φ = Π-is-subsingleton' dfe
       (λ X → Π-is-subsingleton' dfe'
       (λ A → Π-is-subsingleton dfe''
       (λ i → being-singleton-is-subsingleton dfe'')))

  γ : is-subsingleton (hfunext 𝓤 𝓥)
  γ = Π-is-subsingleton' dfe
       (λ X → Π-is-subsingleton' dfe'
       (λ A → Π-is-subsingleton dfe''
       (λ f → Π-is-subsingleton dfe''
       (λ g → being-equiv-is-subsingleton dfe'' dfe''
               (happly f g)))))

vv-and-hfunext-are-singletons : Univalence
                              → is-singleton (vvfunext 𝓤 𝓥)
                              × is-singleton (hfunext  𝓤 𝓥)

vv-and-hfunext-are-singletons {𝓤} {𝓥} ua =

 f (vv-and-hfunext-are-subsingletons-lemma
     (univalence-gives-dfunext' (ua (𝓤 ⁺))       (ua ((𝓤 ⁺) ⊔ (𝓥 ⁺))))
     (univalence-gives-dfunext' (ua (𝓤 ⊔ (𝓥 ⁺))) (ua (𝓤 ⊔ (𝓥 ⁺))))
     (univalence-gives-dfunext' (ua (𝓤 ⊔ 𝓥))     (ua (𝓤 ⊔ 𝓥))))

 where
  f : is-subsingleton (vvfunext 𝓤 𝓥) × is-subsingleton (hfunext 𝓤 𝓥)
    → is-singleton (vvfunext 𝓤 𝓥) × is-singleton (hfunext 𝓤 𝓥)

  f (i , j) = pointed-subsingletons-are-singletons (vvfunext 𝓤 𝓥)
                (univalence-gives-vvfunext' (ua 𝓤) (ua (𝓤 ⊔ 𝓥))) i ,

              pointed-subsingletons-are-singletons (hfunext 𝓤 𝓥)
                (univalence-gives-hfunext' (ua 𝓤) (ua (𝓤 ⊔ 𝓥))) j
\end{code}
