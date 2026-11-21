Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Powerset where

open import MGS.More-FunExt-Consequences public

propext : ∀ 𝓤  → 𝓤 ⁺ ̇
propext 𝓤 = {P Q : 𝓤 ̇ } → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ＝ Q

global-propext : 𝓤ω
global-propext = ∀ {𝓤} → propext 𝓤

univalence-gives-propext : is-univalent 𝓤 → propext 𝓤
univalence-gives-propext ua {P} {Q} i j f g = Eq→Id ua P Q γ
 where
  γ : P ≃ Q
  γ = logically-equivalent-subsingletons-are-equivalent P Q i j (f , g)

Ω : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ω 𝓤 = Σ P ꞉ 𝓤 ̇ , is-subsingleton P

_holds : Ω 𝓤 → 𝓤 ̇
_holds (P , i) = P

holds-is-subsingleton : (p : Ω 𝓤) → is-subsingleton (p holds)
holds-is-subsingleton (P , i) = i

Ω-ext : dfunext 𝓤 𝓤 → propext 𝓤 → {p q : Ω 𝓤}
      → (p holds → q holds) → (q holds → p holds) → p ＝ q

Ω-ext {𝓤} fe pe {p} {q} f g
 = to-subtype-＝
      (λ _ → being-subsingleton-is-subsingleton fe)
      (pe (holds-is-subsingleton p) (holds-is-subsingleton q) f g)

Ω-is-a-set : dfunext 𝓤 𝓤 → propext 𝓤 → is-set (Ω 𝓤)
Ω-is-a-set {𝓤} fe pe = types-with-wconstant-＝-endomaps-are-sets (Ω 𝓤) c
 where
  A : (p q : Ω 𝓤) → 𝓤 ̇
  A p q = (p holds → q holds) × (q holds → p holds)

  i : (p q : Ω 𝓤) → is-subsingleton (A p q)
  i p q = Σ-is-subsingleton
           (Π-is-subsingleton fe
             (λ _ → holds-is-subsingleton q))
             (λ _ → Π-is-subsingleton fe (λ _ → holds-is-subsingleton p))

  g : (p q : Ω 𝓤) → p ＝ q → A p q
  g p q e = (u , v)
   where
    a : p holds ＝ q holds
    a = ap _holds e

    u : p holds → q holds
    u = Id→fun a

    v : q holds → p holds
    v = Id→fun (a ⁻¹)

  h : (p q : Ω 𝓤) → A p q → p ＝ q
  h p q (u , v) = Ω-ext fe pe u v

  f : (p q : Ω 𝓤) → p ＝ q → p ＝ q
  f p q e = h p q (g p q e)

  k : (p q : Ω 𝓤) (d e : p ＝ q) → f p q d ＝ f p q e
  k p q d e = ap (h p q) (i p q (g p q d) (g p q e))

  c : (p q : Ω 𝓤) → Σ f ꞉ (p ＝ q → p ＝ q), wconstant f
  c p q = (f p q , k p q)

powersets-are-sets : hfunext 𝓤 (𝓥 ⁺)
                   → dfunext 𝓥 𝓥
                   → propext 𝓥
                   → {X : 𝓤 ̇ } → is-set (X → Ω 𝓥)

powersets-are-sets fe fe' pe = Π-is-set fe (λ x → Ω-is-a-set fe' pe)

𝓟 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓟 {𝓤} X = X → Ω 𝓤

powersets-are-sets' : Univalence
                    → {X : 𝓤 ̇ } → is-set (𝓟 X)

powersets-are-sets' {𝓤} ua = powersets-are-sets
                               (univalence-gives-hfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                               (univalence-gives-dfunext (ua 𝓤))
                               (univalence-gives-propext (ua 𝓤))

_∈_ : {X : 𝓤 ̇ } → X → 𝓟 X → 𝓤 ̇
x ∈ A = A x holds

_∉_ : {X : 𝓤 ̇ } → X → 𝓟 X → 𝓤 ̇
x ∉ A = ¬(x ∈ A)

_⊆_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓤 ̇
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-is-subsingleton : {X : 𝓤 ̇ } (A : 𝓟 X) (x : X) → is-subsingleton (x ∈ A)
∈-is-subsingleton A x = holds-is-subsingleton (A x)

⊆-is-subsingleton : dfunext 𝓤 𝓤
                  → {X : 𝓤 ̇ } (A B : 𝓟 X) → is-subsingleton (A ⊆ B)

⊆-is-subsingleton fe A B = Π-is-subsingleton fe
                            (λ x → Π-is-subsingleton fe
                            (λ _ → ∈-is-subsingleton B x))

⊆-refl : {X : 𝓤 ̇ } (A : 𝓟 X) → A ⊆ A
⊆-refl A x = 𝑖𝑑 (x ∈ A)

⊆-refl-consequence : {X : 𝓤 ̇ } (A B : 𝓟 X)
                   → A ＝ B → (A ⊆ B) × (B ⊆ A)

⊆-refl-consequence {X} A A (refl A) = ⊆-refl A , ⊆-refl A

subset-extensionality : propext 𝓤
                      → dfunext 𝓤 𝓤
                      → dfunext 𝓤 (𝓤 ⁺)
                      → {X : 𝓤 ̇ } {A B : 𝓟 X}
                      → A ⊆ B → B ⊆ A → A ＝ B

subset-extensionality pe fe fe' {X} {A} {B} h k = fe' φ
 where
  φ : (x : X) → A x ＝ B x
  φ x = to-subtype-＝
           (λ _ → being-subsingleton-is-subsingleton fe)
           (pe (holds-is-subsingleton (A x)) (holds-is-subsingleton (B x))
               (h x) (k x))

subset-extensionality' : Univalence
                       → {X : 𝓤 ̇ } {A B : 𝓟 X}
                       → A ⊆ B → B ⊆ A → A ＝ B

subset-extensionality' {𝓤} ua = subset-extensionality
                                 (univalence-gives-propext (ua 𝓤))
                                 (univalence-gives-dfunext (ua 𝓤))
                                 (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))

prop-univalence prop-univalence' : (𝓤 : Universe) → 𝓤 ⁺ ̇
prop-univalence  𝓤 = (A : 𝓤 ̇ ) → is-prop A → (X : 𝓤 ̇ ) → is-equiv (Id→Eq A X)
prop-univalence' 𝓤
 = (A : 𝓤 ̇ ) → is-prop A → (X : 𝓤 ̇ ) → is-prop X → is-equiv (Id→Eq A X)

prop-univalence-agreement : prop-univalence' 𝓤 ⇔ prop-univalence 𝓤
prop-univalence-agreement
 = (λ pu' A i X e → pu' A i X (equiv-to-subsingleton (≃-sym e) i) e) ,
   (λ pu  A i X _ → pu  A i X)

props-form-exponential-ideal
 props-are-closed-under-Π
 prop-vvfunext
 prop-hfunext : ∀ 𝓤 → 𝓤 ⁺ ̇

props-form-exponential-ideal 𝓤 = (X A : 𝓤 ̇ ) → is-prop A → is-prop (X → A)

props-are-closed-under-Π 𝓤 = {X : 𝓤 ̇ } {A : X → 𝓤 ̇ }
                           → is-prop X
                           → ((x : X) → is-prop (A x))
                           → is-prop (Π A)

prop-vvfunext 𝓤 = {X : 𝓤 ̇ } {A : X → 𝓤 ̇ }
                → is-prop X
                → ((x : X) → is-singleton (A x))
                → is-singleton (Π A)

prop-hfunext 𝓤 = {X : 𝓤 ̇ } {A : X → 𝓤 ̇ }
               → is-prop X
               → (f g : Π A) → is-equiv (happly f g)

first-propositional-function-extensionality-agreement :

    (props-are-closed-under-Π 𝓤 → prop-vvfunext 𝓤)
  × (prop-vvfunext 𝓤            → prop-hfunext 𝓤)
  × (prop-hfunext 𝓤             → props-are-closed-under-Π 𝓤)

second-propositional-function-extensionality-agreement :

    propext 𝓤 → (props-form-exponential-ideal 𝓤 ⇔ props-are-closed-under-Π 𝓤)

characterization-of-propositional-univalence
 : prop-univalence 𝓤
 ⇔ (propext 𝓤 × props-are-closed-under-Π 𝓤)

prop-univalence-gives-propext : prop-univalence 𝓤 → propext 𝓤
prop-univalence-gives-propext pu {P} {Q} i j f g = δ
 where
  γ : P ≃ Q
  γ = logically-equivalent-subsingletons-are-equivalent P Q i j (f , g)

  δ : P ＝ Q
  δ = inverse (Id→Eq P Q) (pu P i Q) γ

prop-≃-induction : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
prop-≃-induction 𝓤 𝓥 = (P : 𝓤 ̇ )
                     → is-prop P
                     → (A : (X : 𝓤 ̇ ) → P ≃ X → 𝓥 ̇ )
                     → A P (id-≃ P) → (X : 𝓤 ̇ ) (e : P ≃ X) → A X e

prop-J-equiv : prop-univalence 𝓤
             → (𝓥 : Universe) → prop-≃-induction 𝓤 𝓥
prop-J-equiv {𝓤} pu 𝓥 P i A a X e = γ
 where
  A' : (X : 𝓤 ̇ ) → P ＝ X → 𝓥 ̇
  A' X q = A X (Id→Eq P X q)

  f : (X : 𝓤 ̇ ) (q : P ＝ X) → A' X q
  f = ℍ P A' a

  r : P ＝ X
  r = inverse (Id→Eq P X) (pu P i X) e

  g : A X (Id→Eq P X r)
  g = f X r

  γ : A X (id e)
  γ = transport (A X) (inverses-are-sections (Id→Eq P X) (pu P i X) e) g

prop-precomp-is-equiv : prop-univalence 𝓤
                      → (X Y Z : 𝓤 ̇ )
                      → is-prop X
                      → (f : X → Y)
                      → is-equiv f
                      → is-equiv (λ (g : Y → Z) → g ∘ f)
prop-precomp-is-equiv {𝓤} pu X Y Z i f f-is-equiv =
   prop-J-equiv pu 𝓤 X i (λ _ e → is-equiv (λ g → g ∘ ⌜ e ⌝))
     (id-is-equiv (X → Z)) Y (f , f-is-equiv)

prop-univalence-gives-props-form-exponential-ideal
 : prop-univalence 𝓤
 → props-form-exponential-ideal 𝓤

prop-univalence-gives-props-form-exponential-ideal {𝓤} pu X A A-is-prop = γ
 where
  Δ : 𝓤 ̇
  Δ = Σ a₀ ꞉ A , Σ a₁ ꞉ A , a₀ ＝ a₁

  δ : A → Δ
  δ a = (a , a , refl a)

  π₀ π₁ : Δ → A
  π₀ (a₀ , a₁ , a) = a₀
  π₁ (a₀ , a₁ , a) = a₁

  δ-is-equiv : is-equiv δ
  δ-is-equiv = invertibles-are-equivs δ (π₀ , η , ε)
   where
    η : (a : A) → π₀ (δ a) ＝ a
    η a = refl a

    ε : (d : Δ) → δ (π₀ d) ＝ d
    ε (a , a , refl a) = refl (a , a , refl a)

  φ : (Δ → A) → (A → A)
  φ π = π ∘ δ

  φ-is-equiv : is-equiv φ
  φ-is-equiv = prop-precomp-is-equiv pu A Δ A A-is-prop δ δ-is-equiv

  p : φ π₀ ＝ φ π₁
  p = refl (𝑖𝑑 A)

  q : π₀ ＝ π₁
  q = equivs-are-lc φ φ-is-equiv p

  h : (f₀ f₁ : X → A) → f₀ ∼ f₁
  h f₀ f₁ x = A-is-prop (f₀ x) (f₁ x)

  γ : (f₀ f₁ : X → A) → f₀ ＝ f₁
  γ f₀ f₁ = ap (λ π x → π (f₀ x , f₁ x , h f₀ f₁ x)) q

props-are-closed-under-Π-gives-prop-vvfunext
 : props-are-closed-under-Π 𝓤 → prop-vvfunext 𝓤
props-are-closed-under-Π-gives-prop-vvfunext
 c {X} {A} X-is-prop A-is-prop-valued
 = γ
 where
  f : Π A
  f x = center (A x) (A-is-prop-valued x)

  d : (g : Π A) → f ＝ g
  d
   = c X-is-prop
      (λ (x : X) → singletons-are-subsingletons (A x) (A-is-prop-valued x))
      f

  γ : is-singleton (Π A)
  γ = f , d

prop-vvfunext-gives-prop-hfunext : prop-vvfunext 𝓤 → prop-hfunext 𝓤
prop-vvfunext-gives-prop-hfunext vfe {X} {Y} X-is-prop f = γ
 where
  a : (x : X) → is-singleton (Σ y ꞉ Y x , f x ＝ y)
  a x = singleton-types'-are-singletons (Y x) (f x)

  c : is-singleton (Π x ꞉ X , Σ y ꞉ Y x , f x ＝ y)
  c = vfe X-is-prop a

  ρ : (Σ g ꞉ Π Y , f ∼ g) ◁ (Π x ꞉ X , Σ y ꞉ Y x , f x ＝ y)
  ρ = ≃-gives-▷ ΠΣ-distr-≃

  d : is-singleton (Σ g ꞉ Π Y , f ∼ g)
  d = retract-of-singleton ρ c

  e : (Σ g ꞉ Π Y , f ＝ g) → (Σ g ꞉ Π Y , f ∼ g)
  e = NatΣ (happly f)

  i : is-equiv e
  i
   = maps-of-singletons-are-equivs e (singleton-types'-are-singletons (Π Y) f) d

  γ : (g : Π Y) → is-equiv (happly f g)
  γ = NatΣ-equiv-gives-fiberwise-equiv (happly f) i

prop-hfunext-gives-props-are-closed-under-Π
 : prop-hfunext 𝓤 → props-are-closed-under-Π 𝓤
prop-hfunext-gives-props-are-closed-under-Π
 hfe {X} {A} X-is-prop A-is-prop-valued f g
 = γ
 where
  γ : f ＝ g
  γ
   = inverse
      (happly f g)
      (hfe X-is-prop f g)
      (λ x → A-is-prop-valued x (f x) (g x))

first-propositional-function-extensionality-agreement =
  props-are-closed-under-Π-gives-prop-vvfunext ,
  prop-vvfunext-gives-prop-hfunext ,
  prop-hfunext-gives-props-are-closed-under-Π

prop-vvfunext-gives-props-are-closed-under-Π
 : prop-vvfunext 𝓤 → props-are-closed-under-Π 𝓤
prop-vvfunext-gives-props-are-closed-under-Π vfe
 = prop-hfunext-gives-props-are-closed-under-Π
    (prop-vvfunext-gives-prop-hfunext vfe)

being-prop-is-prop : prop-vvfunext 𝓤
                   → {X : 𝓤 ̇ } → is-prop (is-prop X)

being-prop-is-prop vfe {X} i j = γ
 where
  k : is-set X
  k = subsingletons-are-sets X i

  a : (x y : X) → i x y ＝ j x y
  a x y = k x y (i x y) (j x y)

  b : (x : X) → i x ＝ j x
  b x = prop-vvfunext-gives-props-are-closed-under-Π vfe i
            (subsingletons-are-sets X i x) (i x) (j x)

  c : (x : X) → is-prop ((y : X) → x ＝ y)
  c x
   = singletons-are-subsingletons
      ((y : X) → x ＝ y)
      (vfe i
        (λ y → pointed-subsingletons-are-singletons (x ＝ y) (i x y) (k x y)))

  γ : i ＝ j
  γ = prop-vvfunext-gives-props-are-closed-under-Π vfe i c i j

being-singleton-is-prop : props-are-closed-under-Π 𝓤
                        →  {X : 𝓤 ̇ } → is-prop (is-singleton X)

being-singleton-is-prop c {X} (x , φ) (y , γ) = p
 where
  i : is-subsingleton X
  i = singletons-are-subsingletons X (y , γ)

  s : is-set X
  s = subsingletons-are-sets X i

  a : (z : X) → is-subsingleton ((t : X) → z ＝ t)
  a z = c i (λ x → s z x)

  b : x ＝ y
  b = φ y

  p : (x , φ) ＝ (y , γ)
  p = to-subtype-＝ a b

Id-of-props-is-prop : propext 𝓤
                    → prop-vvfunext 𝓤
                    → (P : 𝓤 ̇ )
                    → is-prop P
                    → (X : 𝓤 ̇ ) → is-prop (P ＝ X)

Id-of-props-is-prop {𝓤} pe vfe P i = Hedberg P (λ X → h X , k X)
 where
  module _ (X : 𝓤 ̇ ) where
   f : P ＝ X → is-prop X × (P ⇔ X)
   f p = transport is-prop p i , Id→fun p , (Id→fun (p ⁻¹))

   g : is-prop X × (P ⇔ X) → P ＝ X
   g (l , φ , ψ) = pe i l φ ψ

   h : P ＝ X → P ＝ X
   h = g ∘ f

   j : is-prop (is-prop X × (P ⇔ X))
   j
    = ×-is-subsingleton'
       ((λ (_ : P ⇔ X) → being-prop-is-prop vfe) ,
        (λ (l : is-prop X)
           → ×-is-subsingleton
              (prop-vvfunext-gives-props-are-closed-under-Π vfe i (λ _ → l))
              (prop-vvfunext-gives-props-are-closed-under-Π vfe l (λ _ → i))))

   k : wconstant h
   k p q = ap g (j (f p) (f q))

being-equiv-of-props-is-prop : props-are-closed-under-Π 𝓤
                             → {X Y : 𝓤 ̇ }
                             → is-prop X
                             → is-prop Y
                             → (f : X → Y) → is-prop (is-equiv f)

being-equiv-of-props-is-prop c i j f = c j (λ y → being-singleton-is-prop c)

propext-and-props-are-closed-under-Π-give-prop-univalence
 : propext 𝓤
 → props-are-closed-under-Π 𝓤
 → prop-univalence 𝓤

propext-and-props-are-closed-under-Π-give-prop-univalence pe c A i X = γ
 where
  l : A ≃ X → is-subsingleton X
  l e = equiv-to-subsingleton (≃-sym e) i

  eqtoid : A ≃ X → A ＝ X
  eqtoid e = pe i
                (equiv-to-subsingleton (≃-sym e) i)
                ⌜ e ⌝
                ⌜ ≃-sym e ⌝

  m : is-subsingleton (A ≃ X)
  m (f₀ , k₀) (f₁ , k₁) = δ
    where
     j : (f : A → X) → is-prop (is-equiv f)
     j = being-equiv-of-props-is-prop c i
              (equiv-to-subsingleton (≃-sym (f₀ , k₀)) i)

     p : f₀ ＝ f₁
     p = c i (λ (a : A) → l (f₁ , k₁)) f₀ f₁

     δ : (f₀ , k₀) ＝ (f₁ , k₁)
     δ = to-subtype-＝ j p

  ε : (e : A ≃ X) → Id→Eq A X (eqtoid e) ＝ e
  ε e = m (Id→Eq A X (eqtoid e)) e

  η : (q : A ＝ X) → eqtoid (Id→Eq A X q) ＝ q
  η q = Id-of-props-is-prop pe
          (props-are-closed-under-Π-gives-prop-vvfunext c)
          A i X
          (eqtoid (Id→Eq A X q)) q

  γ : is-equiv (Id→Eq A X)
  γ = invertibles-are-equivs (Id→Eq A X) (eqtoid , η , ε)

prop-postcomp-invertible : {X Y A : 𝓤 ̇ }
                         → props-form-exponential-ideal 𝓤
                         → is-prop X
                         → is-prop Y
                         → (f : X → Y)
                         → invertible f
                         → invertible (λ (h : A → X) → f ∘ h)

prop-postcomp-invertible {𝓤} {X} {Y} {A} pei i j f (g , η , ε) = γ
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h

  g' : (A → Y) → (A → X)
  g' k = g ∘ k

  η' : (h : A → X) → g' (f' h) ＝ h
  η' h = pei A X i (g' (f' h)) h

  ε' : (k : A → Y) → f' (g' k) ＝ k
  ε' k = pei A Y j (f' (g' k)) k

  γ : invertible f'
  γ = (g' , η' , ε')

prop-postcomp-is-equiv : {X Y A : 𝓤 ̇ }
                       → props-form-exponential-ideal 𝓤
                       → is-prop X
                       → is-prop Y
                       → (f : X → Y)
                       → is-equiv f
                       → is-equiv (λ (h : A → X) → f ∘ h)

prop-postcomp-is-equiv pei i j f e =
 invertibles-are-equivs
  (λ h → f ∘ h)
  (prop-postcomp-invertible pei i j f (equivs-are-invertible f e))

props-form-exponential-ideal-gives-vvfunext
 : props-form-exponential-ideal 𝓤 → prop-vvfunext 𝓤
props-form-exponential-ideal-gives-vvfunext {𝓤} pei {X} {A} X-is-prop φ = γ
 where
  f : Σ A → X
  f = pr₁

  A-is-prop-valued : (x : X) → is-prop (A x)
  A-is-prop-valued x = singletons-are-subsingletons (A x) (φ x)

  k : is-prop (Σ A)
  k = Σ-is-subsingleton X-is-prop A-is-prop-valued

  f-is-equiv : is-equiv f
  f-is-equiv = pr₁-is-equiv φ

  g : (X → Σ A) → (X → X)
  g h = f ∘ h

  e : is-equiv g
  e = prop-postcomp-is-equiv pei k X-is-prop f f-is-equiv

  i : is-singleton (Σ h ꞉ (X → Σ A), f ∘ h ＝ 𝑖𝑑 X)
  i = e (𝑖𝑑 X)

  r : (Σ h ꞉ (X → Σ A), f ∘ h ＝ 𝑖𝑑 X) → Π A
  r (h , p) x = transport A (happly (f ∘ h) (𝑖𝑑 X) p x) (pr₂ (h x))

  s : Π A → (Σ h ꞉ (X → Σ A), f ∘ h ＝ 𝑖𝑑 X)
  s ψ = (λ x → x , ψ x) , refl (𝑖𝑑 X)

  η : ∀ ψ → r (s ψ) ＝ ψ
  η ψ = refl (r (s ψ))

  γ : is-singleton (Π A)
  γ = retract-of-singleton (r , s , η) i

prop-univalence-gives-props-are-closed-under-Π
 : prop-univalence 𝓤 → props-are-closed-under-Π 𝓤
prop-univalence-gives-props-are-closed-under-Π pu =
    prop-vvfunext-gives-props-are-closed-under-Π
        (props-form-exponential-ideal-gives-vvfunext
              (prop-univalence-gives-props-form-exponential-ideal pu))

propext-and-props-closed-under-Π-give-props-form-exponential-ideal :

    propext 𝓤
  → props-are-closed-under-Π 𝓤
  → props-form-exponential-ideal 𝓤

propext-and-props-closed-under-Π-give-props-form-exponential-ideal pe c =
  prop-univalence-gives-props-form-exponential-ideal
      (propext-and-props-are-closed-under-Π-give-prop-univalence pe c)

props-form-exponential-ideal-gives-props-are-closed-under-Π :

    props-form-exponential-ideal 𝓤
  → props-are-closed-under-Π 𝓤

props-form-exponential-ideal-gives-props-are-closed-under-Π pei =
     prop-vvfunext-gives-props-are-closed-under-Π
         (props-form-exponential-ideal-gives-vvfunext pei)

characterization-of-propositional-univalence {𝓤} = α , β
 where
  α : prop-univalence 𝓤 → propext 𝓤 × props-are-closed-under-Π 𝓤
  α pu = prop-univalence-gives-propext pu ,
         prop-univalence-gives-props-are-closed-under-Π pu

  β : propext 𝓤 × props-are-closed-under-Π 𝓤 → prop-univalence 𝓤
  β (pe , fe) = propext-and-props-are-closed-under-Π-give-prop-univalence pe fe

second-propositional-function-extensionality-agreement {𝓤} pe =
  props-form-exponential-ideal-gives-props-are-closed-under-Π ,
  propext-and-props-closed-under-Π-give-props-form-exponential-ideal pe

infix  40 _∈_

\end{code}
