Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Yoneda where

open import MGS.Unique-Existence public
open import MGS.Embeddings public

𝓨 : {X : 𝓤 ̇ } → X → (X → 𝓤 ̇ )
𝓨 {𝓤} {X} = Id X

𝑌 : (X : 𝓤 ̇ ) → X → (X → 𝓤 ̇ )
𝑌 {𝓤} X = 𝓨 {𝓤} {X}

transport-lemma : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                → (τ : Nat (𝓨 x) A)
                → (y : X) (p : x ＝ y) → τ y p ＝ transport A p (τ x (refl x))

transport-lemma A x τ x (refl x) = refl (τ x (refl x))

𝓔 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X) → Nat (𝓨 x) A → A x
𝓔 A x τ = τ x (refl x)

𝓝 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X) → A x → Nat (𝓨 x) A
𝓝 A x a y p = transport A p a

yoneda-η : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
         → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
         → 𝓝 A x ∘ 𝓔 A x ∼ id

yoneda-η fe fe' A x = γ
 where
  γ : (τ : Nat (𝓨 x) A) → (λ y p → transport A p (τ x (refl x))) ＝ τ
  γ τ = fe (λ y → fe' (λ p → (transport-lemma A x τ y p)⁻¹))

yoneda-ε : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
         → 𝓔 A x ∘ 𝓝 A x ∼ id

yoneda-ε A x = γ
 where
  γ : (a : A x) → transport A (refl x) a ＝ a
  γ = refl

is-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
is-fiberwise-equiv τ = ∀ x → is-equiv (τ x)

𝓔-is-equiv : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
           → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
           → is-fiberwise-equiv (𝓔 A)

𝓔-is-equiv fe fe' A x = invertibles-are-equivs (𝓔 A x )
                         (𝓝 A x , yoneda-η fe fe' A x , yoneda-ε A x)

𝓝-is-equiv : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
           → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
           → is-fiberwise-equiv (𝓝 A)

𝓝-is-equiv fe fe' A x = invertibles-are-equivs (𝓝 A x)
                         (𝓔 A x , yoneda-ε A x , yoneda-η fe fe' A x)

Yoneda-Lemma : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
             → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
             → Nat (𝓨 x) A ≃ A x

Yoneda-Lemma fe fe' A x = 𝓔 A x , 𝓔-is-equiv fe fe' A x

retract-universal-lemma : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                        → ((y : X) → A y ◁ (x ＝ y))
                        → ∃! A

retract-universal-lemma A x ρ = i
 where
  σ : Σ A ◁ singleton-type' x
  σ = Σ-retract ρ

  i : ∃! A
  i = retract-of-singleton σ (singleton-types'-are-singletons (domain A) x)

fiberwise-equiv-universal : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                            (x : X) (τ : Nat (𝓨 x) A)
                          → is-fiberwise-equiv τ
                          → ∃! A

fiberwise-equiv-universal A x τ e = retract-universal-lemma A x ρ
 where
  ρ : ∀ y → A y ◁ (x ＝ y)
  ρ y = ≃-gives-▷ ((τ y) , e y)

universal-fiberwise-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                          → ∃! A
                          → (x : X) (τ : Nat (𝓨 x) A) → is-fiberwise-equiv τ

universal-fiberwise-equiv {𝓤} {𝓥} {X} A u x τ = γ
 where
  g : singleton-type' x → Σ A
  g = NatΣ τ

  e : is-equiv g
  e = maps-of-singletons-are-equivs g (singleton-types'-are-singletons X x) u

  γ : is-fiberwise-equiv τ
  γ = NatΣ-equiv-gives-fiberwise-equiv τ e

hfunext→ : hfunext 𝓤 𝓥
         → ((X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (f : Π A) → ∃! g ꞉ Π A , f ∼ g)

hfunext→ hfe X A f = fiberwise-equiv-universal (f ∼_) f (happly f) (hfe f)

→hfunext : ((X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (f : Π A) → ∃! g ꞉ Π A , f ∼ g)
         → hfunext 𝓤 𝓥

→hfunext φ {X} {A} f = universal-fiberwise-equiv (f ∼_) (φ X A f) f (happly f)

fiberwise-equiv-criterion : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                            (x : X)
                          → ((y : X) → A y ◁ (x ＝ y))
                          → (τ : Nat (𝓨 x) A) → is-fiberwise-equiv τ

fiberwise-equiv-criterion A x ρ τ = universal-fiberwise-equiv A
                                     (retract-universal-lemma A x ρ) x τ

fiberwise-equiv-criterion' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                            (x : X)
                          → ((y : X) → (x ＝ y) ≃ A y)
                          → (τ : Nat (𝓨 x) A) → is-fiberwise-equiv τ

fiberwise-equiv-criterion' A x e = fiberwise-equiv-criterion A x
                                    (λ y → ≃-gives-▷ (e y))

_≃̇_ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
A ≃̇ B = ∀ x → A x ≃ B x

is-representable : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-representable A = Σ x ꞉ domain A , 𝓨 x ≃̇ A

representable-universal : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                        → is-representable A
                        → ∃! A

representable-universal A (x , e) = retract-universal-lemma A x
                                     (λ x → ≃-gives-▷ (e x))

universal-representable : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → ∃! A
                        → is-representable A

universal-representable {𝓤} {𝓥} {X} {A} ((x , a) , p) = x , φ
 where
  e : is-fiberwise-equiv (𝓝 A x a)
  e = universal-fiberwise-equiv A ((x , a) , p) x (𝓝 A x a)

  φ : (y : X) → (x ＝ y) ≃ A y
  φ y = (𝓝 A x a y , e y)

fiberwise-retractions-are-equivs : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                                 → (τ : Nat (𝓨 x) A)
                                 → ((y : X) → has-section (τ y))
                                 → is-fiberwise-equiv τ

fiberwise-retractions-are-equivs {𝓤} {𝓥} {X} A x τ s = γ
 where
  ρ : (y : X) → A y ◁ (x ＝ y)
  ρ y = τ y , s y

  i : ∃! A
  i = retract-universal-lemma A x ρ

  γ : is-fiberwise-equiv τ
  γ = universal-fiberwise-equiv A i x τ

fiberwise-◁-gives-≃ : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (x : X)
                    → ((y : X) → A y ◁ (x ＝ y))
                    → ((y : X) → A y ≃ (x ＝ y))

fiberwise-◁-gives-≃ X A x ρ = γ
 where
  f : (y : X) → (x ＝ y) → A y
  f y = retraction (ρ y)

  e : is-fiberwise-equiv f
  e = fiberwise-retractions-are-equivs A x f (λ y → retraction-has-section (ρ y))

  γ : (y : X) → A y ≃ (x ＝ y)
  γ y = ≃-sym (f y , e y)

embedding-criterion' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → ((x x' : X) → (f x ＝ f x') ◁ (x ＝ x'))
                     → is-embedding f

embedding-criterion' f ρ = embedding-criterion f
                            (λ x → fiberwise-◁-gives-≃ (domain f)
                                    (λ - → f x ＝ f -) x (ρ x))

being-fiberwise-equiv-is-subsingleton : global-dfunext
                                      → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                                      → (τ : Nat A B)
                                      → is-subsingleton (is-fiberwise-equiv τ)

being-fiberwise-equiv-is-subsingleton fe τ =
 Π-is-subsingleton fe (λ y → being-equiv-is-subsingleton fe fe (τ y))

being-representable-is-subsingleton : global-dfunext
                                    → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                                    → is-subsingleton (is-representable A)

being-representable-is-subsingleton fe {X} A r₀ r₁ = γ
 where
  u : ∃! A
  u = representable-universal A r₀

  i : (x : X) (τ : Nat (𝓨 x) A) → is-singleton (is-fiberwise-equiv τ)
  i x τ = pointed-subsingletons-are-singletons
           (is-fiberwise-equiv τ)
           (universal-fiberwise-equiv A u x τ)
           (being-fiberwise-equiv-is-subsingleton fe τ)

  ε : (x : X) → (𝓨 x ≃̇ A) ≃ A x
  ε x = ((y : X) → 𝓨 x y ≃ A y)                       ≃⟨ ΠΣ-distr-≃ ⟩
        (Σ τ ꞉ Nat (𝓨 x) A , is-fiberwise-equiv τ)    ≃⟨ pr₁-≃ (i x) ⟩
        Nat (𝓨 x) A                                   ≃⟨ Yoneda-Lemma fe fe A x ⟩
        A x                                           ■

  δ : is-representable A ≃ Σ A
  δ = Σ-cong ε

  v : is-singleton (is-representable A)
  v = equiv-to-singleton δ u

  γ : r₀ ＝ r₁
  γ = singletons-are-subsingletons (is-representable A) v r₀ r₁

𝓨-is-embedding : Univalence → (X : 𝓤 ̇ ) → is-embedding (𝑌 X)
𝓨-is-embedding {𝓤} ua X A = γ
 where
  hfe : global-hfunext
  hfe = univalence-gives-global-hfunext ua

  dfe : global-dfunext
  dfe = univalence-gives-global-dfunext ua

  p = λ x → (𝓨 x ＝ A)                 ≃⟨ i  x ⟩
            ((y : X) → 𝓨 x y ＝ A y)   ≃⟨ ii x ⟩
            ((y : X) → 𝓨 x y ≃ A y)   ■
    where
     i  = λ x → (happly (𝓨 x) A , hfe (𝓨 x) A)
     ii = λ x → Π-cong dfe dfe
                 (λ y → univalence-≃ (ua 𝓤)
                         (𝓨 x y) (A y))

  e : fiber 𝓨 A ≃ is-representable A
  e = Σ-cong p

  γ : is-subsingleton (fiber 𝓨 A)
  γ = equiv-to-subsingleton e (being-representable-is-subsingleton dfe A)

\end{code}
