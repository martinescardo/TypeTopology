This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Size where

open import MGS.Powerset                public
open import MGS.Universe-Lifting        public
open import MGS.Subsingleton-Truncation public

_has-size_ : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
X has-size 𝓥 = Σ Y ꞉ 𝓥 ̇ , X ≃ Y

propositional-resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
propositional-resizing 𝓤 𝓥 = (P : 𝓤 ̇ ) → is-subsingleton P → P has-size 𝓥

resize-up : (X : 𝓤 ̇ ) → X has-size (𝓤 ⊔ 𝓥)
resize-up {𝓤} {𝓥} X = (Lift 𝓥 X , ≃-Lift X)

resize-up-subsingleton : propositional-resizing 𝓤 (𝓤 ⊔ 𝓥)
resize-up-subsingleton {𝓤} {𝓥} P i = resize-up {𝓤} {𝓥} P

resize : propositional-resizing 𝓤 𝓥
       → (P : 𝓤 ̇ ) (i : is-subsingleton P) → 𝓥 ̇

resize ρ P i = pr₁ (ρ P i)

resize-is-subsingleton : (ρ : propositional-resizing 𝓤 𝓥)
                         (P : 𝓤 ̇ ) (i : is-subsingleton P)
                       → is-subsingleton (resize ρ P i)

resize-is-subsingleton ρ P i = equiv-to-subsingleton (≃-sym (pr₂ (ρ P i))) i

to-resize : (ρ : propositional-resizing 𝓤 𝓥)
            (P : 𝓤 ̇ ) (i : is-subsingleton P)
          → P → resize ρ P i

to-resize ρ P i = ⌜ pr₂ (ρ P i) ⌝

from-resize : (ρ : propositional-resizing 𝓤 𝓥)
              (P : 𝓤 ̇ ) (i : is-subsingleton P)
            → resize ρ P i → P

from-resize ρ P i = ⌜ ≃-sym (pr₂ (ρ P i)) ⌝

Propositional-resizing : 𝓤ω
Propositional-resizing = {𝓤 𝓥 : Universe} → propositional-resizing 𝓤 𝓥

EM-gives-PR : EM 𝓤 → propositional-resizing 𝓤 𝓥
EM-gives-PR {𝓤} {𝓥} em P i = Q (em P i) , e
 where
   Q : P + ¬ P → 𝓥 ̇
   Q (inl p) = Lift 𝓥 𝟙
   Q (inr n) = Lift 𝓥 𝟘

   j : (d : P + ¬ P) → is-subsingleton (Q d)
   j (inl p) = equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton
   j (inr n) = equiv-to-subsingleton (Lift-≃ 𝟘) 𝟘-is-subsingleton

   f : (d : P + ¬ P) → P → Q d
   f (inl p) p' = lift ⋆
   f (inr n) p  = !𝟘 (Lift 𝓥 𝟘) (n p)

   g : (d : P + ¬ P) → Q d → P
   g (inl p) q = p
   g (inr n) q = !𝟘 P (lower q)

   e : P ≃ Q (em P i)
   e = logically-equivalent-subsingletons-are-equivalent
        P (Q (em P i)) i (j (em P i)) (f (em P i) , g (em P i))

has-size-is-subsingleton : Univalence
                         → (X : 𝓤 ̇ ) (𝓥 :  Universe)
                         → is-subsingleton (X has-size 𝓥)

has-size-is-subsingleton {𝓤} ua X 𝓥 = univalence→' (ua 𝓥) (ua (𝓤 ⊔ 𝓥)) X

PR-is-subsingleton : Univalence → is-subsingleton (propositional-resizing 𝓤 𝓥)
PR-is-subsingleton {𝓤} {𝓥} ua =
 Π-is-subsingleton (univalence-gives-global-dfunext ua)
  (λ P → Π-is-subsingleton (univalence-gives-global-dfunext ua)
  (λ i → has-size-is-subsingleton ua P 𝓥))

Impredicativity : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
Impredicativity 𝓤 𝓥 = (Ω 𝓤) has-size 𝓥

is-impredicative : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-impredicative 𝓤 = Impredicativity 𝓤 𝓤

PR-gives-Impredicativity⁺ : global-propext
                          → global-dfunext
                          → propositional-resizing 𝓥 𝓤
                          → propositional-resizing 𝓤 𝓥
                          → Impredicativity 𝓤 (𝓥 ⁺)

PR-gives-Impredicativity⁺ {𝓥} {𝓤} pe fe ρ σ = γ
 where
  φ : Ω 𝓥 → Ω 𝓤
  φ (Q , j) = resize ρ Q j , resize-is-subsingleton ρ Q j

  ψ : Ω 𝓤 → Ω 𝓥
  ψ (P , i) = resize σ P i , resize-is-subsingleton σ P i

  η : (p : Ω 𝓤) → φ (ψ p) ＝ p
  η (P , i) = Ω-ext fe pe a b
   where
    Q : 𝓥 ̇
    Q = resize σ P i

    j : is-subsingleton Q
    j = resize-is-subsingleton σ P i

    a : resize ρ Q j → P
    a = from-resize σ P i ∘ from-resize ρ Q j

    b : P → resize ρ Q j
    b = to-resize ρ Q j ∘ to-resize σ P i

  ε : (q : Ω 𝓥) → ψ (φ q) ＝ q
  ε (Q , j) = Ω-ext fe pe a b
   where
    P : 𝓤 ̇
    P = resize ρ Q j

    i : is-subsingleton P
    i = resize-is-subsingleton ρ Q j

    a : resize σ P i → Q
    a = from-resize ρ Q j ∘ from-resize σ P i

    b : Q → resize σ P i
    b = to-resize σ P i ∘ to-resize ρ Q j

  γ : (Ω 𝓤) has-size (𝓥 ⁺)
  γ = Ω 𝓥 , invertibility-gives-≃ ψ (φ , η , ε)

PR-gives-impredicativity⁺ : global-propext
                          → global-dfunext
                          → propositional-resizing (𝓤 ⁺) 𝓤
                          → is-impredicative (𝓤 ⁺)

PR-gives-impredicativity⁺ pe fe = PR-gives-Impredicativity⁺
                                   pe fe (λ P i → resize-up P)

PR-gives-impredicativity₁ : global-propext
                          → global-dfunext
                          → propositional-resizing 𝓤 𝓤₀
                          → Impredicativity 𝓤 𝓤₁

PR-gives-impredicativity₁ pe fe = PR-gives-Impredicativity⁺
                                   pe fe (λ P i → resize-up P)

Impredicativity-gives-PR : propext 𝓤
                         → dfunext 𝓤 𝓤
                         → Impredicativity 𝓤 𝓥
                         → propositional-resizing 𝓤 𝓥

Impredicativity-gives-PR {𝓤} {𝓥} pe fe (O , e) P i = Q , ε
 where
  𝟙'' : 𝓤 ̇
  𝟙'' = Lift 𝓤 𝟙

  k : is-subsingleton 𝟙''
  k (lift ⋆) (lift ⋆) = refl (lift ⋆)

  down : Ω 𝓤 → O
  down = ⌜ e ⌝

  O-is-set : is-set O
  O-is-set = equiv-to-set (≃-sym e) (Ω-is-set fe pe)

  Q : 𝓥 ̇
  Q = down (𝟙'' , k) ＝ down (P , i)

  j : is-subsingleton Q
  j = O-is-set (down (Lift 𝓤 𝟙 , k)) (down (P , i))

  φ : Q → P
  φ q = Id→fun
         (ap _holds (equivs-are-lc down (⌜⌝-is-equiv e) q))
         (lift ⋆)

  γ : P → Q
  γ p = ap down (to-subtype-＝
                    (λ _ → being-subsingleton-is-subsingleton fe)
                    (pe k i (λ _ → p) (λ _ → lift ⋆)))

  ε : P ≃ Q
  ε = logically-equivalent-subsingletons-are-equivalent P Q i j (γ , φ)

PR-gives-existence-of-truncations : global-dfunext
                                  → Propositional-resizing
                                  → subsingleton-truncations-exist

PR-gives-existence-of-truncations fe R =
 record
 {
   ∥_∥ =

    λ {𝓤} X → resize R
               (is-inhabited X)
               (inhabitation-is-subsingleton fe X) ;

   ∥∥-is-subsingleton =

    λ {𝓤} {X} → resize-is-subsingleton R
                 (is-inhabited X)
                 (inhabitation-is-subsingleton fe X) ;

   ∣_∣ =

    λ {𝓤} {X} x → to-resize R
                   (is-inhabited X)
                   (inhabitation-is-subsingleton fe X)
                   (inhabited-intro x) ;

   ∥∥-recursion =

    λ {𝓤} {𝓥} {X} {P} i u s → from-resize R P i
                                (inhabited-recursion
                                  (resize-is-subsingleton R P i)
                                  (to-resize R P i ∘ u)
                                  (from-resize R
                                    (is-inhabited X)
                                    (inhabitation-is-subsingleton fe X) s))
 }

module powerset-union-existence
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

 open basic-truncation-development pt hfe

 family-union : {X : 𝓤 ⊔ 𝓥 ̇ } {I : 𝓥 ̇ } → (I → 𝓟 X) → 𝓟 X
 family-union {𝓤} {𝓥} {X} {I} A = λ x → (∃ i ꞉ I , x ∈ A i) , ∃-is-subsingleton

 𝓟𝓟 : 𝓤 ̇ → 𝓤 ⁺⁺ ̇
 𝓟𝓟 X = 𝓟 (𝓟 X)

 existence-of-unions : (𝓤 : Universe) → 𝓤 ⁺⁺ ̇
 existence-of-unions 𝓤 =
  (X : 𝓤 ̇ ) (𝓐 : 𝓟𝓟 X) → Σ B ꞉ 𝓟 X , ((x : X) → (x ∈ B) ↔ (∃ A ꞉ 𝓟 X , (A ∈ 𝓐) × (x ∈ A)))

 existence-of-unions₁ : (𝓤 :  Universe) → _ ̇
 existence-of-unions₁ 𝓤 =
  (X : 𝓤 ̇ )
  (𝓐 : (X → Ω _) → Ω _)
     → Σ B ꞉ (X → Ω _) , ((x : X) → (x ∈ B) ↔ (∃ A ꞉ (X → Ω _) , (A ∈ 𝓐) × (x ∈ A)))

 existence-of-unions₂ : (𝓤 :  Universe) → 𝓤 ⁺⁺ ̇
 existence-of-unions₂ 𝓤 =
  (X : 𝓤 ̇ )
  (𝓐 : (X → Ω 𝓤) → Ω (𝓤 ⁺))
     → Σ B ꞉ (X → Ω 𝓤) , ((x : X) → (x ∈ B) ↔ (∃ A ꞉ (X → Ω 𝓤) , (A ∈ 𝓐) × (x ∈ A)))

 existence-of-unions-agreement : existence-of-unions 𝓤 ＝ existence-of-unions₂ 𝓤
 existence-of-unions-agreement = refl _

 existence-of-unions-gives-PR : existence-of-unions 𝓤
                              → propositional-resizing (𝓤 ⁺) 𝓤

 existence-of-unions-gives-PR {𝓤} α = γ
  where
   γ : (P : 𝓤 ⁺ ̇ ) → (i : is-subsingleton P) → P has-size 𝓤
   γ P i = Q , e
    where
    𝟙ᵤ : 𝓤 ̇
    𝟙ᵤ = Lift 𝓤 𝟙

    ⋆ᵤ : 𝟙ᵤ
    ⋆ᵤ = lift ⋆

    𝟙ᵤ-is-subsingleton : is-subsingleton 𝟙ᵤ
    𝟙ᵤ-is-subsingleton = equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton

    𝓐 : 𝓟𝓟 𝟙ᵤ
    𝓐 = λ (A : 𝓟 𝟙ᵤ) → P , i

    B : 𝓟 𝟙ᵤ
    B = pr₁ (α 𝟙ᵤ 𝓐)

    φ : (x : 𝟙ᵤ) → (x ∈ B) ↔ (∃ A ꞉ 𝓟 𝟙ᵤ , (A ∈ 𝓐) × (x ∈ A))
    φ = pr₂ (α 𝟙ᵤ 𝓐)

    Q : 𝓤 ̇
    Q = ⋆ᵤ ∈ B

    j : is-subsingleton Q
    j = ∈-is-subsingleton B ⋆ᵤ

    f : P → Q
    f p = b
     where
      a : Σ A ꞉ 𝓟 𝟙ᵤ , (A ∈ 𝓐) × (⋆ᵤ ∈ A)
      a = (λ (x : 𝟙ᵤ) → 𝟙ᵤ , 𝟙ᵤ-is-subsingleton) , p , ⋆ᵤ

      b : ⋆ᵤ ∈ B
      b = rl-implication (φ ⋆ᵤ) ∣ a ∣

    g : Q → P
    g q = ∥∥-recursion i b a
     where
      a : ∃ A ꞉ 𝓟 𝟙ᵤ , (A ∈ 𝓐) × (⋆ᵤ ∈ A)
      a = lr-implication (φ ⋆ᵤ) q

      b : (Σ A ꞉ 𝓟 𝟙ᵤ , (A ∈ 𝓐) × (⋆ᵤ ∈ A)) → P
      b (A , m , _) = m

    e : P ≃ Q
    e = logically-equivalent-subsingletons-are-equivalent P Q i j (f , g)

 PR-gives-existence-of-unions : propositional-resizing (𝓤 ⁺) 𝓤
                              → existence-of-unions 𝓤

 PR-gives-existence-of-unions {𝓤} ρ X 𝓐 = B , (λ x → lr x , rl x)
  where
   β : X → 𝓤 ⁺ ̇
   β x = ∃ A ꞉ 𝓟 X , (A ∈ 𝓐) × (x ∈ A)

   i : (x : X) → is-subsingleton (β x)
   i x = ∃-is-subsingleton

   B : 𝓟 X
   B x = (resize ρ (β x) (i x) , resize-is-subsingleton ρ (β x) (i x))

   lr : (x : X) → x ∈ B → ∃ A ꞉ 𝓟 X , (A ∈ 𝓐) × (x ∈ A)
   lr x = from-resize ρ (β x) (i x)

   rl : (x : X) → (∃ A ꞉ 𝓟 X , (A ∈ 𝓐) × (x ∈ A)) → x ∈ B
   rl x = to-resize ρ (β x) (i x)

module basic-powerset-development
        (hfe : global-hfunext)
        (ρ   : Propositional-resizing)
       where

  pt : subsingleton-truncations-exist
  pt = PR-gives-existence-of-truncations (hfunext-gives-dfunext hfe) ρ

  open basic-truncation-development pt hfe
  open powerset-union-existence pt hfe

  ⋃ : {X : 𝓤 ̇ } → 𝓟𝓟 X → 𝓟 X
  ⋃ 𝓐 = pr₁ (PR-gives-existence-of-unions ρ _ 𝓐)

  ⋃-property : {X : 𝓤 ̇ } (𝓐 : 𝓟𝓟 X)
             → (x : X) → (x ∈ ⋃ 𝓐) ↔ (∃ A ꞉ 𝓟 X , (A ∈ 𝓐) × (x ∈ A))

  ⋃-property 𝓐 = pr₂ (PR-gives-existence-of-unions ρ _ 𝓐)

  intersections-exist :
    (X : 𝓤 ̇ )
    (𝓐 : 𝓟𝓟 X)
       → Σ B ꞉ 𝓟 X , ((x : X) → (x ∈ B) ↔ ((A : 𝓟 X) → A ∈ 𝓐 → x ∈ A))

  intersections-exist {𝓤} X 𝓐 = B , (λ x → lr x , rl x)
   where
    β : X → 𝓤 ⁺ ̇
    β x = (A : 𝓟 X) → A ∈ 𝓐 → x ∈ A

    i : (x : X) → is-subsingleton (β x)
    i x = Π-is-subsingleton hunapply
           (λ A → Π-is-subsingleton hunapply
           (λ _ → ∈-is-subsingleton A x))

    B : 𝓟 X
    B x = (resize ρ (β x) (i x) , resize-is-subsingleton ρ (β x) (i x))

    lr : (x : X) → x ∈ B → (A : 𝓟 X) → A ∈ 𝓐 → x ∈ A
    lr x = from-resize ρ (β x) (i x)

    rl : (x : X) → ((A : 𝓟 X) → A ∈ 𝓐 → x ∈ A) → x ∈ B
    rl x = to-resize ρ (β x) (i x)

  ⋂ : {X : 𝓤 ̇ } → 𝓟𝓟 X → 𝓟 X
  ⋂ {𝓤} {X} 𝓐 = pr₁ (intersections-exist X 𝓐)

  ⋂-property : {X : 𝓤 ̇ } (𝓐 : 𝓟𝓟 X)
             → (x : X) → (x ∈ ⋂ 𝓐) ↔ ((A : 𝓟 X) → A ∈ 𝓐 → x ∈ A)

  ⋂-property {𝓤} {X} 𝓐 = pr₂ (intersections-exist X 𝓐)

  ∅ full : {X : 𝓤 ̇ } → 𝓟 X

  ∅    = λ x → (Lift _ 𝟘 , equiv-to-subsingleton (Lift-≃ 𝟘) 𝟘-is-subsingleton)

  full = λ x → (Lift _ 𝟙 , equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton)

  ∅-property : (X : 𝓤 ̇ ) → (x : X) → ¬ (x ∈ ∅)
  ∅-property X x = lower

  full-property : (X : 𝓤 ̇ ) → (x : X) → x ∈ full
  full-property X x = lift ⋆

  _∩_ _∪_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓟 X

  (A ∪ B) = λ x → ((x ∈ A) ∨ (x ∈ B)) , ∨-is-subsingleton

  (A ∩ B) = λ x → ((x ∈ A) × (x ∈ B)) ,
                  ×-is-subsingleton
                    (∈-is-subsingleton A x)
                    (∈-is-subsingleton B x)

  ∪-property : {X : 𝓤 ̇ } (A B : 𝓟 X)
             → (x : X) → x ∈ (A ∪ B) ↔ (x ∈ A) ∨ (x ∈ B)

  ∪-property {𝓤} {X} A B x = id , id

  ∩-property : {X : 𝓤 ̇ } (A B : 𝓟 X)
             → (x : X) → x ∈ (A ∩ B) ↔ (x ∈ A) × (x ∈ B)

  ∩-property {𝓤} {X} A B x = id , id

  infix  20 _∩_
  infix  20 _∪_

  Top : (𝓤 : Universe) → 𝓤 ⁺⁺ ̇
  Top 𝓤 = Σ X ꞉ 𝓤 ̇ , is-set X
                     × (Σ 𝓞 ꞉ 𝓟𝓟 X , full ∈ 𝓞
                                   × ((U V : 𝓟 X) → U ∈ 𝓞 → V ∈ 𝓞 → (U ∩ V) ∈ 𝓞)
                                   × ((𝓖 : 𝓟𝓟 X) → 𝓖 ⊆ 𝓞 → ⋃ 𝓖 ∈ 𝓞))

\end{code}
