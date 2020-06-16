Martin Escardo, 15 June 2020

We consider σ-sup-lattices. We have ℕ-indexed joins and ⊥ (and hence
finite joins). We also assume ⊤.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (*)
open import UF-FunExt
open import UF-Subsingletons

module sigma-sup-lattice
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        {𝓤 : Universe}
       where

open import UF-Base
-- open import UF-SIP
open import UF-Equiv hiding (_≅_)
-- open import UF-Univalence
open import UF-Subsingletons-FunExt

σ-sup-lattice-structure : 𝓤 ̇ → 𝓤 ̇
σ-sup-lattice-structure X = X × X × ((ℕ → X) → X)

is-σ-sup-order : {X : 𝓤 ̇ } → σ-sup-lattice-structure X → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-σ-sup-order {𝓥} {X} (⊤ , ⊥ , ⋁) _≤_ = ((x y : X) → is-prop (x ≤ y))
                                        × ((x : X) → x ≤ x)
                                        × ((x y z : X) → x ≤ y → y ≤ z → x ≤ z)
                                        × ((x y : X) → x ≤ y → y ≤ x → x ≡ y)
                                        × ((x : X) → x ≤ ⊤)
                                        × ((x : X) → ⊥ ≤ x)
                                        × ((x : ℕ → X) → ((n : ℕ) → x n ≤ ⋁ x))
                                        × ((x : ℕ → X) (u : X) → ((n : ℕ) → x n ≤ u) → ⋁ x ≤ u)

private _*_ : {X : 𝓤 ̇} → X → X → (ℕ → X)
(x * y)       0  = x
(x * y) (succ _) = y

intrinsic-order : {X : 𝓤 ̇ } → σ-sup-lattice-structure X → X → X → 𝓤 ̇
intrinsic-order (⊤ , ⊥ , ⋁) x y = ⋁ (x * y) ≡ y

syntax intrinsic-order s x y = x ≤[ s ] y

any-σ-sup-order-is-intrinsic-order : {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X) (_≤_ : X → X → 𝓥 ̇ )
                                   → is-σ-sup-order s _≤_
                                   → (x y : X) → x ≤ y ⇔ x ≤[ s ] y
any-σ-sup-order-is-intrinsic-order {𝓥} {X} (⊤ , ⊥ , ⋁) _≤_ (≤-prop-valued , ≤-refl , ≤-trans , ≤-anti , top , bottom , ⋁-is-ub , ⋁-is-lb-of-ubs) x y = a , b
 where
  s = (⊤ , ⊥ , ⋁)
  a : x ≤ y → x ≤[ s ] y
  a l = iv
   where
    i :  (n : ℕ) → (x * y) n ≤ y
    i       0  = l
    i (succ n) = ≤-refl y
    ii : ⋁ (x * y) ≤ y
    ii = ⋁-is-lb-of-ubs (x * y) y i
    iii : y ≤ ⋁ (x * y)
    iii = ⋁-is-ub (x * y) (succ 0)
    iv : ⋁ (x * y) ≡ y
    iv = ≤-anti (⋁ (x * y)) y ii iii
  b : x ≤[ s ] y → x ≤ y
  b l = iii
   where
    i : ⋁ (x * y) ≤ y
    i = transport (⋁ (x * y) ≤_) l (≤-refl (⋁ (x * y)))
    ii : x ≤ ⋁ (x * y)
    ii = ⋁-is-ub (x * y) 0
    iii : x ≤ y
    iii = ≤-trans _ _ _ ii i

at-most-one-σ-sup-order : {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X) (_≤_ _≤'_ : X → X → 𝓥 ̇ )
                                   → is-σ-sup-order s _≤_
                                   → is-σ-sup-order s _≤'_
                                   → _≤_ ≡ _≤'_
at-most-one-σ-sup-order s _≤_ _≤'_ (i , i') (j , j') = γ
 where
  a : ∀ x y → x ≤ y → x ≤' y
  a x y = v ∘ u
   where
    u : x ≤ y → x ≤[ s ] y
    u = lr-implication (any-σ-sup-order-is-intrinsic-order s _≤_ (i , i') x y)
    v : x ≤[ s ] y → x ≤' y
    v = rl-implication (any-σ-sup-order-is-intrinsic-order s _≤'_ (j , j') x y)

  b : ∀ x y → x ≤' y → x ≤ y
  b x y = v ∘ u
   where
    u : x ≤' y → x ≤[ s ] y
    u = lr-implication (any-σ-sup-order-is-intrinsic-order s _≤'_ (j , j') x y)
    v : x ≤[ s ] y → x ≤ y
    v = rl-implication (any-σ-sup-order-is-intrinsic-order s _≤_ (i , i') x y)

  γ : _≤_ ≡ _≤'_
  γ = dfunext fe (λ x → dfunext fe (λ y → pe (i x y) (j x y) (a x y) (b x y)))

being-σ-sup-order-is-prop : {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X) (_≤_ : X → X → 𝓥 ̇ )
                          → is-prop (is-σ-sup-order s _≤_)
being-σ-sup-order-is-prop (⊤ , ⊥ , ⋁) _≤_ = prop-criterion γ
 where
  s = (⊤ , ⊥ , ⋁)
  γ : is-σ-sup-order s _≤_ → is-prop (is-σ-sup-order s _≤_)
  γ (≤-prop-valued , ≤-refl , ≤-trans , ≤-anti , top , bottom , ⋁-is-ub , ⋁-is-lb-of-ubs) =
    ×₈-is-prop (Π₂-is-prop fe (λ x y → being-prop-is-prop fe))
               (Π-is-prop  fe (λ x → ≤-prop-valued x x))
               (Π₅-is-prop fe (λ x _ z _ _ → ≤-prop-valued x z))
               (Π₄-is-prop fe (λ x y _ _ → type-with-prop-valued-refl-antisym-rel-is-set _≤_ ≤-prop-valued ≤-refl ≤-anti))
               (Π-is-prop  fe (λ x → ≤-prop-valued x ⊤))
               (Π-is-prop  fe (λ x → ≤-prop-valued ⊥ x))
               (Π₂-is-prop fe (λ x n → ≤-prop-valued (x n) (⋁ x)))
               (Π₃-is-prop fe (λ x u _ → ≤-prop-valued (⋁ x) u))


σ-sup-lattice-axioms : (𝓥 : Universe) {X : 𝓤 ̇ } → σ-sup-lattice-structure X → 𝓤 ⊔ (𝓥 ⁺) ̇
σ-sup-lattice-axioms 𝓥 {X} s = Σ _≤_ ꞉ (X → X → 𝓥 ̇ ) , (is-σ-sup-order s _≤_)

σ-sup-lattice-axioms-is-prop : {𝓥 : Universe}
                             → {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X)
                             → is-prop (σ-sup-lattice-axioms 𝓥 {X} s)
σ-sup-lattice-axioms-is-prop s (_≤_ , a) (_≤'_ , a') = to-subtype-≡
                                                        (being-σ-sup-order-is-prop s)
                                                        (at-most-one-σ-sup-order s _≤_ _≤'_ a a')

σ-Sup-Lattice : (𝓥  : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
σ-Sup-Lattice 𝓥 = Σ X ꞉  𝓤 ̇ , Σ s ꞉ σ-sup-lattice-structure X , σ-sup-lattice-axioms 𝓥 s

{- Trying to get a purely equational presentation of σ-sup-lattices (very sketchy)

contained-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (X → Y) → 𝓤 ⊔ 𝓥 ̇
contained-image {𝓤} {𝓥} {X} {Y} f g = (x : X) → Σ x' ꞉ X , f x ≡ g x'

same-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (X → Y) → 𝓤 ⊔ 𝓥 ̇
same-image f g = contained-image f g × contained-image g f


 module observations
         {𝓥 : Universe}
         (X : 𝓤 ̇ )
         (⋁ : (ℕ → X) → X)
         (_≤_ : X → X → 𝓥 ̇ )
         (≤-refl : (x : X) → x ≤ x)
         (≤-trans : (x y z : X) → x ≤ y → y ≤ z → x ≤ z)
         (≤-anti : (x y : X) → x ≤ y → y ≤ x → x ≡ y)
         (⋁-is-ub : (x : ℕ → X) → ((n : ℕ) → x n ≤ ⋁ x))
         (⋁-is-lb-of-ubs : (x : ℕ → X) (u : X) → ((n : ℕ) → x n ≤ u) → ⋁ x ≤ u)
         (⋁-idempotent : (x : X) → ⋁ (n ↦ x) ≡ x)
         (⋁-transp : (x : ℕ → ℕ → X) → ⋁ (i ↦ ⋁ (j ↦ x i j)) ≡ ⋁ (j ↦ ⋁ (i ↦ x i j)))
         (⋁-assoc : (x y : ℕ → X) → same-image x y → ⋁ x ≡ ⋁ y)
        where


  _≤'_ : X → X → 𝓤 ̇
  x ≤' y = ⋁ (x * y) ≡ y
   where
    α : ℕ → X
    α 0        = x
    α (succ _) = y

  ≤'-refl : (x : X) → x ≤' x
  ≤'-refl x = ⋁ (x * x) ≡⟨ ap ⋁ b ⟩
              ⋁ (n ↦ x) ≡⟨ ⋁-idempotent x ⟩
              x ∎
   where
    a : (n : ℕ) → (x * x) n ≡ x
    a 0 = refl
    a (succ n) = refl
    b : x * x ≡ (n ↦ x)
    b = dfunext {!!} a

  ≤'-trans : (x y z : X) → x ≤' y → y ≤' z → x ≤' z
  ≤'-trans x y z l m = {!!}
   where
    a : (x * ⋁ ((y * z)))
          ≡ (x * z)
    a = ap (x *_) m
    b : ⋁ (x * (⋁ (y * z)))
      ≡ ⋁ (x * z)
    b = ap ⋁ a
    c : ⋁ (x * (⋁ (y * z)))
      ≡ {!!}
    c = {!!}
  {-

  x y y y y y y y y y y y y y y ...
  y z z z z z z z z z z z z z z ...
  y z z z z z z z z z z z z z z ...
  y z z z z z z z z z z z z z z ...
  .
  .
  .
  x x x x x x x x x x x x x x x ...
  z z z z z z z z z z z z z z z ...
  z z z z z z z z z z z z z z z ...
  z z z z z z z z z z z z z z z ...


  -}


  ≤'-anti : (x y : X) → x ≤' y → y ≤' x → x ≡ y
  ≤'-anti x y l m = x ≡⟨ m ⁻¹ ⟩
                    ⋁ (y * x) ≡⟨ ⋁-assoc (y * x) (x * y) γ ⟩
                    ⋁ (x * y) ≡⟨ l ⟩
                    y ∎
   where
    a : contained-image (y * x)
                        (x * y)
    a 0 = 1 , refl
    a (succ _) = 0 , refl
    b : contained-image (x * y)
                        (y * x)
    b 0 = 1 , refl
    b (succ _) = 0 , refl
    γ : same-image (y * x)
                   (x * y)
    γ = a , b

  ≤-gives-≤' : (x y : X) → x ≤ y → x ≤' y
  ≤-gives-≤' x y l = ≤-anti (⋁ (x * y)) y i ii
   where
    a :  (n : ℕ) → (x * y) n ≤ y
    a 0 = l
    a (succ n) = ≤-refl y
    i : ⋁ (x * y) ≤ y
    i = ⋁-is-lb-of-ubs (x * y) y a
    ii : y ≤ ⋁ (x * y)
    ii = ⋁-is-ub (x * y) (succ 0)

  ≤'-gives-≤ : (x y : X) → x ≤' y → x ≤ y
  ≤'-gives-≤ x y l = c
   where
    a : ⋁ (x * y) ≤ y
    a = transport (⋁ (x * y) ≤_) l (≤-refl (⋁ (x * y)))
    b : x ≤ ⋁ (x * y)
    b = ⋁-is-ub (x * y) 0
    c : x ≤ y
    c = ≤-trans _ _ _ b a
-}

{-
 σ-sup-lattice-axioms : (X : 𝓤 ̇ ) → σ-sup-lattice-structure X → 𝓤 ⊔ (𝓥 ⁺) ̇
 σ-sup-lattice-axioms X (⊤ , _∧_ , ⋁) = I × II × III × IV × V × VI × VII
  where
   I   = is-set X
   II  = (x : X) → x ∧ x ≡ x
   III = (x y : X) → x ∧ y ≡ y ∧ x
   IV  = (x y z : X) → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
   V   = (x : X) → x ∧ ⊤ ≡ x
   VI  = (x : X) {ℕ : 𝓥 ̇ } (y : ℕ → X) → x ∧ (⋁ y) ≡ ⋁ (n ↦ (x ∧ y n))
   _≤_ : X → X → 𝓤 ̇
   x ≤ y = x ∧ y ≡ x
   VII = {ℕ : 𝓥 ̇ } (x : ℕ → X)
       → ((n : ℕ) → x n ≤ ⋁ x)
       × ((u : X) → ((n : ℕ) → x n ≤ u) → ⋁ x ≤ u)

 σ-sup-lattice-axioms-is-prop : funext 𝓤 𝓤
                      → funext 𝓤 (𝓤 ⊔ (𝓥 ⁺)) → funext (𝓥 ⁺) (𝓤 ⊔ 𝓥) → funext (𝓤 ⊔ 𝓥) 𝓤
                      → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) → funext 𝓥 𝓤 → funext 𝓤 (𝓤 ⊔ 𝓥)
                      → (X : 𝓤 ̇ ) (s : σ-sup-lattice-structure X)
                      → is-prop (σ-sup-lattice-axioms X s)
 σ-sup-lattice-axioms-is-prop fe fe₁ fe₂ fe₃ fe₄ fe₅ fe₆ X (⊤ , _∧_ , ⋁) = prop-criterion δ
  where
   δ : σ-sup-lattice-axioms X (⊤ , _∧_ , ⋁) → is-prop (σ-sup-lattice-axioms X (⊤ , _∧_ , ⋁))
   δ (i , ii-vii) =
     ×-is-prop (being-set-is-prop fe)
    (×-is-prop (Π-is-prop fe (λ x →            i {x ∧ x} {x}))
    (×-is-prop (Π-is-prop fe (λ x →
                Π-is-prop fe (λ y →            i {x ∧ y} {y ∧ x})))
    (×-is-prop (Π-is-prop fe (λ x →
                Π-is-prop fe (λ y →
                Π-is-prop fe (λ z →            i {x ∧ (y ∧ z)} {(x ∧ y) ∧ z}))))
    (×-is-prop (Π-is-prop fe (λ x →            i {x ∧ ⊤} {x}))
    (×-is-prop (Π-is-prop fe₁ (λ x →
                Π-is-prop' fe₂ (λ ℕ →
                Π-is-prop fe₃ (λ y →           i {x ∧ ⋁ y} {⋁ (λ n → x ∧ y n)}))))
               (Π-is-prop' fe₂ (λ n
              → Π-is-prop  fe₄  (λ 𝕪 →
              ×-is-prop (Π-is-prop fe₅ (λ n →  i {𝕪 n ∧ ⋁ 𝕪} {𝕪 n}))
                        (Π-is-prop fe₆ (λ u →
                         Π-is-prop fe₃ (λ _ →  i {⋁ 𝕪 ∧ u} {⋁ 𝕪})))))))))))
 Σ-sup-lattice : (𝓤 ⊔ 𝓥)⁺ ̇
 Σ-sup-lattice = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ σ-sup-lattice-structure A , σ-sup-lattice-axioms A s

 _≅[Σ-sup-lattice]_ : Σ-sup-lattice → Σ-sup-lattice → 𝓤 ⊔ (𝓥 ⁺) ̇
 (A , (⊤ , _∧_ , ⋁) , _) ≅[Σ-sup-lattice] (A' , (⊤' , _∧'_ , ⋁') , _) =

                         Σ f ꞉ (A → A')
                             , is-equiv f
                             × (f ⊤ ≡ ⊤')
                             × ((λ a b → f (a ∧ b)) ≡ (λ a b → f a ∧' f b))
                             × ((λ {ℕ} (𝕒 : ℕ → A) → f (⋁ 𝕒)) ≡ (λ {ℕ} 𝕒 → ⋁' (n ↦ f (𝕒 n))))

 characterization-of-Σ-sup-lattice-≡ : is-univalent 𝓤
                             → funext 𝓤 (𝓤 ⊔ (𝓥 ⁺)) → funext (𝓥 ⁺) (𝓤 ⊔ 𝓥) → funext (𝓤 ⊔ 𝓥) 𝓤
                             → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) → funext 𝓥 𝓤 → funext 𝓤 (𝓤 ⊔ 𝓥)
                             → (A B : Σ-sup-lattice)
                             → (A ≡ B) ≃ (A ≅[Σ-sup-lattice] B)
 characterization-of-Σ-sup-lattice-≡ ua fe₁ fe₂ fe₃ fe₄ fe₅ fe₆ =
   sip.characterization-of-≡ ua
    (sip-with-axioms.add-axioms
       σ-sup-lattice-axioms
       (σ-sup-lattice-axioms-is-prop (univalence-gives-funext ua) fe₁ fe₂ fe₃ fe₄ fe₅ fe₆)
      (sip-join.join
        pointed-type.sns-data
      (sip-join.join
        ∞-magma.sns-data
        ∞-hugemagma.sns-data)))
-}
\end{code}
