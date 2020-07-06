Martin Escardo, 15 June 2020

We consider topped σ-sup-lattices. We have ℕ-indexed joins and ⊥ (and
hence finite joins). We also have a top element ⊤.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (*)
open import UF-FunExt
open import UF-Subsingletons

module sigma-sup-lattice
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import UF-Base
open import UF-SIP
open import UF-Equiv hiding (_≅_)
open import UF-Univalence
open import UF-Subsingletons-FunExt

σ-sup-lattice-structure : 𝓤 ̇ → 𝓤 ̇
σ-sup-lattice-structure X = X × X × ((ℕ → X) → X)

\end{code}

A compatible order for σ-sup-lattice structure (⊤ , ⊥ , ⋁) is a
partial order (prop-valued, reflexive, transitive and antisymmetric
binary relation) such that ⊥ is the smallest element, ⊤ is the largest
element, and ⋁ x is the least upper bound of the sequence x.

\begin{code}

is-σ-sup-compatible-order : {X : 𝓤 ̇ } → σ-sup-lattice-structure X → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-σ-sup-compatible-order {𝓤} {𝓥} {X} (⊤ , ⊥ , ⋁) _≤_ = I × II × III × IV × V × VI × VII × VIII
 where
  I    = (x y : X) → is-prop (x ≤ y)
  II   = (x : X) → x ≤ x
  III  = (x y z : X) → x ≤ y → y ≤ z → x ≤ z
  IV   = (x y : X) → x ≤ y → y ≤ x → x ≡ y
  V    = (x : X) → x ≤ ⊤
  VI   = (x : X) → ⊥ ≤ x
  VII  = (x : ℕ → X) (n : ℕ) → x n ≤ ⋁ x
  VIII = (x : ℕ → X) (u : X) → ((n : ℕ) → x n ≤ u) → ⋁ x ≤ u
\end{code}

We can define the binary sup x ∨ y of two elements x and y by
⋁ (x * y) where x * y is the infinite sequence consisting of x
followed by infinitely many y's. Then we can define the intrinsic
order by x ≤ y iff x ∨ y = y.

\begin{code}

private _*_ : {X : 𝓤 ̇} → X → X → (ℕ → X)
(x * y)       0  = x
(x * y) (succ _) = y

intrinsic-order : {X : 𝓤 ̇ } → σ-sup-lattice-structure X → (X → X → 𝓤 ̇ )
intrinsic-order (⊤ , ⊥ , ⋁) x y = ⋁ (x * y) ≡ y

syntax intrinsic-order s x y = x ≤[ s ] y

\end{code}

Any compatible order is logically equivalent to the intrinsic order:

\begin{code}

any-σ-sup-order-is-intrinsic-order : {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X) (_≤_ : X → X → 𝓥 ̇ )
                                   → is-σ-sup-compatible-order s _≤_
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

\end{code}

Therefore, by functional and propositional extensionality, there is at
most one compatible order:

\begin{code}

at-most-one-σ-sup-order : {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X) (_≤_ _≤'_ : X → X → 𝓥 ̇ )
                        → is-σ-sup-compatible-order s _≤_
                        → is-σ-sup-compatible-order s _≤'_
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

\end{code}

Hence being order compatible is property (rather than just data):

\begin{code}

being-σ-sup-order-is-prop : {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X) (_≤_ : X → X → 𝓥 ̇ )
                          → is-prop (is-σ-sup-compatible-order s _≤_)
being-σ-sup-order-is-prop (⊤ , ⊥ , ⋁) _≤_ = prop-criterion γ
 where
  s = (⊤ , ⊥ , ⋁)
  γ : is-σ-sup-compatible-order s _≤_ → is-prop (is-σ-sup-compatible-order s _≤_)
  γ (≤-prop-valued , ≤-refl , ≤-trans , ≤-anti , top , bottom , ⋁-is-ub , ⋁-is-lb-of-ubs) =
    ×₈-is-prop (Π₂-is-prop fe (λ x y → being-prop-is-prop fe))
               (Π-is-prop  fe (λ x → ≤-prop-valued x x))
               (Π₅-is-prop fe (λ x _ z _ _ → ≤-prop-valued x z))
               (Π₄-is-prop fe (λ x y _ _ → type-with-prop-valued-refl-antisym-rel-is-set
                                            _≤_ ≤-prop-valued ≤-refl ≤-anti))
               (Π-is-prop  fe (λ x → ≤-prop-valued x ⊤))
               (Π-is-prop  fe (λ x → ≤-prop-valued ⊥ x))
               (Π₂-is-prop fe (λ x n → ≤-prop-valued (x n) (⋁ x)))
               (Π₃-is-prop fe (λ x u _ → ≤-prop-valued (⋁ x) u))
\end{code}

The σ-sup-lattice axiom says that there exists a compatible order,
which is then unique by the above:

\begin{code}

σ-sup-lattice-axiom : (𝓥 : Universe) {X : 𝓤 ̇ } → σ-sup-lattice-structure X → 𝓤 ⊔ (𝓥 ⁺) ̇
σ-sup-lattice-axiom 𝓥 {X} s = Σ _≤_ ꞉ (X → X → 𝓥 ̇ ) , (is-σ-sup-compatible-order s _≤_)

σ-sup-lattice-axiom-gives-is-set : {X : 𝓤 ̇ } {s : σ-sup-lattice-structure X}
                                 → σ-sup-lattice-axiom 𝓥 s → is-set X
σ-sup-lattice-axiom-gives-is-set (_≤_ , ≤-prop-valued , ≤-refl , _ , ≤-anti , _) =
  type-with-prop-valued-refl-antisym-rel-is-set _≤_ ≤-prop-valued ≤-refl ≤-anti


σ-sup-lattice-axiom-is-prop : {𝓥 : Universe}
                            → {X : 𝓤 ̇ } (s : σ-sup-lattice-structure X)
                            → is-prop (σ-sup-lattice-axiom 𝓥 {X} s)
σ-sup-lattice-axiom-is-prop s (_≤_ , a) (_≤'_ , a') = to-subtype-≡
                                                        (being-σ-sup-order-is-prop s)
                                                        (at-most-one-σ-sup-order s _≤_ _≤'_ a a')

σ-Sup-Lattice : (𝓤 𝓥  : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
σ-Sup-Lattice 𝓤 𝓥 = Σ X ꞉  𝓤 ̇ , Σ s ꞉ σ-sup-lattice-structure X , σ-sup-lattice-axiom 𝓥 s

open sip public

⊤⟨_⟩ : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) → ⟨ 𝓐 ⟩
⊤⟨ A , (⊤ , ⊥ , ⋁) , _ ⟩ = ⊤

⊥⟨_⟩ : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) → ⟨ 𝓐 ⟩
⊥⟨ A , (⊤ , ⊥ , ⋁) , _ ⟩ = ⊥

⋁⟨_⟩ : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) → (ℕ → ⟨ 𝓐 ⟩) → ⟨ 𝓐 ⟩
⋁⟨ A , (⊤ , ⊥ , ⋁) , _ ⟩ = ⋁

⟨_⟩-is-set : (L : σ-Sup-Lattice 𝓤 𝓥) → is-set ⟨ L ⟩
⟨_⟩-is-set (X , s , a) = σ-sup-lattice-axiom-gives-is-set a

⟨_⟩-order : (𝓐 : σ-Sup-Lattice 𝓤 𝓥)
            → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → 𝓥 ̇
⟨ A , (⊤ , ⊥ , ⋁) , (_≤_ , _) ⟩-order = _≤_

order : (𝓐 : σ-Sup-Lattice 𝓤 𝓥)
      → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → 𝓥 ̇
order = ⟨_⟩-order

syntax order 𝓐 x y = x ≤⟨ 𝓐 ⟩ y

⟨_⟩-structure : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) → σ-sup-lattice-structure ⟨ 𝓐 ⟩
⟨ A , s , (_≤_ , i-viii) ⟩-structure = s

⟨_⟩-≤-is-σ-sup-compatible-order : (𝓐 : σ-Sup-Lattice 𝓤 𝓥)
                                → is-σ-sup-compatible-order ⟨ 𝓐 ⟩-structure (⟨ 𝓐 ⟩-order)
⟨ A , _ , (_≤_ , i-viii) ⟩-≤-is-σ-sup-compatible-order = i-viii

⟨_⟩-order-is-prop-valued : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (a b : ⟨ 𝓐 ⟩) → is-prop (a ≤⟨ 𝓐 ⟩ b)
⟨ A , _ , (_≤_ , i , ii , iii , iv , v , vi , vii , viii) ⟩-order-is-prop-valued = i

⟨_⟩-refl : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (a : ⟨ 𝓐 ⟩) → a ≤⟨ 𝓐 ⟩ a
⟨ A , _ , (_≤_ , i , ii , iii , iv , v , vi , vii , viii) ⟩-refl = ii


⟨_⟩-trans : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (a b c : ⟨ 𝓐 ⟩) → a ≤⟨ 𝓐 ⟩ b → b ≤⟨ 𝓐 ⟩ c → a ≤⟨ 𝓐 ⟩ c
⟨ A , _ , (_≤_ , i , ii , iii , iv , v , vi , vii , viii) ⟩-trans = iii


⟨_⟩-antisym : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (a b : ⟨ 𝓐 ⟩) → a ≤⟨ 𝓐 ⟩ b → b ≤⟨ 𝓐 ⟩ a → a ≡ b
⟨ A , _ , (_≤_ , i , ii , iii , iv , v , vi , vii , viii) ⟩-antisym = iv


⟨_⟩-⊤-maximum : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (a : ⟨ 𝓐 ⟩) → a ≤⟨ 𝓐 ⟩ ⊤⟨ 𝓐 ⟩
⟨ A , _ , (_≤_ , i , ii , iii , iv , v , vi , vii , viii) ⟩-⊤-maximum = v


⟨_⟩-⊥-minimum : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (a : ⟨ 𝓐 ⟩) → ⊥⟨ 𝓐 ⟩ ≤⟨ 𝓐 ⟩ a
⟨ A , _ , (_≤_ , i , ii , iii , iv , v , vi , vii , viii) ⟩-⊥-minimum = vi


⟨_⟩-⋁-is-ub : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (a : ℕ → ⟨ 𝓐 ⟩) (n : ℕ) → a n ≤⟨ 𝓐 ⟩ ⋁⟨ 𝓐 ⟩ a
⟨ A , _ , (_≤_ , i , ii , iii , iv , v , vi , vii , viii) ⟩-⋁-is-ub = vii

⟨_⟩-⋁-is-lb-of-ubs : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (a : ℕ → ⟨ 𝓐 ⟩) (u : ⟨ 𝓐 ⟩)
                   → ((n : ℕ) → a n ≤⟨ 𝓐 ⟩ u) → ⋁⟨ 𝓐 ⟩ a ≤⟨ 𝓐 ⟩ u
⟨ A , _ , (_≤_ , i , ii , iii , iv , v , vi , vii , viii) ⟩-⋁-is-lb-of-ubs = viii

⟨_⟩-⋁-idempotent : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (a : ⟨ 𝓐 ⟩)
                  → ⋁⟨ 𝓐 ⟩ (n ↦ a) ≡ a
⟨_⟩-⋁-idempotent 𝓐 a = ⟨ 𝓐 ⟩-antisym _ _
                              (⟨ 𝓐 ⟩-⋁-is-lb-of-ubs (n ↦ a) a (λ n → ⟨ 𝓐 ⟩-refl a))
                              (⟨ 𝓐 ⟩-⋁-is-ub (n ↦ a) 0)

⟨_⟩-⋁-transp : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) (c : ℕ → ℕ → ⟨ 𝓐 ⟩)
              → ⋁⟨ 𝓐 ⟩ (i ↦ ⋁⟨ 𝓐 ⟩ (j ↦ c i j)) ≡ ⋁⟨ 𝓐 ⟩ (j ↦ ⋁⟨ 𝓐 ⟩ (i ↦ c i j))
⟨_⟩-⋁-transp {𝓤} {𝓥} 𝓐 c = ⟨ 𝓐 ⟩-antisym _ _ m l
 where
  ⋁ = ⋁⟨ 𝓐 ⟩
  _≤_ : ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → 𝓥 ̇
  a ≤ b = a ≤⟨ 𝓐 ⟩ b

  p : ∀ i₀ j₀ → c i₀ j₀ ≤ ⋁ (i ↦ ⋁ (j ↦ c i j))
  p i₀ j₀ = ⟨ 𝓐 ⟩-trans _ _ _ p₀ p₁
   where
    p₀ : c i₀ j₀ ≤ ⋁ (j ↦ c i₀ j)
    p₀ = ⟨ 𝓐 ⟩-⋁-is-ub (λ j → c i₀ j) j₀
    p₁ : ⋁ (j ↦ c i₀ j) ≤ ⋁ (i ↦ ⋁ (j ↦ c i j))
    p₁ = ⟨ 𝓐 ⟩-⋁-is-ub (λ i → ⋁ (j ↦ c i j)) i₀

  l : ⋁ (j ↦ ⋁ (i ↦ c i j)) ≤ ⋁ (i ↦ ⋁ (j ↦ c i j))
  l = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs _ _ (λ j → ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs _ _ (λ i → p i j))

  q : ∀ i₀ j₀ → c i₀ j₀ ≤ ⋁ (j ↦ ⋁ (i ↦ c i j))
  q i₀ j₀ = ⟨ 𝓐 ⟩-trans _ _ _ q₀ q₁
   where
    q₀ : c i₀ j₀ ≤ ⋁ (i ↦ c i j₀)
    q₀ = ⟨ 𝓐 ⟩-⋁-is-ub (λ i → c i j₀) i₀
    q₁ : ⋁ (i ↦ c i j₀) ≤ ⋁ (j ↦ ⋁ (i ↦ c i j))
    q₁ = ⟨ 𝓐 ⟩-⋁-is-ub (λ j → ⋁ (i ↦ c i j)) j₀

  m : ⋁ (i ↦ ⋁ (j ↦ c i j)) ≤ ⋁ (j ↦ ⋁ (i ↦ c i j))
  m = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs _ _ (λ i → ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs _ _ (λ j → q i j))

is-σ-sup-lattice-hom· : (𝓐 : σ-Sup-Lattice 𝓤 𝓦) (𝓑 : σ-Sup-Lattice 𝓥 𝓣)
                      → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-σ-sup-lattice-hom·  (_ , (⊤ , ⊥ , ⋁) , _) (_ , (⊤' , ⊥' , ⋁') , _) f =
    (f ⊤ ≡ ⊤')
  × (f ⊥ ≡ ⊥')
  × (∀ 𝕒 → f (⋁ 𝕒) ≡ ⋁' (n ↦ f (𝕒 n)))

σ-sup-lattice-homs-⊤ : (𝓐 : σ-Sup-Lattice 𝓤 𝓦) (𝓑 : σ-Sup-Lattice 𝓥 𝓣)
                   → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
                   → is-σ-sup-lattice-hom· 𝓐 𝓑 f
                   → f ⊤⟨ 𝓐 ⟩ ≡ ⊤⟨ 𝓑 ⟩
σ-sup-lattice-homs-⊤ 𝓐 𝓑 f (i , ii , iii) = i

σ-sup-lattice-homs-⊥ : (𝓐 : σ-Sup-Lattice 𝓤 𝓦) (𝓑 : σ-Sup-Lattice 𝓥 𝓣)
                     → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
                     → is-σ-sup-lattice-hom· 𝓐 𝓑 f
                     → f ⊥⟨ 𝓐 ⟩ ≡ ⊥⟨ 𝓑 ⟩
σ-sup-lattice-homs-⊥ 𝓐 𝓑 f (i , ii , iii) = ii

σ-sup-lattice-homs-⋁ : (𝓐 : σ-Sup-Lattice 𝓤 𝓦) (𝓑 : σ-Sup-Lattice 𝓥 𝓣)
                     → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
                     → is-σ-sup-lattice-hom· 𝓐 𝓑 f
                     → ∀ 𝕒 → f (⋁⟨ 𝓐 ⟩ 𝕒) ≡ ⋁⟨ 𝓑 ⟩ (n ↦ f (𝕒 n))
σ-sup-lattice-homs-⋁ 𝓐 𝓑 f (i , ii , iii) = iii

σ-sup-lattice-homs-≤ : (𝓐 : σ-Sup-Lattice 𝓤 𝓦) (𝓑 : σ-Sup-Lattice 𝓥 𝓣)
                     → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
                     → is-σ-sup-lattice-hom· 𝓐 𝓑 f
                     → ∀ a b → a ≤⟨ 𝓐 ⟩ b → f a ≤⟨ 𝓑 ⟩ f b
σ-sup-lattice-homs-≤ 𝓐 𝓑 f i a b l = m
 where
  c : f a * f b ∼ f ∘ (a * b)
  c 0 = refl
  c (succ n) = refl
  l' : ⋁⟨ 𝓐 ⟩ (a * b) ≡ b
  l' = lr-implication (any-σ-sup-order-is-intrinsic-order _ (⟨ 𝓐 ⟩-order) ⟨ 𝓐 ⟩-≤-is-σ-sup-compatible-order a b) l
  m' : ⋁⟨ 𝓑 ⟩ (f a * f b) ≡ f b
  m' = ⋁⟨ 𝓑 ⟩ (f a * f b)   ≡⟨ ap ⋁⟨ 𝓑 ⟩ (dfunext fe c)                  ⟩
       ⋁⟨ 𝓑 ⟩ (f ∘ (a * b)) ≡⟨ (σ-sup-lattice-homs-⋁ 𝓐 𝓑 f i (a * b))⁻¹ ⟩
       f (⋁⟨ 𝓐 ⟩ (a * b))   ≡⟨ ap f l'                                    ⟩
       f b                   ∎
  m : f a ≤⟨ 𝓑 ⟩ f b
  m = rl-implication (any-σ-sup-order-is-intrinsic-order _ (⟨ 𝓑 ⟩-order) ⟨ 𝓑 ⟩-≤-is-σ-sup-compatible-order  (f a) (f b)) m'

id-is-σ-sup-lattice-hom· : (𝓐 : σ-Sup-Lattice 𝓤 𝓥) → is-σ-sup-lattice-hom· 𝓐 𝓐 id
id-is-σ-sup-lattice-hom· 𝓐 = refl , refl , (λ 𝕒 → refl)

∘-σ-sup-lattice-hom· : (𝓐 : σ-Sup-Lattice 𝓤 𝓤') (𝓑 : σ-Sup-Lattice 𝓥 𝓥') (𝓒 : σ-Sup-Lattice 𝓦 𝓦')
                       (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) (g : ⟨ 𝓑 ⟩ → ⟨ 𝓒 ⟩)
                     → is-σ-sup-lattice-hom· 𝓐 𝓑 f
                     → is-σ-sup-lattice-hom· 𝓑 𝓒 g
                     → is-σ-sup-lattice-hom· 𝓐 𝓒 (g ∘ f)
∘-σ-sup-lattice-hom· 𝓐 𝓑 𝓒 f g (p₀ , r₀ , s₀) (p₁ , r₁ , s₁) = (p₂ , r₂ , s₂)
 where
  p₂ = g (f ⊤⟨ 𝓐 ⟩) ≡⟨ ap g p₀ ⟩
       g ⊤⟨ 𝓑 ⟩     ≡⟨ p₁      ⟩
       ⊤⟨ 𝓒 ⟩       ∎


  r₂ = g (f ⊥⟨ 𝓐 ⟩) ≡⟨ ap g r₀ ⟩
       g ⊥⟨ 𝓑 ⟩     ≡⟨ r₁      ⟩
       ⊥⟨ 𝓒 ⟩       ∎

  s₂ = λ 𝕒 → g (f (⋁⟨ 𝓐 ⟩ 𝕒))           ≡⟨ ap g (s₀ 𝕒)        ⟩
             g (⋁⟨ 𝓑 ⟩ (λ n → f (𝕒 n))) ≡⟨ s₁ (λ n → f (𝕒 n)) ⟩
             ⋁⟨ 𝓒 ⟩ (λ n → g (f (𝕒 n))) ∎
\end{code}
