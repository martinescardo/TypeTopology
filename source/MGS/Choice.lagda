This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Choice where

open import MGS.Unique-Existence        public
open import MGS.Yoneda                  public
open import MGS.Subsingleton-Truncation public
open import MGS.Universe-Lifting        public

simple-unique-choice : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )

                     → ((x : X) → ∃! a ꞉ A x , R x a)
                     → Σ f ꞉ Π A , ((x : X) → R x (f x))

simple-unique-choice X A R s = f , φ
 where
  f : (x : X) → A x
  f x = pr₁ (center (Σ a ꞉ A x , R x a) (s x))

  φ : (x : X) → R x (f x)
  φ x = pr₂ (center (Σ a ꞉ A x , R x a) (s x))

Unique-Choice : (𝓤 𝓥 𝓦 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇
Unique-Choice 𝓤 𝓥 𝓦 = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )
                     → ((x : X) → ∃! a ꞉ A x , R x a)
                     → ∃! f ꞉ Π A , ((x : X) → R x (f x))

vvfunext-gives-unique-choice : vvfunext 𝓤 (𝓥 ⊔ 𝓦) → Unique-Choice 𝓤 𝓥 𝓦
vvfunext-gives-unique-choice vv X A R s = c
 where
  a : ((x : X) → Σ a ꞉ A x , R x a)
    ≃ (Σ f ꞉ ((x : X) → A x), ((x : X) → R x (f x)))

  a = ΠΣ-distr-≃

  b : is-singleton ((x : X) → Σ a ꞉ A x , R x a)
  b = vv s

  c : is-singleton (Σ f ꞉ ((x : X) → A x), ((x : X) → R x (f x)))
  c = equiv-to-singleton' a b

unique-choice-gives-vvfunext : Unique-Choice 𝓤 𝓥 𝓥 → vvfunext 𝓤 𝓥
unique-choice-gives-vvfunext {𝓤} {𝓥} uc {X} {A} φ = γ
 where
  R : (x : X) → A x → 𝓥 ̇
  R x a = A x

  s' : (x : X) → is-singleton (A x × A x)
  s' x = ×-is-singleton (φ x) (φ x)

  s : (x : X) → ∃! y ꞉ A x , R x y
  s = s'

  e : ∃! f ꞉ Π A , ((x : X) → R x (f x))
  e = uc X A R s

  e' : is-singleton (Π A × Π A)
  e' = e

  ρ : Π A ◁ Π A × Π A
  ρ = pr₁ , (λ y → y , y) , refl

  γ : is-singleton (Π A)
  γ = retract-of-singleton ρ e'

unique-choice-gives-hfunext : Unique-Choice 𝓤 𝓥 𝓥 → hfunext 𝓤 𝓥
unique-choice-gives-hfunext {𝓤} {𝓥} uc = →hfunext γ
 where
  γ : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (f : Π A) → ∃! g ꞉ Π A , f ∼ g
  γ X A f = uc X A R e
   where
    R : (x : X) → A x → 𝓥 ̇
    R x a = f x ＝ a
    e : (x : X) → ∃! a ꞉ A x , f x ＝ a
    e x = singleton-types'-are-singletons (A x) (f x)

unique-choice⇔vvfunext : Unique-Choice 𝓤 𝓥 𝓥 ⇔ vvfunext 𝓤 𝓥
unique-choice⇔vvfunext = unique-choice-gives-vvfunext ,
                         vvfunext-gives-unique-choice

module _ (hfe : global-hfunext) where

 private
   hunapply : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ＝ g
   hunapply = inverse (happly _ _) (hfe _ _)

 transport-hunapply : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )
                      (f g : Π A)
                      (φ : (x : X) → R x (f x))
                      (h : f ∼ g)
                      (x : X)
                    → transport (λ - → (x : X) → R x (- x)) (hunapply h) φ x
                    ＝ transport (R x) (h x) (φ x)

 transport-hunapply A R f g φ h x =

   transport (λ - → ∀ x → R x (- x)) (hunapply h) φ x ＝⟨ i  ⟩
   transport (R x) (happly f g (hunapply h) x) (φ x)  ＝⟨ ii ⟩
   transport (R x) (h x) (φ x)                        ∎

  where
   a : {f g : Π A} {φ : ∀ x → R x (f x)} (p : f ＝ g) (x : domain A)
     → transport (λ - → ∀ x → R x (- x)) p φ x
     ＝ transport (R x) (happly f g p x) (φ x)

   a (refl _) x = refl _

   b : happly f g (hunapply h) ＝ h
   b = inverses-are-sections (happly f g) (hfe f g) h

   i  = a (hunapply h) x
   ii = ap (λ - → transport (R x) (- x) (φ x)) b

 unique-choice : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )

               → ((x : X) → ∃! a ꞉ A x , R x a)
               → ∃! f ꞉ ((x : X) → A x), ((x : X) → R x (f x))

 unique-choice X A R s = C , Φ
  where
   f₀ : (x : X) → A x
   f₀ x = pr₁ (center (Σ a ꞉ A x , R x a) (s x))

   φ₀ : (x : X) → R x (f₀ x)
   φ₀ x = pr₂ (center (Σ a ꞉ A x , R x a) (s x))

   C : Σ f ꞉ ((x : X) → A x), ((x : X) → R x (f x))
   C = f₀ , φ₀

   c : (x : X) → (τ : Σ a ꞉ A x , R x a) → f₀ x , φ₀ x ＝ τ
   c x = centrality (Σ a ꞉ A x , R x a) (s x)

   c₁ : (x : X) (a : A x) (r : R x a) → f₀ x ＝ a
   c₁ x a r = ap pr₁ (c x (a , r))

   c₂ : (x : X) (a : A x) (r : R x a)
      → transport (λ - → R x (pr₁ -)) (c x (a , r)) (φ₀ x) ＝ r

   c₂ x a r = apd pr₂ (c x (a , r))

   Φ : (σ : Σ f ꞉ ((x : X) → A x), ((x : X) → R x (f x))) → C ＝ σ
   Φ (f , φ) = to-Σ-＝ (p , hunapply q)
    where
     p : f₀ ＝ f
     p = hunapply (λ x → c₁ x (f x) (φ x))

     q : transport (λ - → (x : X) → R x (- x)) p φ₀ ∼ φ
     q x = transport (λ - → (x : X) → R x (- x)) p φ₀ x           ＝⟨ i   ⟩
           transport (R x) (ap pr₁ (c x (f x , φ x))) (φ₀ x)      ＝⟨ ii  ⟩
           transport (λ σ → R x (pr₁ σ)) (c x (f x , φ x)) (φ₀ x) ＝⟨ iii ⟩
           φ x                                                    ∎
      where
       i   = transport-hunapply A R f₀ f φ₀ (λ x → c₁ x (f x) (φ x)) x
       ii  = (transport-ap (R x) pr₁ (c x (f x , φ x)) (φ₀ x))⁻¹
       iii = c₂ x (f x) (φ x)

module choice
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

  open basic-truncation-development pt hfe public

  simple-unique-choice' : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )

                        → ((x : X) → is-subsingleton (Σ a ꞉ A x , R x a))

                        → ((x : X) → ∃ a ꞉ A x , R x a)
                        → Σ f ꞉ Π A , ((x : X) → R x (f x))

  simple-unique-choice' X A R u φ = simple-unique-choice X A R s
   where
    s : (x : X) → ∃! a ꞉ A x , R x a
    s x = inhabited-subsingletons-are-singletons (Σ a ꞉ A x , R x a) (φ x) (u x)

  AC : ∀ 𝓣 (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
     → is-set X → ((x : X) → is-set (A x)) → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇

  AC 𝓣 X A i j = (R : (x : X) → A x → 𝓣 ̇ )
               → ((x : X) (a : A x) → is-subsingleton (R x a))

               → ((x : X) → ∃ a ꞉ A x , R x a)
               → ∃ f ꞉ Π A , ((x : X) → R x (f x))

  Choice : ∀ 𝓤 → 𝓤 ⁺ ̇
  Choice 𝓤
   = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) (i : is-set X) (j : (x : X) → is-set (A x))
   → AC 𝓤 X A i j

  IAC
   : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → is-set X → ((x : X) → is-set (Y x)) → 𝓤 ⊔ 𝓥 ̇
  IAC X Y i j = ((x : X) → ∥ Y x ∥) → ∥ Π Y ∥

  IChoice : ∀ 𝓤 → 𝓤 ⁺ ̇
  IChoice 𝓤
   = (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) (i : is-set X) (j : (x : X) → is-set (Y x))
   → IAC X Y i j

  Choice-gives-IChoice : Choice 𝓤 → IChoice 𝓤
  Choice-gives-IChoice {𝓤} ac X Y i j φ = γ
   where
    R : (x : X) → Y x → 𝓤 ̇
    R x y = x ＝ x -- Any singleton type in 𝓤 will do.

    k : (x : X) (y : Y x) → is-subsingleton (R x y)
    k x y = i x x

    h : (x : X) → Y x → Σ y ꞉ Y x , R x y
    h x y = (y , refl x)

    g : (x : X) → ∃ y ꞉ Y x , R x y
    g x = ∥∥-functor (h x) (φ x)

    c : ∃ f ꞉ Π Y , ((x : X) → R x (f x))
    c = ac X Y i j R k g

    γ : ∥ Π Y ∥
    γ = ∥∥-functor pr₁ c

  IChoice-gives-Choice : IChoice 𝓤 → Choice 𝓤
  IChoice-gives-Choice {𝓤} iac X A i j R k ψ = γ
   where
    Y : X → 𝓤 ̇
    Y x = Σ a ꞉ A x , R x a

    l : (x : X) → is-set (Y x)
    l x = subsets-of-sets-are-sets (A x) (R x) (j x) (k x)

    a : ∥ Π Y ∥
    a = iac X Y i l ψ

    h : Π Y → Σ f ꞉ Π A , ((x : X) → R x (f x))
    h g = (λ x → pr₁ (g x)) , (λ x → pr₂ (g x))

    γ : ∃ f ꞉ Π A , ((x : X) → R x (f x))
    γ = ∥∥-functor h a

  TAC
   : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → is-set X → ((x : X) → is-set (A x)) → 𝓤 ⊔ 𝓥 ̇
  TAC X A i j = ∥((x : X) → ∥ A x ∥ → A x)∥

  TChoice : ∀ 𝓤 → 𝓤 ⁺ ̇
  TChoice 𝓤
   = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) (i : is-set X) (j : (x : X) → is-set (A x))
   → TAC X A i j

  IChoice-gives-TChoice : IChoice 𝓤 → TChoice 𝓤
  IChoice-gives-TChoice {𝓤} iac X A i j = γ
   where
    B : (x : X) → ∥ A x ∥ → 𝓤 ̇
    B x s = A x

    k : (x : X) (s : ∥ A x ∥) → is-set (B x s)
    k x s = j x

    l : (x : X) → is-set ∥ A x ∥
    l x = subsingletons-are-sets ∥ A x ∥ ∥∥-is-subsingleton

    m : (x : X) →  is-set (∥ A x ∥ → A x)
    m x = Π-is-set hfe (λ s → j x)

    φ : (x : X) → ∥ (∥ A x ∥ → A x) ∥
    φ x = iac ∥ A x ∥ (B x) (l x) (k x) (𝑖𝑑 ∥ A x ∥)

    γ : ∥((x : X) → ∥ A x ∥ → A x)∥
    γ = iac X (λ x → ∥ A x ∥ → A x) i m φ

  TChoice-gives-IChoice : TChoice 𝓤 → IChoice 𝓤
  TChoice-gives-IChoice tac X A i j = γ
   where
    γ : ((x : X) → ∥ A x ∥) → ∥ Π A ∥
    γ g = ∥∥-functor φ (tac X A i j)
     where
      φ : ((x : X) → ∥ A x ∥ → A x) → Π A
      φ f x = f x (g x)

  decidable-equality-criterion : {X : 𝓤 ̇ } (α : 𝟚 → X)
                               → ((x : X) → (∃ n ꞉ 𝟚 , α n ＝ x)
                                          → (Σ n ꞉ 𝟚 , α n ＝ x))
                               → decidable (α ₀ ＝ α ₁)

  decidable-equality-criterion α c = γ d
   where
    r : 𝟚 → image α
    r = corestriction α

    σ : (y : image α) → Σ n ꞉ 𝟚 , r n ＝ y
    σ (x , t) = f u
     where
      u : Σ n ꞉ 𝟚 , α n ＝ x
      u = c x t

      f : (Σ n ꞉ 𝟚 , α n ＝ x) → Σ n ꞉ 𝟚 , r n ＝ (x , t)
      f (n , p) = n , to-subtype-＝ (λ _ → ∃-is-subsingleton) p

    s : image α → 𝟚
    s y = pr₁ (σ y)

    η : (y : image α) → r (s y) ＝ y
    η y = pr₂ (σ y)

    l : left-cancellable s
    l = sections-are-lc s (r , η)

    αr : {m n : 𝟚} → α m ＝ α n → r m ＝ r n
    αr p = to-subtype-＝ (λ _ → ∃-is-subsingleton) p

    rα : {m n : 𝟚} → r m ＝ r n → α m ＝ α n
    rα = ap pr₁

    αs : {m n : 𝟚} → α m ＝ α n → s (r m) ＝ s (r n)
    αs p = ap s (αr p)

    sα : {m n : 𝟚} → s (r m) ＝ s (r n) → α m ＝ α n
    sα p = rα (l p)

    γ : decidable (s (r ₀) ＝ s (r ₁)) → decidable(α ₀ ＝ α ₁)
    γ (inl p) = inl (sα p)
    γ (inr u) = inr (contrapositive αs u)

    d : decidable (s (r ₀) ＝ s (r ₁))
    d = 𝟚-has-decidable-equality (s (r ₀)) (s (r ₁))

  choice-gives-decidable-equality
   : TChoice 𝓤
   → (X : 𝓤 ̇ ) → is-set X → has-decidable-equality X

  choice-gives-decidable-equality {𝓤} tac X i x₀ x₁ = γ
   where
    α : 𝟚 → X
    α ₀ = x₀
    α ₁ = x₁

    A : X → 𝓤 ̇
    A x = Σ n ꞉ 𝟚 , α n ＝ x

    l : is-subsingleton (decidable (x₀ ＝ x₁))
    l = +-is-subsingleton' hunapply (i (α ₀) (α ₁))

    δ : ∥((x : X) → ∥ A x ∥ → A x)∥ → decidable(x₀ ＝ x₁)
    δ = ∥∥-recursion l (decidable-equality-criterion α)

    j : (x : X) → is-set (A x)
    j x = subsets-of-sets-are-sets 𝟚 (λ n → α n ＝ x) 𝟚-is-set (λ n → i (α n) x)

    h : ∥((x : X) → ∥ A x ∥ → A x)∥
    h = tac X A i j

    γ : decidable (x₀ ＝ x₁)
    γ = δ h

  choice-gives-EM : propext 𝓤 → TChoice (𝓤 ⁺) → EM 𝓤
  choice-gives-EM {𝓤} pe tac = em
   where
    ⊤ : Ω 𝓤
    ⊤ = (Lift 𝓤 𝟙 , equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton)

    δ : (ω : Ω 𝓤) → decidable (⊤ ＝ ω)
    δ = choice-gives-decidable-equality tac (Ω 𝓤) (Ω-is-a-set hunapply pe) ⊤

    em : (P : 𝓤 ̇ ) → is-subsingleton P → P + ¬ P
    em P i = γ (δ (P , i))
     where
      γ : decidable (⊤ ＝ (P , i)) → P + ¬ P

      γ (inl r) = inl (Id→fun s (lift ⋆))
       where
        s : Lift 𝓤 𝟙 ＝ P
        s = ap pr₁ r

      γ (inr n) = inr (contrapositive f n)
       where
        f : P → ⊤ ＝ P , i
        f p = Ω-ext hunapply pe (λ (_ : Lift 𝓤 𝟙) → p) (λ (_ : P) → lift ⋆)

  global-choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
  global-choice 𝓤 = (X : 𝓤 ̇ ) → X + is-empty X

  global-∥∥-choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
  global-∥∥-choice 𝓤 = (X : 𝓤 ̇ ) → ∥ X ∥ → X

  open exit-∥∥ pt hfe

  global-choice-gives-wconstant : global-choice 𝓤
                                → (X : 𝓤 ̇ ) → wconstant-endomap X

  global-choice-gives-wconstant g X = decidable-has-wconstant-endomap (g X)

  global-choice-gives-global-∥∥-choice : global-choice  𝓤
                                       → global-∥∥-choice 𝓤

  global-choice-gives-global-∥∥-choice {𝓤} c X = γ (c X)
   where
    γ : X + is-empty X → ∥ X ∥ → X
    γ (inl x) s = x
    γ (inr n) s = !𝟘 X (∥∥-recursion 𝟘-is-subsingleton n s)

  global-∥∥-choice-gives-all-types-are-sets : global-∥∥-choice 𝓤
                                            → (X : 𝓤 ̇ ) → is-set X

  global-∥∥-choice-gives-all-types-are-sets {𝓤} c X =
    types-with-wconstant-＝-endomaps-are-sets X
        (λ x y → ∥∥-choice-function-gives-wconstant-endomap (c (x ＝ y)))

  global-∥∥-choice-gives-universe-is-set : global-∥∥-choice (𝓤 ⁺)
                                         → is-set (𝓤 ̇ )

  global-∥∥-choice-gives-universe-is-set {𝓤} c =
    global-∥∥-choice-gives-all-types-are-sets c (𝓤 ̇ )

  global-∥∥-choice-gives-choice : global-∥∥-choice 𝓤
                                → TChoice 𝓤

  global-∥∥-choice-gives-choice {𝓤} c X A i j = ∣(λ x → c (A x))∣

  global-∥∥-choice-gives-EM : propext 𝓤
                            → global-∥∥-choice (𝓤 ⁺)
                            → EM  𝓤

  global-∥∥-choice-gives-EM {𝓤} pe c =
    choice-gives-EM pe (global-∥∥-choice-gives-choice c)

  global-∥∥-choice-gives-global-choice : propext 𝓤
                                       → global-∥∥-choice 𝓤
                                       → global-∥∥-choice (𝓤 ⁺)
                                       → global-choice 𝓤

  global-∥∥-choice-gives-global-choice {𝓤} pe c c⁺ X = γ
   where
    d : decidable ∥ X ∥
    d = global-∥∥-choice-gives-EM pe c⁺ ∥ X ∥ ∥∥-is-subsingleton

    f : decidable ∥ X ∥ → X + is-empty X
    f (inl i) = inl (c X i)
    f (inr φ) = inr (contrapositive ∣_∣ φ)

    γ : X + is-empty X
    γ = f d

  Global-Choice Global-∥∥-Choice : 𝓤ω
  Global-Choice    = ∀ 𝓤 → global-choice  𝓤
  Global-∥∥-Choice = ∀ 𝓤 → global-∥∥-choice 𝓤

  Global-Choice-gives-Global-∥∥-Choice : Global-Choice → Global-∥∥-Choice
  Global-Choice-gives-Global-∥∥-Choice c 𝓤 =
    global-choice-gives-global-∥∥-choice (c 𝓤)

  Global-∥∥-Choice-gives-Global-Choice : global-propext
                                       → Global-∥∥-Choice → Global-Choice

  Global-∥∥-Choice-gives-Global-Choice pe c 𝓤 =
    global-∥∥-choice-gives-global-choice pe (c 𝓤) (c (𝓤 ⁺))

  global-∥∥-choice-inconsistent-with-univalence : Global-∥∥-Choice
                                                → Univalence
                                                → 𝟘

  global-∥∥-choice-inconsistent-with-univalence g ua = γ (g 𝓤₁) (ua 𝓤₀)
   where
    open example-of-a-nonset

    γ : global-∥∥-choice 𝓤₁ → is-univalent 𝓤₀ → 𝟘
    γ g ua = 𝓤₀-is-not-a-set ua (global-∥∥-choice-gives-universe-is-set g)

  global-choice-inconsistent-with-univalence : Global-Choice
                                             → Univalence
                                             → 𝟘

  global-choice-inconsistent-with-univalence g =
    global-∥∥-choice-inconsistent-with-univalence
      (Global-Choice-gives-Global-∥∥-Choice g)

  global-choice-gives-all-types-are-sets : global-choice 𝓤
                                         → (X : 𝓤 ̇ ) → is-set X

  global-choice-gives-all-types-are-sets {𝓤} c X = hedberg (λ x y → c (x ＝ y))

\end{code}
