Martin Escardo

In univalent logic, as opposed to Curry-Howard logic, a proposition is
a prop or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

About (sub)singletons using function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-Subsingletons-FunExt where

open import SpartanMLTT

open import UF-Base
open import UF-Subsingletons renaming (⊤Ω to ⊤ ; ⊥Ω to ⊥)
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-LeftCancellable
open import UF-Retracts

Π-is-prop : funext 𝓤 𝓥
          → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          → ((x : X) → is-prop (A x))
          → is-prop (Π A)
Π-is-prop fe i f g = dfunext fe (λ x → i x (f x) (g x))

Π-is-prop' : funext 𝓤 𝓥
           → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
           → ((x : X) → is-prop (A x))
           → is-prop ({x : X} → A x)
Π-is-prop' fe {X} {A} i = retract-of-prop retr (Π-is-prop fe i)
 where
  retr : retract ({x : X} → A x) of Π A
  retr = (λ f {x} → f x) , (λ g x → g {x}) , (λ x → refl)

Π-is-singleton : funext 𝓤 𝓥
               → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
               → ((x : X) → is-singleton (A x))
               → is-singleton (Π A)
Π-is-singleton fe i = (λ x → pr₁ (i x)) , (λ f → dfunext fe (λ x → pr₂ (i x) (f x)))

being-prop-is-prop : {X : 𝓤 ̇ }
                   → funext 𝓤 𝓤
                   → is-prop (is-prop X)
being-prop-is-prop {𝓤} {X} fe f g = c₁
 where
  l : is-set X
  l = props-are-sets f

  c : (x y : X) → f x y ≡ g x y
  c x y = l (f x y) (g x y)

  c₀ : (x : X) → f x ≡ g x
  c₀ x = dfunext fe (c x)

  c₁ : f ≡ g
  c₁  = dfunext fe c₀

identifications-of-props-are-props : propext 𝓤
                                   → funext 𝓤 𝓤
                                   → (P : 𝓤 ̇ )
                                   → is-prop P
                                   → (X : 𝓤 ̇ )
                                   → is-prop (X ≡ P)
identifications-of-props-are-props {𝓤} pe fe P i = local-hedberg' P (λ X → g X ∘ f X , k X)
 where
  f : (X : 𝓤 ̇ ) → X ≡ P → is-prop X × (X ⇔ P)
  f X refl = i , (id , id)

  g : (X : 𝓤 ̇ ) → is-prop X × (X ⇔ P) → X ≡ P
  g X (l , φ , γ) = pe l i φ γ

  j : (X : 𝓤 ̇ ) → is-prop (is-prop X × (X ⇔ P))
  j X = ×-prop-criterion ((λ _ → being-prop-is-prop fe) ,
                          (λ l → ×-is-prop (Π-is-prop fe (λ x → i))
                                            (Π-is-prop fe (λ p → l))))

  k : (X : 𝓤 ̇ ) → wconstant (g X ∘ f X)
  k X p q = ap (g X) (j X (f X p) (f X q))

being-singleton-is-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-prop (is-singleton X)
being-singleton-is-prop fe {X} (x , φ) (y , γ) = to-Σ-≡ (φ y , dfunext fe λ z → iss {y} {z} _ _)
 where
  isp : is-prop X
  isp = singletons-are-props (y , γ)

  iss : is-set X
  iss = props-are-sets isp

∃!-is-prop : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) → is-prop (∃! A)
∃!-is-prop fe = being-singleton-is-prop fe

Π-is-set : funext 𝓤 𝓥
         → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → ((x : X) → is-set (A x))
         → is-set (Π A)
Π-is-set {𝓤} {𝓥} fe {X} {A} isa {f} {g} = b
 where
  a : is-prop (f ∼ g)
  a p q = dfunext fe λ x → isa x (p x) (q x)

  b : is-prop (f ≡ g)
  b = left-cancellable-reflects-is-prop happly (section-lc happly (pr₂ (fe f g))) a

\end{code}

The meat of the following proof is being-set-is-prop'. The rest of the
code is to deal with implicit arguments in conjunction with function
extensionality. The solution is not ideal. Ideally, functions with
implicit parameters should be the same as their versions with explicit
parameters.

\begin{code}

being-set-is-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-prop (is-set X)
being-set-is-prop {𝓤} fe {X} = h
 where
  is-set' : 𝓤 ̇ → 𝓤 ̇
  is-set' X = (x y : X) → is-prop (x ≡ y)

  being-set-is-prop' : {X : 𝓤 ̇ } → funext 𝓤 𝓤 → is-prop (is-set' X)
  being-set-is-prop' fe = Π-is-prop fe
                              (λ x → Π-is-prop fe
                              (λ y → being-prop-is-prop fe))

  f : {X : 𝓤 ̇ } → is-set' X → is-set X
  f s {x} {y} = s x y

  g : {X : 𝓤 ̇ } → is-set X → is-set' X
  g s x y = s {x} {y}

  h : is-prop (is-set X)
  h = subtype-of-prop-is-prop g (ap f) (being-set-is-prop' fe)

negations-are-props : {X : 𝓤 ̇ } → funext 𝓤 𝓤₀ → is-prop (¬ X)
negations-are-props fe = Π-is-prop fe (λ x → 𝟘-is-prop)

decidability-of-prop-is-prop : funext 𝓤 𝓤₀ → {P : 𝓤 ̇ } → is-prop P → is-prop (P + ¬ P)
decidability-of-prop-is-prop fe₀ i = sum-of-contradictory-props
                                      i
                                      (negations-are-props fe₀)
                                      (λ p u → u p)

Ω-extensionality : funext 𝓤 𝓤
                 → propext 𝓤
                 → {p q : Ω 𝓤}
                 → (p holds → q holds)
                 → (q holds → p holds)
                 → p ≡ q

Ω-extensionality {𝓤} fe pe {p} {q} f g =
 to-Σ-≡ (pe (holds-is-prop p) (holds-is-prop q) f g ,
         being-prop-is-prop fe _ _)

Ω-is-set : funext 𝓤 𝓤 → propext 𝓤 → is-set (Ω 𝓤)
Ω-is-set {𝓤} fe pe = Id-collapsibles-are-sets pc
 where
  A : (p q : Ω 𝓤) → 𝓤 ̇
  A p q = (p holds → q holds) × (q holds → p holds)

  A-is-prop : (p q : Ω 𝓤) → is-prop (A p q)
  A-is-prop p q = Σ-is-prop (Π-is-prop fe
                                   (λ _ → holds-is-prop q))
                                   (λ _ → Π-is-prop fe (λ _ → holds-is-prop p))

  g : (p q : Ω 𝓤) → p ≡ q → A p q
  g p q e = (b , c)
   where
    a : p holds ≡ q holds
    a = ap _holds e

    b : p holds → q holds
    b = transport id a

    c : q holds → p holds
    c = transport id (a ⁻¹)

  h  : (p q : Ω 𝓤) → A p q → p ≡ q
  h p q (u , v) = Ω-extensionality fe pe u v

  f  : (p q : Ω 𝓤) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)

  wconstant-f : (p q : Ω 𝓤) (d e : p ≡ q) → f p q d ≡ f p q e
  wconstant-f p q d e = ap (h p q) (A-is-prop p q (g p q d) (g p q e))

  pc : {p q : Ω 𝓤} → Σ f ꞉ (p ≡ q → p ≡ q) , wconstant f
  pc {p} {q} = (f p q , wconstant-f p q)

powersets-are-sets'' : funext 𝓤 (𝓥 ⁺)
                     → funext 𝓥 𝓥
                     → propext 𝓥
                     → {A : 𝓤 ̇ } → is-set (A → Ω 𝓥)
powersets-are-sets'' fe fe' pe = Π-is-set fe (λ x → Ω-is-set fe' pe)

powersets-are-sets : funext 𝓥 (𝓥 ⁺)
                   → propext 𝓥
                   → {A : 𝓥 ̇ } → is-set (A → Ω 𝓥)
powersets-are-sets {𝓥} fe = powersets-are-sets'' fe (lower-funext 𝓥 (𝓥 ⁺) fe)

empty-types-are-props : {X : 𝓤 ̇ } → ¬ X → is-prop X
empty-types-are-props f x = 𝟘-elim (f x)

equal-𝟘-is-empty : {X : 𝓤 ̇ } → X ≡ 𝟘 → ¬ X
equal-𝟘-is-empty e x = 𝟘-elim (transport id e x)

empty-types-are-≡-𝟘 : funext 𝓤 𝓤₀ → propext 𝓤 → {X : 𝓤 ̇ } → ¬ X → X ≡ 𝟘
empty-types-are-≡-𝟘 fe pe f = pe (empty-types-are-props f)
                                 𝟘-is-prop
                                 (λ x → 𝟘-elim (f x))
                                 𝟘-elim

not : funext 𝓤 𝓤₀ → Ω 𝓤 → Ω 𝓤
not fe (P , i) = (¬ P , negations-are-props fe)

equal-⊤-is-true : (P : 𝓤 ̇ ) (i : is-prop P) → (P , i) ≡ ⊤ → P
equal-⊤-is-true P hp r = f ⋆
 where
  s : 𝟙 ≡ P
  s = (ap pr₁ r)⁻¹

  f : 𝟙 → P
  f = transport id s

\end{code}

TODO. In the following, rather than using a P and i, use a p = (P , i) in Ω 𝓤.

\begin{code}

holds-gives-equal-𝟙 : propext 𝓤 → (P : 𝓤 ̇ ) → is-prop P → P → P ≡ 𝟙
holds-gives-equal-𝟙 pe P i p = pe i 𝟙-is-prop unique-to-𝟙 (λ _ → p)

true-is-equal-⊤ : propext 𝓤
                → funext 𝓤 𝓤
                → (P : 𝓤 ̇ ) (i : is-prop P)
                → P → (P , i) ≡ ⊤
true-is-equal-⊤ pe fe P i p = to-Σ-≡ (holds-gives-equal-𝟙 pe P i p ,
                                      being-prop-is-prop fe _ _)

holds-gives-equal-⊤ : propext 𝓤 → funext 𝓤 𝓤 → (p : Ω 𝓤) → p holds → p ≡ ⊤
holds-gives-equal-⊤ pe fe (P , i) = true-is-equal-⊤ pe fe P i

equal-𝟙-gives-holds : (P : 𝓤 ̇ ) → P ≡ 𝟙 → P
equal-𝟙-gives-holds P r = Idtofun (r ⁻¹) ⋆

equal-⊤-gives-holds : (p : Ω 𝓤) → p ≡ ⊤ → p holds
equal-⊤-gives-holds p r = equal-𝟙-gives-holds (p holds) (ap pr₁ r)

not-𝟘-is-𝟙 : funext 𝓤 𝓤₀
           → propext 𝓤
           → (¬ 𝟘) ≡ 𝟙
not-𝟘-is-𝟙 fe pe = pe (negations-are-props fe)
                      𝟙-is-prop
                      (λ _ → ⋆)
                      (λ _ z → 𝟘-elim z)

equal-⊥-gives-not-equal-⊤ : (fe : Fun-Ext)
                            (pe : propext 𝓤)
                            (p : Ω 𝓤)
                            → p ≡ ⊥ → not fe p ≡ ⊤
equal-⊥-gives-not-equal-⊤ fe pe p r = to-subtype-≡ (λ _ → being-prop-is-prop fe) t
 where
  s : p holds ≡ 𝟘
  s = ap _holds r

  t : ¬ (p holds) ≡ 𝟙
  t = ap ¬_ s ∙ not-𝟘-is-𝟙 fe pe

false-is-equal-⊥ : propext 𝓤
                 → funext 𝓤 𝓤
                 → (P : 𝓤 ̇ ) (i : is-prop P)
                 → ¬ P → (P , i) ≡ ⊥
false-is-equal-⊥ pe fe P i f = to-Σ-≡ (pe i 𝟘-is-prop (λ p → 𝟘-elim (f p)) 𝟘-elim ,
                                       being-prop-is-prop fe _ _)

not-equal-⊤-gives-equal-⊥ : (fe : Fun-Ext)
                            (pe : propext 𝓤)
                            (p : Ω 𝓤)
                          → not fe p ≡ ⊤ → p ≡ ⊥
not-equal-⊤-gives-equal-⊥ fe pe p r = to-subtype-≡ (λ _ → being-prop-is-prop fe) t
 where
  f : (not fe p) holds
  f = Idtofun (ap _holds r ⁻¹) ⋆

  t : p holds ≡ 𝟘
  t = empty-types-are-≡-𝟘 fe pe f

Ω-ext : propext 𝓤
       → funext 𝓤 𝓤
       → {p q : Ω 𝓤}
       → (p ≡ ⊤ → q ≡ ⊤)
       → (q ≡ ⊤ → p ≡ ⊤)
       → p ≡ q

Ω-ext pe fe {(P , i)} {(Q , j)} f g = to-Σ-≡ (pe i j I II ,
                                              being-prop-is-prop fe _ _ )
 where
  I : P → Q
  I x = equal-⊤-is-true Q j (f (true-is-equal-⊤ pe fe P i x))

  II : Q → P
  II y = equal-⊤-is-true P i (g (true-is-equal-⊤ pe fe Q j y))


Ω-discrete-gives-EM : funext 𝓤 𝓤
                    → propext 𝓤
                    → ((p q : Ω 𝓤) → decidable (p ≡ q))
                    → (P : 𝓤 ̇ ) → is-prop P → P + ¬ P
Ω-discrete-gives-EM {𝓤} fe pe δ P i = f (δ p q)
 where
  p q : Ω 𝓤
  p = (P , i)
  q = (𝟙 , 𝟙-is-prop)

  f : decidable (p ≡ q) → P + ¬ P
  f (inl e) = inl (equal-𝟙-gives-holds P (ap pr₁ e))
  f (inr ν) = inr (λ (x : P) → ν (to-subtype-≡
                                   (λ _ → being-prop-is-prop fe)
                                   (holds-gives-equal-𝟙 pe P i x)))

\end{code}

Without excluded middle, we have that:

\begin{code}

no-truth-values-other-than-⊥-or-⊤ : funext 𝓤 𝓤
                                  → propext 𝓤
                                  → ¬ (Σ p ꞉ Ω 𝓤 , (p ≢ ⊥) × (p ≢ ⊤))
no-truth-values-other-than-⊥-or-⊤ fe pe ((P , i) , (f , g)) = φ u
 where
  u : ¬ P
  u p = g l
    where
     l : (P , i) ≡ ⊤
     l = Ω-extensionality fe pe unique-to-𝟙 (λ _ → p)

  φ : ¬¬ P
  φ u = f l
    where
     l : (P , i) ≡ ⊥
     l = Ω-extensionality fe pe (λ p → 𝟘-elim (u p)) unique-from-𝟘

has-three-distinct-points : 𝓤 ̇ → 𝓤 ̇
has-three-distinct-points X = Σ (x , y , z) ꞉ X × X × X , (x ≢ y) × (y ≢ z) × (z ≢ x)

no-three-distinct-propositions : funext 𝓤 𝓤
                               → propext 𝓤
                               → ¬ has-three-distinct-points (Ω 𝓤)
no-three-distinct-propositions fe pe ((p , q , r) , u , v , w) = XI
 where
  I : p ≢ ⊥
  I a = no-truth-values-other-than-⊥-or-⊤ fe pe (q , II , III)
   where
    II : q ≢ ⊥
    II b = u (a ∙ b ⁻¹)

    III : q ≢ ⊤
    III c = no-truth-values-other-than-⊥-or-⊤ fe pe (r , IV , V)
     where
      IV : r ≢ ⊥
      IV d = w (d ∙ a ⁻¹)

      V : r ≢ ⊤
      V e = v (c ∙ e ⁻¹)

  VI : p ≢ ⊤
  VI a = no-truth-values-other-than-⊥-or-⊤ fe pe (q , VII , X)
   where
    VII : q ≢ ⊥
    VII b = no-truth-values-other-than-⊥-or-⊤ fe pe (r , VIII , IX)
     where
      VIII : r ≢ ⊥
      VIII c = v (b ∙ c ⁻¹)

      IX : r ≢ ⊤
      IX d = w (d ∙ a ⁻¹)

    X : q ≢ ⊤
    X e = u (a ∙ e ⁻¹)

  XI : 𝟘
  XI = no-truth-values-other-than-⊥-or-⊤ fe pe (p , I , VI)

\end{code}

(The above function was added 19th March 2021.)

The above implies that if Fin n is embedded in Ω 𝓤, then n ≤ 2. That
is, every finite subset of Ω has at most two elements. See the module
Fin.lagda.


In the above and in the following, 𝟘-elim is used to coerce from 𝟘 {𝓤}
to 𝟘 {𝓤₀} as this is where negations take values in.

\begin{code}

⊥-is-not-⊤ : ⊥ {𝓤} ≢ ⊤ {𝓤}
⊥-is-not-⊤ b = 𝟘-elim (𝟘-is-not-𝟙 (ap _holds b))

\end{code}

Sometimes it is convenient to work with the type of true propositions,
which is a singleton and hence a subsingleton. But we will leave this
type nameless:

\begin{code}

𝟙-is-true-props-center : funext 𝓤 𝓤
                       → propext 𝓤
                       → (σ : Σ P ꞉ 𝓤 ̇ , is-prop P × P) → (𝟙 , 𝟙-is-prop , ⋆) ≡ σ
𝟙-is-true-props-center fe pe = γ
 where
  φ : ∀ P → is-prop (is-prop P × P)
  φ P (i , p) = ×-is-prop (being-prop-is-prop fe) i (i , p)

  γ : ∀ σ → (𝟙 , 𝟙-is-prop , ⋆) ≡ σ
  γ (P , i , p) = to-subtype-≡ φ s
   where
    s : 𝟙 ≡ P
    s = pe 𝟙-is-prop i (λ _ → p) (λ _ → ⋆)

the-true-props-form-a-singleton-type : funext 𝓤 𝓤
                                     → propext 𝓤
                                     → is-singleton (Σ P ꞉ 𝓤 ̇ , is-prop P × P)
the-true-props-form-a-singleton-type fe pe = (𝟙 , 𝟙-is-prop , ⋆) , 𝟙-is-true-props-center fe pe


the-true-props-form-a-prop : funext 𝓤 𝓤
                           → propext 𝓤
                           → is-prop (Σ P ꞉ 𝓤 ̇ , is-prop P × P)
the-true-props-form-a-prop fe pe = singletons-are-props (the-true-props-form-a-singleton-type fe pe)

\end{code}

Added 16th June 2020. (Should have added this ages ago to avoid
boiler-plate code.)

\begin{code}

Π₂-is-prop : Fun-Ext
           → {X : 𝓤 ̇ }
             {Y : X → 𝓥 ̇ }
             {Z : (x : X) → Y x → 𝓦 ̇ }
           → ((x : X) (y : Y x) → is-prop (Z x y))
           → is-prop ((x : X) (y : Y x) → Z x y)
Π₂-is-prop fe i = Π-is-prop fe (λ x → Π-is-prop fe (i x))

Π₃-is-prop : Fun-Ext
           → {X : 𝓤 ̇ }
             {Y : X → 𝓥 ̇ }
             {Z : (x : X) → Y x → 𝓦 ̇ }
             {T : (x : X) (y : Y x) → Z x y → 𝓣 ̇ }
           → ((x : X) (y : Y x) (z : Z x y) → is-prop (T x y z))
           → is-prop ((x : X) (y : Y x) (z : Z x y) → T x y z)
Π₃-is-prop fe i = Π-is-prop fe (λ x → Π₂-is-prop fe (i x))

Π₄-is-prop : Fun-Ext
           → {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ : Universe}
             {A : 𝓤 ̇ }
             {B : A → 𝓥₀ ̇ }
             {C : (a : A) → B a → 𝓥₁ ̇ }
             {D : (a : A) (b : B a) → C a b → 𝓥₂ ̇ }
             {E : (a : A) (b : B a) (c : C a b) → D a b c → 𝓥₃ ̇ }
           → ((a : A) (b : B a) (c : C a b) (d : D a b c) → is-prop (E a b c d))
           → is-prop ((a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d)
Π₄-is-prop fe i = Π-is-prop fe (λ x → Π₃-is-prop fe (i x))

Π₅-is-prop : Fun-Ext
           → {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ : Universe}
             {A : 𝓤 ̇ }
             {B : A → 𝓥₀ ̇ }
             {C : (a : A) → B a → 𝓥₁ ̇ }
             {D : (a : A) (b : B a) → C a b → 𝓥₂ ̇ }
             {E : (a : A) (b : B a) (c : C a b) → D a b c → 𝓥₃ ̇ }
             {F : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d → 𝓥₄ ̇ }
           → ((a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) → is-prop (F a b c d e))
           → is-prop ((a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) → F a b c d e)
Π₅-is-prop fe i = Π-is-prop fe (λ x → Π₄-is-prop fe (i x))

\end{code}
