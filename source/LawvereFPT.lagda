Martin Escardo, 5th September 2018.

On Lawvere's Fixed Point Theorem (LFPT).

 * http://tac.mta.ca/tac/reprints/articles/15/tr15abs.html
 * https://ncatlab.org/nlab/show/Lawvere%27s+fixed+point+theorem
 * http://arxiv.org/abs/math/0305282

We give an application to Cantor's theorem for the universe.

We begin with split surjections, or retractions, because they can be
formulated in MLTT, and then move to surjections, which need further
extensions of MLTT, or hypotheses, such as propositional truncation.

Many other things have been added since the above abstract was
written.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module LawvereFPT where

open import SpartanMLTT

\end{code}

The following pointwise weakening of split surjection is sufficient to
prove LFPT and allows us to avoid function extensionality in its
applications:

\begin{code}


open import Two-Properties
open import NaturalNumbers-Properties
open import UF-Retracts
open import UF-Equiv
open import UF-Miscelanea
open import UF-FunExt

module retract-version where

\end{code}

We will use the decoration "·" for pointwise versions of notions and
constructions (for example, we can read "has-section· r" as saying
that r has a pointwise section).

\begin{code}

 has-section· : {A : 𝓤 ̇ } {X : 𝓥 ̇ } → (A → (A → X)) → 𝓤 ⊔ 𝓥 ̇
 has-section· r = Σ s ꞉ (codomain r → domain r) , ∀ g a → r (s g) a ≡ g a

 section-gives-section· : {A : 𝓤 ̇ } {X : 𝓥 ̇ } (r : A → (A → X))
                        → has-section r → has-section· r
 section-gives-section· r (s , rs) = s , λ g a → ap (λ - → - a) (rs g)

 section·-gives-section : {A : 𝓤 ̇ } {X : 𝓥 ̇ } (r : A → (A → X))
                        → funext 𝓤 𝓥
                        → has-section· r → has-section r
 section·-gives-section r fe (s , rs·) = s , λ g → dfunext fe (rs· g)

 LFPT· : {A : 𝓤 ̇ } {X : 𝓥 ̇ } (r : A → (A → X))
       → has-section· r
       → (f : X → X) → Σ x ꞉ X , x ≡ f x
 LFPT· {𝓤} {𝓥} {A} {X} r (s , rs) f = x , p
  where
   g : A → X
   g a = f (r a a)
   a : A
   a = s g
   x : X
   x = r a a
   p : x ≡ f x
   p = x         ≡⟨ refl ⟩
       r (s g) a ≡⟨ rs g a ⟩
       g a       ≡⟨ refl ⟩
       f x       ∎

 LFPT : {A : 𝓤 ̇ } {X : 𝓥 ̇ }
      → retract (A → X) of A
      → (f : X → X) → Σ x ꞉ X , x ≡ f x
 LFPT (r , h) = LFPT· r (section-gives-section· r h)

 LFPT-≃ : {A : 𝓤 ⊔ 𝓥 ̇ } {X : 𝓤 ̇ }
        → A ≃ (A → X)
        → (f : X → X) → Σ x ꞉ X , x ≡ f x
 LFPT-≃ p = LFPT (≃-gives-▷ p)

 LFPT-≡ : {A : 𝓤 ⊔ 𝓥 ̇ } {X : 𝓤 ̇ }
        → A ≡ (A → X)
        → (f : X → X) → Σ x ꞉ X , x ≡ f x
 LFPT-≡ p = LFPT (Id-retract-r p)

 \end{code}

As a simple application, it follows that negation doesn't have fixed points:

 \begin{code}

 ¬-no-fp : ¬ (Σ X ꞉ 𝓤 ̇ , X ≡ ¬ X)
 ¬-no-fp {𝓤} (X , p) = pr₁(γ id)
  where
   γ : (f : 𝟘 → 𝟘) → Σ x ꞉ 𝟘 , x ≡ f x
   γ = LFPT-≡ p

 \end{code}

 We apply LFPT twice to get the following: first every function
 𝓤 ̇ → 𝓤 ̇ has a fixed point, from which for any type X we get a type B
 with B ≡ (B → X), and hence with (B → X) a retract of B, for which we
 apply LFPT again to get that every X → X has a fixed point.

 \begin{code}

 cantor-theorem-for-universes :
     (𝓤 𝓥 : Universe) (A : 𝓥 ̇ ) (r : A → (A → 𝓤 ̇ ))
   → has-section· r
   → (X : 𝓤 ̇ ) (f : X → X) → Σ x ꞉ X , x ≡ f x
 cantor-theorem-for-universes 𝓤 𝓥 A r h X = LFPT-≡ {𝓤} {𝓤} p
  where
   B : 𝓤 ̇
   B = pr₁(LFPT· r h (λ B → B → X))
   p : B ≡ (B → X)
   p = pr₂(LFPT· r h (λ B → B → X))

 \end{code}

 Taking X to be 𝟘 we get a contradiction, i.e. an inhabitant of the
 empty type 𝟘 (in fact, we get an inhabitant of any type by considering
 the identity function):

 \begin{code}

 Cantor-theorem-for-universes :
     (𝓤 𝓥 : Universe) (A : 𝓥 ̇ )
   → (r : A → (A → 𝓤 ̇ )) → ¬ has-section· r
 Cantor-theorem-for-universes 𝓤 𝓥 A r h = 𝟘-elim(pr₁ (cantor-theorem-for-universes 𝓤 𝓥 A r h 𝟘 id))

 \end{code}

 The original version of Cantor's theorem was for powersets, which
 here are types of maps into the subtype classifier Ω 𝓤 of the universe 𝓤.

 Function extensionality is needed in order to define negation
 Ω 𝓤 → Ω 𝓤, to show that P → 𝟘 is a proposition.

 \begin{code}

 open import UF-Subsingletons
 open import UF-Subsingletons-FunExt

 not-no-fp : (fe : funext 𝓤 𝓤₀) → ¬ (Σ P ꞉ Ω 𝓤 , P ≡ not fe P)
 not-no-fp {𝓤} fe (P , p) = ¬-no-fp (P holds , q)
  where
   q : P holds ≡ ¬(P holds)
   q = ap _holds p

 cantor-theorem : (𝓤 𝓥 : Universe) (A : 𝓥 ̇ )
                → funext 𝓤 𝓤₀ → (r : A → (A → Ω 𝓤)) → ¬ has-section· r
 cantor-theorem 𝓤 𝓥 A fe r (s , rs) = not-no-fp fe not-fp
  where
   not-fp : Σ B ꞉ Ω 𝓤 , B ≡ not fe B
   not-fp = LFPT· r (s , rs) (not fe)

\end{code}

The original LFPT has surjection, rather than retraction, as an
assumption. The retraction version can be formulated and proved in
pure MLTT. To formulate the original version we consider MLTT extended
with propositional truncation, or rather just MLTT with propositional
truncation as an assumption, given as a parameter for the following
module. This time a pointwise weakening of surjection is not enough.

\begin{code}

open import UF-PropTrunc
open import UF-ImageAndSurjection

module surjection-version (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

 LFPT : {A : 𝓤 ̇ } {X : 𝓥 ̇ } (φ : A → (A → X))
      → is-surjection φ
      → (f : X → X) → ∃ x ꞉ X , x ≡ f x
 LFPT {𝓤} {𝓥} {A} {X} φ s f = ∥∥-functor γ e
  where
   g : A → X
   g a = f (φ a a)
   e : ∃ a ꞉ A , φ a ≡ g
   e = s g
   γ : (Σ a ꞉ A , φ a ≡ g) → Σ x ꞉ X , x ≡ f x
   γ (a , q) = x , p
    where
     x : X
     x = φ a a
     p : x ≡ f x
     p = x         ≡⟨ refl ⟩
         φ a a     ≡⟨ ap (λ - → - a) q ⟩
         g a       ≡⟨ refl ⟩
         f x       ∎

\end{code}

 So in this version of LFPT we have a weaker hypothesis for the
 theorem, but we need a stronger language to formulate and prove it,
 or else an additional hypothesis of the existence of propositional
 truncations.

 For the following theorem, we use both the surjection version and the
 retraction version of LFPT.

\begin{code}

 cantor-theorem-for-universes :
     (𝓤 𝓥 : Universe) (A : 𝓥 ̇ ) (φ : A → (A → 𝓤 ̇ ))
   → is-surjection φ
   → (X : 𝓤 ̇ ) (f : X → X) → ∃ x ꞉ X , x ≡ f x
 cantor-theorem-for-universes 𝓤 𝓥 A φ s X f = ∥∥-functor g t
  where
   t : ∃ B ꞉ 𝓤 ̇  , B ≡ (B → X)
   t = LFPT φ s (λ B → B → X)
   g : (Σ B ꞉ 𝓤 ̇ , B ≡ (B → X)) → Σ x ꞉ X , x ≡ f x
   g (B , p) = retract-version.LFPT-≡ {𝓤} {𝓤} p f

 Cantor-theorem-for-universes :
     (𝓤 𝓥 : Universe) (A : 𝓥 ̇ )
   → (φ : A → (A → 𝓤 ̇ )) → ¬ is-surjection φ
 Cantor-theorem-for-universes 𝓤 𝓥 A r h = 𝟘-elim(∥∥-rec 𝟘-is-prop pr₁ c)
  where
   c : ∃ x ꞉ 𝟘 , x ≡ x
   c = cantor-theorem-for-universes 𝓤 𝓥 A r h 𝟘 id

 cantor-theorem :
     (𝓤 𝓥 : Universe) (A : 𝓥 ̇ )
   → funext 𝓤 𝓤₀ → (φ : A → (A → Ω 𝓤)) → ¬ is-surjection φ
 cantor-theorem 𝓤 𝓥 A fe φ s = ∥∥-rec 𝟘-is-prop (retract-version.not-no-fp fe) t
  where
   t : ∃ B ꞉ Ω 𝓤 , B ≡ not fe B
   t = LFPT φ s (not fe)

 \end{code}

 Another corollary is that the Cantor type (ℕ → 𝟚) and the Baire type
 (ℕ → ℕ) are uncountable:

 \begin{code}

 open import Two

 cantor-uncountable : ¬(Σ φ ꞉ (ℕ → (ℕ → 𝟚)), is-surjection φ)
 cantor-uncountable (φ , s) = ∥∥-rec 𝟘-is-prop (uncurry complement-no-fp) t
  where
   t : ∃ n ꞉ 𝟚 , n ≡ complement n
   t = LFPT φ s complement

 baire-uncountable : ¬(Σ φ ꞉ (ℕ → (ℕ → ℕ)), is-surjection φ)
 baire-uncountable (φ , s) = ∥∥-rec 𝟘-is-prop (uncurry succ-no-fp) t
  where
   t : ∃ n ꞉ ℕ , n ≡ succ n
   t = LFPT φ s succ

\end{code}

The following proofs are originally due to Ingo Blechschmidt during
the Autumn School "Proof and Computation", Fischbachau, 2018, after I
posed the problem of showing that the universe is uncountable to
him. This version is an adaptation jointly developed by the two of us
to use LFTP, also extended to replace "discrete" by "set" at the cost
of "jumping" a universe.

\begin{code}

module Blechschmidt (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open ImageAndSurjection pt
 open import DiscreteAndSeparated

 Π-projection-has-section :
    {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (x₀ : X)
  → is-isolated x₀
  → Π Y
  → has-section (λ (f : Π Y) → f x₀)
 Π-projection-has-section {𝓤} {𝓥} {X} {Y} x₀ i g = s , rs
  where
   s : Y x₀ → Π Y
   s y x = Cases (i x)
            (λ (p : x₀ ≡ x) → transport Y p y)
            (λ (_ : x₀ ≢ x) → g x)
   rs : (y : Y x₀) → s y x₀ ≡ y
   rs y = ap (λ - → Cases - _ _) a
    where
     a : i x₀ ≡ inl refl
     a = isolated-inl x₀ i x₀ refl

 udr-lemma : {A : 𝓤 ̇ } (X : A → 𝓥 ̇ ) (B : 𝓦 ̇ )
             (a₀ : A)
           → is-isolated a₀
           → B
           → retract ((a : A) → X a → B) of X a₀
           → (f : B → B) → Σ b ꞉ B , b ≡ f b
 udr-lemma X B a₀ i b ρ = retract-version.LFPT ρ'
  where
   ρ' : retract (X a₀ → B) of X a₀
   ρ' = retracts-compose ρ ((λ f → f a₀) , Π-projection-has-section a₀ i (λ a x → b))

 universe-discretely-regular' :
    (𝓤 𝓥 : Universe) (A : 𝓤 ̇ ) (X : A → 𝓤 ⊔ 𝓥 ̇ )
  → is-discrete A → Σ B ꞉ 𝓤 ⊔ 𝓥 ̇ , ((a : A) → ¬(X a ≃ B))
 universe-discretely-regular' 𝓤 𝓥 A X d  = B , φ
   where
    B : 𝓤 ⊔ 𝓥 ̇
    B = (a : A) → X a → 𝟚
    φ : (a : A) → ¬(X a ≃ B)
    φ a p = uncurry complement-no-fp (γ complement)
     where
      ρ : retract B of (X a)
      ρ = ≃-gives-▷ p
      γ : (f : 𝟚 → 𝟚) → Σ b ꞉ 𝟚 , b ≡ f b
      γ = udr-lemma X 𝟚 a (d a) ₀ ρ

 universe-discretely-regular :
    {𝓤 𝓥 : Universe} {A : 𝓤 ̇ } (X : A → 𝓤 ⊔ 𝓥 ̇ )
  → is-discrete A → Σ B ꞉ 𝓤 ⊔ 𝓥 ̇ , ((a : A) → X a ≢ B)
 universe-discretely-regular {𝓤} {𝓥} {A} X d =
   γ (universe-discretely-regular' 𝓤 𝓥 A X d)
  where
   γ : (Σ B ꞉ 𝓤 ⊔ 𝓥 ̇ , ((a : A) → ¬(X a ≃ B)))
     → (Σ B ꞉ 𝓤 ⊔ 𝓥 ̇ , ((a : A) → X a ≢ B))
   γ (B , φ) = B , (λ a → contrapositive (idtoeq (X a) B) (φ a))

 Universe-discretely-regular : {𝓤 𝓥 : Universe} {A : 𝓤 ̇ } (X : A → 𝓤 ⊔ 𝓥 ̇ )
                             → is-discrete A → ¬ is-surjection X
 Universe-discretely-regular {𝓤} {𝓥} {A} X d s = ∥∥-rec 𝟘-is-prop n e
  where
   B : 𝓤 ⊔ 𝓥 ̇
   B = pr₁(universe-discretely-regular {𝓤} {𝓥} {A} X d)
   φ : ∀ a → X a ≢ B
   φ = pr₂(universe-discretely-regular {𝓤} {𝓥} {A} X d)
   e : ∃ a ꞉ A , X a ≡ B
   e = s B
   n : ¬(Σ a ꞉ A , X a ≡ B)
   n = uncurry φ

 Universe-uncountable : {𝓤 : Universe} → ¬(Σ X ꞉ (ℕ → 𝓤 ̇ ), is-surjection X)
 Universe-uncountable (X , s) = Universe-discretely-regular X ℕ-is-discrete s

\end{code}

A variation, replacing discreteness by set-hood, at the cost of
"jumping a universe level".

\begin{code}

module Blechschmidt' (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open ImageAndSurjection pt
 open import DiscreteAndSeparated

 Π-projection-has-section :
    {A : 𝓤 ̇ } {X : A → 𝓥 ̇ }
  → funext 𝓥 ((𝓤 ⊔ 𝓦)⁺) → funext (𝓤 ⊔ 𝓦) (𝓤 ⊔ 𝓦) → propext (𝓤 ⊔ 𝓦)
  → (a₀ : A) → is-h-isolated a₀ → has-section (λ (f : (a : A) → X a → Ω (𝓤 ⊔ 𝓦)) → f a₀)
 Π-projection-has-section {𝓤} {𝓥} {𝓦} {A} {X} fe fe' pe a₀ ish = s , rs
  where
   s : (X a₀ → Ω (𝓤 ⊔ 𝓦)) → ((a : A) → X a → Ω (𝓤 ⊔ 𝓦))
   s φ a x = (∃ p ꞉ a ≡ a₀ , φ (transport X p x) holds) , ∥∥-is-prop
   rs : (φ : X a₀ → Ω (𝓤 ⊔ 𝓦)) → s φ a₀ ≡ φ
   rs φ = dfunext fe γ
    where
     a : (x₀ : X a₀) → (∃ p ꞉ a₀ ≡ a₀ , φ (transport X p x₀) holds) → φ x₀ holds
     a x₀ = ∥∥-rec (holds-is-prop (φ x₀)) f
      where
       f : (Σ p ꞉ a₀ ≡ a₀ , φ (transport X p x₀) holds) → φ x₀ holds
       f (p , h) = transport _holds t h
        where
         r : p ≡ refl
         r = ish p refl
         t : φ (transport X p x₀) ≡ φ x₀
         t = ap (λ - → φ(transport X - x₀)) r
     b : (x₀ : X a₀) → φ x₀ holds → ∃ p ꞉ a₀ ≡ a₀ , φ (transport X p x₀) holds
     b x₀ h = ∣ refl , h ∣
     γ : (x₀ : X a₀) → (∃ p ꞉ a₀ ≡ a₀ , φ (transport X p x₀) holds) , ∥∥-is-prop ≡ φ x₀
     γ x₀ = to-Σ-≡ (pe ∥∥-is-prop (holds-is-prop (φ x₀)) (a x₀) (b x₀) ,
                     being-prop-is-prop fe' (holds-is-prop _) (holds-is-prop (φ x₀)))

 usr-lemma : {A : 𝓤 ̇ } (X : A → 𝓥 ̇ )
           → funext 𝓥 ((𝓤 ⊔ 𝓦)⁺) → funext (𝓤 ⊔ 𝓦) (𝓤 ⊔ 𝓦) → propext (𝓤 ⊔ 𝓦)
           → (a₀ : A)
           → is-h-isolated a₀
           → retract ((a : A) → X a → Ω (𝓤 ⊔ 𝓦)) of X a₀
           → (f : Ω (𝓤 ⊔ 𝓦) → Ω (𝓤 ⊔ 𝓦)) → Σ p ꞉ Ω (𝓤 ⊔ 𝓦), p ≡ f p
 usr-lemma {𝓤} {𝓥} {𝓦} {A} X fe fe' pe a₀ i ρ = retract-version.LFPT ρ'
  where
   ρ' : retract (X a₀ → Ω (𝓤 ⊔ 𝓦)) of X a₀
   ρ' = retracts-compose ρ ((λ f → f a₀) , Π-projection-has-section {𝓤} {𝓥} {𝓦} fe fe' pe a₀ i)
\end{code}

We now work with the following assumptions:

\begin{code}

 module _
   (𝓤 𝓥 : Universe)
   (fe' : funext (𝓤 ⁺ ⊔ 𝓥) (𝓤 ⁺))
   (fe  : funext 𝓤 𝓤)
   (fe₀ : funext 𝓤 𝓤₀)
   (pe  : propext 𝓤)
   (A   : 𝓤 ̇ )
   (X   : A → 𝓤 ⁺ ⊔ 𝓥 ̇ )
   (iss : is-set A)
   where

\end{code}

NB. If 𝓥 is 𝓤 or 𝓤', then X : A → 𝓤 ⁺ ̇.

\begin{code}

  universe-set-regular' : Σ B ꞉ 𝓤 ⁺ ⊔ 𝓥 ̇ , ((a : A) → ¬(X a ≃ B))
  universe-set-regular' = B , φ
    where
     B : 𝓤 ⁺ ⊔ 𝓥 ̇
     B = (a : A) → X a → Ω 𝓤
     φ : (a : A) → ¬(X a ≃ B)
     φ a p = retract-version.not-no-fp fe₀ (γ (not fe₀))
      where
       ρ : retract B of (X a)
       ρ = ≃-gives-▷ p
       γ : (f : Ω 𝓤 → Ω 𝓤) → Σ p ꞉ Ω 𝓤 , p ≡ f p
       γ = usr-lemma {𝓤} {𝓥 ⊔ 𝓤 ⁺} {𝓤} {A} X fe' fe pe a iss ρ

  universe-set-regular : Σ B ꞉ 𝓤 ⁺ ⊔ 𝓥 ̇ , ((a : A) → X a ≢ B)
  universe-set-regular = γ universe-set-regular'
   where
    γ : (Σ B ꞉ 𝓤 ⁺ ⊔ 𝓥 ̇ , ((a : A) → ¬(X a ≃ B)))
      → (Σ B ꞉ 𝓤 ⁺ ⊔ 𝓥 ̇ , ((a : A) → X a ≢ B))
    γ (B , φ) = B , (λ a → contrapositive (idtoeq (X a) B) (φ a))

  Universe-set-regular : ¬ is-surjection X
  Universe-set-regular s = ∥∥-rec 𝟘-is-prop (uncurry φ) e
   where
    B : 𝓤 ⁺ ⊔ 𝓥 ̇
    B = pr₁ universe-set-regular
    φ : ∀ a → X a ≢ B
    φ = pr₂ universe-set-regular
    e : ∃ a ꞉ A , X a ≡ B
    e = s B

\end{code}

See also http://www.cs.bham.ac.uk/~mhe/agda-new/Type-in-Type-False.html

Added 12 October 2018. The paper

 Thierry Coquand, The paradox of trees in type theory
 BIT Numerical Mathematics, March 1992, Volume 32, Issue 1, pp 10–14
 https://pdfs.semanticscholar.org/f2f3/30b27f1d7ca99c2550f96581a4400c209ef8.pdf

shows that 𝓤 ̇ : 𝓤 ̇ (aka type-in-type) is inconsistent if 𝓤 is closed
under W types.

We adapt this method of proof to show that there is no type 𝕌 : 𝓤 ̇
with 𝓤 ̇ ≃ 𝕌, without assuming type-in-type.

The construction works in MLTT with empty type 𝟘, identity types, Σ
types, Π types, W types and a universe 𝓤 closed under them. In
particular, extensionality and univalence are not needed. We again use
Lawvere's fixed point theorem.

NB. It should also be possible to replace the diagonal construction of
Lemma₀ by a second application of LFPT (todo).

\begin{code}

module Coquand where

 Lemma₀ : (𝓤 : Universe)
          (A : 𝓤 ̇ )
          (T : A → 𝓤 ̇ )
          (S : 𝓤 ̇ → A)
          (ρ : {X : 𝓤 ̇ } → T (S X) → X)
          (σ : {X : 𝓤 ̇ } → X → T (S X))
          (η : {X : 𝓤 ̇ } (x : X) → ρ (σ x) ≡ x)
        → 𝟘
 Lemma₀ 𝓤 A T S ρ σ η = pr₁ (γ 𝟘 id )
  where
   data 𝕎 : 𝓤 ̇ where
    sup : {a : A} → (T a → 𝕎) → 𝕎

   α : 𝕎 → (𝕎 → 𝓤 ̇ )
   α (sup φ) = fiber φ

   module _ (X : 𝓤 ̇ ) where
    H : 𝕎 → 𝓤 ̇
    H w = α w w → X
    R : 𝕎
    R = sup {S (Σ H)} (pr₁ ∘ ρ)
    B : 𝓤 ̇
    B = α R R
    r : B → (B → X)
    r (t , p) = transport H p (pr₂ (ρ t))
    s : (B → X) → B
    s f = σ (R , f) , ap pr₁ (η (R , f))
    rs : (f : B → X) → r (s f) ≡ f
    rs f = r (s f)
                   ≡⟨ refl ⟩
           transport H (ap pr₁ (η (R , f))) (pr₂ (ρ (σ {Σ H} (R , f))))
                   ≡⟨ (transport-ap H pr₁ (η (R , f)))⁻¹ ⟩
           transport (H ∘ pr₁) (η (R , f)) (pr₂ (ρ (σ {Σ H} (R , f))))
                   ≡⟨ apd pr₂ (η (R , f)) ⟩
           pr₂ ((R , f) ∶ Σ H)
                   ≡⟨ refl ⟩
           f       ∎
    γ : (f : X → X) → Σ x ꞉ X , x ≡ f x
    γ = retract-version.LFPT (r , s , rs)

\end{code}

This can be rephrased as follows, where the use of 𝟘-elim is to
coerce the empty type in the universe 𝓤 to the empty type in the
universe 𝓤₀, which is where our negations take values:

\begin{code}

 Lemma₁ : ∀ 𝓤 (A : 𝓤 ̇ ) (T : A → 𝓤 ̇ ) (S : 𝓤 ̇ → A)
        → ¬((X : 𝓤 ̇ ) → retract X of (T (S X)))
 Lemma₁ 𝓤 A T S ρ = 𝟘-elim (Lemma₀ 𝓤 A T S
                              (λ {X} → retraction (ρ X))
                              (λ {X} → section (ρ X))
                              (λ {X} → retract-condition (ρ X)))

\end{code}

Because equivalences are retractions, it follows that

\begin{code}

 Lemma₂ : ∀ 𝓤 (A : 𝓤 ̇ ) (T : A → 𝓤 ̇ ) (S : 𝓤 ̇ → A)
        → ¬((X : 𝓤 ̇ ) → T (S X) ≃ X)
 Lemma₂ 𝓤 A T S e = Lemma₁ 𝓤 A T S (λ X → ≃-gives-▷ (e X))

\end{code}

And because identitities are equivalences, it follows that

\begin{code}

 Lemma₃ : ∀ 𝓤 (A : 𝓤 ̇ ) (T : A → 𝓤 ̇ ) (S : 𝓤 ̇ → A)
        → ¬((X : 𝓤 ̇ ) → T (S X) ≡ X)
 Lemma₃ 𝓤 A T S p = Lemma₂ 𝓤 A T S (λ X → idtoeq (T (S X)) X (p X))

\end{code}

This means that a universe 𝓤 cannot be a retract of any type in 𝓤:

\begin{code}

 Lemma₄ : ∀ 𝓤 → ¬(Σ A ꞉ 𝓤 ̇ , retract 𝓤 ̇ of A)
 Lemma₄ 𝓤 (A , T , S , TS) = Lemma₃ 𝓤 A T S TS

 corollary : ∀ 𝓤 → ¬(retract 𝓤 ⁺ ̇ of (𝓤 ̇ ))
 corollary 𝓤 ρ = Lemma₄ (𝓤 ⁺) ((𝓤 ̇ ) , ρ)

\end{code}

Therefore, because equivalences are retractions, no universe 𝓤 can be
equivalent to a type in 𝓤:

\begin{code}

 Theorem : ∀ 𝓤 → ¬(Σ X ꞉ 𝓤 ̇ , 𝓤 ̇ ≃ X)
 Theorem 𝓤 (X , e) = Lemma₄ 𝓤 (X , ≃-gives-◁ e)

 Corollary : ∀ 𝓤 → ¬(𝓤 ⁺ ̇ ≃ 𝓤 ̇ )
 Corollary 𝓤 e = Theorem (𝓤 ⁺) ((𝓤 ̇ ), e)

\end{code}
