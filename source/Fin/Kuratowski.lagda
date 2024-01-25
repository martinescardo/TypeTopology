Martin Escardo, 8th April 2021.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module Fin.Kuratowski (pt : propositional-truncations-exist) where

open import Factorial.PlusOneLC
open import Fin.Bishop
open import Fin.Properties
open import Fin.Topology
open import Fin.Type
open import MLTT.Spartan
open import MLTT.Two-Properties
open import TypeTopology.CompactTypes
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence
open import UF.UniverseEmbedding

open CompactTypesPT pt
open PropositionalTruncation pt
open finiteness pt

is-Kuratowski-finite : 𝓤 ̇ → 𝓤 ̇
is-Kuratowski-finite X = ∃ n ꞉ ℕ , Fin n ↠ X

Kuratowski-data : 𝓤 ̇ → 𝓤 ̇
Kuratowski-data X = Σ n ꞉ ℕ , Fin n ↠ X

being-Kuratowski-finite-is-prop : {X : 𝓤 ̇ } → is-prop (is-Kuratowski-finite X)
being-Kuratowski-finite-is-prop = ∃-is-prop

Kuratowski-finite-types-are-∃-compact : Fun-Ext
                                      → {X : 𝓤 ̇ }
                                      → is-Kuratowski-finite X
                                      → is-∃-Compact X {𝓤}
Kuratowski-finite-types-are-∃-compact fe {X} i = γ
 where
  α : Kuratowski-data X → is-Compact X
  α (n , f , s) = surjection-Compact f fe s Fin-Compact

  β : ∥ is-Compact X ∥
  β = ∥∥-functor α i

  γ : is-∃-Compact X
  γ = ∥Compact∥-gives-∃-Compact fe β

finite-types-are-Kuratowski-finite : {X : 𝓤 ̇ }
                                   → is-finite X
                                   → is-Kuratowski-finite X
finite-types-are-Kuratowski-finite {𝓤} {X} X-is-finite = γ
 where
  δ : finite-linear-order X → is-Kuratowski-finite X
  δ (n , 𝕗) = ∣ n , (⌜ 𝕗 ⌝⁻¹ , equivs-are-surjections (⌜⌝⁻¹-is-equiv 𝕗)) ∣

  γ : is-Kuratowski-finite X
  γ = ∥∥-rec being-Kuratowski-finite-is-prop δ (finite-gives-finite' X X-is-finite)

\end{code}

Conversely, if a Kuratowski finite is discrete (that is, it has
decidable equality) then it is finite, because we can use the
decidable equality to remove repetitions, as observed by Tom de Jong
(and implemented by Martin Escardo):

\begin{code}

dkf-lemma : funext 𝓤 𝓤₀
          → {X : 𝓤 ̇ }
          → is-discrete X
          → Kuratowski-data X
          → finite-linear-order X
dkf-lemma {𝓤} fe {X} δ (n , 𝕗) = γ X δ n 𝕗
 where
  γ : (X : 𝓤 ̇ ) → is-discrete X → (n : ℕ) → (Fin n ↠ X) → finite-linear-order X
  γ X δ 0        (f , s) = 0 , empty-≃-𝟘 (λ x → ∥∥-rec 𝟘-is-prop pr₁ (s x))
  γ X δ (succ n) (f , s) = I Δ
   where
    A : Fin n → 𝓤 ̇
    A j = f (suc j) ＝ f 𝟎

    Δ : is-decidable (Σ A)
    Δ = Fin-Compact A (λ j → δ (f (suc j)) (f 𝟎))

    g : Fin n → X
    g i = f (suc i)

    I : is-decidable (Σ A) → finite-linear-order X
    I (inl (j , p)) = IH
     where
      II : (x : X) → (Σ i ꞉ Fin (succ n) , f i ＝ x) → (Σ i ꞉ Fin n , g i ＝ x)
      II x (𝟎 ,     q) = j , (p ∙ q)
      II x (suc i , q) = i , q

      III : is-surjection g
      III x = ∥∥-functor (II x) (s x)

      IH : finite-linear-order X
      IH = γ X δ n (g , III)

    I (inr ν) = succ n' , IX
     where
      X' = X ∖ f 𝟎

      δ' : is-discrete X'
      δ' = lc-maps-reflect-discreteness pr₁ (pr₁-lc (negations-are-props fe)) δ

      g' : Fin n → X'
      g' i = g i , (λ (p : f (suc i) ＝ f 𝟎) → ν (i , p))

      IV : is-surjection g'
      IV (x , u) = VII
       where
        V : ∃ i ꞉ Fin (succ n) , f i ＝ x
        V = s x

        VI : (Σ i ꞉ Fin (succ n) , f i ＝ x) → (Σ i ꞉ Fin n , g' i ＝ (x , u))
        VI (𝟎     , p) = 𝟘-elim (u (p ⁻¹))
        VI (suc i , p) = i , to-subtype-＝ (λ _ → negations-are-props fe) p

        VII : ∃ i ꞉ Fin n , g' i ＝ (x , u)
        VII = ∥∥-functor VI V

      IH : finite-linear-order X'
      IH = γ X' δ' n (g' , IV)

      n' : ℕ
      n' = pr₁ IH

      VIII : X' ≃ Fin n'
      VIII = pr₂ IH

      IX = X           ≃⟨ remove-and-add-isolated-point fe (f 𝟎) (δ (f 𝟎)) ⟩
          (X' + 𝟙)     ≃⟨ +-cong VIII (≃-refl 𝟙) ⟩
          (Fin n' + 𝟙) ■

Kuratowski-finite-discrete-types-are-finite : funext 𝓤 𝓤₀
                                            → {X : 𝓤 ̇ }
                                            → is-discrete X
                                            → is-Kuratowski-finite X
                                            → is-finite X
Kuratowski-finite-discrete-types-are-finite {𝓤} fe {X} δ κ =
 finite'-gives-finite X (∥∥-functor (dkf-lemma fe δ) κ)


surjections-preserve-K-finiteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                  → is-surjection f
                                  → is-Kuratowski-finite X
                                  → is-Kuratowski-finite Y
surjections-preserve-K-finiteness {𝓤} {𝓥} {X} {Y} f s i = j
 where
  γ : Kuratowski-data X → Kuratowski-data Y
  γ (n , g , t) = n , f ∘ g , ∘-is-surjection t s

  j : is-Kuratowski-finite Y
  j = ∥∥-functor γ i


total-K-finite-gives-index-type-K-finite' : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                                          → is-Kuratowski-finite (Σ A)
                                          → is-Kuratowski-finite (Σ x ꞉ X , ∥ A x ∥)
total-K-finite-gives-index-type-K-finite' X A i = γ
 where
  ζ : (x : X) → A x → ∥ A x ∥
  ζ x a = ∣ a ∣

  ζ-is-surjection : (x : X) → is-surjection (ζ x)
  ζ-is-surjection x = pt-is-surjection

  f : Σ A → Σ x ꞉ X , ∥ A x ∥
  f = NatΣ ζ

  f-is-surjection : is-surjection f
  f-is-surjection = NatΣ-is-surjection A (λ x → ∥ A x ∥) ζ ζ-is-surjection

  γ : is-Kuratowski-finite (Σ x ꞉ X , ∥ A x ∥)
  γ = surjections-preserve-K-finiteness f f-is-surjection i

total-K-finite-gives-index-type-K-finite : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                                         → is-Kuratowski-finite (Σ A)
                                         → ((x : X) → ∥ A x ∥)
                                         → is-Kuratowski-finite X
total-K-finite-gives-index-type-K-finite A i s =
 surjections-preserve-K-finiteness pr₁ (pr₁-is-surjection A s) i

\end{code}

The finiteness of all Kuratowski finite types gives the discreteness of
all sets (and hence excluded middle, because the type of truth values
is a set).

\begin{code}

doubleton : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
doubleton {𝓤} {X} x₀ x₁ = Σ x ꞉ X , (x ＝ x₀) ∨ (x ＝ x₁)

doubleton-is-set : {X : 𝓤 ̇ } (x₀ x₁ : X)
                 → is-set X
                 → is-set (doubleton x₀ x₁)
doubleton-is-set {𝓤} {X} x₀ x₁ i = subsets-of-sets-are-sets
                                     X (λ x → (x ＝ x₀) ∨ (x ＝ x₁)) i ∨-is-prop

doubleton-map : {X : 𝓤 ̇ } (x₀ x₁ : X) → Fin 2 → doubleton x₀ x₁
doubleton-map x₀ x₁ 𝟎 = x₀ , ∣ inl refl ∣
doubleton-map x₀ x₁ 𝟏 = x₁ , ∣ inr refl ∣

doubleton-map-is-surjection : {X : 𝓤 ̇ } {x₀ x₁ : X}
                            → is-surjection (doubleton-map x₀ x₁)
doubleton-map-is-surjection {𝓤} {X} {x₀} {x₁} (x , s) = ∥∥-functor γ s
 where
  γ : (x ＝ x₀) + (x ＝ x₁) → Σ n ꞉ Fin 2 , doubleton-map x₀ x₁ n ＝ (x , s)
  γ (inl p) = 𝟎 , to-subtype-＝ (λ _ → ∨-is-prop) (p ⁻¹)
  γ (inr q) = 𝟏 , to-subtype-＝ (λ _ → ∨-is-prop) (q ⁻¹)

doubletons-are-Kuratowki-finite : {X : 𝓤 ̇ } (x₀ x₁ : X)
                                → is-Kuratowski-finite (doubleton x₀ x₁)
doubletons-are-Kuratowki-finite x₀ x₁ = ∣ 2 , doubleton-map x₀ x₁ , doubleton-map-is-surjection ∣


decidable-equality-gives-doubleton-finite : {X : 𝓤 ̇ } (x₀ x₁ : X)
                                          → is-set X
                                          → is-decidable (x₀ ＝ x₁)
                                          → is-finite (doubleton x₀ x₁)
decidable-equality-gives-doubleton-finite x₀ x₁ X-is-set δ = γ δ
 where
  γ : is-decidable (x₀ ＝ x₁) → is-finite (doubleton x₀ x₁)
  γ (inl p) = 1 , ∣ singleton-≃ m l ∣
   where
    l : is-singleton (Fin 1)
    l = 𝟎 , c
     where
      c : is-central (Fin 1) 𝟎
      c 𝟎 = refl

    m : is-singleton (doubleton x₀ x₁)
    m = (doubleton-map x₀ x₁ 𝟎 , c)
     where
      c : is-central (doubleton x₀ x₁) (doubleton-map x₀ x₁ 𝟎)
      c (y , s) = to-subtype-＝ (λ _ → ∨-is-prop) (∥∥-rec X-is-set α s)
       where
        α : (y ＝ x₀) + (y ＝ x₁) → x₀ ＝ y
        α (inl q) = q ⁻¹
        α (inr q) = p ∙ q ⁻¹

  γ (inr ν) = 2 , ∣ ≃-sym (doubleton-map x₀ x₁ , f-is-equiv) ∣
   where
    doubleton-map-lc : left-cancellable (doubleton-map x₀ x₁)
    doubleton-map-lc {𝟎} {𝟎} p = refl
    doubleton-map-lc {𝟎} {𝟏} p = 𝟘-elim (ν (ap pr₁ p))
    doubleton-map-lc {𝟏} {𝟎} p = 𝟘-elim (ν (ap pr₁ (p ⁻¹)))
    doubleton-map-lc {𝟏} {𝟏} p = refl

    doubleton-map-is-embedding : is-embedding (doubleton-map x₀ x₁)
    doubleton-map-is-embedding = lc-maps-into-sets-are-embeddings
                                  (doubleton-map x₀ x₁)
                                  doubleton-map-lc
                                  (doubleton-is-set x₀ x₁ X-is-set)

    f-is-equiv : is-equiv (doubleton-map x₀ x₁)
    f-is-equiv = surjective-embeddings-are-equivs
                  (doubleton-map x₀ x₁)
                  doubleton-map-is-embedding
                  doubleton-map-is-surjection

doubleton-finite-gives-decidable-equality : funext 𝓤 𝓤₀
                                          → {X : 𝓤 ̇ } (x₀ x₁ : X)
                                          → is-set X
                                          → is-finite (doubleton x₀ x₁)
                                          → is-decidable (x₀ ＝ x₁)
doubleton-finite-gives-decidable-equality fe x₀ x₁ X-is-set ϕ = δ
 where
  γ : is-finite (doubleton x₀ x₁) → is-decidable (x₀ ＝ x₁)
  γ (0 , s) = ∥∥-rec (decidability-of-prop-is-prop fe X-is-set) α s
   where
    α : doubleton x₀ x₁ ≃ 𝟘 → is-decidable (x₀ ＝ x₁)
    α (g , i) = 𝟘-elim (g (x₀ , ∣ inl refl ∣))

  γ (1 , s) = inl (∥∥-rec X-is-set β s)
   where
    α : is-prop (Fin 1)
    α 𝟎 𝟎 = refl

    β : doubleton x₀ x₁ ≃ Fin 1 → x₀ ＝ x₁
    β (g , i) = ap pr₁ (equivs-are-lc g i
                         (α (g (doubleton-map x₀ x₁ 𝟎))
                         (g (doubleton-map x₀ x₁ 𝟏))))

  γ (succ (succ n) , s) = ∥∥-rec (decidability-of-prop-is-prop fe X-is-set) f s
   where
    f : doubleton x₀ x₁ ≃ Fin (succ (succ n)) → is-decidable (x₀ ＝ x₁)
    f (g , i) = β
     where
      h : x₀ ＝ x₁ → doubleton-map x₀ x₁ 𝟎 ＝ doubleton-map x₀ x₁ 𝟏
      h = to-subtype-＝ (λ _ → ∨-is-prop)

      α : is-decidable (g (doubleton-map x₀ x₁ 𝟎) ＝ g (doubleton-map x₀ x₁ 𝟏))
        → is-decidable (x₀ ＝ x₁)
      α (inl p) = inl (ap pr₁ (equivs-are-lc g i p))
      α (inr ν) = inr (contrapositive (λ p → ap g (h p)) ν)

      β : is-decidable (x₀ ＝ x₁)
      β = α (Fin-is-discrete
              (g (doubleton-map x₀ x₁ 𝟎))
              (g (doubleton-map x₀ x₁ 𝟏)))

  δ : is-decidable (x₀ ＝ x₁)
  δ = γ ϕ

all-K-finite-types-finite-gives-all-sets-discrete :

    funext 𝓤 𝓤₀
  → ((A : 𝓤 ̇ ) → is-Kuratowski-finite A → is-finite A)
  → (X : 𝓤 ̇ ) → is-set X → is-discrete X

all-K-finite-types-finite-gives-all-sets-discrete {𝓤} fe ϕ X X-is-set x₀ x₁ =
 doubleton-finite-gives-decidable-equality
  fe x₀ x₁ X-is-set
  (ϕ (doubleton x₀ x₁)
  (doubletons-are-Kuratowki-finite x₀ x₁))

all-K-finite-types-finite-gives-EM :

    ((𝓤 : Universe) (A : 𝓤 ̇ ) → is-Kuratowski-finite A → is-finite A)
  → (𝓤 : Universe) → FunExt → PropExt → EM 𝓤
all-K-finite-types-finite-gives-EM ϕ 𝓤 fe pe =
 Ω-discrete-gives-EM (fe 𝓤 𝓤) (pe 𝓤)
  (all-K-finite-types-finite-gives-all-sets-discrete
    (fe (𝓤 ⁺) 𝓤₀) (ϕ (𝓤 ⁺)) (Ω 𝓤) (Ω-is-set (fe 𝓤 𝓤) (pe 𝓤)))

\end{code}

Added 13 April 2021.

Can every Kuratowski finite discrete type be equipped with a linear
order?

Recall that a type is called discrete if it has decidable equality.

Steve Vickers asks this question for the internal language of a
1-topos, and provides a counter model for it in Section 2.4 of the
following paper:

  S.J. Vickers. Strongly Algebraic = SFP (Topically). Mathematical
  Structures in Computer Science 11 (2001) pp. 717-742,
  http://dx.doi.org/10.1017/S0960129501003437
  https://www.cs.bham.ac.uk/~sjv/SFP.pdf

We here work in MLTT with propositional truncations, in Agda notation,
and instead prove that, in the presence of univalence, it is false
that every (Kuratowski) finite type with decidable equality can be
equipped with a linear order.

We also include an open problem related to this.

The following no-selection lemma is contributed by Tom de Jong:

\begin{code}

no-selection : is-univalent 𝓤₀ → ¬ ((X : 𝓤₀ ̇ ) → ∥ X ≃ 𝟚 ∥ → X)
no-selection ua ϕ = γ
 where
  f : {X : 𝓤₀ ̇ } → X ＝ 𝟚 → X ≃ 𝟚
  f {X} = idtoeq X 𝟚

  n : 𝟚
  n = ϕ 𝟚 ∣ ≃-refl 𝟚 ∣

  α : {X : 𝓤₀ ̇ } (p : X ＝ 𝟚) → ϕ X ∣ f p ∣ ＝  ⌜ f p ⌝⁻¹ n
  α refl = refl

  p : 𝟚 ＝ 𝟚
  p = eqtoid ua 𝟚 𝟚 complement-≃

  q : ∣ f refl ∣ ＝ ∣ f p ∣
  q = ∥∥-is-prop ∣ f refl ∣ ∣ f p ∣

  r : f p ＝ complement-≃
  r = idtoeq-eqtoid ua 𝟚 𝟚 complement-≃

  s = n                     ＝⟨ refl ⟩
      ⌜ f refl ⌝⁻¹ n        ＝⟨ (α refl)⁻¹ ⟩
      ϕ 𝟚 ∣ f refl ∣        ＝⟨ ap (ϕ 𝟚) q ⟩
      ϕ 𝟚 ∣ f p ∣           ＝⟨ α p ⟩
      ⌜ f p ⌝⁻¹ n           ＝⟨ ap (λ - → ⌜ - ⌝⁻¹ n) r ⟩
      ⌜ complement-≃ ⌝⁻¹ n  ＝⟨ refl ⟩
      complement n          ∎

  γ : 𝟘
  γ = complement-no-fp n s


𝟚-is-Fin2 : 𝟚 ≃ Fin 2
𝟚-is-Fin2 = qinveq (𝟚-cases 𝟎 𝟏) (g , η , ε)
 where
  g : Fin 2 → 𝟚
  g 𝟎 = ₀
  g 𝟏 = ₁

  η : g ∘ 𝟚-cases 𝟎 𝟏 ∼ id
  η ₀ = refl
  η ₁ = refl

  ε : 𝟚-cases 𝟎 𝟏 ∘ g ∼ id
  ε 𝟎 = refl
  ε 𝟏 = refl

no-orderability-of-finite-types :

 Univalence → ¬ ((X : 𝓤 ̇ ) → is-finite X → finite-linear-order X)

no-orderability-of-finite-types {𝓤} ua ψ = γ
 where
  fe : FunExt
  fe = Univalence-gives-FunExt ua

  α : (X : 𝓤₀ ̇ ) → ∥ X ≃ 𝟚 ∥ → X ≃ 𝟚
  α X s = VII
   where
    X' : 𝓤 ̇
    X' = Lift 𝓤 X

    I : X ≃ 𝟚 → X' ≃ Fin 2
    I 𝕗 = X'    ≃⟨ Lift-≃ 𝓤 X ⟩
          X     ≃⟨ 𝕗 ⟩
          𝟚     ≃⟨ 𝟚-is-Fin2 ⟩
          Fin 2 ■

    II : ∥ X' ≃ Fin 2 ∥
    II = ∥∥-functor I s

    III : is-finite X'
    III = 2 , II

    IV : finite-linear-order X'
    IV = ψ X' III

    n : ℕ
    n = pr₁ IV

    𝕘 : X' ≃ Fin n
    𝕘 = pr₂ IV

    V : ∥ X' ≃ Fin n ∥ → ∥ X' ≃ Fin 2 ∥ → n ＝ 2
    V = ∥∥-rec₂ ℕ-is-set (λ 𝕗 𝕘 → Fin-lc n 2 (≃-sym 𝕗 ● 𝕘))

    VI : n ＝ 2
    VI = V ∣ 𝕘 ∣ II

    VII = X     ≃⟨ ≃-Lift 𝓤 X ⟩
          X'    ≃⟨ 𝕘 ⟩
          Fin n ≃⟨ idtoeq (Fin n) (Fin 2) (ap Fin VI) ⟩
          Fin 2 ≃⟨ ≃-sym 𝟚-is-Fin2 ⟩
          𝟚     ■

  ϕ : (X : 𝓤₀ ̇ ) → ∥ X ≃ 𝟚 ∥ → X
  ϕ X s = ⌜ ≃-sym (α X s) ⌝ ₀

  γ : 𝟘
  γ = no-selection (ua 𝓤₀) ϕ

\end{code}

Because univalence is consistent, it follows that, without univalence,
the statement

  (X : 𝓤 ̇ ) → is-finite X → finite-linear-order X

is not provable.

The same holds if we replace is-finite by is-Kuratowski-finite or if
we consider Kuratowski finite discrete types.

\begin{code}

no-orderability-of-K-finite-types :

 Univalence → ¬ ((X : 𝓤 ̇ ) → is-Kuratowski-finite X → finite-linear-order X)

no-orderability-of-K-finite-types {𝓤} ua ϕ = no-orderability-of-finite-types ua ψ
 where
  ψ : (X : 𝓤 ̇ ) → is-finite X → finite-linear-order X
  ψ X i = ϕ X (finite-types-are-Kuratowski-finite i)

\end{code}

And this gives an alternative answer to the question by Steve Vickers
mentioned above:

\begin{code}

no-orderability-of-K-finite-discrete-types :

 Univalence → ¬ ((X : 𝓤 ̇ ) → is-Kuratowski-finite X → is-discrete X → finite-linear-order X)

no-orderability-of-K-finite-discrete-types {𝓤} ua ϕ = no-orderability-of-finite-types ua ψ
 where
  ψ : (X : 𝓤 ̇ ) → is-finite X → finite-linear-order X
  ψ X i = ϕ X (finite-types-are-Kuratowski-finite i)
              (finite-types-are-discrete pt (Univalence-gives-FunExt ua) i)
\end{code}

TODO. Without univalence, maybe it is the case that from

  (X : 𝓤 ̇ ) → ∥ X ≃ 𝟚 ∥ → X

we can deduce excluded middle or some other constructive taboo.

(It seems not. More later.)

One more notion of finiteness:

\begin{code}

is-subfinite : 𝓤 ̇ → 𝓤 ̇
is-subfinite X = ∃ n ꞉ ℕ , X ↪ Fin n

subfiniteness-data : 𝓤 ̇ → 𝓤 ̇
subfiniteness-data X = Σ n ꞉ ℕ , X ↪ Fin n

\end{code}

Steve Vickers remarked (personal communication) that, in view of
a remark given above, if a type is simultaneously Kuratowski finite
and subfinite, then it is finite, because subfinite types, being
subtypes of types with decidable equality, have decidable equality.

\begin{code}

Kuratowski-subfinite-types-are-finite : funext 𝓤 𝓤₀
                                      → {X : 𝓤 ̇ }
                                      → is-Kuratowski-finite X
                                      → is-subfinite X
                                      → is-finite X
Kuratowski-subfinite-types-are-finite fe {X} k = γ
 where
 δ : subfiniteness-data X → is-finite X
 δ (n , f , e) = Kuratowski-finite-discrete-types-are-finite fe
                  (embeddings-reflect-discreteness f e Fin-is-discrete) k

 γ : is-subfinite X → is-finite X
 γ = ∥∥-rec (being-finite-is-prop X) δ

\end{code}

Summary of finiteness notions for a type X:

     ∃ n ꞉ ℕ , X ≃ Fin n  (is-finite X)
     Σ n ꞉ ℕ , X ≃ Fin n  (finite-linear-order X)

     ∃ n ꞉ ℕ , Fin n ↠ X  (is-Kuratowski-finite X)
     Σ n ꞉ ℕ , Fin n ↠ X  (Kuratowski-data)

     ∃ n ꞉ ℕ , X ↪ Fin n  (is-subfinite)
     Σ n ꞉ ℕ , X ↪ Fin n  (subfiniteness-data)

Addendum.

\begin{code}

select-equiv-with-𝟚-lemma₁ : FunExt
                           → {X : 𝓤 ̇ } (x₀ : X)
                           → is-prop (Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁))
select-equiv-with-𝟚-lemma₁ fe {X} x₀ (y , i) (z , j) = V
 where
  f g : 𝟚 → X
  f = 𝟚-cases x₀ y
  g = 𝟚-cases x₀ z

  f' g' : X → 𝟚
  f' = inverse f i
  g' = inverse g j

  I : z ≠ x₀
  I p = zero-is-not-one
         (₀        ＝⟨ (inverses-are-retractions g j ₀)⁻¹ ⟩
          g' (g ₀) ＝⟨ refl ⟩
          g' x₀    ＝⟨ ap g' (p ⁻¹) ⟩
          g' z     ＝⟨ refl ⟩
          g' (g ₁) ＝⟨ inverses-are-retractions g j ₁ ⟩
          ₁        ∎)

  II : (n : 𝟚) → f n ＝ z → ₁ ＝ n
  II ₀ p = 𝟘-elim (I (p ⁻¹))
  II ₁ p = refl

  III : f (f' z) ＝ z
  III = inverses-are-sections f i z

  IV : y ＝ z
  IV = equivs-are-lc f' (inverses-are-equivs f i)
        (f' y     ＝⟨ refl ⟩
         f' (f ₁) ＝⟨ inverses-are-retractions f i ₁ ⟩
         ₁        ＝⟨ II (f' z) III ⟩
         f' z     ∎)

  V : (y , i) ＝ (z , j)
  V = to-subtype-＝ (λ x₁ → being-equiv-is-prop fe (𝟚-cases x₀ x₁)) IV

select-equiv-with-𝟚-lemma₂ : FunExt
                           → {X : 𝓤 ̇ }
                           → X ≃ 𝟚
                           → (x₀ : X) → Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁)
select-equiv-with-𝟚-lemma₂ fe {X} (f , i) x₀ = γ (f x₀) x₀ refl
 where
  γ : (n : 𝟚) (x₀ : X) → n ＝ f x₀ → Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁)
  γ ₀ x₀ p = (x₁ , j)
   where
    x₁ : X
    x₁ = inverse f i ₁

    h : inverse f i ∼ 𝟚-cases x₀ x₁
    h ₀ = inverse f i ₀      ＝⟨ ap (inverse f i) p ⟩
          inverse f i (f x₀) ＝⟨ inverses-are-retractions f i x₀ ⟩
          x₀                 ＝⟨ refl ⟩
          𝟚-cases x₀ x₁ ₀    ∎
    h ₁ = refl

    j : is-equiv (𝟚-cases x₀ x₁)
    j = equiv-closed-under-∼' (inverses-are-equivs f i) h

  γ ₁ x₀ p = (x₁ , j)
   where
    x₁ : X
    x₁ = inverse f i ₀

    h : inverse f i ∘ complement ∼ 𝟚-cases x₀ x₁
    h ₀ = inverse f i (complement ₀) ＝⟨ refl ⟩
          inverse f i ₁              ＝⟨ ap (inverse f i) p ⟩
          inverse f i (f x₀)         ＝⟨ inverses-are-retractions f i x₀ ⟩
          x₀                         ＝⟨ refl  ⟩
          𝟚-cases x₀ x₁ ₀            ∎
    h ₁ = refl

    j : is-equiv (𝟚-cases x₀ x₁)
    j = equiv-closed-under-∼'
        (∘-is-equiv complement-is-equiv (inverses-are-equivs f i)) h

select-equiv-with-𝟚 : FunExt
                    → {X : 𝓤 ̇ }
                    → ∥ X ≃ 𝟚 ∥
                    → X
                    → X ≃ 𝟚
select-equiv-with-𝟚 fe {X} s x₀ = γ
 where
  α : ∥ X ≃ 𝟚 ∥ → Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁)
  α = ∥∥-rec (select-equiv-with-𝟚-lemma₁ fe x₀)
            (λ 𝕙 → select-equiv-with-𝟚-lemma₂ fe 𝕙 x₀)

  β : Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁)
  β = α s

  γ : X ≃ 𝟚
  γ = ≃-sym (𝟚-cases x₀ (pr₁ β) , pr₂ β)

\end{code}

Hence finding an equivalence from the existence of an equivalence is
logically equivalent to finding a point from the existence of an
equivalence (exercise: moreover, these two things are typally
equivalent):

\begin{code}

select-equiv-with-𝟚-theorem : FunExt
                            → {X : 𝓤 ̇ }
                            → (∥ X ≃ 𝟚 ∥ → X ≃ 𝟚)
                            ↔ (∥ X ≃ 𝟚 ∥ → X)
select-equiv-with-𝟚-theorem fe {X} = α , β
 where
  α : (∥ X ≃ 𝟚 ∥ → X ≃ 𝟚) → ∥ X ≃ 𝟚 ∥ → X
  α f s = ⌜ ≃-sym (f s) ⌝ ₀

  β : (∥ X ≃ 𝟚 ∥ → X) → ∥ X ≃ 𝟚 ∥ → X ≃ 𝟚
  β g s = select-equiv-with-𝟚 fe s (g s)

\end{code}
