```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --without-K --auto-inline
            --experimental-lossy-unification #-}

open import Integers.Addition renaming (_+_ to _+ℤ_)
open import Integers.Order
open import Integers.Integers
open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Quotient
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import PLDI.DyadicRationals
open import PLDI.Prelude

module PLDI.3-TernaryBoehmRealsSearch
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
  (dy : Dyadics)
  where

open import PLDI.1-TernaryBoehmReals pt fe pe sq
open import PLDI.2-FunctionEncodings pt fe pe sq dy hiding (r)

open set-quotients-exist sq
open Dyadics dy                                   
```

# Part I - Searchable types

We first define searchable types.

```agda
decidable-predicate : {𝓤 𝓥 : Universe} → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ̇
decidable-predicate {𝓤} {𝓥} X
 = Σ p ꞉ (X → Ω 𝓥) , ((x : X) → decidable (pr₁ (p x)))

searchable : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → 𝓤 ⊔ 𝓥 ⁺ ̇ 
searchable {𝓤} {𝓥} X
 = Π (p , _) ꞉ decidable-predicate {𝓤} {𝓥} X
 , Σ x₀ ꞉ X , (Σ (pr₁ ∘ p) → pr₁ (p x₀))
```

We often search only uniformly continuous predicates, which -- for general
sequence types -- are defined as follows.

```agda
_≈'_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ≈' β) n = (i : ℕ) → i < n → α n ＝ β n
```

We could use this to define uniformly continuous predicates on 𝕋, and then
prove searchability by using the isomorphism between `𝕋` and `ℕ → 𝟛` to
immediately give us a searcher on such unifoormly continuous predicates using
the below properties:

```agda
decidable-predicate⌜_,_⌝⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y
                         → decidable-predicate {𝓤} {𝓦} X
                         → decidable-predicate {𝓥} {𝓦} Y
decidable-predicate⌜ e , (p , d) ⌝⁻¹ = (p ∘ ⌜ e ⌝⁻¹) , (d ∘ ⌜ e ⌝⁻¹)

decidable-predicate⌜_,_⌝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y
                         → decidable-predicate {𝓥} {𝓦} Y
                         → decidable-predicate {𝓤} {𝓦} X
decidable-predicate⌜ e , (p , d) ⌝ = (p ∘ ⌜ e ⌝) , (d ∘ ⌜ e ⌝)

decidable-predicate⌜_,_⌝-correct
  : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (e : X ≃ Y)
  → ((p , d) : decidable-predicate {𝓥} {𝓦} Y)
  → (y : Y) → pr₁ (p y)
  → pr₁ (pr₁ (decidable-predicate⌜ e , (p , d) ⌝) (⌜ e ⌝⁻¹ y))
decidable-predicate⌜ e , (p , d) ⌝-correct y
 = transport (λ - → pr₁ (p -)) (≃-sym-is-rinv e _ ⁻¹)
              
searchable⌜_,_⌝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y
                → searchable {𝓤} {𝓦} X
                → searchable {𝓥} {𝓦} Y
searchable⌜ e , 𝓔 ⌝ (p , d)
 = ⌜ e ⌝ (pr₁ p')
 , λ (y₀ , py₀) → pr₂ p' ((⌜ e ⌝⁻¹ y₀)
                , decidable-predicate⌜ e , (p , d) ⌝-correct y₀ py₀)
 where p' = 𝓔 (decidable-predicate⌜ e , (p , d) ⌝)
```

However, the searcher given by this isomorphism (like that on signed-digits)
would search the *entire* prefix of the stream from point `pos 0` to point
`pos δ`; despite the fact that -- for ternary Boehm encodings --  the location
information at `pos δ` *includes* all of the location information previous to
that.

Therefore, we prefer to use a different isomorphism: the one induced by the
`replace` function in [`TernaryBoehmReals`](1-TernaryBoehmReals.lagda.md).

# Part II -  Searching quotiented encodings of compact intervals

First, we define the equivalence relation needed to determine uniformly
continuous decidable predicates on Ternary Boehm encodings of any compact
interval `⟪ k , i ⟫`.

This equivalence relation simply takes a modulus of continuity `δ : ℤ` and asks
if `⟨ ι x ⟩ δ ＝ ⟨ ι y ⟩ δ` given `x,y : CompactInterval (k , i)`.

```agda
CompEqRel : (δ : ℤ) ((k , i) : ℤ × ℤ)
          → EqRel {𝓤₀} {𝓤₀} (CompactInterval (k , i))
CompEqRel δ (k , i) = _≣_ , u , r , s , t
 where
   _≣_ : CompactInterval (k , i) → CompactInterval (k , i) → 𝓤₀ ̇ 
   (x ≣ y) = ⟨ ι x ⟩ δ ＝ ⟨ ι y ⟩ δ
   u : is-prop-valued _≣_
   u x y = ℤ-is-set
   r : reflexive _≣_
   r x = refl
   s : symmetric _≣_
   s x y = _⁻¹
   t : transitive _≣_
   t x y z = _∙_
```

Seen as we only need to look at level `δ : ℤ`, we can isolate the bricks on that
level into the type `ℤ[ lower (k , i) δ , upper (k , i) δ ]`.

Indeed, the quotient type `CompactInterval (k , i) / CompEqRel δ (k , i)` is
*equivalent* to the type `ℤ[ lower (k , i) δ , upper (k , i) δ ]`

```agda
Conv→ : (δ : ℤ) → ((k , i) : ℤ × ℤ)
      → CompactInterval (k , i) → ℤ[ lower (k , i) δ , upper (k , i) δ ]
Conv→ δ (k , i) x = ⟨ ι x ⟩ δ , ci-lower-upper (k , i) x δ

Conv← : (δ : ℤ) → ((k , i) : ℤ × ℤ)
      → ℤ[ lower (k , i) δ , upper (k , i) δ ] → CompactInterval (k , i)
Conv← δ (k , i) (z , l≤z≤u) = pr₁ (replace (k , i) (z , δ) l≤z≤u)

CompReplace : (δ : ℤ) ((k , i) : ℤ × ℤ)
            → (x : CompactInterval (k , i))
            → x ≈[ CompEqRel δ (k , i) ] (Conv← δ (k , i) ∘ Conv→ δ (k , i)) x
CompReplace δ (k , i) x = pr₂ (replace (k , i) (z , δ) l≤z≤u) ⁻¹
 where
   γ     = Conv→ δ (k , i) x
   z     = pr₁ γ
   l≤z≤u = pr₂ γ

Conv→-identifies-related-points
  : (δ : ℤ) → ((k , i) : ℤ × ℤ)
  → identifies-related-points {𝓤₀} {𝓤₀} {𝓤₀} {CompactInterval (k , i)}
      (CompEqRel δ (k , i)) (Conv→ δ (k , i))
Conv→-identifies-related-points δ (k , i)
 = to-subtype-＝ {𝓤₀} {𝓤₀} {ℤ} {λ z → lower (k , i) δ ≤ℤ z ≤ℤ upper (k , i) δ}
     (λ z → ≤ℤ²-is-prop {lower (k , i) δ} {upper (k , i) δ} z)

ℤ[_,_]-is-set : (a b : ℤ) → is-set (ℤ[ a , b ])
ℤ[ a , b ]-is-set = subsets-of-sets-are-sets ℤ (λ z → a ≤ℤ z ≤ℤ b)
                      ℤ-is-set (≤ℤ²-is-prop _)
                      
med-map/ : {A : 𝓤 ̇ } (δ : ℤ) ((k , i) : ℤ × ℤ)
         → is-set A
         → (f : CompactInterval (k , i) → A)
         → identifies-related-points (CompEqRel δ (k , i)) f
         → CompactInterval (k , i) / CompEqRel δ (k , i) → A
med-map/ δ (k , i) s = mediating-map/ (CompEqRel δ (k , i)) s

uni-tri/ : {A : 𝓤 ̇ } (δ : ℤ) ((k , i) : ℤ × ℤ)
         → (s : is-set A)
         → (f : CompactInterval (k , i) → A)
         → (p : identifies-related-points (CompEqRel δ (k , i)) f)
         → med-map/ δ (k , i) s f p ∘ η/ (CompEqRel δ (k , i)) ∼ f
uni-tri/ δ (k , i) s f p = universality-triangle/ (CompEqRel δ (k , i)) s f p

med-map : (δ : ℤ) ((k , i) : ℤ × ℤ)
        → CompactInterval (k , i) / CompEqRel δ (k , i)
        → ℤ[ lower (k , i) δ , upper (k , i) δ ]
med-map δ (k , i) = med-map/ δ (k , i)
                      (ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ]-is-set)
                      (Conv→ δ (k , i))
                      (to-subtype-＝ ≤ℤ²-is-prop)

uni-tri : (δ : ℤ) ((k , i) : ℤ × ℤ)
        → (med-map δ (k , i) ∘ η/ (CompEqRel δ (k , i))) ∼ Conv→ δ (k , i)
uni-tri δ (k , i) = uni-tri/ δ (k , i)
                      ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ]-is-set 
                      (Conv→ δ (k , i))
                      (to-subtype-＝ ≤ℤ²-is-prop)
           
compact-equiv : (δ : ℤ) ((k , i) : ℤ × ℤ)
              → CompactInterval (k , i) / CompEqRel δ (k , i)
              ≃ ℤ[ lower (k , i) δ , upper (k , i) δ ]
compact-equiv δ (k , i) = f' , ((g' , fg) , (g' , gf))
 where
  f' : CompactInterval (k , i) / CompEqRel δ (k , i)
     → ℤ[ lower (k , i) δ , upper (k , i) δ ]
  f' = med-map δ (k , i)
  g' : ℤ[ lower (k , i) δ , upper (k , i) δ ]
     → CompactInterval (k , i) / CompEqRel δ (k , i)
  g' = η/ (CompEqRel δ (k , i)) ∘ Conv← δ (k , i)
  fg : f' ∘ g' ∼ id
  fg (z , l≤z≤u)
   = uni-tri δ (k , i) (Conv← δ (k , i) (z , l≤z≤u))
   ∙ to-subtype-＝ ≤ℤ²-is-prop (pr₂ (replace (k , i) (z , δ) l≤z≤u)) 
  gf : g' ∘ f' ∼ id
  gf = /-induction (CompEqRel δ (k , i)) (λ _ → /-is-set (CompEqRel δ (k , i)))
         (λ y → η/-identifies-related-points (CompEqRel δ (k , i))
           (ap (λ - → ⟨ ι (Conv← δ (k , i) -) ⟩ δ)
             (uni-tri δ (k , i) y)
           ∙ CompReplace δ (k , i) y ⁻¹))
```

This gives us a much more efficient searcher for Ternary Boehm reals in compact
intervals, because the searcher on finite subsets of `ℤ` does not need to check
every element of the `𝕋` sequence.

```agda
ℤ[_,_]-searchable' : (l u : ℤ) → (n : ℕ) → l +pos n ＝ u
                  → searchable {𝓤₀} {𝓦} (ℤ[ l , u ])
ℤ[ l , l ]-searchable' 0 refl (p , d)
 = ((l , ℤ≤-refl l , ℤ≤-refl l))
 , λ ((z , l≤z≤u) , pz)
   → transport (pr₁ ∘ p)
       (to-subtype-＝ ≤ℤ²-is-prop ((≤ℤ-antisym l z l≤z≤u) ⁻¹)) pz
ℤ[ l , .(succℤ (l +pos n)) ]-searchable' (succ n) refl (p , d)
 = Cases (d u*) (λ pu → u* , (λ _ → pu))
    (λ ¬pu → ans ,
      (λ ((z , l≤z , z≤u) , pz)
        → Cases (ℤ≤-split z u z≤u)
            (λ z<u → sol ((z , l≤z
                   , transport (z ≤_) (predsuccℤ _) (≤ℤ-back z u z<u))
                   , transport (pr₁ ∘ p) (to-subtype-＝ ≤ℤ²-is-prop refl) pz))
            (λ z＝u → 𝟘-elim (¬pu (transport (pr₁ ∘ p)
                                   (to-subtype-＝ ≤ℤ²-is-prop z＝u) pz)))))
 where
   u = succℤ (l +pos n)
   u* = u , (succ n , refl) , ℤ≤-refl u
   γ : ℤ[ l , l +pos n ] → ℤ[ l , u ]
   γ = ℤ[ l , l +pos n ]-succ
   IH = ℤ[ l , l +pos n ]-searchable' n refl ((p ∘ γ) , (d ∘ γ))
   ans = γ (pr₁ IH)
   sol = pr₂ IH

ℤ[_,_]-searchable : (l u : ℤ) → l ≤ u → searchable {𝓤₀} {𝓦} (ℤ[ l , u ])
ℤ[ l , u ]-searchable (n , p) = ℤ[ l , u ]-searchable' n p

𝕋-compact-searchable
  : ((k , i) : ℤ × ℤ) (δ : ℤ)
  → searchable {𝓤₀} {𝓦} (CompactInterval (k , i) / CompEqRel δ (k , i))
𝕋-compact-searchable (k , i) δ
 = searchable⌜ (≃-sym (compact-equiv δ (k , i)))
 , (ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ]-searchable
     (lower≤upper (k , i) δ)) ⌝
```

# Part III - Directly defining continuity and uniform continuity for 𝕋

We can define uniform continuity on (for example, unary) predicates on 𝕋 as
follows, and show that those on compact intervals are isomorphic to a predicate
on the quotiented, searchable type considered above.

```agda
𝕋¹-uc-predicate : (𝕋 → Ω 𝓦) → 𝓦 ̇
𝕋¹-uc-predicate {𝓦} p
 = Σ δ ꞉ ℤ , ((χ γ : 𝕋) → ⟨ χ ⟩ δ ＝ ⟨ γ ⟩ δ → p χ holds ⇔ p γ holds)

𝕋¹-uc-predicate-ki : ((k , i) : 𝕀s) → (CompactInterval (k , i) → Ω 𝓦) → 𝓦 ̇
𝕋¹-uc-predicate-ki (k , i) p
   = Σ δ ꞉ ℤ , ((χ γ : CompactInterval (k , i))
             → ⟨ ι χ ⟩ δ ＝ ⟨ ι γ ⟩ δ → p χ holds ⇔ p γ holds)

𝕋¹-uc-predicate-equiv
 : {k i : ℤ} → (p : CompactInterval (k , i) → Ω 𝓦)
 → ((δ , _) : 𝕋¹-uc-predicate-ki (k , i) p)
 → ∃! p* ꞉ (CompactInterval (k , i) / CompEqRel δ (k , i) → Ω 𝓦)
 , p* ∘ η/ (CompEqRel δ (k , i)) ∼ p
𝕋¹-uc-predicate-equiv {𝓦} {k} {i} p (δ , ϕ)
 = /-universality (CompEqRel δ (k , i))
    (Ω-is-set (fe 𝓦 𝓦) (pe 𝓦))
    p
    (λ ≡δ → Ω-extensionality (fe 𝓦 𝓦) (pe 𝓦)
              (pr₁ (ϕ _ _ ≡δ))
              (pr₂ (ϕ _ _ ≡δ)))
```

We also define continuity and uniform continuity directly on (for example,
unary) functions of type 𝕋 → 𝕋.

```agda
𝕋¹-c-function : (𝕋 → 𝕋) → 𝓤₀  ̇
𝕋¹-c-function f
 = (ϵ : ℤ) (χ : 𝕋)
 → Σ δ ꞉ ℤ , ((γ : 𝕋) → ⟨ χ ⟩ δ ＝ ⟨ γ ⟩ δ → ⟨ f χ ⟩ ϵ ＝ ⟨ f γ ⟩ ϵ)

𝕋¹-uc-function-ki : ((k , i) : 𝕀s) → (CompactInterval (k , i) → 𝕋) → 𝓤₀  ̇
𝕋¹-uc-function-ki (k , i) f
 = (ϵ : ℤ)
 → Σ δ ꞉ ℤ , ((χ γ : CompactInterval (k , i))
           → ⟨ ι χ ⟩ δ ＝ ⟨ ι γ ⟩ δ → ⟨ f χ ⟩ ϵ ＝ ⟨ f γ ⟩ ϵ)
```

# Part IV - Searching function encodings on ternary Boehm encodings

We now bring in our functions as defined in
[`FunctionEncodings`](2-FunctionEncodings.lagda.md).

We eventually want to show that each function defined using the machinery in
that file yields a uniform continuity oracle that proves it is uniformly
continuous.

However, for now, we instead assume this fact, and use it to show that any
predicate `p : 𝕋 → Ω` and function built via our machinery `f : 𝕋 → 𝕋` yields
a predicate `(p ∘ f) : 𝕋 → Ω` that is searchable on any compact interval given
by a specific-width interval `(k , i) : 𝕀s`.

```agda
F-u-continuous
 : FunctionMachine 1 → 𝕀s → 𝓤₀  ̇ 
F-u-continuous F (k , i)
 = 𝕋¹-uc-function-ki (k , i) (FunctionMachine.f̂ F ∘ [_] ∘ ι)
  
p∘-is-uc : (F : FunctionMachine 1) {(k , i) : 𝕀s}
         → F-u-continuous F (k , i)
         → (p : 𝕋 → Ω 𝓦) → 𝕋¹-uc-predicate {𝓦} p
         → 𝕋¹-uc-predicate-ki {𝓦} (k , i) (p ∘ FunctionMachine.f̂ F ∘ [_] ∘ ι)
p∘-is-uc F uc p (δ , ϕ)
 = pr₁ (uc δ) , λ χ γ χδ≡γδ → ϕ (f̂ [ ι χ ]) (f̂ [ ι γ ]) (pr₂ (uc δ) χ γ χδ≡γδ)
 where open FunctionMachine F
```

Therefore, using the above and `𝕋¹-uc-predicate-equiv`, we have shown the method
of proving that any encoded function on 𝕋 built from our machinery is searchable
on any compact interval given by a specific-width interval encoding.

We conclude here.
