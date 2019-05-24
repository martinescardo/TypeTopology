Tom de Jong & Martin Escardo, 20 May 2019.

 * Directed complete posets.
 * Continuous maps.
 * Function space.
 * Least fixed points.
 * Example: lifting, and the semantic counter-parts of the PCF constants.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-PropTrunc
open import SpartanMLTT

module dcpos (pt : propositional-truncations-exist)
             (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
             (𝓥 : Universe) -- where the index set for directed completeness lives
       where

open PropositionalTruncation pt

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module _
        {𝓤 𝓣 : Universe}
        {D : 𝓤 ̇ }
        (_⊑_ : D → D → 𝓣 ̇ )
       where

 is-prop-valued : 𝓤 ⊔ 𝓣 ̇
 is-prop-valued = (x y : D) → is-prop(x ⊑ y)

 is-reflexive : 𝓤 ⊔ 𝓣 ̇
 is-reflexive = (x : D) → x ⊑ x

 is-transitive : 𝓤 ⊔ 𝓣 ̇
 is-transitive = (x y z : D) → x ⊑ y → y ⊑ z → x ⊑ z

 is-antisymmetric : 𝓤 ⊔ 𝓣 ̇
 is-antisymmetric = (x y : D) → x ⊑ y → y ⊑ x → x ≡ y

 is-upperbound : {I : 𝓥 ̇ } (u : D) (α : I → D) → 𝓥 ⊔ 𝓣 ̇
 is-upperbound u α = (i : domain α) → α i ⊑ u

 is-sup : {I : 𝓥 ̇ } → D → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 is-sup s α = (is-upperbound s α)
            × ((u : D) → is-upperbound u α → s ⊑ u)

 has-sup : {I : 𝓥 ̇ } → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 has-sup α = Σ \(s : D) → is-sup s α

 the-sup : {I : 𝓥 ̇ } {α : I → D} → has-sup α → D
 the-sup (s , i) = s

 sup-property : {I : 𝓥 ̇ } {α : I → D} (h : has-sup α) → is-sup (the-sup h) α
 sup-property (s , i) = i

 is-directed : {I : 𝓥 ̇ } → (I → D) → 𝓥 ⊔ 𝓣 ̇
 is-directed {I} α = (i j : I) → ∃ \(k : I) → (α i ⊑ α k) × (α j ⊑ α k)

 being-directed-is-a-prop : {I : 𝓥 ̇ } (α : I → D) → is-prop (is-directed α)
 being-directed-is-a-prop α = Π-is-prop fe
                               (λ i → Π-is-prop fe
                                       (λ j → ∥∥-is-a-prop ))

 is-directed-complete : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣  ̇
 is-directed-complete = {I : 𝓥 ̇ } {α : I → D} → is-directed α → has-sup α

 dcpo-axioms : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ̇
 dcpo-axioms = is-set D × is-prop-valued × is-reflexive × is-transitive × is-antisymmetric × is-directed-complete

 is-sup-is-a-prop : dcpo-axioms → {I : 𝓥 ̇ } (d : D) (α : I → D) → is-prop (is-sup d α)
 is-sup-is-a-prop (s , p , r , t , a , c) {I} d α = γ
  where
   γ : is-prop (is-sup d α)
   γ = ×-is-prop (Π-is-prop fe (λ (i : I) → p (α i) d))
                 (Π-is-prop fe (λ (x : D) → Π-is-prop fe (λ l → p d x)))

 has-sup-is-a-prop : dcpo-axioms → {I : 𝓥 ̇ } (α : I → D) → is-prop (has-sup α)
 has-sup-is-a-prop (s , p , r , t , a , c) {I} α = γ
  where
   γ : is-prop (has-sup α)
   γ (j , (u , l)) (j' , (u' , l')) = to-Σ-≡ (q , is-sup-is-a-prop (s , p , r , t , a , c) j' α _ _)
    where
     q : j ≡ j'
     q = a j j' (l j' u') (l' j u)

 being-directed-complete-is-a-prop : dcpo-axioms → is-prop is-directed-complete
 being-directed-complete-is-a-prop a = {!!}
 {-
  Π-is-prop' fe
   (λ {I} → Π-is-prop' fe
             (λ {α} → Π-is-prop fe (λ d → has-sup-is-a-prop a α)))
 -}
 dcpo-axioms-is-a-prop : is-prop dcpo-axioms
 dcpo-axioms-is-a-prop = iprops-are-props γ
  where
   γ : dcpo-axioms → is-prop dcpo-axioms
   γ (s , p , r , t , a , c) =
    ×-is-prop  (being-set-is-a-prop fe)
    (×-is-prop (Π-is-prop fe
                 (λ (x : D) → Π-is-prop fe
                                (λ (y : D) → being-a-prop-is-a-prop fe)))
    (×-is-prop (Π-is-prop fe (λ (x : D) → p x x))
    (×-is-prop (Π-is-prop fe
                 (λ (x : D) → Π-is-prop fe
                               (λ (y : D) → Π-is-prop fe
                                             (λ (z : D) → Π-is-prop fe
                                                           (λ (l : x ⊑ y) → Π-is-prop fe
                                                                             (λ (m : y ⊑ z) → p x z))))))
    (×-is-prop (Π-is-prop fe
                 (λ (x : D) → Π-is-prop fe
                               (λ y → Π-is-prop fe
                                       (λ (l : x ⊑ y) → Π-is-prop fe
                                                         λ (m : y ⊑ x) → s))))
              (being-directed-complete-is-a-prop (s , p , r , t , a , c))))))

module _ {𝓤 𝓣 : Universe} where

 DCPO-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO-structure D = Σ \(_⊑_ : D → D → 𝓣 ̇ ) → dcpo-axioms {𝓤} {𝓣} _⊑_

 DCPO : (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO = Σ \(D : 𝓤 ̇ ) → DCPO-structure D

 ⟨_⟩ : DCPO → 𝓤 ̇
 ⟨ D , _⊑_ , d ⟩ = D

 underlying-order : (𝓓 : DCPO) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓣 ̇
 underlying-order (D , _⊑_ , d) = _⊑_

 syntax underlying-order  𝓓 x y = x ⊑⟨ 𝓓 ⟩ y

 sethood : (𝓓 : DCPO) → is-set ⟨ 𝓓 ⟩
 sethood (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = s

 prop-valuedness : (𝓓 : DCPO) → is-prop-valued (underlying-order 𝓓 )
 prop-valuedness (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = p

 reflexivity : (𝓓 : DCPO) → is-reflexive (underlying-order 𝓓)
 reflexivity (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = r

 transitivity : (𝓓 : DCPO) → is-transitive (underlying-order 𝓓)
 transitivity (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = t

 antisymmetry : (𝓓 : DCPO) → is-antisymmetric (underlying-order 𝓓)
 antisymmetry (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = a

 directed-completeness : (𝓓 : DCPO) → is-directed-complete (underlying-order 𝓓)
 directed-completeness (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = c

 is-Directed : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) → 𝓥 ⊔ 𝓣 ̇
 is-Directed 𝓓 α = is-directed (underlying-order 𝓓) α

 ∐ : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} → is-Directed 𝓓 α → ⟨ 𝓓 ⟩
 ∐ 𝓓 δ = pr₁ (directed-completeness 𝓓 δ)

 ∐-is-sup : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
          → ((i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ)
          × ((u : ⟨ 𝓓 ⟩) → ((i : I) → α i ⊑⟨ 𝓓 ⟩ u) → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ u)
 ∐-is-sup 𝓓 δ = pr₂ (directed-completeness 𝓓 δ)

 ∐-is-upperbound : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                 → ((i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ)
 ∐-is-upperbound 𝓓 δ = pr₁ (∐-is-sup 𝓓 δ)

 ∐-is-lowerbound-of-upperbounds : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                                → ((u : ⟨ 𝓓 ⟩) → ((i : I) → α i ⊑⟨ 𝓓 ⟩ u) → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ u)
 ∐-is-lowerbound-of-upperbounds 𝓓 δ = pr₂ (∐-is-sup 𝓓 δ)

is-monotone : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → 𝓤 ⊔ 𝓣 ⊔ 𝓣' ̇
is-monotone 𝓓 𝓔 f = (x y : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ y → f x ⊑⟨ 𝓔 ⟩ f y



is-continuous₀ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
is-continuous₀ 𝓓 𝓔 f = (I : 𝓥 ̇) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                     → Σ \(ε : is-Directed 𝓔 (f ∘ α)) → f (∐ 𝓓 δ) ≡ ∐ 𝓔 ε


is-continuous = is-continuous₀



being-continuous-is-a-prop : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                           → is-prop (is-continuous 𝓓 𝓔 f)
being-continuous-is-a-prop 𝓓 𝓔 f =
   Π-is-prop fe
    (λ I → Π-is-prop fe
            (λ α → Π-is-prop fe
                     (λ δ → Σ-is-prop (being-directed-is-a-prop
                                          (underlying-order 𝓔)
                                          (f ∘ α))
                                      (λ ε → sethood 𝓔))))

continuous-functions-are-monotone : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                                  → is-continuous 𝓓 𝓔 f → is-monotone 𝓓 𝓔 f
continuous-functions-are-monotone 𝓓 𝓔 f cts x y l = γ
  where
   α : 𝟙 {𝓥} + 𝟙 {𝓥} → ⟨ 𝓓 ⟩
   α (inl *) = x
   α (inr *) = y
   δ : is-Directed 𝓓 α
   δ (inl *) (inl *) = ∣ inr * , l , l ∣
   δ (inl *) (inr *) = ∣ inr * , l , reflexivity 𝓓 y ∣
   δ (inr *) (inl *) = ∣ inr * , reflexivity 𝓓 y , l ∣
   δ (inr *) (inr *) = ∣ inr * , reflexivity 𝓓 y , reflexivity 𝓓 y ∣
   ε : is-Directed 𝓔 (f ∘ α)
   ε = pr₁ (cts (𝟙 + 𝟙) α δ)
   a : y ≡ ∐ 𝓓 δ
   a = antisymmetry 𝓓 y (∐ 𝓓 δ)
           (∐-is-upperbound 𝓓 δ (inr *))
           (∐-is-lowerbound-of-upperbounds 𝓓 δ y h)
    where
     h : (i : 𝟙 + 𝟙) → α i ⊑⟨ 𝓓 ⟩ y
     h (inl *) = l
     h (inr *) = reflexivity 𝓓 y

   b = f y       ≡⟨ ap f a ⟩
       f (∐ 𝓓 δ) ≡⟨ pr₂ (cts (𝟙 + 𝟙) α δ) ⟩
       ∐ 𝓔 ε     ∎
   c : f x ⊑⟨ 𝓔 ⟩ ∐ 𝓔 ε
   c = ∐-is-upperbound 𝓔 ε (inl *)
   γ : f x ⊑⟨ 𝓔 ⟩ f y
   γ = transport (λ - → f x ⊑⟨ 𝓔 ⟩ -) (b ⁻¹) c

{-
DCPO[_,_] : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → DCPO {(𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
DCPO[ (D  , _⊑_   , (s  , p  , r  , t  , a  , c )) ,
      (D' , _⊑'_  , (s' , p' , r' , t' , a' , c')) ] = D'' , _⊑''_ , s'' , p'' , r'' , t'' , a'' , c''
 where
  𝓓 : DCPO {{!𝓤!}} {{!𝓣!}}
  𝓓 = (D  , _⊑_   , (s  , p  , r  , t  , a  , c ))
  𝓔 : DCPO {{!𝓤'!}} {{!𝓣'!}}
  𝓔 = (D' , _⊑'_   , (s'  , p'  , r'  , t'  , a'  , c' ))
  D'' = Σ \(f : D → D') → is-continuous 𝓓 𝓔 f
  _⊑''_ : D'' → D'' → {!𝓤 ⊔ 𝓣'!} ̇
  (f , _) ⊑'' (g , _) = ∀ x → f x ⊑' g x
  s'' : is-set D''
  s'' = subsets-of-sets-are-sets (D → D') (is-continuous 𝓓 𝓔) (Π-is-set (fe {!𝓤!} {!𝓤'!}) (λ (x : D) → s')) λ {f} → being-continuous-is-a-prop 𝓓 𝓔 f
  p'' : (f g : D'') → is-prop (f ⊑'' g)
  p'' f g = Π-is-prop (fe {!𝓤!} {!𝓣'!}) (λ (x : D) → p' (pr₁ f x) (pr₁ g x))
  r'' : (f : D'') → f ⊑'' f
  r'' f x = r' (pr₁ f x)
  t'' : (f g h : D'') → f ⊑'' g → g ⊑'' h → f ⊑'' h
  t'' f g h l m x = t' (pr₁ f x) (pr₁ g x) (pr₁ h x) (l x) (m x)
  a'' : (f g : D'') → f ⊑'' g → g ⊑'' f → f ≡ g
  a'' f g l m = to-Σ-≡ (dfunext (fe {!𝓤!} {!𝓤'!}) (λ x → a' (pr₁ f x) (pr₁ g x) (l x) (m x)) ,
                        being-continuous-is-a-prop 𝓓 𝓔 (pr₁ g)
                             (transport (is-continuous 𝓓 𝓔) _ (pr₂ f)) (pr₂ g))
  c'' : (I : _ ̇) (α : I → D'') →
          is-directed _⊑''_ α → has-sup _⊑''_ α
  c'' I α δ = ((λ x → ∐ 𝓔 (λ i → pr₁ (α i) x) (ε x)) , φ-is-continuous) , γ
   where
    blah : (i : I) → is-continuous 𝓓 𝓔 (pr₁ (α i))
    blah = λ i → pr₂ (α i)
    ε : (x : D) → is-directed _⊑'_ (λ i → pr₁ (α i) x)
    ε  x i j = ∥∥-functor h (δ i j)
     where
      h : (Σ \(k : I) → (α i ⊑'' α k) × (α j ⊑'' α k))
        → Σ \(k : I) → (pr₁ (α i) x ⊑' pr₁ (α k) x) × (pr₁ (α j) x ⊑' pr₁ (α k) x)
      h (k , l , m) = k , (l x) , (m x)
    φ : D → D'
    φ x = ∐ 𝓔 (λ i → pr₁ (α i) x) (ε x)
    φ-is-monotone : is-monotone 𝓓 𝓔 φ
    φ-is-monotone = {!!}
    φ-is-continuous : is-continuous 𝓓 𝓔 φ
    φ-is-continuous J β κ = h , fine
     where
      h : (i j : J) → ∃ \(k : J) → (φ (β i) ⊑' φ (β k)) × (φ (β j) ⊑' φ (β k))
      h i j = ∥∥-functor g (κ i j)
       where
        g : (Σ \(k : J) → (β i ⊑ β k) × (β j ⊑ β k)) → Σ (\(k : J) → (φ (β i) ⊑' φ (β k)) × (φ (β j) ⊑' φ (β k)))
        g (k , l , m) = k , φ-is-monotone (β i) (β k) l , φ-is-monotone (β j) (β k) m
      fine : φ (∐ 𝓓 β κ) ≡ ∐ 𝓔 (λ x → φ (β x)) h
      fine = φ (∐ 𝓓 β κ) ≡⟨ refl ⟩
             ∐ 𝓔 (λ i → pr₁ (α i) (∐ 𝓓 β κ) ) (ε (∐ 𝓓 β κ)) ≡⟨ ap (λ - → {!∐ 𝓔 (λ i → -) (ε (∐ 𝓓 β κ))!}) {!!} ⟩
             {!∐ 𝓔 (λ i → ?) (ε (∐ 𝓓 β κ))!} ≡⟨ {!!} ⟩
             ∐ 𝓔 (λ x → φ (β x)) h ∎
    γ : is-sup _⊑''_ (φ , φ-is-continuous) α
    γ = {!!}

DCPO'[_,_] : DCPO {𝓤₁} {𝓤₀} → DCPO {𝓤₁} {𝓤₀} → DCPO {𝓥 ⁺} {𝓤₁}
DCPO'[_,_] = DCPO[_,_]

DCPO''[_,_] : DCPO {𝓤₁} {𝓤₁} → DCPO {𝓤₁} {𝓤₁} → DCPO {𝓥 ⁺} {𝓤₁}
DCPO''[_,_] = DCPO[_,_]
-}
\end{code}

But 𝓥 = 𝓤₀. So we if work with ℕ : 𝓤₁ for the underlying set of the
base type and ℕ : 𝓤₀ for the index set of the directed sets, we are
fine.
