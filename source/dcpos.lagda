Tom de Jong & Martin Escardo, 20 May 2019.

 * Directed complete posets.
 * Continuous maps.
 * Least fixed points.
 * Example: lifting.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-PropTrunc

module dcpos (pt : propositional-truncations-exist)
             (fe : FunExt)
       where

open PropositionalTruncation pt

open import SpartanMLTT
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module _
        {𝓤 𝓥 𝓣 : Universe}
        (D : 𝓤 ̇ )
        (_⊑_ : D → D → 𝓣 ̇ )
       where

 is-prop-valued : 𝓤 ⊔ 𝓣 ̇
 is-prop-valued = (x y : D) → is-prop(x ⊑ y)

 is-reflexive : 𝓤 ⊔ 𝓣 ̇
 is-reflexive = (x : D) → x ⊑ x

 is-transitive : 𝓤 ⊔ 𝓣 ̇
 is-transitive = (x y z : D) → x ⊑ y → y ⊑ z → x ⊑ z

 is-anti-symmetric : 𝓤 ⊔ 𝓣 ̇
 is-anti-symmetric = (x y : D) → x ⊑ y → y ⊑ x → x ≡ y

 _is-upperbound-of_ : {I : 𝓥 ̇ } (u : D) (α : I → D) → 𝓥 ⊔ 𝓣 ̇
 _is-upperbound-of_ {I} u α = (i : I) → α i ⊑ u

 _is-sup-of_ : {I : 𝓥 ̇ } → D → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 _is-sup-of_ {I} s α = (s is-upperbound-of α)
                     × ((u : D) → u is-upperbound-of α → s ⊑ u)

 has-sup : {I : 𝓥 ̇ } → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 has-sup {I} α = Σ \(s : D) → s is-sup-of α

 is-directed : {I : 𝓥 ̇ } → (I → D) → 𝓥 ⊔ 𝓣 ̇
 is-directed {I} α = (i j : I) → ∃ \(k : I) → (α i ⊑ α k) × (α j ⊑ α k)

 being-directed-is-a-prop : {I : 𝓥 ̇ } (α : I → D) → is-prop (is-directed α)
 being-directed-is-a-prop α = Π-is-prop (fe 𝓥 (𝓥 ⊔ 𝓣))
                               (λ i → Π-is-prop (fe 𝓥 (𝓥 ⊔ 𝓣))
                                       (λ j → ∥∥-is-a-prop ))

 is-directed-complete : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣  ̇
 is-directed-complete = (I : 𝓥 ̇ ) (α : I → D) → is-directed α → has-sup α

 dcpo-axioms : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ̇
 dcpo-axioms = is-set D × is-prop-valued × is-reflexive × is-transitive × is-anti-symmetric × is-directed-complete

 is-sup-of-is-a-prop : dcpo-axioms → {I : 𝓥 ̇ } (d : D) (α : I → D) → is-prop (d is-sup-of α)
 is-sup-of-is-a-prop (s , p , r , t , a , c) {I} d α = γ
  where
   γ : is-prop (d is-sup-of α)
   γ = ×-is-prop (Π-is-prop (fe 𝓥 𝓣) (λ (i : I) → p (α i) d))
                 (Π-is-prop (fe 𝓤 (𝓥 ⊔ 𝓣)) (λ (x : D) → Π-is-prop (fe (𝓥 ⊔ 𝓣) 𝓣) (λ l → p d x)))

 has-sup-is-a-prop : dcpo-axioms → {I : 𝓥 ̇ } (α : I → D) → is-prop (has-sup α)
 has-sup-is-a-prop (s , p , r , t , a , c) {I} α = γ
  where
   γ : is-prop (has-sup α)
   γ (j , (u , l)) (j' , (u' , l')) = to-Σ-≡ (q , is-sup-of-is-a-prop (s , p , r , t , a , c) j' α _ _)
    where
     q : j ≡ j'
     q = a j j' (l j' u') (l' j u)

 being-directed-complete-is-a-prop : dcpo-axioms → is-prop is-directed-complete
 being-directed-complete-is-a-prop a =
  Π-is-prop (fe (𝓥 ⁺) (𝓤 ⊔ 𝓥 ⊔ 𝓣))
   (λ I → Π-is-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥 ⊔ 𝓣))
           (λ α → Π-is-prop (fe (𝓥 ⊔ 𝓣) (𝓤 ⊔ 𝓥 ⊔ 𝓣)) (λ d → has-sup-is-a-prop a α)))

 dcpo-axioms-is-a-prop : is-prop dcpo-axioms
 dcpo-axioms-is-a-prop = iprops-are-props γ
  where
   γ : dcpo-axioms → is-prop dcpo-axioms
   γ (s , p , r , t , a , c) =
    ×-is-prop  (being-set-is-a-prop (fe 𝓤 𝓤))
    (×-is-prop (Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓣))
                 (λ (x : D) → Π-is-prop (fe 𝓤 𝓣)
                                (λ (y : D) → being-a-prop-is-a-prop (fe 𝓣 𝓣))))
    (×-is-prop (Π-is-prop (fe 𝓤 𝓣) (λ (x : D) → p x x))
    (×-is-prop (Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓣))
                 (λ (x : D) → Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓣))
                               (λ (y : D) → Π-is-prop (fe 𝓤 𝓣)
                                             (λ (z : D) → Π-is-prop (fe 𝓣 𝓣)
                                                           (λ (l : x ⊑ y) → Π-is-prop (fe 𝓣 𝓣)
                                                                             (λ (m : y ⊑ z) → p x z))))))
    (×-is-prop (Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓣))
                 (λ (x : D) → Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓣))
                               (λ y → Π-is-prop (fe 𝓣 (𝓤 ⊔ 𝓣))
                                       (λ (l : x ⊑ y) → Π-is-prop (fe 𝓣 𝓤)
                                                         λ (m : y ⊑ x) → s))))
              (being-directed-complete-is-a-prop (s , p , r , t , a , c))))))

module _ (𝓤 𝓥 𝓣 : Universe) where

 DCPO-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO-structure D = Σ \(_⊑_ : D → D → 𝓣 ̇ ) → dcpo-axioms {𝓤} {𝓥} {𝓣} D _⊑_

 DCPO : (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO = Σ \(D : 𝓤 ̇ ) → DCPO-structure D

 ⟨_⟩ : DCPO → 𝓤 ̇
 ⟨ D , _⊑_ , d ⟩ = D

 underlying-order : (𝓓 : DCPO) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓣 ̇
 underlying-order (D , _⊑_ , d) = _⊑_

 syntax underlying-order  𝓓 x y = x ⊑⟨ 𝓓 ⟩ y

 directed : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) → 𝓥 ⊔ 𝓣 ̇
 directed 𝓓 α = is-directed ⟨ 𝓓 ⟩ (underlying-order 𝓓) α

 ∐ : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) → directed 𝓓 α → ⟨ 𝓓 ⟩
 ∐ (D  , _⊑_   , (s  , p  , r  , t  , a  , c )) {I} α δ = pr₁ (c I α δ)

 ∐-is-sup : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) (δ : directed 𝓓 α)
          → ((i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 α δ)
          × ((u : ⟨ 𝓓 ⟩) → ((i : I) → α i ⊑⟨ 𝓓 ⟩ u) → ∐ 𝓓 α δ ⊑⟨ 𝓓 ⟩ u)
 ∐-is-sup (D  , _⊑_   , (s  , p  , r  , t  , a  , c )) {I} α δ = pr₂ (c I α δ)

 ∐-is-upperbound : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) (δ : directed 𝓓 α)
          → ((i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 α δ)
 ∐-is-upperbound 𝓓 {I} α δ = pr₁ (∐-is-sup 𝓓 α δ)

 ∐-is-lowerbound-of-upperbounds : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) (δ : directed 𝓓 α)
                                → ((u : ⟨ 𝓓 ⟩) → ((i : I) → α i ⊑⟨ 𝓓 ⟩ u) → ∐ 𝓓 α δ ⊑⟨ 𝓓 ⟩ u)
 ∐-is-lowerbound-of-upperbounds 𝓓 {I} α δ = pr₂ (∐-is-sup 𝓓 α δ)

 is-monotone : (𝓓 𝓔 : DCPO) → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → 𝓤 ⊔ 𝓣 ̇
 is-monotone 𝓓 𝓔 f = (x y : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ y → f x ⊑⟨ 𝓔 ⟩ f y

 is-continuous : (𝓓 𝓔 : DCPO) → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ̇
 is-continuous 𝓓 𝓔 f = (I : 𝓥 ̇) (α : I → ⟨ 𝓓 ⟩) (δ : directed 𝓓 α)
                     → Σ \(ε : directed 𝓔 (f ∘ α)) → f (∐ 𝓓 α δ) ≡ ∐ 𝓔 (f ∘ α) ε

 being-continuous-is-a-prop : (𝓓 𝓔 : DCPO) (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → is-prop (is-continuous 𝓓 𝓔 f)
 being-continuous-is-a-prop 𝓓 (E  , _⊑'_   , (s'  , p'  , r'  , t'  , a'  , c' )) f =
   Π-is-prop (fe (𝓥 ⁺) (𝓤 ⊔ 𝓥 ⊔ 𝓣))
    (λ I → Π-is-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥 ⊔ 𝓣))
            (λ α → Π-is-prop (fe (𝓥 ⊔ 𝓣) (𝓤 ⊔ 𝓥 ⊔ 𝓣))
                     (λ δ → Σ-is-prop (being-directed-is-a-prop ⟨ 𝓔 ⟩
                                          (underlying-order 𝓔)
                                          (f ∘ α))
                                      λ ε → s')))
  where
   𝓔 : DCPO
   𝓔 = (E  , _⊑'_   , (s'  , p'  , r'  , t'  , a'  , c' ))

 continuous-functions-are-monotone : (𝓓 𝓔 : DCPO) (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                                   → is-continuous 𝓓 𝓔 f → is-monotone 𝓓 𝓔 f
 continuous-functions-are-monotone (D  , _⊑_   , (s  , p  , r  , t  , a  , c ))
                                   (E  , _⊑'_   , (s'  , p'  , r'  , t'  , a'  , c' )) f cts x y l = γ
  where
   𝓓 𝓔 : DCPO
   𝓓 = (D  , _⊑_   , (s  , p  , r  , t  , a  , c ))
   𝓔 = (E  , _⊑'_   , (s'  , p'  , r'  , t'  , a'  , c' ))
   α : 𝟙 {𝓥} + 𝟙 {𝓥} → D
   α (inl *) = x
   α (inr *) = y
   δ : directed 𝓓 α
   δ (inl *) (inl *) = ∣ inr * , l   , l   ∣
   δ (inl *) (inr *) = ∣ inr * , l   , r y ∣
   δ (inr *) (inl *) = ∣ inr * , r y , l   ∣
   δ (inr *) (inr *) = ∣ inr * , r y , r y ∣
   ε : directed 𝓔 (f ∘ α)
   ε = pr₁ (cts (𝟙 + 𝟙) α δ)
   q : f (∐ 𝓓 α δ) ≡ ∐ 𝓔 (f ∘ α) ε
   q = pr₂ (cts (𝟙 + 𝟙) α δ)
   blah : y ≡ ∐ 𝓓 α δ
   blah = a y (∐ 𝓓 α δ)
           (∐-is-upperbound 𝓓 α δ (inr *))
           (∐-is-lowerbound-of-upperbounds 𝓓 α δ y h)
    where
     h : (i : 𝟙 + 𝟙) → α i ⊑ y
     h (inl *) = l
     h (inr *) = r y

   bb : f y ≡ ∐ 𝓔 (f ∘ α) ε
   bb = ap f blah ∙ q
   bbb' : (f ∘ α) (inl *) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 (f ∘ α) ε
   bbb' = ∐-is-upperbound 𝓔 (f ∘ α) ε (inl *)
   bbb : f x ⊑⟨ 𝓔 ⟩ ∐ 𝓔 (f ∘ α) ε
   bbb = bbb'
   γ : f x ⊑' f y
   γ = transport (λ - → f x ⊑' -) (bb ⁻¹) bbb


DCPO[_,_] : DCPO 𝓤 𝓥 𝓣 → DCPO {!!} 𝓥 𝓣 → DCPO {!!} {!!} {!!}
DCPO[ (D  , _⊑_   , (s  , p  , r  , t  , a  , c )) ,
      (D' , _⊑'_  , (s' , p' , r' , t' , a' , c')) ] = {!!} -- D'' , _⊑''_ , {!!} , p'' , r'' , t'' , a'' , c''
 where
  𝓓 : DCPO {!𝓤!} {!𝓥!} {!𝓣!}
  𝓓 = (D  , _⊑_   , (s  , p  , r  , t  , a  , c ))
  𝓔 : DCPO {!𝓤!} {!𝓥!} {!𝓣!}
  𝓔 = (D' , _⊑'_   , (s'  , p'  , r'  , t'  , a'  , c' ))
  D'' = Σ \(f : D → D') → is-continuous {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 𝓔 f
{-
  _⊑''_ : D'' → D'' → {!𝓤 ⊔ 𝓣!} ̇
  (f , _) ⊑'' (g , _) = ∀ x → f x ⊑' g x
  s'' : is-set D''
  s'' = {!!}
  p'' : (f g : D'') → is-prop (f ⊑'' g)
  p'' f g = Π-is-prop (fe {!𝓤!} {!𝓣!}) (λ (x : D) → p' (pr₁ f x) (pr₁ g x))
  r'' : (f : D'') → f ⊑'' f
  r'' f x = r' (pr₁ f x)
  t'' : (f g h : D'') → f ⊑'' g → g ⊑'' h → f ⊑'' h
  t'' f g h l m x = t' (pr₁ f x) (pr₁ g x) (pr₁ h x) (l x) (m x)
  a'' : (f g : D'') → f ⊑'' g → g ⊑'' f → f ≡ g
  a'' f g l m = to-Σ-≡ (dfunext (fe {!𝓤!} {!𝓤!}) (λ x → a' (pr₁ f x) (pr₁ g x) (l x) (m x)) ,
                        being-continuous-is-a-prop {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 𝓔 (pr₁ g)
                             (transport (is-continuous {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 𝓔) _ (pr₂ f)) (pr₂ g))
  c'' : (I : _ ̇) (α : I → D'') →
          is-directed D'' _⊑''_ α → has-sup D'' _⊑''_ α
  c'' I α δ = ((λ x → ∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓔 (λ i → pr₁ (α i) x) (ε x)) , φ-is-continuous) , γ
   where
    blah : (i : I) → is-continuous {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 𝓔 (pr₁ (α i))
    blah = λ i → pr₂ (α i)
    ε : (x : D) → is-directed D' _⊑'_ (λ i → pr₁ (α i) x)
    ε  x i j = ∥∥-functor h (δ i j)
     where
      h : (Σ \(k : I) → (α i ⊑'' α k) × (α j ⊑'' α k))
        → Σ \(k : I) → (pr₁ (α i) x ⊑' pr₁ (α k) x) × (pr₁ (α j) x ⊑' pr₁ (α k) x)
      h (k , l , m) = k , (l x) , (m x)
    φ : D → D'
    φ x = ∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓔 (λ i → pr₁ (α i) x) (ε x)
    φ-is-monotone : is-monotone {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 𝓔 φ
    φ-is-monotone = {!!}
    φ-is-continuous : is-continuous {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 𝓔 φ
    φ-is-continuous J β κ = h , fine
     where
      h : (i j : J) → ∃ \(k : J) → (φ (β i) ⊑' φ (β k)) × (φ (β j) ⊑' φ (β k))
      h i j = ∥∥-functor g (κ i j)
       where
        g : (Σ \(k : J) → (β i ⊑ β k) × (β j ⊑ β k)) → Σ (\(k : J) → (φ (β i) ⊑' φ (β k)) × (φ (β j) ⊑' φ (β k)))
        g (k , l , m) = k , φ-is-monotone (β i) (β k) l , φ-is-monotone (β j) (β k) m
      fine : φ (∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 β κ) ≡ ∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓔 (λ x → φ (β x)) h
      fine = φ (∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 β κ) ≡⟨ refl ⟩
             ∐ {!𝓤!} {!!} {!!} 𝓔 (λ i → pr₁ (α i) (∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 β κ) ) (ε (∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 β κ)) ≡⟨ ap (λ - → {!∐ {!𝓤!} {!!} {!!} 𝓔 (λ i → -) (ε (∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 β κ))!}) {!!} ⟩
             {!∐ {!𝓤!} {!!} {!!} 𝓔 (λ i → ?) (ε (∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓓 β κ))!} ≡⟨ {!!} ⟩
             ∐ {!𝓤!} {!𝓥!} {!𝓣!} 𝓔 (λ x → φ (β x)) h ∎
    γ : _is-sup-of_ D'' _⊑''_ (φ , φ-is-continuous) α
    γ = {!!}
-}


\end{code}
