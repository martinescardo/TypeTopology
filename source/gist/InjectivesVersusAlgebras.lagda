Martin Escardo, 22nd October 2024

This file is now obsolete. The main ideas are at
InjectiveTypes.Algebra, in a better way. There are still a few
speculative ideas towards the end. In any case, I will probably
delete this file soon.

Incomplete blackboard thoughts on injectives as algebras of the
partial-map classifier monad, also known as the lifting monad.

Comment added 13th Feb 2025.

The original paper on injectives in HoTT/UF characterizes the
injective types as the algebras of the lifting monad. This file
records incomplete thoughts trying to make this more precise. There is
more to be said that is not written down here (mainly for lack of
time, but also because there are things we don't know and are
speculative at the moment).

At the moment, no mathematical prose motivating the above is
given. When the file is ready, if it is ever ready, it will be moved
to the InjectiveTypes folder, with such suitable prose. At the moment,
these are just formal versions of thoughts for myself, which I choose
to be publicly visible. In any case, if this file succeeds in its
objective, the final form will be completely different. This is just a
blackboard file.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module gist.InjectivesVersusAlgebras
        (fe : FunExt)
       where

fe' : Fun-Ext
fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence

module _ (𝓤 𝓥 : Universe)
         (D : 𝓤 ⊔ 𝓥 ̇ )
         (⨆ : {P : 𝓤 ̇ } → is-prop P → (P → D) → D)
         (⨆-property : (P : 𝓤 ̇ )
                        (i : is-prop P)
                        (f : P → D)
                        (p : P)
                      → ⨆ i f ＝ f p)
       where

 ⨆-change-of-variable : is-univalent 𝓤
                       → {P : 𝓤 ̇ } (i : is-prop P)
                         {Q : 𝓤 ̇ } (j : is-prop Q)
                         (e : P ≃ Q)
                         (f : P → D)
                       → ⨆ i f ＝ ⨆ j (f ∘ ⌜ e ⌝⁻¹)
 ⨆-change-of-variable ua {P} i {Q} j e f = JEq ua P A I Q e j
  where
   A : (Q : 𝓤 ̇ ) → P ≃ Q → 𝓤 ⊔ 𝓥 ̇
   A Q e = (j : is-prop Q) → ⨆ i f ＝ ⨆ j (f ∘ ⌜ e ⌝⁻¹)

   I : A P (≃-refl P)
   I j = ap (λ - → ⨆ - f) (being-prop-is-prop fe' i j)

 ⨆-assoc : 𝓤 ⁺ ⊔ 𝓥 ̇
 ⨆-assoc =
    (P : 𝓤 ̇ )
    (Q : P → 𝓤 ̇ )
    (i : is-prop P)
    (j : (p : P) → is-prop (Q p))
    (k : is-prop (Σ Q))
    (f : Σ Q → D)
  → ⨆ i (λ p → ⨆ (j p) (λ q → f (p , q))) ＝ ⨆ k f

 module _ {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
          (j : X → Y)
          (e : is-embedding j)
          (f : X → D)
        where

  extension : Y → D
  extension y = ⨆ (e y) (λ ((x , _) : fiber j y) → f x)

  extension-property : (x : X) → extension (j x) ＝ f x
  extension-property x = ⨆-property
                          (fiber j (j x))
                          (e (j x))
                          (λ ((x , _) : fiber j (j x)) → f x)
                          (x , refl)

 iter-extension : is-univalent 𝓤
                → ⨆-assoc
                → {X : 𝓤 ̇ } {Y : 𝓤 ̇ } {Z : 𝓤 ̇ }
                  (f : X → D)
                  (j : X → Y)
                  (k : Y → Z)
                  (j-emb : is-embedding j)
                  (k-emb : is-embedding k)
                → extension k k-emb (extension j j-emb f)
                ∼ extension (k ∘ j) (∘-is-embedding j-emb k-emb) f
 iter-extension ua a f j k j-emb k-emb z = I
  where
   II : ⨆
         (k-emb z)
         (λ ((y , q) : fiber k z) → ⨆
                                     (j-emb y)
                                     (λ ((x , p) : fiber j y) → f x))
     ＝ ⨆
        (Σ-is-prop (k-emb z) (λ t → j-emb (pr₁ t)))
        (λ (w : Σ v ꞉ fiber k z , fiber j (pr₁ v)) → f (pr₁ (pr₂ w)))
   II = a (fiber k z)
          (λ w → fiber j (pr₁ w))
          (k-emb z)
          (λ t → j-emb (pr₁ t))
          (Σ-is-prop (k-emb z) (λ t → j-emb (pr₁ t)))
          (λ w → f (pr₁ (pr₂ w)))

   III : ⨆
          (Σ-is-prop (k-emb z) (λ t → j-emb (pr₁ t)))
          (λ (w : Σ v ꞉ fiber k z , fiber j (pr₁ v)) → f (pr₁ (pr₂ w)))
       ＝ ⨆
          (∘-is-embedding j-emb k-emb z)
          (λ ((x , _) : fiber (k ∘ j) z) → f x)
   III = ⨆-change-of-variable ua _ _ (≃-sym (fiber-of-composite j k z)) _

   I : ⨆
        (k-emb z)
        (λ ((y , _) : fiber k z) → ⨆
                                    (j-emb y)
                                    (λ ((x , _) : fiber j y) → f x))
    ＝ ⨆
        (∘-is-embedding j-emb k-emb z)
        (λ ((x , _) : fiber (k ∘ j) z) → f x)
   I = II ∙ III

module _ (𝓤 : Universe)
         (D : 𝓤 ̇ )
         (_/_ : {X : 𝓤 ̇ } {Y : 𝓤 ̇ } → (X → D) → (X ↪ Y) → (Y → D))
         (extension-property : {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (f : X → D) (j : X ↪ Y)
                             →  f / j ∘ ⌊ j ⌋ ∼ f)
       where

 ⨆ : {P : 𝓤 ̇ } → is-prop P → (P → D) → D
 ⨆ {P} P-is-prop g = (g / (embedding-into-𝟙 P P-is-prop)) ⋆

 ⨆-change-of-variable' : is-univalent 𝓤
                        → {P : 𝓤 ̇ } (i : is-prop P)
                          {Q : 𝓤 ̇ } (j : is-prop Q)
                          (e : P ≃ Q)
                          (f : P → D)
                        → ⨆ i f ＝ ⨆ j (f ∘ ⌜ e ⌝⁻¹)
 ⨆-change-of-variable' ua {P} i {Q} j e f = JEq ua P A I Q e j
  where
   A : (Q : 𝓤 ̇ ) → P ≃ Q → 𝓤 ̇
   A Q e = (j : is-prop Q) → ⨆ i f ＝ ⨆ j (f ∘ ⌜ e ⌝⁻¹)

   I : A P (≃-refl P)
   I j = ap (λ - → ⨆ - f) (being-prop-is-prop fe' i j)

 fiber-map : {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (f : X → D) (j : X ↪ Y) (y : Y)
           → fiber ⌊ j ⌋ y → D
 fiber-map f j y (x , _) = f x

 _/̇_ : {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
      → (X → D)
      → (X ↪ Y)
      → Y → D
 f /̇ j = λ y → ⨆ (⌊ j ⌋-is-embedding y) (fiber-map f j y)

 _ : {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
     (f : X → D)
     (j : X ↪ Y)
   → f /̇ j ＝ (λ y → (fiber-map f j y / fiber-to-𝟙 j y) ⋆)
 _ = λ f j → refl

 ⨆-property : (P : 𝓤 ̇ )
               (i : is-prop P)
               (f : P → D)
               (p : P)
              → ⨆ i f ＝ f p
 ⨆-property P i f = extension-property f (embedding-into-𝟙 P i)

 extension-assoc : 𝓤 ⁺ ̇
 extension-assoc = {X : 𝓤 ̇ } {Y : 𝓤 ̇ } {Z : 𝓤 ̇ }
                   (f : X → D) (j : X ↪ Y) (k : Y ↪ Z)
                 → (f / j) / k ∼ f / (k ∘↪ j)

 Extensions-are-Pointwise : 𝓤 ⁺ ̇
 Extensions-are-Pointwise = {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (f : X → D) (j : X ↪ Y)
                          → f / j ∼ f /̇ j

 ⨆-assoc' : Extensions-are-Pointwise
           → is-univalent 𝓤
           → extension-assoc
           → (P : 𝓤 ̇ )
             (Q : P → 𝓤 ̇ )
             (a : is-prop P)
             (b : (p : P) → is-prop (Q p))
             (c : is-prop (Σ Q))
             (f : Σ Q → D)
           → ⨆ a (λ p → ⨆ (b p) (λ q → f (p , q))) ＝ ⨆ c f
 ⨆-assoc' extensions-are-pointwise ua ea P Q a b c f
  = ⨆ a (λ p → ⨆ (b p) (λ q → f (p , q))) ＝⟨ ap (⨆ a) II ⟩
    ⨆ a (f / u)                           ＝⟨refl⟩
    ((f / u) / v) ⋆                       ＝⟨ ea f u v ⋆ ⟩
    (f / (v ∘↪ u)) ⋆                      ＝⟨ ap (λ - → (f / -) ⋆) III ⟩
    (f / w) ⋆                             ＝⟨refl⟩
    ⨆ c f                                 ∎
      where
       u : Σ Q ↪ P
       u = pr₁ , pr₁-is-embedding b

       v : P ↪ 𝟙
       v = embedding-into-𝟙 P a

       w : Σ Q ↪ 𝟙
       w = embedding-into-𝟙 (Σ Q) c

       I : (p : P)
         → ⨆ (⌊ u ⌋-is-embedding p) (fiber-map f u p)
         ＝ ⨆ (b p) (λ q → f (p , q))
       I p = ⨆-change-of-variable' ua
              (⌊ u ⌋-is-embedding p)
              (b p)
              I₀
              (fiber-map f u p)
        where
         g : fiber ⌊ u ⌋ p → Q p
         g ((p' , q) , _) = transport Q (a p' p) q

         h : Q p → fiber ⌊ u ⌋ p
         h q = (p , q) , a (⌊ u ⌋ (p , q)) p

         I₀ : fiber ⌊ u ⌋ p ≃ Q p
         I₀ = g ,
              logical-equivs-of-props-are-equivs (⌊ u ⌋-is-embedding p) (b p) g h

       II : (λ p → ⨆ (b p) (λ q → f (p , q))) ＝ f / u
       II = dfunext fe' (λ p →
             ⨆ (b p) (λ q → f (p , q))                  ＝⟨ (I p)⁻¹ ⟩
             ⨆ (⌊ u ⌋-is-embedding p) (fiber-map f u p) ＝⟨refl⟩
             (f /̇ u) p                                  ＝⟨ II' p ⟩
             (f / u) p                                  ∎)
              where
               II' = λ p → (extensions-are-pointwise f u p)⁻¹

       III : (v ∘↪ u) ＝ w
       III = to-subtype-＝ (being-embedding-is-prop fe') refl

\end{code}

Added 28 Feb 2025 incomplete, resumed 19th May 2025.

It is natural to conjecture that the Π- and Σ-ainjectivity structures
are natural. But even weak naturality fails.

\begin{code}

open import InjectiveTypes.Blackboard fe hiding (ηΠ ; ηΣ)

module unnaturality where

 weak-naturalityΠ : 𝓤ω
 weak-naturalityΠ =
    (𝓤 𝓥 𝓦 𝓣 𝓣' : Universe)
    (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) (X : 𝓦 ̇ ) (Y : 𝓣 ̇ )
    (k : A → B)
    (j : X → Y)
    (g : A → X)
    (h : B → Y)
    (f : X → 𝓣' ̇ )
    (square : j ∘ g ∼ h ∘ k)
    (b : B)
  → ((f ∘ g) / k) b
  → (f / j) (h b)

 weak-naturalityΣ : 𝓤ω
 weak-naturalityΣ =
    (𝓤 𝓥 𝓦 𝓣 𝓣' : Universe)
    (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) (X : 𝓦 ̇ ) (Y : 𝓣 ̇ )
    (k : A → B)
    (j : X → Y)
    (g : A → X)
    (h : B → Y)
    (f : X → 𝓣' ̇ )
    (square : j ∘ g ∼ h ∘ k)
    (b : B)
  → (f ∖ j) (h b)
  → ((f ∘ g) ∖ k) b

 weak-naturalityΠ-fails : weak-naturalityΠ → 𝟘
 weak-naturalityΠ-fails wn =
  wn 𝓤₀ 𝓤₀ 𝓤₀ 𝓤₀ 𝓤₀
     𝟘 𝟙 𝟙 𝟙
     unique-to-𝟙
     id
     unique-to-𝟙
     id
     (λ _ → 𝟘)
     (λ (a : 𝟘) → refl)
     ⋆
     pr₁
     (⋆ , refl)

 weak-naturalityΣ-fails : weak-naturalityΣ → 𝟘
 weak-naturalityΣ-fails wn = pr₁ (pr₁ t)
  where
   t : (𝟘 × (⋆ ＝ ⋆)) × 𝟙
   t = wn 𝓤₀ 𝓤₀ 𝓤₀ 𝓤₀ 𝓤₀
          𝟘 𝟙 𝟙 𝟙
          unique-to-𝟙
          id
          unique-to-𝟙
          id
          (λ _ → 𝟙)
          (λ (a : 𝟘) → refl)
          ⋆
          ((⋆ , refl) , ⋆)

\end{code}

But we have pullback naturality.

For simplicity, instead of working with a square as above and assuming
that it is a pullback, we start with h,j as above and define A to be
their pullback.

\begin{code}

module pullback-naturality-for-Σ-and-Π
         {B : 𝓥 ̇ } {X : 𝓦 ̇ } {Y : 𝓣 ̇ }
         (h : B → Y)
         (j : X → Y)
       where

 A : 𝓦 ⊔ 𝓥 ⊔ 𝓣 ̇
 A = Σ x ꞉ X , Σ b ꞉ B , j x ＝ h b

 g : A → X
 g (x , b , e) = x

 k : A → B
 k (x , b , e) = b

 square : j ∘ g ∼ h ∘ k
 square (x , b , e) = e

 module _ (f : X → 𝓣' ̇ ) where

  forthΠ : (b : B) → (f / j) (h b) → ((f ∘ g) / k) b
  forthΠ .(k a) ϕ (a , refl) = ϕ (g a , square a)

  backΠ : (b : B) → ((f ∘ g) / k) b → (f / j) (h b)
  backΠ b γ (x , e) = γ ((x , b , e) , refl)

  ηΠ' : (b : B) (γ : ((f ∘ g) / k) b) → forthΠ b (backΠ b γ) ∼ γ
  ηΠ' b γ ((x , .b , e) , refl) = refl

  εΠ' : (b : B) (ϕ : (f / j) (h b)) → backΠ b (forthΠ b ϕ) ∼ ϕ
  εΠ' b ϕ (a , e) = refl

  ηΠ : (b : B) → forthΠ b ∘ backΠ b ∼ id
  ηΠ b γ = dfunext fe' (ηΠ' b γ)

  εΠ : (b : B) → backΠ b ∘ forthΠ b ∼ id
  εΠ b ϕ = dfunext fe' (εΠ' b ϕ)

  Π-naturality : (b : B) → (f / j) (h b) ≃ ((f ∘ g) / k) b
  Π-naturality b = qinveq
                    (forthΠ b)
                    (backΠ b , εΠ b , ηΠ b)

  forthΣ : (b : B) → (f ∖ j) (h b) → ((f ∘ g) ∖ k) b
  forthΣ b ((x , e) , y) = ((x , b , e) , refl) , y

  backΣ : (b : B) → ((f ∘ g) ∖ k) b → (f ∖ j) (h b)
  backΣ b (((x , b , e) , refl) , y) = (x , e) , y

  ηΣ : (b : B) → forthΣ b ∘ backΣ b ∼ id
  ηΣ b (((x , b , e) , refl) , y) = refl

  εΣ : (b : B) → backΣ b ∘ forthΣ b ∼ id
  εΣ b ((x , e) , y) = refl

  Σ-naturality : (b : B) → (f ∖ j) (h b) ≃ ((f ∘ g) ∖ k) b
  Σ-naturality b = qinveq
                    (forthΣ b)
                    (backΣ b , εΣ b , ηΣ b)

\end{code}

We now generalize the above to any aflabbiness structure, but make the
universes less general for now.

TODO. Make the universes as general as possible. (This will work
easily if we instead assume that we are given an arbitrary pullback.)

\begin{code}

module pullback-naturality-for-ainjectivity-induced-by-aflabbiness
         {B : 𝓤 ̇ } {X : 𝓤 ̇ } {Y : 𝓤 ̇ }
         (h : B → Y)
         (j : X → Y)
       where

 A : 𝓤 ̇
 A = Σ x ꞉ X , Σ b ꞉ B , j x ＝ h b

 g : A → X
 g (x , b , e) = x

 k : A → B
 k (x , b , e) = b

 square : j ∘ g ∼ h ∘ k
 square (x , b , e) = e

 module _ (D : 𝓦 ̇ )
          (φ : aflabby D 𝓤)
          (j-is-embedding : is-embedding j)
          (f : X → D)
        where

  ϕ : (P : 𝓤 ̇ ) → is-prop P → (P → D) → D
  ϕ P i f = pr₁ (φ P i f)

  ϕ-change-of-variable : is-univalent 𝓤
                       → {P : 𝓤 ̇ } (i : is-prop P)
                         {Q : 𝓤 ̇ } (j : is-prop Q)
                         (e : P ≃ Q)
                         (f : P → D)
                       → ϕ P i f ＝ ϕ Q j (f ∘ ⌜ e ⌝⁻¹)
  ϕ-change-of-variable ua {P} i {Q} j e f = JEq ua P C I Q e j
   where
    C : (Q : 𝓤 ̇ ) → P ≃ Q → 𝓤 ⊔ 𝓦 ̇
    C Q e = (j : is-prop Q) → ϕ P i f ＝ ϕ Q j (f ∘ ⌜ e ⌝⁻¹)

    I : C P (≃-refl P)
    I j = ap (λ - → ϕ P - f) (being-prop-is-prop fe' i j)

  D-is-ainjective : ainjective-type D 𝓤 𝓤
  D-is-ainjective = aflabby-types-are-ainjective D φ

  _∣_ : {X : 𝓤 ̇ } {Y : 𝓤 ̇ } → (X → D) → (X ↪ Y) → (Y → D)
  (f ∣ (j , j-is-embedding)) y = ϕ (fiber j y) (j-is-embedding y) (f ∘ pr₁)

\end{code}

The following is just the fact that pullbacks of embeddings are
embeddings.

\begin{code}

  k-is-embedding : is-embedding k
  k-is-embedding b = I
   where
    have : fiber k b ＝ (Σ (x , b' , e) ꞉ A ,  b' ＝ b)
    have = refl

    I : is-prop (fiber k b)
    I ((x₁ , .b , e₁) , refl) ((x₂ , .b , e₂) , refl) = III II
     where
      II : (x₁ , e₁) ＝ (x₂ , e₂)
      II = j-is-embedding (h b) (x₁ , e₁) (x₂ , e₂)

      III : {σ τ : fiber j (h b)}
          → σ ＝ τ
          → ((pr₁ σ , b , pr₂ σ) , refl)
          ＝[ fiber k b ]
            ((pr₁ τ , b , pr₂ τ) , refl)
      III refl = refl

  𝕛 : X ↪ Y
  𝕛 = (j , j-is-embedding)

  𝕜 : A ↪ B
  𝕜 = (k , k-is-embedding)

  naturality : is-univalent 𝓤 → (b : B) → (f ∣ 𝕛) (h b) ＝ ((f ∘ g) ∣ 𝕜) b
  naturality ua b =
   (f ∣ 𝕛) (h b)                                       ＝⟨refl⟩
   ϕ (fiber j (h b)) (j-is-embedding (h b)) (f ∘ pr₁) ＝⟨ I ⟩
   ϕ (fiber k b) (k-is-embedding b) (f ∘ pr₁ ∘ u)     ＝⟨ II ⟩
   ϕ (fiber k b) (k-is-embedding b) (f ∘ g ∘ pr₁)     ＝⟨refl⟩
   ((f ∘ g) ∣ 𝕜) b                                     ∎
    where
     u : fiber k b → fiber j (h b)
     u ((x , b' , e) , refl) = x , e

     v : fiber j (h b) → fiber k b
     v (x , e) = (x , b , e) , refl

     I = ϕ-change-of-variable
          ua
          (j-is-embedding (h b))
          (k-is-embedding b)
          (logically-equivalent-props-are-equivalent
            (j-is-embedding (h b))
            (k-is-embedding b)
            v
            u)
          (f ∘ pr₁)

     H : f ∘ pr₁ ∘ u ∼ f ∘ g ∘ pr₁
     H ((x , b' , e) , refl) = refl

     II = ap (ϕ (fiber k b) (k-is-embedding b)) (dfunext fe' H)

\end{code}

Digression with speculative ideas.

\begin{code}

module lifting-algebras-as-categories
        (𝓤 : Universe)
        (D : 𝓤 ⁺ ̇ )
        (⨆ : {P : 𝓤 ̇ } → is-prop P → (P → D) → D)
        (⨆-property : (P : 𝓤 ̇ )
                       (i : is-prop P)
                       (f : P → D)
                       (p : P)
                     → ⨆ i f ＝ f p)
       where

\end{code}

A definedness predicate, generalizing the above examples.

\begin{code}

  δ : D → 𝓤 ⁺ ̇
  δ d = (P : 𝓤 ̇ ) (i : is-prop P) → ⨆ i (λ (p : P) → d) ＝ d → P

  δ' : D → 𝓤 ⁺ ̇
  δ' d = (P : 𝓤 ̇ ) (i : is-prop P) (f : P → D) → ⨆ i f ＝ d → P

  δ'-is-prop-valued : (d : D) → is-prop (δ' d)
  δ'-is-prop-valued d = Π₄-is-prop fe' (λ _ i _ _ → i)

  δ-is-prop-valued : (d : D) → is-prop (δ d)
  δ-is-prop-valued d = Π₃-is-prop fe' (λ _ i _ → i)

  δ-gives-δ' : (d : D) → δ d → δ' d
  δ-gives-δ' d a' P i f e =
   a' P i (⨆ i (λ _ → d) ＝⟨ ap (⨆ i) (dfunext fe' I) ⟩
   ⨆ i f                 ＝⟨ e ⟩
   d                      ∎)
    where
     I = λ p → d     ＝⟨ e ⁻¹ ⟩
               ⨆ i f ＝⟨ ⨆-property P i f p ⟩
               f p   ∎

  δ'-gives-δ : (d : D) → δ' d → δ d
  δ'-gives-δ d a P i = a P i (λ _ → d)

\end{code}

So they are equivalent because logically equivalent propositional are
(typally) equivalent.

I wrote "hom x y" instead of "x ⊑ y" in a previous version of this
file. This would be indeed more accurate.

The idea is that an algebra of the lifting monad has the structure of
an ∞-category which is almost an ∞-groupoid, except for having a
bottom element.

\begin{code}

  _⊑_ : D → D → 𝓤 ⁺ ̇
  x ⊑ y = δ x → x ＝ y

  δ-is-monotone : {x y : D} → x ⊑ y → δ x → δ y
  δ-is-monotone α a = transport δ (α a) a

  δ-property : (P : 𝓤 ̇ ) (i : is-prop P) (f : P → D)
             → δ (⨆ i f)
             → P
  δ-property P i f a = a P i e
   where
    e : ⨆ i (λ _ → ⨆ i f) ＝ ⨆ i f
    e = ap (⨆ i) (dfunext fe' (⨆-property P i f))

  ⊥ : D
  ⊥ = ⨆ 𝟘-is-prop unique-from-𝟘

  ⊥-is-undefined : ¬ δ ⊥
  ⊥-is-undefined a = 𝟘-elim (δ-property 𝟘 𝟘-is-prop 𝟘-elim a)

\end{code}

The idea of δ x is that it gives a positive (but still propositional)
way of saying that x is different from ⊥.

\begin{code}

  ⊥-least : (x : D) → ⊥ ⊑ x
  ⊥-least x a = 𝟘-elim (⊥-is-undefined a)

  being-upper-bound-of-⊥-is-prop : (x : D) → is-prop (⊥ ⊑ x)
  being-upper-bound-of-⊥-is-prop x α β =
   dfunext fe' (λ (a : δ ⊥) → 𝟘-elim (⊥-is-undefined a))

  being-upper-bound-of-⊥-is-singleton : (x : D) → is-singleton (⊥ ⊑ x)
  being-upper-bound-of-⊥-is-singleton x =
   pointed-props-are-singletons
    (⊥-least x)
    (being-upper-bound-of-⊥-is-prop x)

\end{code}

The ∞-categorical structure alluded above.

\begin{code}

  idD : {x : D} → x ⊑ x
  idD {x} a = refl

  _□_ : {x y z : D} → x ⊑ y → y ⊑ z → x ⊑ z
  α □ β = λ a → α a ∙ β (δ-is-monotone α a)

  idD-left : {x y : D} (α : x ⊑ y)
           → α □ idD ∼ α
  idD-left {x} {y} α a = refl

  idD-right : {x y : D} (α : x ⊑ y)
            → idD □ α ∼ α
  idD-right {x} {y} α a = refl-left-neutral

  assocD : {x y z t : D} (α : x ⊑ y) (β : y ⊑ z) (γ : z ⊑ t)
         → α □ (β □ γ) ∼ (α □ β) □ γ
  assocD {x} {y} {z} {t} α β γ a =
   (α □ (β □ γ)) a    ＝⟨refl⟩
   α a ∙ (β b ∙ γ c)  ＝⟨ (∙assoc (α a) (β b) (γ c))⁻¹ ⟩
   (α a ∙ β b) ∙ γ c  ＝⟨ I ⟩
   (α a ∙ β b) ∙ γ c' ＝⟨refl⟩
   ((α □ β) □ γ) a    ∎
    where
     b : δ y
     b = δ-is-monotone α a

     c c' : δ z
     c  = δ-is-monotone β b
     c' = δ-is-monotone (α □ β) a

     I = ap (λ - → (α a ∙ β b) ∙ γ -) (δ-is-prop-valued z c c')

  colimit-conjecture : 𝓤 ⁺ ̇
  colimit-conjecture =
   (P : 𝓤 ̇ ) (i : is-prop P) (f : P → D)
      → Σ α ꞉ ((p : P) → f p ⊑ ⨆ i f)
            , ((u : D) (β : (p : P) → f p ⊑ u)
                  → ∃! γ ꞉ ⨆ i f ⊑ u , ((p : P) → α p □ γ ＝ β p))

  colimit-conjecture-particular : 𝓤 ⁺ ̇
  colimit-conjecture-particular =
   (d : D)
      → Σ α ꞉ d ＝ d
            , ((u : D) (β : d ＝ u)
                  → ∃! γ ꞉ d ＝ u , (α ∙ γ ＝ β))

  sanity-check : colimit-conjecture-particular
  sanity-check d = (refl , ϕ)
   where
    ϕ : (u : D) (β : d ＝ u) → ∃! γ ꞉ d ＝ u , (refl ∙ γ ＝ β)
    ϕ u = equivs-are-vv-equivs (refl ∙_) II
     where
      I : (refl ∙_) ∼ id
      I γ = refl-left-neutral

      II : is-equiv (refl ∙_)
      II = equiv-closed-under-∼ id (refl ∙_) (id-is-equiv (d ＝ u)) I

\end{code}

More modestly, for now we have the following weakening of the conjecture.

\begin{code}

  ⨆-is-lub
    : (P : 𝓤 ̇ ) (i : is-prop P) (f : P → D)
    → ((p : P) → f p ⊑ ⨆ i f)
    × ((u : D) → ((p : P) → f p ⊑ u) → ⨆ i f ⊑ u)
  ⨆-is-lub P i f = α , ψ
   where
    α : (p : P) → f p ⊑ ⨆ i f
    α p a = (⨆-property P i f p)⁻¹

    ψ : (u : D) → ((p : P) → f p ⊑ u) → ⨆ i f ⊑ u
    ψ u β c =
      ⨆ i f ＝⟨ I ⟩
      f p   ＝⟨ β p (transport δ I c) ⟩
      u     ∎
       where
        p : P
        p = δ-property P i f c

        I : ⨆ i f ＝ f p
        I = ⨆-property P i f p

\end{code}

This completes the proof. But notice that we also have

\begin{code}

    φ : (u : D) → ⨆ i f ⊑ u → ((p : P) → f p ⊑ u)
    φ u γ = λ p → α p □ γ

\end{code}

which should be an inverse of ψ, so that we can use the same idea of
the sanity check to prove the colimit conjecture. This is the next
thing to try.

\begin{code}

    φ-explicitly : (u : D) (γ : ⨆ i f ⊑ u)
                 → φ u γ ＝ λ p a → α p a ∙ γ (δ-is-monotone (α p) a)
    φ-explicitly u γ = refl

    ψ-explicitly : (u : D) (β : (p : P) → f p ⊑ u)
                 → ψ u β
                 ＝ λ c → ⨆-property P i f (δ-property P i f c)
                        ∙ β (δ-property P i f c)
                            (transport δ (⨆-property P i f (δ-property P i f c)) c)
    ψ-explicitly u β = refl

\end{code}

It is interesting to instantiate the above to D := 𝓤 and ⨆ := Σ or ⨆ := Π.

Then we have that ⊥ is respectively the empty type 𝟘 or the unit type 𝟙.

Moreover, δΣ X ≃ ∥ X ∥, whereas δΠ X is a positive way of saying that X is not 𝟙.

(And, of course, ∥ X ∥ is a positive way of saying that X is not 𝟘,
without exhibiting a point of X.)

\begin{code}

δΣ : 𝓤 ̇ → 𝓤 ⁺ ̇
δΣ {𝓤} X = (P : 𝓤 ̇ ) → is-prop P → (P × X) ≃ X → P

δΣ-is-prop-valued : (X : 𝓤 ̇ ) → is-prop (δΣ X)
δΣ-is-prop-valued X = Π₃-is-prop fe' (λ _ i _ → i)

δΠ : 𝓤 ̇ → 𝓤 ⁺ ̇
δΠ {𝓤} X = (P : 𝓤 ̇ ) → is-prop P → (P → X) ≃ X → P

δΠ-is-prop-valued : (X : 𝓤 ̇ ) → is-prop (δΠ X)
δΠ-is-prop-valued X = Π₃-is-prop fe' (λ _ i _ → i)

𝟘-is-not-Σ-defined : ¬ δΣ (𝟘 {𝓤})
𝟘-is-not-Σ-defined f = 𝟘-elim (f 𝟘 𝟘-is-prop (≃-sym ×𝟘))

pointed-is-Σ-defined : {X : 𝓤 ̇ } → X → δΣ X
pointed-is-Σ-defined x P i e = pr₁ (⌜ e ⌝⁻¹ x)

open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 inhabited-is-Σ-defined : {X : 𝓤 ̇ } → ∥ X ∥ → δΣ X
 inhabited-is-Σ-defined {𝓤} {X} = ∥∥-rec (δΣ-is-prop-valued X) pointed-is-Σ-defined

 Σ-defined-is-inhabited : {X : 𝓤 ̇ } → δΣ X → ∥ X ∥
 Σ-defined-is-inhabited {𝓤} {X} f = f ∥ X ∥ ∥∥-is-prop e
  where
    e : ∥ X ∥ × X ≃ X
    e = qinveq pr₂
         ((λ x → ∣ x ∣ , x) ,
          (λ (s , x) → to-×-＝ (∥∥-is-prop ∣ x ∣ s) refl) ,
          (λ x → refl))

𝟙-is-not-Π-defined : ¬ δΠ (𝟙 {𝓤})
𝟙-is-not-Π-defined f = 𝟘-elim (f 𝟘 𝟘-is-prop (≃-sym (𝟘→ fe')))

𝟘-is-Π-defined-gives-DNE : δΠ 𝟘
                         → (P : 𝓤₀ ̇ ) → is-prop P → ¬¬ P → P
𝟘-is-Π-defined-gives-DNE f P i ϕ = f P i e
 where
  e : (P → 𝟘) ≃ 𝟘
  e = qinveq ϕ
       ((λ z p → z) ,
        (λ u → dfunext fe' (λ p → 𝟘-is-prop (ϕ u) (u p))) ,
        (λ z → 𝟘-elim z))

DNE-gives-𝟘-is-Π-defined : ((P : 𝓤₀ ̇ ) → is-prop P → ¬¬ P → P)
                         → δΠ 𝟘
DNE-gives-𝟘-is-Π-defined dne P i e = dne P i ⌜ e ⌝

\end{code}

So the Π-definedness of 𝟘 is undecided in our constructive setting.

Is there any example of a type that we can prove to be Π-defined?
