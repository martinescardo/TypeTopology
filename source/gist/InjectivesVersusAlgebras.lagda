Martin Escardo, 22nd October 2024

Incomplete blackboard thoughts on injectives as algebras of the
partial-map classifier monad, also known as the lifting monad.

Added 13th Feb 2025.

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

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt

module gist.InjectivesVersusAlgebras
        (fe : FunExt)
       where

fe' : Fun-Ext
fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence

module _ (𝓤 𝓥 : Universe)
         (D : 𝓤 ⊔ 𝓥 ̇ )
         (⨆ : {P : 𝓤 ̇} → is-prop P → (P → D) → D)
         (⨆-property : (P : 𝓤 ̇)
                        (i : is-prop P)
                        (f : P → D)
                        (p : P)
                      → ⨆ i f ＝ f p)
       where

 ⨆-change-of-variable : is-univalent 𝓤
                       → {P : 𝓤 ̇} (i : is-prop P)
                         {Q : 𝓤 ̇} (j : is-prop Q)
                         (e : P ≃ Q)
                         (f : P → D)
                       → ⨆ i f ＝ ⨆ j (f ∘ ⌜ e ⌝⁻¹)
 ⨆-change-of-variable ua {P} i {Q} j e f = JEq ua P A I Q e j
  where
   A : (Q : 𝓤 ̇) → P ≃ Q → 𝓤 ⊔ 𝓥 ̇
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

  δ : D → 𝓥 ⊔  𝓤 ⁺ ̇
  δ d = {P : 𝓤 ̇ } (i : is-prop P) (f : P → D) → ⨆ i f ＝ d → P

  δ' : D → 𝓥 ⊔  𝓤 ⁺ ̇
  δ' d = {P : 𝓤 ̇ } (i : is-prop P) → ⨆ i (λ _ → d) ＝ d → P

  δ-gives-δ' : (d : D) → δ d → δ' d
  δ-gives-δ' d π {P} i = π i (λ _ → d)

  δ'-gives-δ : (d : D) → δ' d → δ d
  δ'-gives-δ d π {P} i f e =
   π i (⨆ i (λ _ → d) ＝⟨ ap (⨆ i) (dfunext fe' (λ p → e ⁻¹ ∙ ⨆-property P i f p)) ⟩
   ⨆ i f              ＝⟨ e ⟩
   d                   ∎)

  hom : D → D → 𝓥 ⊔  𝓤 ⁺ ̇
  hom x y = δ x → x ＝ y

  idD : {x : D} → hom x x
  idD {x} = λ _ → refl

  compD : {x y z : D} → hom x y → hom y z → hom x z
  compD {x} {y} {z} α β π = α π ∙ β (transport δ (α π) π)

{-
  assocD : {x y z t : D} (α : hom x y) (β : hom y z) (γ : hom z t)
         → compD α (compD β γ) ∼ compD (compD α β) γ
  assocD {x} {y} {z} {t} α β γ π = ?
-}

  extension : (Y → D)
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

\end{code}

TODO. Define algebraic injectivity data to be iterative if

 (f | j) | k = f | (k ∘ j).

The above shows one direction that iterative algebraic injectivity
data on D is equivalent to lifting algebra structure on D.

Notice the following.

If g = f | j then by definition g ∘ j = f
If h = g | k then by definition h ∘ k = g

So (h ∘ k) ∘ j = h ∘ (k ∘ j)

\begin{code}

module _ (𝓤 : Universe)
         (D : 𝓤 ̇ )
         (_/_ : {X : 𝓤 ̇} {Y : 𝓤 ̇ } → (X → D) → (X ↪ Y) → (Y → D))
         (extension-property : {X : 𝓤 ̇} {Y : 𝓤 ̇ } (f : X → D) (j : X ↪ Y)
                             →  f / j ∘ ⌊ j ⌋ ∼ f)
       where

 ⨆ : {P : 𝓤 ̇} → is-prop P → (P → D) → D
 ⨆ {P} P-is-prop g = (g / (embedding-into-𝟙 P P-is-prop)) ⋆

 ⨆-change-of-variable' : is-univalent 𝓤
                        → {P : 𝓤 ̇} (i : is-prop P)
                          {Q : 𝓤 ̇} (j : is-prop Q)
                          (e : P ≃ Q)
                          (f : P → D)
                        → ⨆ i f ＝ ⨆ j (f ∘ ⌜ e ⌝⁻¹)
 ⨆-change-of-variable' ua {P} i {Q} j e f = JEq ua P A I Q e j
  where
   A : (Q : 𝓤 ̇) → P ≃ Q → 𝓤 ̇
   A Q e = (j : is-prop Q) → ⨆ i f ＝ ⨆ j (f ∘ ⌜ e ⌝⁻¹)

   I : A P (≃-refl P)
   I j = ap (λ - → ⨆ - f) (being-prop-is-prop fe' i j)


 fiber-to-𝟙 : {X : 𝓤 ̇} {Y : 𝓤 ̇ } (j : X ↪ Y) (y : Y)
            → fiber ⌊ j ⌋ y ↪ 𝟙
 fiber-to-𝟙 j y = embedding-into-𝟙 {𝓤} {𝓤} (fiber ⌊ j ⌋ y) (⌊ j ⌋-is-embedding y)

 fiber-map : {X : 𝓤 ̇} {Y : 𝓤 ̇ } (f : X → D) (j : X ↪ Y) (y : Y)
           → fiber ⌊ j ⌋ y → D
 fiber-map f j y (x , _) = f x

 _/̇_ : {X : 𝓤 ̇} {Y : 𝓤 ̇ }
      → (X → D)
      → (X ↪ Y)
      → Y → D
 f /̇ j = λ y → ⨆ (⌊ j ⌋-is-embedding y) (fiber-map f j y)

 ⨆-property : (P : 𝓤 ̇)
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
 Extensions-are-Pointwise = {X : 𝓤 ̇} {Y : 𝓤 ̇ } (f : X → D) (j : X ↪ Y)
                          → f / j ∼ f /̇ j

{-
 extensions-are-pointwise : Extensions-are-Pointwise
 extensions-are-pointwise = {!!}
-}

\end{code}

Is the above the case? Or does it need to be an assumption?

\begin{code}

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
    ⨆ a (f / u)                           ＝⟨ refl ⟩
    ((f / u) / v) ⋆                       ＝⟨ ea f u v ⋆ ⟩
    (f / (v ∘↪ u)) ⋆                      ＝⟨ ap (λ - → (f / -) ⋆) III ⟩
    (f / w) ⋆                             ＝⟨ refl ⟩
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
             ⨆ (⌊ u ⌋-is-embedding p) (fiber-map f u p) ＝⟨ refl ⟩
             (f /̇ u) p                                  ＝⟨ II' p ⟩
             (f / u) p                                  ∎)
              where
               II' = λ p → (extensions-are-pointwise f u p)⁻¹

       III : (v ∘↪ u) ＝ w
       III = to-subtype-＝ (being-embedding-is-prop fe') refl

\end{code}

Added 16th Feb 2025.

\begin{code}

{-
module _ (𝓤 𝓥 : Universe)
         (D : 𝓤 ⊔ 𝓥 ̇ )
         (⨆ : {P : 𝓤 ̇} → is-prop P → (P → D) → D)
         (⨆-property : (P : 𝓤 ̇)
                        (i : is-prop P)
                        (f : P → D)
                        (p : P)
                      → ⨆ i f ＝ f p)
         (P : 𝓤 ̇ )
         (P-is-prop : is-prop P)
         (Q : 𝓤 ̇ )
         (Q-is-prop : is-prop Q)
         (j : P → Q)
         (f : P → D)
      where

 j-is-embedding : is-embedding j
 j-is-embedding = maps-of-props-are-embeddings j P-is-prop Q-is-prop

 g h : Q → D
 g q = ⨆ P-is-prop f
 h q = ⨆ (j-is-embedding q) (λ ((p , _) : fiber j q) → f p)

 try : g ∼ h
 try q =
  g q ＝⟨ refl ⟩
  ⨆ P-is-prop f ＝⟨ {!!} ⟩
  {!!} ＝⟨ {!!} ⟩
  {!!} ＝⟨ {!!} ⟩
  {!!} ＝⟨ {!!} ⟩
  {!!} ＝⟨ {!!} ⟩
  {!!} ＝⟨ {!!} ⟩
  {!!} ＝⟨ {!!} ⟩
  {!!} ＝⟨ {!!} ⟩
  ⨆ (j-is-embedding q) (λ ((p , _) : fiber j q) → f p) ＝⟨ refl ⟩
  h q ∎
-}

\end{code}

Added 28 Feb 2025.

\begin{code}

-- open import InjectiveTypes.Blackboard fe

-- module _ {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } {Y : 𝓣 ̇ }
--          (k : A → B)
--          (j : X → Y)
--          (g : A → X)
--          (h : B → Y)
--          (square : h ∘ k ∼ j ∘ g)
--          (pb : {𝓣' : Universe} (C : 𝓣' ̇) → (C → X) → (C → B) → (C → A))
--          (f : X → 𝓣' ̇ )
--        where


--  blah' : (b : B) → (f ∖ j) (h b) → ((f ∘ g) ∖ k) b
--  blah' b ((x , d) , y) = (pb X id (λ _ → b) x , {!!}) , {!!}

--  halb' : (b : B) → ((f ∘ g) ∖ k) b → (f ∖ j) (h b)
--  halb' .(k a) ((a , refl) , y) = (g a , ((square a)⁻¹)) , y


--  blah : (b : B) → (f / j) (h b) → ((f ∘ g) / k) b
--  blah .(k a) ϕ (a , refl) = ϕ (g a , ((square a)⁻¹))

--  halb : (b : B) → ((f ∘ g) / k) b → (f / j) (h b)
--  halb b γ (x , e) = {!!}
--   where
--    III : x ＝ g {!!}
--    III = {!!}
--    IV : b ＝ k {!!}
--    IV = {!!}
--    II : f (g {!!})
--    II = γ ({!!} , {!!})
--    I = {!!} ＝⟨ {!!} ⟩
--        {!!} ＝⟨ {!!} ⟩
--        {!!} ＝⟨ {!!} ⟩
--        {!!} ＝⟨ {!!} ⟩
--        {!!} ＝⟨ {!!} ⟩
--        {!!} ＝⟨ {!!} ⟩
--        {!!} ＝⟨ {!!} ⟩
--        {!!} ＝⟨ {!!} ⟩
--        {!!} ＝⟨ {!!} ⟩
--        {!!} ＝⟨ {!!} ⟩
--        {!!} ∎

--  try : (b : B) → (f / j) (h b) ≃ ((f ∘ g) / k) b
--  try b =
--   (f / j) (h b) ≃⟨ ≃-refl _ ⟩
--   ((w : fiber j (h b)) → f (pr₁ w)) ≃⟨ curry-uncurry fe ⟩
--   ((x : X) (e : j x ＝ h b) → f x) ≃⟨ {!!} ⟩
--   {!!} ≃⟨ {!!} ⟩
--   {!!} ≃⟨ {!!} ⟩
--   {!!} ≃⟨ {!!} ⟩
--   {!!} ≃⟨ {!!} ⟩
--   {!!} ≃⟨ {!!} ⟩
--   {!!} ≃⟨ {!!} ⟩
--   {!!} ≃⟨ {!!} ⟩
--   {!!} ≃⟨ {!!} ⟩
--   {!!} ≃⟨ {!!} ⟩
--   {!!} ≃⟨ Π-cong fe' fe' {!!} ⟩
--   ((a : A) (e : k a ＝ b) → f (g a)) ≃⟨ ≃-sym (curry-uncurry fe) ⟩
--   ((t : fiber k b) → f (g (pr₁ t))) ≃⟨ ≃-refl _ ⟩
--   ((f ∘ g) / k) b ■

-- \end{code}
