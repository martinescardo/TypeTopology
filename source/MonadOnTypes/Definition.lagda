Martin Escardo, Paulo Oliva, 2023 - 2024

(Strong, wild) universe-polymorphic monads on types.

We use ℓ : Universe → Universe to control the functor part. E.g. for
the powerset monad, as the powerset of a type in 𝓤 lands in the next
universe 𝓤⁺, we take ℓ 𝓤 = 𝓤⁺, but for the list monad we take
ℓ 𝓤 = 𝓤. For the J and K monads with answer type R : 𝓦,
we have ℓ 𝓤 = 𝓤 ⊔ 𝓦.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt

\end{code}

In the following definition, it works to make ℓ into a field, but this
requires the pragma --no-level-universe, which we don't want to
use. In fact, our code originally did have ℓ as a field, using that
pragma.

\begin{code}

module MonadOnTypes.Definition where

record Monad {ℓ : Universe → Universe} : 𝓤ω where
 constructor
  monad
 field
  functor : {𝓤 : Universe} → 𝓤 ̇ → ℓ 𝓤 ̇

 private
  T = functor

 field
  η       : {𝓤 : Universe} {X : 𝓤 ̇ } → X → T X
  ext     : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → T Y) → T X → T Y
  ext-η   : {𝓤 : Universe} {X : 𝓤 ̇ } → ext (η {𝓤} {X}) ∼ 𝑖𝑑 (T X)
  unit    : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → T Y) (x : X)
          → ext f (η x) ＝ f x
  assoc   : {𝓤 𝓥 𝓦 : Universe}
            {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
            (g : Y → T Z) (f : X → T Y) (t : T X)
          → ext (λ x → ext g (f x)) t ＝ ext g (ext f t)

 map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → T X → T Y
 map f = ext (η ∘ f)

 map-id : {X : 𝓤 ̇ } → map (𝑖𝑑 X) ∼ 𝑖𝑑 (T X)
 map-id = ext-η

 map-∘ : Fun-Ext
       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
         (f : X → Y) (g : Y → Z)
       → map (g ∘ f) ∼ map g ∘ map f
 map-∘ fe f g t =
  map (g ∘ f) t                               ＝⟨refl⟩
  ext (λ x → η (g (f x))) t                   ＝⟨ by-unit ⟩
  ext (λ x → ext (λ y → η (g y)) (η (f x))) t ＝⟨ by-assoc ⟩
  ext (λ x → η (g x)) (ext (λ x → η (f x)) t) ＝⟨refl⟩
  (map g ∘ map f) t                           ∎
   where
    by-unit  = ap (λ - → ext - t)
                  (dfunext fe (λ x → (unit (λ y → η (g y)) (f x))⁻¹))
    by-assoc = assoc (λ x → η (g x)) (λ x → η (f x)) t

 map-∘₃ : Fun-Ext
       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {T : 𝓣 ̇ }
         (f : X → Y) (g : Y → Z) (h : Z → T)
       → map (h ∘ g ∘ f) ∼ map h ∘ map g ∘ map f
 map-∘₃ fe f g h t =
  map (h ∘ g ∘ f) t         ＝⟨ by-Tiality ⟩
  (map (h ∘ g) ∘ map f) t   ＝⟨ again-by-functoriality ⟩
  (map h ∘ map g) (map f t) ＝⟨refl⟩
  (map h ∘ map g ∘ map f) t ∎
   where
    by-Tiality  = map-∘ fe f (h ∘ g) t
    again-by-functoriality = ap (λ - → (- ∘ map f) t) (dfunext fe (map-∘ fe g h))

 μ : {X : 𝓤 ̇ } → T (T X) → T X
 μ = ext id

 ext-is-μ-map : Fun-Ext
              → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                (f : X → T Y)
              → ext f ∼ μ ∘ map f
 ext-is-μ-map fe f tt =
  ext f tt                  ＝⟨ by-unit ⁻¹ ⟩
  ext (ext id ∘ η ∘ f) tt   ＝⟨ by-assoc ⟩
  (ext id ∘ ext (η ∘ f)) tt ＝⟨refl⟩
  (μ ∘ map f) tt            ∎
   where
    by-unit  = ap (λ - → ext (- ∘ f) tt) (dfunext fe (unit id))
    by-assoc = assoc id (η ∘ f) tt

 μ-assoc : Fun-Ext
         → {X : 𝓤 ̇ }
         → μ {𝓤} {X} ∘ map (μ {𝓤} {X}) ∼ μ {𝓤} {X} ∘ μ {ℓ 𝓤} {T X}
 μ-assoc fe ttt =
  (μ ∘ map μ) ttt       ＝⟨ (ext-is-μ-map fe μ ttt)⁻¹ ⟩
  ext μ ttt             ＝⟨refl⟩
  ext (ext id ∘ id) ttt ＝⟨ assoc id id ttt ⟩
  ext id (ext id ttt)   ＝⟨refl⟩
  (μ ∘ μ) ttt           ∎

 η-natural : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             (h : X → Y)
           → map h ∘ η {𝓤} {X} ∼ η {𝓥} {Y} ∘ h
 η-natural h x =
  map h (η x)               ＝⟨refl⟩
  ext (λ x → η (h x)) (η x) ＝⟨ unit (λ x → η (h x)) x ⟩
  η (h x)                   ∎

 μ-natural : Fun-Ext
           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             (h : X → Y)
           → map h ∘ μ {𝓤} {X}  ∼ μ {𝓥} {Y} ∘ map (map h)
 μ-natural fe h tt =
  (map h ∘ μ) tt                            ＝⟨refl⟩
  ext (η ∘ h) (ext id tt)                   ＝⟨ by-assoc ⁻¹ ⟩
  ext (ext (η ∘ h)) tt                      ＝⟨ by-unit ⁻¹ ⟩
  ext (λ t → ext id (η (ext (η ∘ h) t))) tt ＝⟨ again-by-assoc ⟩
  ext id (ext (λ t → η (ext (η ∘ h) t)) tt) ＝⟨refl⟩
  (μ ∘ map (map h)) tt                      ∎
   where
    by-assoc       = assoc (λ x → η (h x)) id tt
    by-unit        = ap (λ - → ext - tt)
                        (dfunext fe (λ t → unit id (ext (η ∘ h) t)))
    again-by-assoc = assoc id (λ x → η (ext (η ∘ h) x)) tt

 η-unit₀ : {X : 𝓤 ̇ } → μ {𝓤} {X} ∘ η {ℓ 𝓤} {T X} ∼ id
 η-unit₀ t = μ (η t)      ＝⟨refl⟩
             ext id (η t) ＝⟨ unit id t ⟩
             t            ∎

 η-unit₁ : Fun-Ext
         → {X : 𝓤 ̇ } → μ {𝓤} {X} ∘ map (η {𝓤} {X}) ∼ id
 η-unit₁ fe t =
  μ (map η t)                    ＝⟨refl⟩
  ext id (ext (η ∘ η) t)         ＝⟨ by-assoc ⟩
  ext (λ x → ext id (η (η x))) t ＝⟨ by-unit ⟩
  ext η t                        ＝⟨ ext-η t ⟩
  t                              ∎
   where
    by-assoc = (assoc id (λ x → η (η x)) t)⁻¹
    by-unit  = ap (λ - → ext - t) (dfunext fe (λ x → unit id (η x)))

 _⊗_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
     → T X
     → ((x : X) → T (Y x))
     → T (Σ x ꞉ X , Y x)
 t ⊗ f = ext (λ x → map (λ y → x , y) (f x)) t

open Monad public

tensor : {ℓ : Universe → Universe} (𝕋 : Monad {ℓ})
       → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
       → functor 𝕋 X
       → ((x : X) → functor 𝕋 (Y x))
       → functor 𝕋 (Σ x ꞉ X , Y x)
tensor 𝕋 = _⊗_ 𝕋

syntax tensor 𝕋 t f = t ⊗[ 𝕋 ] f

\end{code}

TODO. Is "tensor" an appropriate terminology? Would (left)
convolution, in the sense of Day, be better?

    https://ncatlab.org/nlab/show/tensorial+strength
    https://ncatlab.org/nlab/show/Day+convolution

\begin{code}

𝕀𝕕 : Monad
𝕀𝕕 = record {
      functor = id ;
      η       = id ;
      ext     = id ;
      ext-η   = λ x → refl ;
      unit    = λ f x → refl ;
      assoc   = λ g f x → refl
    }

𝕀𝕕⊗ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
     (x : X)
     (f : (x : X) → (Y x))
   → x ⊗[ 𝕀𝕕 ] f ＝ x , f x
𝕀𝕕⊗ x f = refl

\end{code}

If we want to call a monad T, then we can use the following module:

\begin{code}

module T-definitions {ℓ : Universe → Universe} (𝕋 : Monad {ℓ}) where

 ℓᵀ : Universe → Universe
 ℓᵀ = ℓ

 T : 𝓤 ̇ → ℓᵀ 𝓤 ̇
 T = functor 𝕋

 ηᵀ : {X : 𝓤 ̇ } → X → T X
 ηᵀ = η 𝕋

 extᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → T Y) → T X → T Y
 extᵀ = ext 𝕋

 extᵀ-η : {X : 𝓤 ̇ } → extᵀ (ηᵀ {𝓤} {X}) ∼ 𝑖𝑑 (T X)
 extᵀ-η = ext-η 𝕋

 unitᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → T Y) → extᵀ f ∘ ηᵀ ∼ f
 unitᵀ = unit 𝕋

 assocᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
          (g : Y → T Z) (f : X → T Y)
        → extᵀ (extᵀ g ∘ f) ∼ extᵀ g ∘ extᵀ f
 assocᵀ = assoc 𝕋

 mapᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → T X → T Y
 mapᵀ = map 𝕋

 mapᵀ-id : {X : 𝓤 ̇ } → mapᵀ (𝑖𝑑 X) ∼ 𝑖𝑑 (T X)
 mapᵀ-id = map-id 𝕋

 mapᵀ-∘ : Fun-Ext
        → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
          (f : X → Y) (g : Y → Z)
        → mapᵀ (g ∘ f) ∼ mapᵀ g ∘ mapᵀ f
 mapᵀ-∘ = map-∘ 𝕋

 ηᵀ-natural : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              (f : X → Y)
           → mapᵀ f ∘ ηᵀ ∼ ηᵀ ∘ f
 ηᵀ-natural = η-natural 𝕋

 μᵀ : {X : 𝓤 ̇ } → T (T X) → T X
 μᵀ = μ 𝕋

 μᵀ-assoc : Fun-Ext → {X : 𝓤 ̇ } → μᵀ ∘ mapᵀ μᵀ ∼ μᵀ ∘ μᵀ
 μᵀ-assoc = μ-assoc 𝕋

 μᵀ-natural : Fun-Ext
            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              (h : X → Y)
            → mapᵀ h ∘ μᵀ {𝓤} {X}  ∼ μᵀ {𝓥} {Y} ∘ mapᵀ (mapᵀ h)
 μᵀ-natural = μ-natural 𝕋

 ηᵀ-unit₀ : {X : 𝓤 ̇ } → μᵀ {𝓤} {X} ∘ ηᵀ {ℓᵀ 𝓤} {T X} ∼ id
 ηᵀ-unit₀ = η-unit₀ 𝕋

 ηᵀ-unit₁ : Fun-Ext
         → {X : 𝓤 ̇ } → μᵀ {𝓤} {X} ∘ mapᵀ (ηᵀ {𝓤} {X}) ∼ id
 ηᵀ-unit₁ = η-unit₁ 𝕋

 _⊗ᵀ_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
      → T X
      → ((x : X) → T (Y x))
      → T (Σ x ꞉ X , Y x)
 _⊗ᵀ_ = _⊗_ 𝕋

\end{code}

For some results, we need our monad to satisfy the condition
extᵀ-const defined below. Ohad Kammar pointed out to us that this
condition is equivalent to the monad being affine. We include his
proof here.

References given by Ohad Kammar and Alex Simpson:

[1] Anders Kock, Bilinearity and Cartesian closed monads,
Math. Stand. 29 (1971) 161-174.
https://users-math.au.dk/kock/BCCM.pdf

[2]
https://www.denotational.co.uk/publications/kammar-plotkin-algebraic-foundations-for-effect-dependent-optimisations.pdf

[3] https://www.denotational.co.uk/publications/kammar-ohad-thesis.pdf

[4] Gavin Wraith mentions affine theories in his lecture notes form
1969 (Prop. 3.5 here:
https://www.denotational.co.uk/scans/wraith-algebraic-theories.pdf)

[5] Bart Jacobs' "Semantics of weakening and contraction".
https://doi.org/10.1016/0168-0072(94)90020-5

\begin{code}

module _ {ℓ : Universe → Universe} (𝕋 : Monad {ℓ}) where

 open T-definitions 𝕋

 is-affine : (𝓤 : Universe) → ℓᵀ 𝓤 ⊔ 𝓤 ̇
 is-affine 𝓤 = is-equiv (ηᵀ {𝓤} {𝟙})

 ext-const' : 𝓤 ̇ → 𝓤ω
 ext-const' X = {𝓥 : Universe} {Y : 𝓥 ̇ } (u : T Y)
              → extᵀ (λ (x : X) → u) ∼ λ (t : T X) → u

 ext-const : 𝓤ω
 ext-const = {𝓤 : Universe} {X : 𝓤 ̇ } → ext-const' X

 affine-gives-ext-const' : Fun-Ext → is-affine 𝓤 → ext-const' 𝟙
 affine-gives-ext-const' {𝓤} fe a {Y} u t = γ
  where
   f = λ (x : 𝟙) → u

   I : f ∘ inverse (ηᵀ {𝓤} {𝟙}) a ∼ extᵀ f
   I s = (f ∘ inverse ηᵀ a) s         ＝⟨ I₀ ⟩
         extᵀ f (ηᵀ (inverse ηᵀ a s)) ＝⟨ I₁ ⟩
         extᵀ f s                     ∎
    where
     I₀ = (unitᵀ f (inverse ηᵀ a s))⁻¹
     I₁ = ap (extᵀ f) (inverses-are-sections ηᵀ a s)

   γ : extᵀ f t ＝ u
   γ = extᵀ f t                   ＝⟨ (ap (λ - → - t) (dfunext fe I))⁻¹ ⟩
       (f ∘ inverse (ηᵀ {𝓤} {𝟙}) a) t ＝⟨refl⟩
       u                          ∎

 affine-gives-ext-const : Fun-Ext → ({𝓤 : Universe} → is-affine 𝓤) → ext-const
 affine-gives-ext-const fe a {𝓤} {X} {𝓥} {Y} u t = γ
  where
   g : X → T Y
   g _ = u

   f : T 𝟙 → T Y
   f _ = u

   h : 𝟙 → T Y
   h _ = u

   k : X → T 𝟙
   k = ηᵀ {𝓤} {𝟙} ∘ unique-to-𝟙

   I : extᵀ h ＝ f
   I = dfunext fe (affine-gives-ext-const' fe a u)

   γ = extᵀ g t             ＝⟨refl⟩
       extᵀ (f ∘ k) t       ＝⟨ ap (λ - → extᵀ (- ∘ k) t) (I ⁻¹) ⟩
       extᵀ (extᵀ h ∘ k) t  ＝⟨ assocᵀ h k t ⟩
       extᵀ h (extᵀ k t)    ＝⟨ ap (λ - → - (extᵀ k t)) I ⟩
       f (extᵀ k t)         ＝⟨refl⟩
       u                    ∎

 ext-const-gives-affine : ext-const → is-affine 𝓤
 ext-const-gives-affine {𝓤} ϕ = γ
  where
   η⁻¹ : T 𝟙 → 𝟙
   η⁻¹ t = ⋆

   I : η⁻¹ ∘ ηᵀ ∼ id
   I ⋆ = refl

   II : ηᵀ ∘ η⁻¹ ∼ id
   II t = (ηᵀ ∘ η⁻¹) t        ＝⟨refl⟩
          ηᵀ ⋆                ＝⟨ (ϕ {𝓤} {𝟙} (ηᵀ ⋆) t)⁻¹ ⟩
          extᵀ (λ x → ηᵀ ⋆) t ＝⟨refl⟩
          extᵀ ηᵀ t           ＝⟨ extᵀ-η t ⟩
          t                   ∎

   γ : is-equiv (ηᵀ {𝓤} {𝟙})
   γ = qinvs-are-equivs ηᵀ (η⁻¹ , I , II)

\end{code}

Monad algebras.

\begin{code}

record Algebra {ℓ : Universe → Universe} (𝕋 : Monad {ℓ}) (A : 𝓦 ̇ ) : 𝓤ω where

 open T-definitions 𝕋

 field
  structure-map : T A → A

 private
  α = structure-map

 field
  aunit  : α ∘ η 𝕋 ∼ id
  aassoc : α ∘ extᵀ (ηᵀ ∘ α) ∼ α ∘ extᵀ id

 extension : {X : 𝓤 ̇ } → (X → A) → T X → A
 extension f = α ∘ mapᵀ f

 _extends_ : {X : 𝓤 ̇ } → (T X → A) → (X → A) → 𝓦 ⊔ 𝓤 ̇
 g extends f = g ∘ ηᵀ ∼ f

 extension-property : {X : 𝓤 ̇ } (f : X → A)
                    → (extension f) extends f
 extension-property f x =
  (extension f ∘ ηᵀ) x ＝⟨refl⟩
  α (mapᵀ f (ηᵀ x))    ＝⟨ ap α (ηᵀ-natural f x) ⟩
  α (ηᵀ (f x))         ＝⟨ aunit (f x) ⟩
  f x                  ∎

 is-hom-from-free : {X : 𝓤 ̇ } → (T X → A) → 𝓦 ⊔ ℓᵀ (ℓᵀ 𝓤) ̇
 is-hom-from-free h = h ∘ μᵀ ∼ α ∘ mapᵀ h

 extension-is-hom : Fun-Ext
                  → {X : 𝓤 ̇ } (f : X → A)
                  → is-hom-from-free (extension f)
 extension-is-hom fe f tt =
  (extension f ∘ μᵀ) tt           ＝⟨refl⟩
  (α ∘ mapᵀ f ∘ μᵀ) tt            ＝⟨ ap α (μᵀ-natural fe f tt) ⟩
  (α ∘ μᵀ ∘ mapᵀ (mapᵀ f)) tt     ＝⟨ (aassoc (mapᵀ (mapᵀ f) tt))⁻¹ ⟩
  (α ∘ mapᵀ α ∘ mapᵀ (mapᵀ f)) tt ＝⟨ ap α ((mapᵀ-∘ fe (mapᵀ f) α tt)⁻¹) ⟩
  (α ∘ mapᵀ (α ∘ mapᵀ f)) tt      ＝⟨refl⟩
  (α ∘ mapᵀ (extension f)) tt     ∎

 at-most-one-extension : Fun-Ext
                       → {X : 𝓤 ̇ } (g h : T X → A)
                       → g ∘ ηᵀ ∼ h ∘ ηᵀ
                       → is-hom-from-free g
                       → is-hom-from-free h
                       → g ∼ h
 at-most-one-extension fe g h g-h-agreement g-is-hom h-is-hom tt =
  g tt                      ＝⟨refl⟩
  (g ∘ id) tt               ＝⟨ by-unit₁ ⁻¹ ⟩
  (g ∘ μᵀ ∘ mapᵀ ηᵀ) tt     ＝⟨ by-g-is-hom ⟩
  (α ∘ mapᵀ g ∘ mapᵀ ηᵀ) tt ＝⟨ by-functoriality ⁻¹ ⟩
  (α ∘ mapᵀ (g ∘ ηᵀ)) tt    ＝⟨ by-agreement ⟩
  (α ∘ mapᵀ (h ∘ ηᵀ)) tt    ＝⟨ by-functoriality-again ⟩
  (α ∘ mapᵀ h ∘ mapᵀ ηᵀ) tt ＝⟨ by-h-is-hom ⁻¹ ⟩
  (h ∘ μᵀ ∘ mapᵀ ηᵀ) tt     ＝⟨ by-unit₁-again ⟩
  h tt                      ∎
   where
    by-unit₁ = ap g (ηᵀ-unit₁ fe tt)
    by-g-is-hom = g-is-hom (mapᵀ ηᵀ tt)
    by-functoriality = ap α (mapᵀ-∘ fe ηᵀ g tt)
    by-agreement = ap (λ - → (α ∘ mapᵀ -) tt) (dfunext fe g-h-agreement)
    by-functoriality-again = ap α (mapᵀ-∘ fe ηᵀ h tt)
    by-h-is-hom = h-is-hom (mapᵀ ηᵀ tt)
    by-unit₁-again = ap h (ηᵀ-unit₁ fe tt)

 extension-uniqueness : Fun-Ext
                      → {X : 𝓤 ̇ } (f : X → A) (h : T X → A)
                      → h extends f
                      → is-hom-from-free h
                      → extension f ∼ h
 extension-uniqueness fe f h h-extends-f h-is-hom =
  at-most-one-extension fe (extension f) h e (extension-is-hom fe f) h-is-hom
  where
   e : extension f ∘ ηᵀ ∼ h ∘ ηᵀ
   e tt = (extension f ∘ ηᵀ) tt ＝⟨ extension-property f tt ⟩
          f tt                  ＝⟨ (h-extends-f tt)⁻¹ ⟩
          (h ∘ ηᵀ) tt           ∎

open Algebra public

\end{code}

Free algebras.

\begin{code}

module _ {ℓ : Universe → Universe} (𝕋 : Monad {ℓ}) where

 open T-definitions 𝕋

 free : Fun-Ext → (X : 𝓤 ̇ ) → Algebra 𝕋 (T X)
 free fe X =
  record {
   structure-map = μᵀ ;
   aunit         = ηᵀ-unit₀ ;
   aassoc        = μᵀ-assoc fe
  }

 is-hom : {A : 𝓥 ̇ } {B : 𝓦 ̇ }
          (𝓐 : Algebra 𝕋 A)
          (𝓑 : Algebra 𝕋 B)
        → (A → B)
        → ℓᵀ 𝓥 ⊔ 𝓦 ̇
 is-hom 𝓐 𝓑 h = h ∘ α ∼ β ∘ mapᵀ h
  where
   α = structure-map 𝓐
   β = structure-map 𝓑

 monad-extension-is-hom : (fe : Fun-Ext)
                          {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          (f : X → T Y)
                        → is-hom (free fe X) (free fe Y) (extᵀ f)
 monad-extension-is-hom fe {X} {Y} f tt =
  (extᵀ f ∘ μᵀ) tt             ＝⟨ by-ext-is-μ-map ⟩
  (μᵀ ∘ mapᵀ f ∘ μᵀ) tt        ＝⟨ extension-is-hom (free fe Y) fe f tt ⟩
  (μᵀ ∘ mapᵀ (μᵀ ∘ mapᵀ f)) tt ＝⟨ again-by-ext-is-μ-map ⁻¹ ⟩
  (μᵀ ∘ mapᵀ (extᵀ f)) tt      ∎
   where
    by-ext-is-μ-map = ext-is-μ-map 𝕋 fe f (μᵀ tt)
    again-by-ext-is-μ-map = ap (λ - → (μᵀ ∘ mapᵀ -) tt)
                               (dfunext fe (ext-is-μ-map 𝕋 fe f))

 hom-∘ : Fun-Ext
       → {A : 𝓥 ̇ } {B : 𝓦 ̇ } {C : 𝓣 ̇ }
         (𝓐 : Algebra 𝕋 A)
         (𝓑 : Algebra 𝕋 B)
         (𝓒 : Algebra 𝕋 C)
       → (f : A → B)
       → (g : B → C)
       → is-hom 𝓐 𝓑 f
       → is-hom 𝓑 𝓒 g
       → is-hom 𝓐 𝓒 (g ∘ f)
 hom-∘ fe 𝓐 𝓑 𝓒 f g f-is-hom g-is-hom t =
  g (f (α t))           ＝⟨ ap g (f-is-hom t) ⟩
  g (β (mapᵀ f t))      ＝⟨ g-is-hom (mapᵀ f t) ⟩
  γ (mapᵀ g (mapᵀ f t)) ＝⟨ ap γ ((mapᵀ-∘ fe f g t)⁻¹) ⟩
  γ (mapᵀ (g ∘ f) t)    ∎
   where
    α = structure-map 𝓐
    β = structure-map 𝓑
    γ = structure-map 𝓒

 extension-assoc : {A : 𝓦 ̇ }
                   (𝓐 : Algebra 𝕋 A)
                 → Fun-Ext
                 → {X : 𝓤  ̇} {Y : 𝓥 ̇ }
                   (g : Y → A) (f : X → T Y)
                 → extension 𝓐 (extension 𝓐 g ∘ f) ∼ extension 𝓐 g ∘ extᵀ f
 extension-assoc {𝓦} {𝓤} {𝓥} {A} 𝓐 fe {X} {Y} g f =
  extension-uniqueness 𝓐 fe ϕ h h-extends-ϕ h-is-hom
  where
   ϕ : X → A
   ϕ = extension 𝓐 g ∘ f

   h : T X → A
   h = extension 𝓐 g ∘ extᵀ f

   h-extends-ϕ : h ∘ ηᵀ ∼ ϕ
   h-extends-ϕ x =
    (h ∘ ηᵀ) x                      ＝⟨refl⟩
    (extension 𝓐 g ∘ extᵀ f ∘ ηᵀ) x ＝⟨ ap (extension 𝓐 g) (unitᵀ f x) ⟩
    (extension 𝓐 g ∘ f) x           ＝⟨refl⟩
    ϕ x                             ∎

   h-is-hom : is-hom (free fe X) 𝓐 h
   h-is-hom = hom-∘ fe
               (free fe X) (free fe Y) 𝓐
               (extᵀ f) (extension 𝓐 g)
               (monad-extension-is-hom fe f) (extension-is-hom 𝓐 fe g)


\end{code}

If we want to call an algebra (literally) α, we can used this module:

\begin{code}

module α-definitions
        {ℓ : Universe → Universe}
        (𝕋 : Monad {ℓ})
        {𝓦₀ : Universe}
        (A : 𝓦₀ ̇ )
        (𝓐 : Algebra 𝕋 A)
       where

 open T-definitions 𝕋

 α : T A → A
 α = structure-map 𝓐

 α-unitᵀ : α ∘ ηᵀ ∼ id
 α-unitᵀ = aunit 𝓐

 α-assocᵀ : α ∘ extᵀ (ηᵀ ∘ α) ∼ α ∘ extᵀ id
 α-assocᵀ = aassoc 𝓐

 α-assocᵀ' : α ∘ mapᵀ α ∼ α ∘ μᵀ
 α-assocᵀ' = α-assocᵀ

 α-extᵀ : {X : 𝓤 ̇ } → (X → A) → T X → A
 α-extᵀ q = α ∘ mapᵀ q

 α-extᵀ-unit : {X : 𝓤 ̇ }
               (f : X → A)
             → α-extᵀ f ∘ ηᵀ ∼ f
 α-extᵀ-unit = extension-property 𝓐

 α-extᵀ-assoc : Fun-Ext
              → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                (g : Y → A) (f : X → T Y)
              → α-extᵀ (α-extᵀ g ∘ f) ∼ α-extᵀ g ∘ extᵀ f
 α-extᵀ-assoc = extension-assoc 𝕋 𝓐

 α-curryᵀ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
          → ((Σ x ꞉ X , Y x) → A)
          → (x : X) → T (Y x) → A
 α-curryᵀ q x = α-extᵀ (curry q x)

\end{code}

TODO. Define monad morphism (for example overline is a monad morphism
from J to K).
