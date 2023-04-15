Jon Sterling, started 16th Dec 2022

A duploid is a preduploid that has "shifts" between positive and negative
objects.

1. An "upshift" for an object `A` is a negative object `⇑A` together with an
invertible thunkable map `wrap : A ⊢ ⇑A`.

2. A "downshift" for an object `A` is a positive object `⇓A` together with an
invertible linear map `force : ⇓A ⊢ A`.

Note that the inverses to the maps specified above are uniquely determined.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.IdentitySystems
open import UF.SIP

module Duploids.Duploid (fe : Fun-Ext) (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Categories.Category fe
open import Categories.Functor fe
open import Duploids.DeductiveSystem fe
open import Duploids.Preduploid fe pt

module _ (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓

 module _ (A : ob) where
  upshift-data : 𝓤 ⊔ 𝓥 ̇
  upshift-data = Σ ⇑A ꞉ ob , ⇑A ⊢ A

  downshift-data : 𝓤 ⊔ 𝓥 ̇
  downshift-data = Σ ⇓A ꞉ ob , A ⊢ ⇓A

 module _ {A : ob} where
  upshift-axioms : upshift-data A → 𝓤 ⊔ 𝓥 ̇
  upshift-axioms (⇑A , force) =
   is-negative ⇑A ×
   (Σ delay ꞉ A ⊢ ⇑A ,
    is-inverse force delay
    × is-linear force)

  downshift-axioms : downshift-data A → 𝓤 ⊔ 𝓥 ̇
  downshift-axioms (⇓A , wrap) =
   is-positive ⇓A ×
   (Σ unwrap ꞉ ⇓A ⊢ A ,
    is-inverse wrap unwrap
    × is-thunkable wrap)

  module upshift-data (ush : upshift-data A) where
   upshift : ob
   upshift = pr₁ ush

   force : upshift ⊢ A
   force = pr₂ ush

  module downshift-data (dsh : downshift-data A) where
   downshift : ob
   downshift = pr₁ dsh

   wrap : A ⊢ downshift
   wrap = pr₂ dsh

  module upshift-axioms {ush : upshift-data A} (ax : upshift-axioms ush) where
   open upshift-data ush

   upshift-negative : is-negative upshift
   upshift-negative = pr₁ ax

   delay : A ⊢ upshift
   delay = pr₁ (pr₂ ax)

   force-delay-inverse : is-inverse force delay
   force-delay-inverse = pr₁ (pr₂ (pr₂ ax))

   force-linear : is-linear force
   force-linear = pr₂ (pr₂ (pr₂ ax))

  module downshift-axioms {dsh : downshift-data A} (ax : downshift-axioms dsh) where
   open downshift-data dsh

   downshift-positive : is-positive downshift
   downshift-positive = pr₁ ax

   unwrap : downshift ⊢ A
   unwrap = pr₁ (pr₂ ax)

   wrap-unwrap-inverse : is-inverse wrap unwrap
   wrap-unwrap-inverse = pr₁ (pr₂ (pr₂ ax))

   wrap-thunkable : is-thunkable wrap
   wrap-thunkable = pr₂ (pr₂ (pr₂ ax))

  upshift-axioms-is-prop : {ush : _} → is-prop (upshift-axioms ush)
  upshift-axioms-is-prop ax0 ax1 =
   let module ax0 = upshift-axioms ax0 in
   let module ax1 = upshift-axioms ax1 in
   to-×-＝
    (being-negative-is-prop _ _)
    (to-Σ-＝
     (thunkable-inverse-is-unique
       ax1.force-delay-inverse
       ax0.force-delay-inverse
       (ax0.upshift-negative _ _) ,
      to-×-＝
       (being-inverse-is-prop _ _)
       (being-linear-is-prop _ _)))

  downshift-axioms-is-prop : {dsh : _} → is-prop (downshift-axioms dsh)
  downshift-axioms-is-prop ax0 ax1 =
   let module ax0 = downshift-axioms ax0 in
   let module ax1 = downshift-axioms ax1 in
   to-×-＝
    (being-positive-is-prop _ _)
    (to-Σ-＝
     (linear-inverse-is-unique
       ax1.wrap-unwrap-inverse
       ax0.wrap-unwrap-inverse
       (ax0.downshift-positive _ _) ,
      to-×-＝
       (being-inverse-is-prop _ _)
       (being-thunkable-is-prop _ _)))

 module _ (A : ob) where
  has-upshift : 𝓤 ⊔ 𝓥 ̇
  has-upshift = Σ ush ꞉ upshift-data A , upshift-axioms ush

  has-downshift : 𝓤 ⊔ 𝓥 ̇
  has-downshift = Σ dsh ꞉ downshift-data A , downshift-axioms dsh

  module has-upshift (h : has-upshift) where
   open upshift-data (pr₁ h) public
   open upshift-axioms (pr₂ h) public

  module has-downshift (h : has-downshift) where
   open downshift-data (pr₁ h) public
   open downshift-axioms (pr₂ h) public

 negative-linear-isomorph : (A : ob) → 𝓤 ⊔ 𝓥 ̇
 negative-linear-isomorph A =
  Σ N ꞉ ob ,
  Σ f ꞉ N ⊢ A ,
  Σ g ꞉ A ⊢ N ,
  is-negative N
  × is-linear f
  × is-linear g
  × is-inverse f g

 positive-thunkable-isomorph : (A : ob) → 𝓤 ⊔ 𝓥 ̇
 positive-thunkable-isomorph A =
  Σ P ꞉ ob ,
  Σ f ꞉ P ⊢ A ,
  Σ g ꞉ A ⊢ P ,
  is-positive P
  × is-thunkable f
  × is-thunkable g
  × is-inverse f g

 is-negatively-univalent : 𝓤 ⊔ 𝓥 ̇
 is-negatively-univalent =
  (N : ob)
  → is-negative N
  → is-singleton (negative-linear-isomorph N)

 is-positively-univalent : 𝓤 ⊔ 𝓥 ̇
 is-positively-univalent =
  (P : ob)
  → is-positive P
  → is-singleton (positive-thunkable-isomorph P)

 module _ (puni : is-positively-univalent) (N : ob) (N-neg : is-negative N) where
  open deductive-system-extras 𝓓

  has-downshift-is-prop : is-prop (has-downshift N)
  has-downshift-is-prop ((P , wrap) , ax) ((P' , wrap') , ax') =
   to-Σ-＝ (main , downshift-axioms-is-prop _ _)
   where
    module ax = downshift-axioms ax
    module ax' = downshift-axioms ax'

    fwd : P' ⊢ P
    fwd = cut ax'.unwrap wrap

    bwd : P ⊢ P'
    bwd = cut ax.unwrap wrap'

    fwd-thunkable : is-thunkable fwd
    fwd-thunkable = cut-thunkable _ _ (N-neg _ _) ax.wrap-thunkable

    bwd-thunkable : is-thunkable bwd
    bwd-thunkable = cut-thunkable _ _ (N-neg _ _) ax'.wrap-thunkable

    lem : cut wrap (cut ax.unwrap wrap') ＝ wrap'
    lem =
     cut wrap (cut ax.unwrap wrap')
      ＝⟨ ax.wrap-thunkable _ _ _ _ ⁻¹ ⟩
     cut (cut wrap ax.unwrap) wrap'
      ＝⟨ ap (λ - → cut - wrap') (pr₁ ax.wrap-unwrap-inverse) ⟩
     cut (idn _) wrap'
      ＝⟨ idn-L _ _ _ ⟩
     wrap' ∎

    lem' : cut wrap' (cut ax'.unwrap wrap) ＝ wrap
    lem' =
     cut wrap' (cut ax'.unwrap wrap)
      ＝⟨ ax'.wrap-thunkable _ _ _ _ ⁻¹ ⟩
     cut (cut wrap' ax'.unwrap) wrap
      ＝⟨ ap (λ - → cut - wrap) (pr₁ ax'.wrap-unwrap-inverse) ⟩
     cut (idn _) wrap
      ＝⟨ idn-L _ _ _ ⟩
     wrap ∎

    fwd-bwd : cut fwd bwd ＝ idn P'
    fwd-bwd =
      cut (cut ax'.unwrap wrap) (cut ax.unwrap wrap')
       ＝⟨ N-neg _ _ _ _ _ _ ⟩
      cut ax'.unwrap (cut wrap (cut ax.unwrap wrap'))
       ＝⟨ ap (cut ax'.unwrap) lem ⟩
      cut ax'.unwrap wrap'
       ＝⟨ pr₂ ax'.wrap-unwrap-inverse ⟩
      idn P' ∎

    bwd-fwd : cut bwd fwd ＝ idn P
    bwd-fwd =
     cut (cut ax.unwrap wrap') (cut ax'.unwrap wrap)
      ＝⟨ N-neg _ _ _ _ _ _ ⟩
     cut ax.unwrap (cut wrap' (cut ax'.unwrap wrap))
      ＝⟨ ap (cut ax.unwrap) lem' ⟩
     cut ax.unwrap wrap
      ＝⟨ pr₂ ax.wrap-unwrap-inverse ⟩
     idn P ∎

    isomorph : positive-thunkable-isomorph P
    isomorph =
     P' , fwd , bwd , ax'.downshift-positive , fwd-thunkable , bwd-thunkable ,
     fwd-bwd , bwd-fwd

    base : positive-thunkable-isomorph P
    base =
     P , idn P , idn P , ax.downshift-positive ,  idn-thunkable _ , idn-thunkable _ ,
     idn-L _ _ _ , idn-L _ _ _

    base-isomorph : base ＝ isomorph
    base-isomorph =
     pr₂ (puni P ax.downshift-positive) base ⁻¹
     ∙ pr₂ (puni P ax.downshift-positive) isomorph

    main : P , wrap ＝ P' , wrap'
    main =
     P , wrap ＝⟨ ap (P ,_) (idn-R _ _ _ ⁻¹) ⟩
     P , cut wrap (idn _)
      ＝⟨ ap (λ (X , f , g , _) → X , cut wrap g) base-isomorph ⟩
     P' , cut wrap (cut ax.unwrap wrap')
      ＝⟨ ap (P' ,_) (ax.wrap-thunkable _ _ _ _ ⁻¹) ⟩
     P' , cut (cut wrap ax.unwrap) wrap'
      ＝⟨ ap (λ - → P' , cut - wrap') (pr₁ ax.wrap-unwrap-inverse) ⟩
     P' , cut (idn _) wrap'
      ＝⟨ ap (P' ,_) (idn-L _ _ _) ⟩
     P' , wrap' ∎


 module _ (nuni : is-negatively-univalent) (P : ob) (P-pos : is-positive P) where
  open deductive-system-extras 𝓓

  has-upshift-is-prop : is-prop (has-upshift P)
  has-upshift-is-prop ((N , force), ax) ((N' , force'), ax') =
   to-Σ-＝ (main , upshift-axioms-is-prop _ _)

   where
    module ax = upshift-axioms ax
    module ax' = upshift-axioms ax'

    fwd : N' ⊢ N
    fwd = cut force' ax.delay

    bwd : N ⊢ N'
    bwd = cut force ax'.delay

    fwd-linear : is-linear fwd
    fwd-linear = cut-linear force' ax.delay ax'.force-linear (P-pos _ _)

    bwd-linear : is-linear bwd
    bwd-linear = cut-linear force ax'.delay ax.force-linear (P-pos _ _)

    lem : cut (cut force' ax.delay) force ＝ force'
    lem =
     cut (cut force' ax.delay) force ＝⟨ ax.force-linear _ _ _ _ ⟩
     cut force' (cut ax.delay force) ＝⟨ ap (cut force') (pr₂ ax.force-delay-inverse) ⟩
     cut force' (idn _) ＝⟨ idn-R _ _ _ ⟩
     force' ∎

    lem' : cut (cut force ax'.delay) force' ＝ force
    lem' =
     cut (cut force ax'.delay) force' ＝⟨ ax'.force-linear _ _ _ _ ⟩
     cut force (cut ax'.delay force') ＝⟨ ap (cut force) (pr₂ ax'.force-delay-inverse) ⟩
     cut force (idn _) ＝⟨ idn-R _ _ _ ⟩
     force ∎

    fwd-bwd : cut fwd bwd ＝ idn N'
    fwd-bwd =
     cut (cut force' ax.delay) (cut force ax'.delay)
      ＝⟨ P-pos _ _ _ _ _ _ ⁻¹ ⟩
     cut (cut (cut force' ax.delay) force) ax'.delay
      ＝⟨ ap (λ - → cut - ax'.delay) lem ⟩
     cut force' ax'.delay ＝⟨ pr₁ ax'.force-delay-inverse ⟩
     idn N' ∎

    bwd-fwd : cut bwd fwd ＝ idn N
    bwd-fwd =
     cut (cut force ax'.delay) (cut force' ax.delay)
     ＝⟨ P-pos _ _ _ _ _ _ ⁻¹ ⟩
     cut (cut (cut force ax'.delay) force') ax.delay
     ＝⟨ ap (λ - → cut - ax.delay) lem' ⟩
     cut force ax.delay ＝⟨ pr₁ ax.force-delay-inverse ⟩
     idn N ∎

    isomorph : negative-linear-isomorph N
    isomorph =
     N' , fwd , bwd , ax'.upshift-negative , fwd-linear , bwd-linear ,
     fwd-bwd , bwd-fwd

    base : negative-linear-isomorph N
    base =
     N , idn N , idn N , ax.upshift-negative ,  idn-linear _ , idn-linear _ ,
     idn-L _ _ _ , idn-L _ _ _

    base-isomorph : base ＝ isomorph
    base-isomorph =
     pr₂ (nuni N ax.upshift-negative) base ⁻¹
     ∙ pr₂ (nuni N ax.upshift-negative) isomorph

    main : N , force ＝ N' , force'
    main =
     (N , force) ＝⟨ ap (N ,_) (idn-L _ _ _ ⁻¹) ⟩
     (N , cut (idn N) force) ＝⟨ ap (λ (X , f , _) → X , cut f force) base-isomorph ⟩
     (N' , cut (cut force' ax.delay) force) ＝⟨ ap (N' ,_) lem ⟩
     N' , force' ∎




 -- This should most likely be revised to only require upshifts for positives
 -- and downshifts for negatives.
 has-all-shifts : 𝓤 ⊔ 𝓥 ̇
 has-all-shifts = (A : ob) → has-upshift A × has-downshift A

 duploid-structure : 𝓤 ⊔ 𝓥 ̇
 duploid-structure = ((A : ob) → is-polarized str A) × has-all-shifts

 module duploid-structure (dup-str : duploid-structure) where
  underlying-preduploid : preduploid 𝓤 𝓥
  underlying-preduploid = make ob _⊢_ idn cut' (ax , pr₁ dup-str)

  module _ (A : ob) where
   private
    A-has-shifts = pr₂ dup-str A
    module ⇑A = has-upshift A (pr₁ A-has-shifts)
    module ⇓A = has-downshift A (pr₂ A-has-shifts)

   ⇑ = ⇑A.upshift
   ⇓ = ⇓A.downshift

   ⇑-negative = ⇑A.upshift-negative
   ⇓-positive = ⇓A.downshift-positive

  module _ {A : ob} where
   private
    A-has-shifts = pr₂ dup-str A
    module ⇑A = has-upshift A (pr₁ A-has-shifts)
    module ⇓A = has-downshift A (pr₂ A-has-shifts)

   open ⇑A hiding (upshift) public
   open ⇓A hiding (downshift) public

  open preduploid underlying-preduploid public



 -- This is not necessarily a proposition, because we do not yet know how to
 -- state the property that a deductive system is univalent.

record duploid 𝓤 𝓥 : (𝓤 ⊔ 𝓥)⁺ ̇ where
 field
  ob : 𝓤 ̇
  _⊢_ : ob → ob → 𝓥 ̇
  idn : (A : ob) → A ⊢ A
  cut' : (A B C : ob) (f : A ⊢ B) (g : B ⊢ C) → A ⊢ C
  ⇑ : ob → ob
  ⇓ : ob → ob

  force : {A : ob} → ⇑ A ⊢ A
  delay : {A : ob} → A ⊢ ⇑ A

  wrap : {A : ob} → A ⊢ ⇓ A
  unwrap : {A : ob} → ⇓ A ⊢ A

 cut : {A B C : ob} (f : A ⊢ B) (g : B ⊢ C) → A ⊢ C
 cut = cut' _ _ _

 str : deductive-system-structure 𝓤 𝓥
 str = ob , _⊢_ , idn , cut'

 field
  ax-preduploid : preduploid-axioms str

 underlying-preduploid : preduploid 𝓤 𝓥
 underlying-preduploid = make ob _⊢_ idn cut' ax-preduploid

 underlying-deductive-system : deductive-system 𝓤 𝓥
 underlying-deductive-system = preduploid.underlying-deductive-system underlying-preduploid

 open deductive-system-axioms str (deductive-system.ax underlying-deductive-system)  public


 open ⊢-properties str

 field
  -- TODO: restrct the upshift to positives and the downshift to negatives
  ⇑-negative : (A : ob) → is-negative (⇑ A)
  ⇓-positive : (A : ob) → is-positive (⇓ A)

  force-linear : {A : ob} → is-linear (force {A})
  wrap-thunkable : {A : ob} → is-thunkable (wrap {A})
  force-delay-inverse : {A : ob} → is-inverse (force {A}) (delay {A})
  wrap-unwrap-inverse : {A : ob} → is-inverse (wrap {A}) (unwrap {A})

 delay-thunkable : {A : ob} → is-thunkable (delay {A})
 delay-thunkable {A} = ⇑-negative A A delay

 unwrap-linear : {A : ob} → is-linear (unwrap {A})
 unwrap-linear {A} = ⇓-positive A A unwrap

 open ⊢-properties str public

module duploids-as-sums where
 module _ (𝓓 : Σ D ꞉ deductive-system 𝓤 𝓥 , duploid-structure D) where
  private
   D = pr₁ 𝓓
   str = pr₂ 𝓓

  module str = duploid-structure D str

  duploid-from-sum : duploid 𝓤 𝓥
  duploid.ob duploid-from-sum = str.ob
  duploid._⊢_ duploid-from-sum = str._⊢_
  duploid.idn duploid-from-sum = str.idn
  duploid.cut' duploid-from-sum = str.cut'
  duploid.⇑ duploid-from-sum = str.⇑
  duploid.⇓ duploid-from-sum = str.⇓
  duploid.force duploid-from-sum = str.force
  duploid.delay duploid-from-sum = str.delay
  duploid.wrap duploid-from-sum = str.wrap
  duploid.unwrap duploid-from-sum = str.unwrap
  duploid.ax-preduploid duploid-from-sum = str.ax
  duploid.⇑-negative duploid-from-sum = str.⇑-negative
  duploid.⇓-positive duploid-from-sum = str.⇓-positive
  duploid.force-linear duploid-from-sum = str.force-linear
  duploid.wrap-thunkable duploid-from-sum = str.wrap-thunkable
  duploid.force-delay-inverse duploid-from-sum = str.force-delay-inverse
  duploid.wrap-unwrap-inverse duploid-from-sum = str.wrap-unwrap-inverse

 module _ (𝓓 : duploid 𝓤 𝓥) where
  private module 𝓓 = duploid 𝓓

  private 𝓓₀ = 𝓓.underlying-deductive-system

  module _ (A : 𝓓.ob) where
   duploid-upshift-data : upshift-data 𝓓₀ A
   pr₁ duploid-upshift-data = 𝓓.⇑ A
   pr₂ duploid-upshift-data = 𝓓.force

   duploid-upshift-axioms : upshift-axioms 𝓓₀ duploid-upshift-data
   pr₁ duploid-upshift-axioms = 𝓓.⇑-negative A
   pr₁ (pr₂ duploid-upshift-axioms) = 𝓓.delay
   pr₁ (pr₂ (pr₂ duploid-upshift-axioms)) = 𝓓.force-delay-inverse
   pr₂ (pr₂ (pr₂ duploid-upshift-axioms)) = 𝓓.force-linear

   duploid-has-upshifts : has-upshift 𝓓₀ A
   pr₁ duploid-has-upshifts = duploid-upshift-data
   pr₂ duploid-has-upshifts = duploid-upshift-axioms

   duploid-downshift-data : downshift-data 𝓓₀ A
   pr₁ duploid-downshift-data = 𝓓.⇓ A
   pr₂ duploid-downshift-data = 𝓓.wrap

   duploid-downshift-axioms : downshift-axioms 𝓓₀ duploid-downshift-data
   pr₁ duploid-downshift-axioms = 𝓓.⇓-positive A
   pr₁ (pr₂ duploid-downshift-axioms) = 𝓓.unwrap
   pr₁ (pr₂ (pr₂ duploid-downshift-axioms)) = 𝓓.wrap-unwrap-inverse
   pr₂ (pr₂ (pr₂ duploid-downshift-axioms)) = 𝓓.wrap-thunkable

   duploid-has-downshifts : has-downshift 𝓓₀ A
   pr₁ duploid-has-downshifts = duploid-downshift-data
   pr₂ duploid-has-downshifts = duploid-downshift-axioms

  duploid-has-all-shifts : has-all-shifts 𝓓.underlying-deductive-system
  pr₁ (duploid-has-all-shifts A) = duploid-has-upshifts A
  pr₂ (duploid-has-all-shifts A) = duploid-has-downshifts A


  duploid-duploid-structure : duploid-structure 𝓓₀
  pr₁ duploid-duploid-structure = preduploid.ob-is-polarized 𝓓.underlying-preduploid
  pr₂ duploid-duploid-structure = duploid-has-all-shifts

  duploid-to-sum : Σ D ꞉ deductive-system 𝓤 𝓥 , duploid-structure D
  duploid-to-sum = 𝓓₀ , duploid-duploid-structure

 duploid-to-sum-is-equiv : is-equiv (duploid-to-sum {𝓤} {𝓥})
 pr₁ (pr₁ duploid-to-sum-is-equiv) = duploid-from-sum
 pr₂ (pr₁ duploid-to-sum-is-equiv) _ = refl
 pr₁ (pr₂ duploid-to-sum-is-equiv) = duploid-from-sum
 pr₂ (pr₂ duploid-to-sum-is-equiv) _ = refl

 duploid-sum-equiv : duploid 𝓤 𝓥 ≃ (Σ D ꞉ deductive-system 𝓤 𝓥 , duploid-structure D)
 duploid-sum-equiv = _ , duploid-to-sum-is-equiv


-- Some preliminary "quick notation" for working with duploids
module duploid-notation (𝓓 : duploid 𝓤 𝓥) where
 open duploid 𝓓
 _>>_ = cut
 𝒹 = delay
 𝒻 = force
 𝓌 = wrap
 𝓊 = unwrap

module duploid-extras (𝓓 : duploid 𝓤 𝓥) where
 private
  module 𝓓 = duploid 𝓓
 open preduploid-extras 𝓓.underlying-preduploid public
 open duploid-notation 𝓓

 module _ {U V : _} {f : U 𝓓.⊢ V} where
  abstract
   lem-𝒹[𝒻-] : 𝒹 >> (𝒻 >> f) ＝ f
   lem-𝒹[𝒻-] =
    𝒹 >> (𝒻 >> f) ＝⟨ 𝓓.delay-thunkable _ _ _ _ ⁻¹ ⟩
    (𝒹 >> 𝒻) >> f ＝⟨ lem-rewrite-idn-L (pr₂ 𝓓.force-delay-inverse) ⟩
    f ∎

   lem-[-𝓌]𝓊 : (f >> 𝓌) >> 𝓊 ＝ f
   lem-[-𝓌]𝓊 =
    (f >> 𝓌) >> 𝓊 ＝⟨ 𝓓.unwrap-linear _ _ _ _ ⟩
    f >> (𝓌 >> 𝓊) ＝⟨ lem-rewrite-idn-R (pr₁ 𝓓.wrap-unwrap-inverse) ⟩
    f ∎

   lem-𝓌[𝓊-] : 𝓌 >> (𝓊 >> f) ＝ f
   lem-𝓌[𝓊-] =
    𝓌 >> (𝓊 >> f) ＝⟨ 𝓓.wrap-thunkable _ _ _ _ ⁻¹ ⟩
    (𝓌 >> 𝓊) >> f ＝⟨ lem-rewrite-idn-L (pr₁ 𝓓.wrap-unwrap-inverse) ⟩
    f ∎

   lem-[-𝒹]𝒻 : (f >> 𝒹) >> 𝒻 ＝ f
   lem-[-𝒹]𝒻 =
    (f >> 𝒹) >> 𝒻 ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
    f >> (𝒹 >> 𝒻) ＝⟨ lem-rewrite-idn-R (pr₂ 𝓓.force-delay-inverse) ⟩
    f ∎

 module _ {U V : _} {f : 𝓓.⇓ U 𝓓.⊢ V} where
  abstract
   lem-𝓊[𝓌-] : 𝓊 >> (𝓌 >> f) ＝ f
   lem-𝓊[𝓌-] =
    (𝓊 >> (𝓌 >> f)) ＝⟨ f-lin _ _ _ _ ⁻¹ ⟩
    (𝓊 >> 𝓌) >> f ＝⟨ lem-rewrite-idn-L (pr₂ 𝓓.wrap-unwrap-inverse) ⟩
    f ∎
    where
     f-lin : 𝓓.is-linear f
     f-lin = 𝓓.⇓-positive U V f


\end{code}
