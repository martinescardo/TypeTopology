Jon Sterling, started 16th Dec 2022

A duploid is a preduploid that has "shifts" between positive and negative
objects.

1. An "upshift" for an object `A` is a negative object `⇑A` together with an
invertible thunkable map `wrap : A ⊢ ⇑A`.

2. A "downshift" for an object `A` is a positive object `⇓A` together with an
invertible linear map `force : ⇓A ⊢ A`.

Note that the inverses to the maps specified above are uniquely determined.  The
upshift and downshift, when viewed in terms of the categories obtained from the
duploid, will ultimately form a pair of adjunctions `↑⊣↓` and `⇓⊣⇑`
respectively:

1. The upshift becomes a *left* adjoint functor `↑ : 𝓟-thunk → 𝓝-lin` from the
category of positive types and thunkable maps to the category of negative
objects and linear maps. Its right adjoint is the downshift `↓ : 𝓝-lin →
𝓟-thunk`.

2. The upshift becomes a *right* adjoint functor `⇑ : 𝓟 → 𝓝` from the category
of positive types and all maps to the category of negative objects and all
maps. Its left adjoint is the downshift `⇓ : 𝓝 → 𝓟`.

The category of positive objects and all maps is the Kleisli category for the
monad of the adjunction `↑⊣↓`; the category of negative objects and all maps is
the Kleisli category for the comonad of `↑⊣↓`. Then the (flipped) adjunction
`⇓⊣⇑` is the usual adjunction between the Kleisli categories for the monad and
the comonad respectively.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import UF.FunExt
open import UF.PropTrunc

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

-- forget linearity
module 𝓢⇒𝓝 (𝓓 : duploid 𝓤 𝓥) where
 private
  module 𝓓 = duploid 𝓓
  𝓝 = NegativesAndAllMaps.precat 𝓓.underlying-preduploid
  𝓢 = NegativesAndLinearMaps.precat 𝓓.underlying-preduploid

 open functor-of-precategories
 open duploid-notation 𝓓

 structure : functor-structure 𝓢 𝓝
 pr₁ structure A = A
 pr₂ structure A B f = pr₁ f

 axioms : functor-axioms 𝓢 𝓝 structure
 pr₁ axioms _ = refl
 pr₂ axioms _ _ _ _ _ = refl

 fun : functor 𝓢 𝓝
 fun = make structure axioms

-- forget thunkability
module 𝓒⇒𝓟 (𝓓 : duploid 𝓤 𝓥) where
 private
  module 𝓓 = duploid 𝓓
  𝓒 = PositivesAndThunkableMaps.precat 𝓓.underlying-preduploid
  𝓟 = PositivesAndAllMaps.precat 𝓓.underlying-preduploid

 open functor-of-precategories
 open duploid-notation 𝓓

 structure : functor-structure 𝓒 𝓟
 pr₁ structure A = A
 pr₂ structure A B f = pr₁ f

 axioms : functor-axioms 𝓒 𝓟 structure
 pr₁ axioms _ = refl
 pr₂ axioms _ _ _ _ _ = refl

 fun : functor 𝓒 𝓟
 fun = make structure axioms


module 𝓟⇒𝓢 (𝓓 : duploid 𝓤 𝓥) where
 private
  module 𝓓 = duploid 𝓓
  𝓟 = PositivesAndAllMaps.precat 𝓓.underlying-preduploid
  𝓝 = NegativesAndAllMaps.precat 𝓓.underlying-preduploid
  𝓢 = NegativesAndLinearMaps.precat 𝓓.underlying-preduploid

  module 𝓟 = precategory 𝓟
  module 𝓝 = precategory 𝓝
  module 𝓢 = precategory 𝓢

 open functor-of-precategories
 open duploid-notation 𝓓

 module str where
  ob : 𝓟.ob → 𝓢.ob
  ob (A , A-pos) = 𝓓.⇑ A , 𝓓.⇑-negative A

  hom-𝓝 : (A B : 𝓟.ob) → 𝓟.hom A B → 𝓝.hom (ob A) (ob B)
  hom-𝓝 A B f = 𝒻 >> (f >> 𝒹)

  hom-linear : (A B : 𝓟.ob) (f : 𝓟.hom A B) → 𝓓.is-linear (hom-𝓝 A B f)
  hom-linear A B f U V g h =
   ((h >> g) >> (𝒻 >> (f >> 𝒹))) ＝⟨ hg-th _ _ _ _ ⁻¹ ⟩
   ((h >> g) >> 𝒻) >> (f >> 𝒹) ＝⟨ ap (_>> (f >> 𝒹)) (𝓓.force-linear _ _ _ _) ⟩
   (h >> (g >> 𝒻)) >> (f >> 𝒹) ＝⟨ f𝒹-lin _ _ _ _ ⟩
   (h >> ((g >> 𝒻) >> (f >> 𝒹))) ＝⟨ ap (h >>_) (g-th _ _ _ _) ⟩
   h >> (g >> (𝒻 >> (f >> 𝒹))) ∎
   where
    f𝒹-lin : 𝓓.is-linear (f >> 𝒹)
    f𝒹-lin = pr₂ A (𝓓.⇑ (pr₁ B)) (f >> 𝒹)

    g-th : 𝓓.is-thunkable g
    g-th = 𝓓.⇑-negative (pr₁ A) V g

    hg-th : 𝓓.is-thunkable (h >> g)
    hg-th = 𝓓.⇑-negative (pr₁ A) U (h >> g)

  hom : (A B : 𝓟.ob) (f : 𝓟.hom A B) → 𝓢.hom (ob A) (ob B)
  hom A B f = hom-𝓝 A B f , hom-linear A B f

  structure : functor-structure 𝓟 𝓢
  structure = ob , hom

 module ax where
  private
   abstract
    preserves-idn-𝓝 : (A : 𝓟.ob) → 𝒻 >> (𝓓.idn _ >> 𝒹) ＝ 𝓓.idn (𝓓.⇑ (pr₁ A))
    preserves-idn-𝓝 (A , A-pos) =
     𝒻 >> (𝓓.idn A >> 𝒹) ＝⟨ ap (𝒻 >>_) (𝓓.idn-L _ _ _) ⟩
     𝒻 >> 𝒹 ＝⟨ pr₁ 𝓓.force-delay-inverse ⟩
     𝓓.idn (𝓓.⇑ A) ∎

    preserves-seq-𝓝
     : (A B C : 𝓟.ob)
     → (f : 𝓟.hom A B)
     → (g : 𝓟.hom B C)
     → 𝒻 >> ((f >> g) >> 𝒹) ＝ (𝒻 >> (f >> 𝒹)) >> (𝒻 >> (g >> 𝒹))
    preserves-seq-𝓝 (A , A-pos) (B , B-pos) (C , C-pos) f g =
     𝒻 >> ((f >> g) >> 𝒹) ＝⟨ ap (𝒻 >>_) (𝒹-linear _ _ _ _) ⟩
     𝒻 >> (f >> (g >> 𝒹)) ＝⟨ g-𝒹-linear _ _ _ _ ⁻¹ ⟩
     ((𝒻 >> f) >> (g >> 𝒹)) ＝⟨ ap (_>> (g >> 𝒹)) (help1 ⁻¹) ⟩
     ((𝒻 >> (f >> 𝒹)) >> 𝒻) >> (g >> 𝒹) ＝⟨ g-𝒹-linear _ _ _ _ ⟩
     (𝒻 >> (f >> 𝒹)) >> (𝒻 >> (g >> 𝒹)) ∎
     where
      help2 : (f >> 𝒹) >> 𝒻 ＝ f
      help2 =
       (f >> 𝒹) >> 𝒻 ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
       f >> (𝒹 >> 𝒻) ＝⟨ ap (f >>_) (pr₂ 𝓓.force-delay-inverse) ⟩
       f >> 𝓓.idn _ ＝⟨ 𝓓.idn-R _ _ _ ⟩
       f ∎

      help1 : ((𝒻 >> (f >> 𝒹)) >> 𝒻) ＝ 𝒻 >> f
      help1 =
       ((𝒻 >> (f >> 𝒹)) >> 𝒻) ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
       (𝒻 >> ((f >> 𝒹) >> 𝒻)) ＝⟨ ap (𝒻 >>_) help2 ⟩
       (𝒻 >> f) ∎

      g-𝒹-linear : 𝓓.is-linear (g >> 𝒹)
      g-𝒹-linear = B-pos (𝓓.⇑ C) (g >> 𝒹)

      𝒹-linear : 𝓓.is-linear (𝒹 {C})
      𝒹-linear = C-pos (𝓓.⇑ C) 𝒹


    preserves-idn : statement-preserves-idn 𝓟 𝓢 str.structure
    preserves-idn A =
     NegativesAndLinearMaps.to-hom-＝ 𝓓.underlying-preduploid (str.ob A) (str.ob A) _ _
      (preserves-idn-𝓝 A)

    preserves-seq : statement-preserves-seq 𝓟 𝓢 str.structure
    preserves-seq A B C f g =
     NegativesAndLinearMaps.to-hom-＝ 𝓓.underlying-preduploid (str.ob A) (str.ob C) _ _
      (preserves-seq-𝓝 A B C f g)


  axioms : functor-axioms 𝓟 𝓢 str.structure
  axioms = preserves-idn , preserves-seq

 fun : functor 𝓟 𝓢
 fun = make str.structure ax.axioms


-- The ↑ functor
module 𝓒⇒𝓢 (𝓓 : duploid 𝓤 𝓥) where
 private
  module 𝓓 = duploid 𝓓
  𝓒 = PositivesAndThunkableMaps.precat 𝓓.underlying-preduploid
  𝓟 = PositivesAndAllMaps.precat 𝓓.underlying-preduploid
  𝓝 = NegativesAndAllMaps.precat 𝓓.underlying-preduploid
  𝓢 = NegativesAndLinearMaps.precat 𝓓.underlying-preduploid

 open functor-of-precategories

 fun : functor 𝓒 𝓢
 fun = composite-functor.fun (𝓒⇒𝓟.fun 𝓓) (𝓟⇒𝓢.fun 𝓓)

-- The ⇑ functor
module 𝓟⇒𝓝 (𝓓 : duploid 𝓤 𝓥) where
 private
  module 𝓓 = duploid 𝓓
  𝓟 = PositivesAndAllMaps.precat 𝓓.underlying-preduploid
  𝓝 = NegativesAndAllMaps.precat 𝓓.underlying-preduploid
  𝓢 = NegativesAndLinearMaps.precat 𝓓.underlying-preduploid

 open functor-of-precategories

 fun : functor 𝓟 𝓝
 fun = composite-functor.fun (𝓟⇒𝓢.fun 𝓓) (𝓢⇒𝓝.fun 𝓓)

\end{code}
