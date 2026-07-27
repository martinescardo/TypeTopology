Martin Escardo, July 2026.

Given a large, locally small setoid, we show that the free egroup on it
is large, in the sense that no egroup whose underlying type and
equivalence relation are both small is isomorphic to it.

We then give an example, which is what the EGroups development is for,
by taking the universe as a setoid under type equivalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.List renaming (_∷_ to _•_ ; _++_ to _◦_)

module EGroups.Large where

open import UF.Equiv hiding (_≅_)
open import UF.Size
open import Relations.SRTclosure
open import Various.LawvereFPT

open import EGroups.Setoid
open import EGroups.Type
open import EGroups.Size

module large-free-egroup
        {𝓤 : Universe}
        (A : 𝓤 ⁺ ̇ )
        (_≈_ : A → A → 𝓤 ̇ )
        (≈r : reflexive  _≈_)
        (≈s : symmetric  _≈_)
        (≈t : transitive _≈_)
       where

 open import EGroups.Reduction A _≈_ ≈r ≈s ≈t
 open import EGroups.Free A _≈_ ≈r ≈s ≈t

\end{code}

We introduce the setoid of generators, together with three lemmas.
First, ≈-related generators are convertible, via a ▷-peak. Second, if
two generators are ≈[FA]-related, then their underlying unsigned
elements are ≈-related. Third, a generator witness for s exhibits s as
convertible to a single generator.

\begin{code}

 𝔸 : Setoid (𝓤 ⁺) 𝓤
 𝔸 = A , _≈_ , ≈r , ≈s , ≈t

 η-∿ : (a a' : A) → a ≈ a' → η a ∿ η a'
 η-∿ a a' e = srt-transitive _▷_ (η a) w (η a')
               (srt-symmetric _▷_ w (η a) (srt-extension _▷_ w (η a) I))
               (srt-extension _▷_ w (η a') I')
  where
   w : FA
   w = (₀ , a) • (₁ , a') • (₀ , a') • []

   I' : w ▷ η a'
   I' = [] ,
       ((₀ , a') • []) ,
       (₀ , a) ,
       (₁ , a') ,
       refl ,
       refl ,
       (refl , ≈s a a' e)

   I : w ▷ η a
   I = ((₀ , a) • []) ,
        [] ,
        (₁ , a') ,
        (₀ , a') ,
        refl ,
        refl , (
        refl , ≈r a')

 η-≈[FA]→≈ : {a a' : A} → η a ≈[FA] η a' → a ≈ a'
 η-≈[FA]→≈ ((_ , e) , _) = e

 generator→∿ : (s : FA) (w : generator s) → s ∿ η (underlying-generator w)
 generator→∿ s (n , ρ , a , p) = rt-gives-srt _▷_ s (η a) (n , I)
  where
   I : iteration _▷_ n s (η a)
   I = transport (iteration _▷_ n s) (p ⁻¹) (chain-lemma→ s n ρ)

\end{code}

We now prove the theorem. If some egroup 𝓖 whose underlying type and
equivalence relation are both small is isomorphic to the free egroup,
then 𝔸 is a small setoid. The map κ = G ∘ η into ⟨𝓖⟩ is both
≈-respecting and ≈-reflecting, so 𝔸 is setoid-isomorphic to the small
setoid of generators inside ⟨𝓖⟩.

\begin{code}

 small-copy-gives-small-setoid
  : (𝓖 : EGroup 𝓤 𝓤) → 𝓖 ≅ free-egroup → is-small-setoid 𝓤 𝔸
 small-copy-gives-small-setoid 𝓖 (F , (F-resp , _) , G , (G-resp , _) , FG , GF)
  = T , iso
  where
   κ : A → ⟨ 𝓖 ⟩
   κ a = G (η a)

   κ-respects : (a a' : A) → a ≈ a' → κ a ≈⟨ 𝓖 ⟩ κ a'
   κ-respects a a' e = G-resp (η-∿ a a' e)

   κ-reflects : (a a' : A) → κ a ≈⟨ 𝓖 ⟩ κ a' → a ≈ a'
   κ-reflects a a' r =
    η-≈[FA]→≈
     (η-identifies-∿-related-points a a'
       (srt-transitive _▷_ (η a) (F (G (η a'))) (η a')
         (srt-transitive _▷_ (η a) (F (G (η a))) (F (G (η a')))
           (srt-symmetric _▷_ (F (G (η a))) (η a) (FG (η a)))
           (F-resp r))
         (FG (η a'))))

   abstract
    is-gen : ⟨ 𝓖 ⟩ → 𝓤 ̇
    is-gen y = resized (generator (F y)) (generator-is-small (F y))

    to-gen : (y : ⟨ 𝓖 ⟩) → is-gen y → generator (F y)
    to-gen y = ⌜ resizing-condition (generator-is-small (F y)) ⌝

    from-gen : (y : ⟨ 𝓖 ⟩) → generator (F y) → is-gen y
    from-gen y = ⌜ resizing-condition (generator-is-small (F y)) ⌝⁻¹

    to-from-gen : (y : ⟨ 𝓖 ⟩) (w : generator (F y))
                → to-gen y (from-gen y w) ＝ w
    to-from-gen y =
     inverses-are-sections
      ⌜ resizing-condition (generator-is-small (F y)) ⌝
      (⌜⌝-is-equiv (resizing-condition (generator-is-small (F y))))

   ∣T∣ : 𝓤 ̇
   ∣T∣ = Σ y ꞉ ⟨ 𝓖 ⟩ , is-gen y

   _≈ᵀ_ : ∣T∣ → ∣T∣ → 𝓤 ̇
   (y , _) ≈ᵀ (y' , _) = y ≈⟨ 𝓖 ⟩ y'

   T : Setoid 𝓤 𝓤
   T = ∣T∣
     , _≈ᵀ_
     , (λ (y , _) → erefl 𝓖 y)
     , (λ (y , _) (y' , _) r → esym 𝓖 y y' r)
     , (λ (y , _) (y' , _) (y'' , _) r r' → etrans 𝓖 y y' y'' r r')

   gen-of : (a : A) → generator (F (κ a))
   gen-of a = ∿→generator (srt-symmetric _▷_ (F (G (η a))) (η a) (FG (η a)))

   to : A → ∣T∣
   to a = κ a , from-gen (κ a) (gen-of a)

   from : ∣T∣ → A
   from (y , w) = underlying-generator (to-gen y w)

   to-resp : is-setoid-map 𝔸 T to
   to-resp {a} {a'} e = κ-respects a a' e

   from-resp : is-setoid-map T 𝔸 from
   from-resp {y , w} {y' , w'} r =
    η-≈[FA]→≈
     (η-identifies-∿-related-points (from (y , w)) (from (y' , w'))
       (srt-transitive _▷_ (η (from (y , w))) (F y') (η (from (y' , w')))
         (srt-transitive _▷_ (η (from (y , w))) (F y) (F y')
           (srt-symmetric _▷_ (F y) (η (from (y , w)))
             (generator→∿ (F y) (to-gen y w)))
           (F-resp r))
         (generator→∿ (F y') (to-gen y' w'))))

   to-from : (t : ∣T∣) → to (from t) ≈ᵀ t
   to-from (y , w) =
    etrans 𝓖 (κ a₀) (G (F y)) y
      (esym 𝓖 (G (F y)) (κ a₀) (G-resp (generator→∿ (F y) (to-gen y w))))
      (GF y)
    where
     a₀ : A
     a₀ = underlying-generator (to-gen y w)

   from-to : (a : A) → from (to a) ≈ a
   from-to a =
    transport (λ z → z ≈ a)
     (ap (underlying-generator {F (κ a)}) ((to-from-gen (κ a) (gen-of a)) ⁻¹))
     (underlying-generator-∿→generator
       (srt-symmetric _▷_ (F (G (η a))) (η a) (FG (η a))))

   iso : 𝔸 ≅ˢ T
   iso = record
          { to        = to
          ; from      = from
          ; to-resp   = to-resp
          ; from-resp = from-resp
          ; to-from   = to-from
          ; from-to   = from-to
          }

\end{code}

Taking the contrapositive, if 𝔸 is a large setoid then the free egroup
on 𝔸, which lives in the next universe, has no small copy.

\begin{code}

 large-setoid-gives-large-egroup
  : is-large-setoid 𝓤 𝔸
  → (𝓖 : EGroup 𝓤 𝓤) → ¬ (𝓖 ≅ free-egroup)
 large-setoid-gives-large-egroup 𝔸-large 𝓖 iso
  = 𝔸-large (small-copy-gives-small-setoid 𝓖 iso)

 there-is-a-large-egroup
  : is-large-setoid 𝓤 𝔸
  → Σ 𝓕 ꞉ EGroup (𝓤 ⁺) (𝓤 ⁺) , ((𝓖 : EGroup 𝓤 𝓤) → ¬ (𝓖 ≅ 𝓕))
 there-is-a-large-egroup 𝔸-large
  = free-egroup , large-setoid-gives-large-egroup 𝔸-large

\end{code}

An example of a large egroup, which is what the EGroups development is for.

We instantiate the above with the universe 𝓤, taken as a setoid
under type equivalence _≃_. This gives an egroup in the next universe
𝓤⁺ that is isomorphic to no egroup in the universe 𝓤, in a Spartan
MLTT with no HoTT/UF assumptions.

\begin{code}

module _ (𝓤 : Universe) where

 open large-free-egroup
       (𝓤 ̇ ) _≃_ ≃-refl (λ X Y → ≃-sym) (λ X Y Z → _●_)
      renaming (𝔸 to 𝕌)

\end{code}

The universe setoid 𝕌 = (𝓤 ̇ , _≃_) is large.

\begin{code}

 universe-setoid-is-large : is-large-setoid 𝓤 𝕌
 universe-setoid-is-large (T , iso) =
  generalized-Coquand.Lemma₂ ∣ T ∣
   (_≅ˢ_.from iso) (_≅ˢ_.to iso) (_≅ˢ_.from-to iso)

\end{code}

Therefore the free egroup on the universe setoid, which lives in the
next universe, is isomorphic to no egroup whose underlying type and
equivalence relation are both small.

\begin{code}

 large-egroup-in-the-next-universe
  : Σ 𝓕 ꞉ EGroup (𝓤 ⁺) (𝓤 ⁺) , ((𝓖 : EGroup 𝓤 𝓤) → ¬ (𝓖 ≅ 𝓕))
 large-egroup-in-the-next-universe
  = there-is-a-large-egroup universe-setoid-is-large

\end{code}
