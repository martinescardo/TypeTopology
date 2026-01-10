Ian Ray. 28th August 2025.

The structure identity principle (SIP), coined by Peter Aczel, allows an
treatment of identificiation in Univalent Foundations that, with much care,
escapes "transport hell". Many have formulated there own terminology and
approach to SIP (including Egbert Rijke in "Introduction to Homotopy Type
Theory"; Martin Escardo see files: StructureIdentityPrinciple, Yoneda and
SigmaIdentity; as well as many others!) In recent times, some have
considered 'reflexive graphs' as a more systematic approach to SIP (see
"Using Displayed Univalent Graphs to Formalize Higher Groups in Univalent
Foundations" by Johannes Schipp von Branitz and Ulrik Buchholtz; and
"Reflexive graph lenses in univalent foundations" by Jonathan Sterling).

We will develop a portion of the theory of reflexive graphs here while
primarily following Jonathon Sterling's treatment from the aformentioned
paper.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.ReflexiveGraphs where

open import MLTT.Spartan

\end{code}

A reflexive graph consists of a type, a binary type valued relation and a
reflexivity datum.

\begin{code}

module _ (𝓤 𝓥 : Universe) where

 refl-graph : (𝓤 ⊔ 𝓥)⁺ ̇
 refl-graph = Σ A ꞉ 𝓤 ̇ , Σ R ꞉ (A → A → 𝓥 ̇) , ((x : A) → R x x)

\end{code}

We give some boiler plate/syntax

\begin{code}

⊰_⊱ : refl-graph 𝓤 𝓥 → 𝓤 ̇
⊰ (A , _) ⊱ = A

edge-rel : (𝓐 : refl-graph 𝓤 𝓥) → ⊰ 𝓐 ⊱ → ⊰ 𝓐 ⊱ → 𝓥 ̇
edge-rel (_ , R , _) = R

syntax edge-rel 𝓐 x y = x ≈⟨ 𝓐 ⟩ y

𝓻 : (𝓐 : refl-graph 𝓤 𝓥) → (x : ⊰ 𝓐 ⊱) → x ≈⟨ 𝓐 ⟩ x
𝓻 (_ , _ , r) x = r x

\end{code}

We define a homomorphism of reflexive graphs as a sigma and record type.

TODO. Decide which is preferred. So far this notion hasn't been used but it
seems to be an important theoretical notion...

\begin{code}

refl-graph-hom : (𝓐 : refl-graph 𝓤 𝓥) (𝓐' : refl-graph 𝓤' 𝓥')
               → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
refl-graph-hom 𝓐 𝓐'
 = Σ F ꞉ (⊰ 𝓐 ⊱ → ⊰ 𝓐' ⊱) ,
    Σ F' ꞉ ((x y : ⊰ 𝓐 ⊱) → x ≈⟨ 𝓐 ⟩ y → F x ≈⟨ 𝓐' ⟩ F y) ,
     ((x : ⊰ 𝓐 ⊱) → F' x x (𝓻 𝓐 x) ＝ 𝓻 𝓐' (F x))

record refl-graph-hom-record
 (𝓐 : refl-graph 𝓤 𝓥) (𝓐' : refl-graph 𝓤' 𝓥') : 𝓤ω where
 field
  func : ⊰ 𝓐 ⊱ → ⊰ 𝓐' ⊱
  act : (x y : ⊰ 𝓐 ⊱) → x ≈⟨ 𝓐 ⟩ y → func x ≈⟨ 𝓐' ⟩ func y
  pres-ref : (x : ⊰ 𝓐 ⊱) → act x x (𝓻 𝓐 x) ＝ 𝓻 𝓐' (func x)

\end{code}
