The following is based on http://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf

\begin{code}


module SyntheticTopology (isOpenProp : U ̇ → U ̇)
                         (isd : isDominance isOpenProp)
                         (pt : PropTrunc) where
                         
 open PropositionalTruncation (pt)
 
 𝕊 : U' ̇
 𝕊 = Σ \(G : U ̇) → isOpenProp G

 ⊤ : 𝕊
 ⊤ = (𝟙 , 𝟙-isDominant (isOpenProp , isd))

 OpenSubset : U ̇ → U' ̇
 OpenSubset X = X → 𝕊

 _∈_ : {X : U ̇} → X → OpenSubset X → U ̇
 x ∈ G = pr₁(G x)

 isCompact : U ̇ → U' ̇
 isCompact X = (G : OpenSubset X) → isOpenProp(∀ (x : X) → x ∈ G)

 isOvert : U ̇ → U' ̇
 isOvert X = (G : OpenSubset X) → isOpenProp (∃ \(x : X) → x ∈ G)

 isClosedProp : U ̇ → U' ̇
 isClosedProp F = ∀ G → isOpenProp G → isOpenProp(F → G)

 isClosedSubset : {X : U ̇} → (X → U ̇) → U' ̇
 isClosedSubset A = ∀ x → isClosedProp(A x)

 isDiscrete : U ̇ → U ̇
 isDiscrete X = (x y : X) → isOpenProp(x ≡ y)

 isHausdorff : U ̇ → U' ̇
 isHausdorff X = (x y : X) → isClosedProp(x ≡ y)


\end{code}

TODO. Prove the theorems of loc. cit.
