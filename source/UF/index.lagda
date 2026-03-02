\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.index where

import UF.Base
import UF.Choice
import UF.ClassicalLogic
import UF.Classifiers
import UF.Classifiers-Old
import UF.CoconesofSpans                    -- by [2]
import UF.Connected
import UF.ConnectedTypes                    -- by [2]
import UF.CumulativeHierarchy               -- by [1]
import UF.CumulativeHierarchy-LocallySmall  -- by [1]
import UF.DependentEquality
import UF.DiscreteAndSeparated
import UF.Embeddings
import UF.Equiv
import UF.Equiv-FunExt
import UF.EquivalenceExamples
import UF.ExitPropTrunc
import UF.FundamentalLemmaOfTransportAlongEquivalences
import UF.FunExt
import UF.FunExt-Properties
import UF.FunExt-from-Naive-FunExt
import UF.Groupoids
import UF.HLevels
import UF.Hedberg
import UF.HedbergApplications
import UF.HiddenSwap
import UF.IdEmbedding
import UF.IdentitySystems
import UF.ImageAndSurjection
import UF.ImageAndSurjection-Variation
import UF.JoinConstruction                  -- by [2]
import UF.JoinofMaps                        -- by [2]
import UF.Knapp-UA
import UF.KrausLemma
import UF.LeftCancellable
import UF.Logic
import UF.Lower-FunExt
import UF.NotNotStablePropositions
import UF.PairFun
import UF.Powerset
import UF.Powerset-Fin
import UF.Powerset-MultiUniverse
import UF.Powerset-Resizing
import UF.PreSIP
import UF.PreSIP-Examples
import UF.PreUnivalence
import UF.PropIndexedPiSigma
import UF.PropTrunc
import UF.PropTrunc-Variation
import UF.Pullback
import UF.Pushouts                   -- by [2]
import UF.Replacement                -- by [2]
import UF.Retracts
import UF.Retracts-FunExt
import UF.SIP
import UF.SIP-Examples
import UF.Section-Embedding
import UF.SemistrictIdentity
import UF.SetTrunc
import UF.Sets
import UF.Sets-Properties
import UF.SequentialColimits         -- by [2]
import UF.SigmaIdentity
import UF.Singleton-Properties       -- by [2]
import UF.Size
import UF.Size-TruncatedConnected    -- by [2]
import UF.SmallnessProperties
import UF.StructureIdentityPrinciple -- Obsolete but keep. Use UF.SIP instead
import UF.Subsingletons
import UF.Subsingletons-FunExt
import UF.Subsingletons-Properties
import UF.SubtypeClassifier
import UF.SubtypeClassifier-Properties
import UF.TruncationLevels
import UF.Truncations                -- by [2]
import UF.TruncatedTypes             -- by [2]
import UF.UA-FunExt
import UF.Univalence
import UF.UniverseEmbedding
import UF.Universes
import UF.Yoneda

\end{code}

[1] de Jong, Kraus, Nordvall Forsberg and Xu.
[2] Ray
