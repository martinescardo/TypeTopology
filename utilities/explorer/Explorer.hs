-- Martin Escardo 6th May 2026.
--
-- Program to explore this repositorie's dependency graph.
-- Best run from ghci. See examples below.
--
-- To use this program, you must first run ./generateHaskellgraph.sh.

module Explorer where

import Data.Graph
import Data.Function
import Data.Tuple
import Data.List
import qualified Data.Map.Lazy as M

-- Build the dependency graph and its transpose. There is an edge from
-- x to y if x imports y.

import DependencyGraph

bounds :: (Int,Int)
bounds = (minimum (map fst labels) , maximum (map fst labels))

graph :: Graph
graph = buildG bounds imports

tgraph :: Graph
tgraph = transposeG graph

-- Tools for (de)coding strings.

type Filename = String

filenames :: [Filename]
filenames = map snd labels

code2name :: M.Map Int Filename
code2name = M.fromList labels

name2code :: M.Map Filename Int
name2code = M.fromList (map swap labels)

just :: Maybe a -> a
just Nothing = undefined
just (Just x) = x

code :: Filename -> Int
code s = just (M.lookup s name2code )

decode :: Int -> Filename
decode n = just (M.lookup n code2name)

-- Some useful queries the user may want to perform.

descendants :: Filename -> [Filename]
descendants s = [ decode r | r <- reachable graph (code s) ]

ancestors :: Filename -> [Filename]
ancestors s = [ decode r | r <- reachable tgraph (code s) ]

nodescendants :: Filename -> Int
nodescendants s = length (descendants s)

noancestors :: Filename -> Int
noancestors s = length (ancestors s)

topologicalsort :: [Filename]
topologicalsort = map decode (topSort graph)

reaches :: Filename -> Filename -> Bool
reaches s t = path graph (code s) (code t)

tablenodescendants :: [(Filename,Int)]
tablenodescendants = sortOn snd [ (s , nodescendants s) | s <- filenames ]

tablenoancestors :: [(Filename,Int)]
tablenoancestors = sortOn snd [ (s , noancestors s) | s <- filenames ]

height :: Tree a -> Int
height (Node a []) = 0
height (Node a ts) = maximum (map height ts) + 1

hd :: [a] -> a
hd []    = undefined
hd (x:_) = x

longestdistancefrom :: Filename -> Int
longestdistancefrom s = height (hd (dfs graph [code s]))

longestdistanceto :: Filename -> Int
longestdistanceto s = height (hd (dfs tgraph [code s]))

height' :: Tree a -> (Int,[a])
height' (Node a ts) = suc' (foldl max' (0,[]) (map height' ts))
  where
    max' (m,s) (n,t) = if m > n then (m,s) else (n,t)
    suc' (m,s) = (m+1,a:s)

longestpathfrom :: Filename -> [Filename]
longestpathfrom s = map decode (snd (height' (hd (dfs graph [code s]))))

longestpathto :: Filename -> [Filename]
longestpathto s = reverse (map decode (snd (height' (hd (dfs tgraph [code s])))))

-- For more available features, to possibly incorporate here, see
-- https://hackage-content.haskell.org/package/containers-0.8/docs/Data-Graph.html

-- We simulate the unix command `less` (but you have to press enter to continue).

mprint :: Show a => [a] -> IO ()
mprint = mapM_ print

breakpoint = 20

less :: Show a => [a] -> IO ()
less s = if length s < breakpoint
         then mprint s
         else do
          let (t,u) = splitAt breakpoint s
          mprint t
          getLine
          less u

-- Examples.

example1  = less tablenodescendants
example2  = less tablenoancestors
example3  = less (ancestors "UF.Base")
example4  = less (descendants "UF.Base")
example5  = nodescendants "UF.Base"
example6  = noancestors "UF.Base"
example7  = reaches "InjectiveTypes.Blackboard" "UF.Sets"
example8  = reaches "InjectiveTypes.Blackboard" "UF.SIP"
example9  = less (longestpathto "InjectiveTypes.Blackboard")
example10 = less (longestpathfrom "InjectiveTypes.Blackboard")
example11 = longestdistancefrom "InjectiveTypes.Blackboard"
example12 = longestdistanceto "InjectiveTypes.Blackboard"
example13 = less (longestpathfrom "AllModulesIndex")
example14 = length (longestpathfrom "AllModulesIndex")
