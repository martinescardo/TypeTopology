{-|
Module      : GenerateMakefile
Description : Translate a Dot dependency graph of Agda modules into a Makefile.
Author      : Ayberk Tosun
-}

module Main where

import Data.List (isInfixOf)
import Data.Char (isSpace)
import System.IO (IOMode(ReadMode), openFile, hGetContents, hClose)

agdaVersion :: String
agdaVersion = "2.6.4.3"

data Declaration = Variable Int String
                 | Dependency Int Int
                 deriving (Eq, Show)

type ModuleID = Int

-- | Remove all spaces in a string.
trim :: String -> String
trim = filter (not . isSpace)

-- | Parse a line of the form "x -> y", which expresses a dependency.
parseDependency :: String -> Declaration
parseDependency s = Dependency (read $ tail s1) (read $ tail s2)
  where
    s1 = trim . takeWhile (/= '-') $ s
    s2 = trim . init . tail $ dropWhile (/= '>') s

-- | Removes the symbols ';', '[', ']', and '"'.
removeSymbols :: String -> String
removeSymbols = filter (\c -> c /= ';' && c /= ']' && c /= ']' && c /= '"')

-- | Parse a line that is either of the form "x[label="foo"];" or "x -> y;".
parse :: String -> Declaration
parse s
  | "label" `isInfixOf` s = let
                              v     = trim $ takeWhile (/= '[') s
                              fname = removeSymbols $ dropWhile (/= '"') $ s
                            in Variable (read (tail v)) fname
  | "->" `isInfixOf` s    = parseDependency s
  | otherwise             = error "cannot parse line"

-- | Extract mappings of variables to file names from a list of declarations.
fileNames :: [Declaration] -> [(Int, String)]
fileNames []                  = []
fileNames (Variable n s:ds)   = (n, s) : fileNames ds
fileNames (Dependency _ _:ds) = fileNames ds

-- | Get the dependencies of a given module 'n'.
dependencies :: ModuleID -> [Declaration] -> [ModuleID]
dependencies n []                             = []
dependencies n (Variable _ _:ds)              = dependencies n ds
dependencies n (Dependency n' m:ds) | n == n' = m : dependencies n ds
dependencies n (Dependency n' m:ds)           = dependencies n ds

-- | Collect together the list of dependencies for every module.
allDependencies :: [(Int, String)] -> [Declaration] -> [Int] -> [(Int, [Int])]
allDependencies fs decls is = [ (i, dependencies i decls) | i <- is ]

-- | Replace '.' with '/' in the given string.
substDotForSlash :: String -> String
substDotForSlash s = f <$> s
  where
    f :: Char -> Char
    f c = if c == '.' then '/' else c

-- | Given a module ID 'n', returns the path of the .agdai file corresponding
-- to that module.
agdaiFile :: [(Int, String)] -> ModuleID -> String
agdaiFile fs n =
  case n `lookup` fs of
    Just fname -> "_build/" ++ agdaVersion ++ "/agda/source/"
                  ++ substDotForSlash fname ++ ".agdai"
    Nothing    -> error "file name not found"

-- | Given a module ID 'n', returns the path of the source file for module 'n'.
lagdaFile :: [(Int, String)] -> Int -> String
lagdaFile fs n =
  case n `lookup` fs of
    Just fname -> "source/" ++ substDotForSlash fname ++ ".lagda"
    Nothing    -> error "file name not found"

-- | Generates the target for a given module ID 'n'.
generateMakefileTarget :: [(Int, String)] -> [Declaration] -> Int -> String
generateMakefileTarget fs decls n = concat [l1, l2, l3]
  where
    is = dependencies n decls
    l1 = agdaiFile fs n
         ++ ": " ++ unwords (lagdaFile fs n : (agdaiFile fs <$> is)) ++ "\n"
    l2 = "\tagda --safe " ++ lagdaFile fs n ++ "\n"
    l3 = "\ttouch $@" ++ "\n"

-- | Goes through all of the declarations and generates the corresponding list of
-- Makefile targets
generateMakefile :: [(Int, String)] -> [Declaration] -> [Int] -> [String]
generateMakefile fs decls []     = []
generateMakefile fs decls (n:ns) =
  generateMakefileTarget fs decls n : generateMakefile fs decls ns

-- | Emit target for "Primitive.agdai".
emitTargetForPrimitive :: IO ()
emitTargetForPrimitive = do
  putStrLn $ "_build/" ++ agdaVersion ++ "/agda/source/Agda/Primitive.agdai:"
  putStrLn $ "\tagda --safe source/MLTT/Universes.lagda\n"

-- | Emit all the targets of the Makefile to be generated.
emitLineForTargetAll :: IO ()
emitLineForTargetAll =
  putStrLn $ "all: _build/" ++ agdaVersion ++ "/agda/source/index.agdai\n"

main :: IO ()
main = do
  handle       <- openFile "admin-utilities/dependency_graph.dot" ReadMode
  content      <- hGetContents handle

  let
    declarations = parse <$> (tail . init . lines $ content)
    fnames       = fileNames declarations
    fileIds      = fst <$> fnames
    primId       = head [ n | (n, s) <- fnames, s == "Agda.Primitive" ]

  emitLineForTargetAll
  emitTargetForPrimitive
  mapM_ putStrLn $ generateMakefile fnames declarations (filter (/= primId) fileIds)
  hClose handle
