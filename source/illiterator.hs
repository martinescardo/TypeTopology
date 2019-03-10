{-
   Agda illiterator.

   This Haskell program converts from .lagda files to .agda files.
   Keeps only what is within code environments, removing lines which
   consist of comments without code. It it a unix pipe. There are
   no command-line options.

   Typical usage:

   $ cat file.lagda | runhaskell illiterator.hs > file.agda
-}

import Data.Char

isComment :: String -> Bool
isComment [] = False
isComment (x : xs) = (x == '-' && not (null xs) && head xs == '-')
                     || (isSpace x && isComment xs)

begin = "\\begin{code}"
end   = "\\end{code}"

illiterator, copy :: [String] -> String

illiterator [] = []
illiterator (xs:xss)
  | take (length begin) (dropWhile isSpace xs) == begin  = copy xss
  | otherwise                                            = illiterator xss


copy [] = []
copy (xs:xss)
  | take (length end) (dropWhile isSpace xs) == end  = "\n" ++ illiterator xss
  | isComment xs                                     = copy xss
  | otherwise                                        = xs ++ "\n" ++ copy xss


reduceBlankLines :: String -> String
reduceBlankLines "" = ""
reduceBlankLines ('\n' : '\n' : '\n' : xs) = reduceBlankLines ('\n' : '\n' : xs)
reduceBlankLines (x:xs) = x : reduceBlankLines xs

pipe :: String -> String
pipe stdin = reduceBlankLines(illiterator(lines stdin))


main :: IO()
main = interact pipe
