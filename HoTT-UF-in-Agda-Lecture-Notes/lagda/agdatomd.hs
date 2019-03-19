-- $ cat file.lagda | runhaskell agdatomd.hs > file.md

begin = "\\begin{code}"
end   = "\\end{code}"

begin' = "```agda"
end'   = "```"

lagda2md :: [String] -> [String]

lagda2md [] = []
lagda2md (xs:xss)
  | take (length begin) xs == begin  = begin' : "\n" : lagda2md xss
  | take (length end)   xs == end    = end'   : "\n" : lagda2md xss
  | otherwise                        = xs     : "\n" : lagda2md xss

pipe :: String -> String
pipe stdin = concat(lagda2md(lines stdin))

main :: IO()
main = interact pipe
