{-|
Author       : Ayberk Tosun, 2025
Description  : Calculates the count of total Agda source files as well as the
               lines in these files, and adds this information to
               `source/index.lagda`.
-}

module Main where

import qualified Data.ByteString.Char8 as BS
import           Data.List
import           Data.String
import           Data.Time
import           System.IO
import           System.Process

type DateString = String
type LineCount  = Int
type FileCount  = Int

caseShouldNotHappenMsg :: String
caseShouldNotHappenMsg = "This case should not happen"

isAgdaFile :: String -> Bool
isAgdaFile fname =
  (".lagda" `isSuffixOf` fname) || (".agda" `isSuffixOf` fname)

getListOfAgdaFiles :: IO [String]
getListOfAgdaFiles = do
  output <- readProcess "git" ["ls-files", "source"] ""
  let filePaths = lines output
  return $ filter isAgdaFile filePaths

lineCount :: FilePath -> IO Int
lineCount path = do
  content <- BS.readFile path
  return $ BS.count '\n' content

totalAgdaLineCount :: [FilePath] -> IO Int
totalAgdaLineCount paths = totalAgdaLineCountAux paths 0
  where
    totalAgdaLineCountAux :: [FilePath] -> Int -> IO Int
    totalAgdaLineCountAux []     acc = return acc
    totalAgdaLineCountAux (p:ps) acc = do k <- lineCount p
                                          totalAgdaLineCountAux ps (k+acc)

findIndexOfCountLine :: Handle -> IO Int
findIndexOfCountLine handle = findIndexOfCountLineAux handle 1
  where
    findIndexOfCountLineAux :: Handle -> Int -> IO Int
    findIndexOfCountLineAux h k = do
      line <- hGetLine h
      if "In our last count, on" `isInfixOf` line then
        return k
      else
        findIndexOfCountLineAux h (k+1)

ukTimeZone :: TimeZone
ukTimeZone = TimeZone 0 False "GMT"

formatLineCount :: LineCount -> String
formatLineCount lc | lc < 1000000 = show (lc `div` 1000) ++ "K"
formatLineCount _                 = error "This case is not handled yet"

newCountMessageLine1 :: DateString -> FileCount -> String
newCountMessageLine1 date fc =
  concat $ [ "   * In our last count, on "
           , date
           , ", this development has "
           , show fc
           , " Agda" ]

newCountMessageLine2 :: LineCount -> String
newCountMessageLine2 lc =
  concat $ [ "     files with "
           , formatLineCount lc
           , " lines of code, including comments and blank"
           ]

placeNewMessage :: (DateString, FileCount, LineCount) -> [String] -> [String]
placeNewMessage _           []             = error caseShouldNotHappenMsg
placeNewMessage _           [_]            = error caseShouldNotHappenMsg
placeNewMessage (d, fc, lc) (l1:_:ls)
  | "In our last count, on" `isInfixOf` l1 = l1':l2':ls
                                               where
                                                 l1' = newCountMessageLine1 d fc
                                                 l2' = newCountMessageLine2 lc
placeNewMessage info        (l1:l2:ls)     = l1 : placeNewMessage info (l2:ls)

getCurrentDateInISO8601 :: IO DateString
getCurrentDateInISO8601 = do
  now <- getCurrentTime
  let ukTime = utcToLocalTime ukTimeZone now
  return $ formatTime defaultTimeLocale "%Y-%m-%d" ukTime

updateIndexFile :: (DateString, FileCount, LineCount) -> IO ()
updateIndexFile (d, fc, lc) = do
  indexFileContent <- readFile "source/index.lagda"
  let indexFileLines  = lines indexFileContent
      indexFileLines' = placeNewMessage (d, fc, lc) indexFileLines
  writeFile "source/index-updated.lagda" $ unlines indexFileLines'

main :: IO ()
main = do
  -- Get the count of Agda files.
  fileNames <- getListOfAgdaFiles
  let fc = length fileNames :: FileCount

  -- Sum up the number of lines in each of these files.
  lc <- totalAgdaLineCount fileNames

  -- Get the current date.
  d <- getCurrentDateInISO8601

  -- Finally, we update `source/index.lagda` with this new information.
  updateIndexFile (d, fc, lc)
