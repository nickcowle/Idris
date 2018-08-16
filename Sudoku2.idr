import Data.Seq

-- Transliteration of F# solution with no additional type-safety

BoardZipper : Type
BoardZipper = (List $ List Int, List Int, List $ Maybe Int, List $ List $ Maybe Int)

PartialBoard : Type
PartialBoard = List $ List $ Maybe Int

tilesDistinct : Eq a => List $ Maybe a -> Bool
tilesDistinct ts with (catMaybes ts)
  | vs = length vs == length (nub vs)

chunkBySize : Nat -> List a -> List $ List a
chunkBySize n xs with (splitAt n xs)
  | (chunk, []) = [chunk]
  | (chunk, rest) = chunk :: chunkBySize n rest

squares : PartialBoard -> PartialBoard
squares = map join . join . map transpose . chunkBySize 3 . map (chunkBySize 3)

rowsValid : PartialBoard -> Bool
rowsValid = all tilesDistinct

isValid : PartialBoard -> Bool
isValid board = rowsValid board && rowsValid (transpose board) && rowsValid (squares board)

mapAndAppend : (a -> b) -> List a -> List b -> List b
mapAndAppend f [] ys = ys
mapAndAppend f (x :: xs) ys = mapAndAppend f xs (f x :: ys)

toPartialBoard : BoardZipper -> PartialBoard
toPartialBoard (crs, cr, pr, prs) = mapAndAppend (map Just) crs ((mapAndAppend Just cr pr) :: prs)

solveBoard : BoardZipper -> Seq $ List $ List Int
solveBoard (crs, [], [], []) = [ reverse crs ]
solveBoard (crs, [], [], pr :: prs) = solveBoard (crs, [], pr, prs)
solveBoard (crs, cr, [], prs) = solveBoard ((reverse cr) :: crs, [], [], prs)
solveBoard (crs, cr, (Just i :: pr), prs) = solveBoard (crs, i :: cr, pr, prs)
solveBoard (crs, cr, (Nothing :: pr), prs) =
  concat $ (map solveBoard) $ filter (isValid . toPartialBoard) $ map (\i => (crs, i :: cr, pr, prs)) $ range 1 9

-- Parsing and printing

parseTile : Char -> Maybe Int
parseTile ' ' = Nothing
parseTile  c  = Just $ cast c - 48

parseBoard : String -> BoardZipper
parseBoard = (\prs => ([], [], [], prs)) . map (map parseTile . unpack) . lines

printTile : Maybe Int -> Char
printTile Nothing = ' '
printTile (Just v) = cast $ v + 48

printBoard : PartialBoard -> String
printBoard = unlines . map (pack . map printTile)

testBoard : BoardZipper
testBoard =
  parseBoard $
    "     6  1\n" ++
    " 2  5 7  \n" ++
    "5  12  6 \n" ++
    "      6 3\n" ++
    "  28 49  \n" ++
    "6 7      \n" ++
    " 5  19  8\n" ++
    "  1 8  4 \n" ++
    "8  2     "

main : IO ()
main =
  let solution = head $ solveBoard testBoard in
  let printed = printBoard $ map (map Just) solution in
  putStrLn $ "The first solution is:\n" ++ printed

