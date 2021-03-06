import Data.Fin
import Data.Seq
import Data.Vect

-- Switch the row and column type from List to Vect 9

Tile : Type
Tile = Fin 9

PartialRow : Type
PartialRow = Vect 9 $ Maybe Tile

CompleteRow : Type
CompleteRow = Vect 9 Tile

data BoardZipper : Type where
  MkBoard : (partialRowCount + completeRowCount = 8) ->
            (partialTileCount + completeTileCount = 9) ->
            Vect completeRowCount CompleteRow ->
            Vect completeTileCount Tile ->
            Vect partialTileCount (Maybe Tile) ->
            Vect partialRowCount PartialRow ->
            BoardZipper

PartialBoard : Type
PartialBoard = Vect 9 PartialRow

CompleteBoard : Type
CompleteBoard = Vect 9 CompleteRow

tilesDistinct : Eq a => Vect n $ Maybe a -> Bool
tilesDistinct ts with (catMaybes ts)
  | (n ** vs) = n == length (nub $ toList vs)

chunk : Vect 9 a -> Vect 3 $ Vect 3 a
chunk [a,b,c,d,e,f,g,h,i] = [[a,b,c],[d,e,f],[g,h,i]]

squares : PartialBoard -> PartialBoard
squares = map concat . Data.Vect.concat . map transpose . chunk . map chunk

rowsValid : PartialBoard -> Bool
rowsValid = all tilesDistinct

isValid : PartialBoard -> Bool
isValid board = rowsValid board && rowsValid (transpose board) && rowsValid (squares board)

mapAndAppend : (a -> b) -> Vect n a -> Vect m b -> Vect (m + n) b
mapAndAppend {m} f [] ys = rewrite plusZeroRightNeutral m in ys
mapAndAppend {n = S k} {m} f (x :: xs) ys =
  rewrite sym $ plusSuccRightSucc m k in mapAndAppend f xs (f x :: ys)

toPartialBoard : BoardZipper -> PartialBoard
toPartialBoard (MkBoard s1 s2 crs cr pr prs) =
  let pr = mapAndAppend Just cr pr in
  let pr = replace {P=\n => Vect n $ Maybe Tile} s2 pr in
  let prs = mapAndAppend (map Just) crs (pr :: prs) in
  replace {P=\n => Vect n $ Vect 9 $ Maybe Tile} (cong s1) prs

sumSuccRightSucc : (S a + b = c) -> (a + S b = c)
sumSuccRightSucc = trans $ sym $ plusSuccRightSucc _ _

solveBoard : BoardZipper -> Seq CompleteBoard
solveBoard (MkBoard s1 s2 crs cr [] []) with (s1, s2)
  | (Refl, Refl) = [ reverse $ reverse cr :: crs ]
solveBoard (MkBoard s1 s2 crs cr [] (pr :: prs)) with (s2)
  | Refl = solveBoard (MkBoard (sumSuccRightSucc s1) Refl (reverse cr :: crs) [] pr prs)
solveBoard (MkBoard s1 s2 crs cr (Just i :: pr) prs) =
  solveBoard (MkBoard s1 (sumSuccRightSucc s2) crs (i :: cr) pr prs)
solveBoard (MkBoard s1 s2 crs cr (Nothing :: pr) prs) =
  concat $ map solveBoard $ filter (isValid . toPartialBoard) $ map (\i => MkBoard s1 (sumSuccRightSucc s2) crs (i :: cr) pr prs) $ fins 9

-- Parsing and printing

parseTile : Char -> Maybe Tile
parseTile ' ' = Nothing
parseTile c =
  let i : Int = cast c - 49 in
  natToFin (toNat i) 9

toVect : (n : Nat) -> List a -> Vect n a
toVect n xs with (exactLength n $ fromList xs)
  | (Just ys) = ys

parseBoard : String -> BoardZipper
parseBoard s with (toVect 9 $ map (toVect 9 . map parseTile . unpack) $ lines s)
  | (pr::prs) = MkBoard Refl Refl [] [] pr prs

printTile : Maybe Tile -> Char
printTile Nothing = ' '
printTile (Just v) = cast (toIntNat $ finToNat v + 49)

printBoard : PartialBoard -> String
printBoard = unlines . map (pack . map printTile . Prelude.List.toList) . toList

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

