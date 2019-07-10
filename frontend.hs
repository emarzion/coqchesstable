module Frontend where

import Base hiding (map)
import Rainbow

file_of_char :: Char -> Maybe File
file_of_char 'a' = Just A
file_of_char 'A' = Just A
file_of_char 'b' = Just B
file_of_char 'B' = Just B
file_of_char 'c' = Just C
file_of_char 'C' = Just C
file_of_char 'd' = Just D
file_of_char 'D' = Just D
file_of_char _ = Nothing

rank_of_char :: Char -> Maybe Rank
rank_of_char '1' = Just R1
rank_of_char '2' = Just R2
rank_of_char '3' = Just R3
rank_of_char '4' = Just R4
rank_of_char _ = Nothing

add_nums :: [a] -> [(Int,a)]
add_nums = go 1 where
    go _ [] = []
    go n (x:xs) = (n,x):go (n+1) xs

showResult :: Result -> String -> IO()
showResult Draw str = putChunkLn $ bold $ fore black $ back grey $ chunk str
showResult (Mate _) str = putChunkLn $ bold $ fore black $ back white $ chunk str

pprResult :: Result -> String
pprResult Draw = "Draw"
pprResult (Mate n) = "White mate in " ++ show n ++ " plies."

pprPiece :: Piece -> String
pprPiece WR = "R"
pprPiece _ = "K"

pprFile :: File -> String
pprFile A = "a"
pprFile B = "b"
pprFile C = "c"
pprFile D = "d"

pprRank :: Rank -> String
pprRank R1 = "1"
pprRank R2 = "2"
pprRank R3 = "3"
pprRank R4 = "4"

pprMove :: Move -> String
pprMove ((p,_),(f,r)) = pprPiece p ++ pprFile f ++ pprRank r

readPosition :: IO (File,Rank)
readPosition = do
    x <- getLine
    case x of
        [c1,c2] -> case file_of_char c1 of
            Nothing -> putStrLn "Invalid input" >> readPosition
            Just f -> case rank_of_char c2 of
                Just r -> return (f,r)
                Nothing -> putStrLn "Invalid input" >> readPosition
        _ -> putStrLn "Invalid input" >> readPosition

readColor :: IO Color
readColor = do
    x <- getLine
    if x == "black" || x == "Black" then return Black
    else if x == "white" || x == "White" then return White else
        putStrLn "Invalid input" >> readColor

startloop :: IO ()
startloop = do
    t <- getPosition
    queryBase t

getPosition :: IO Tuple
getPosition = do 
    putStrLn "White King:"
    wk <- readPosition
    putStrLn "Black King:"
    bk <- readPosition
    putStrLn "White Rook:"
    wr <- readPosition
    putStrLn "Color to play:"
    color <- readColor
    return (((color,wk),bk),wr)

queryBase :: Tuple -> IO()
queryBase t = do
    case query t of
        Nothing -> putStrLn "Illegal tuple" >> getPosition >> return ()
        Just (r,ps) -> do
            showResult r $ pprResult r
            foldr (>>) (return ()) $ map (\(i,(m,r')) -> showResult r' $ (show i ++ ". " ++ pprMove m ++ ": " ++ pprResult r')) (add_nums ps)
