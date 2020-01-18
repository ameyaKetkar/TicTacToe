module TicTacToe

import Data.Vect

data SquareBoard : Nat -> Type -> Type where
    SB : Vect i (Vect i (Maybe a)) -> SquareBoard i a

data XO = X | O

implementation Eq XO where
    X == X = True
    O == O = True
    _ == _ = False

myReplicate : a -> (k : Nat) -> Vect k a
myReplicate a Z = Nil
myReplicate a (S k) = a :: myReplicate a k

makeBoard : (Maybe a) -> (k : Nat) -> SquareBoard k a
makeBoard a k =  SB $ myReplicate (myReplicate a k) k

addToken : SquareBoard k a -> Fin k -> Fin k -> a -> SquareBoard k a
addToken (SB s) m n xo = SB $ updateAt m (\v => updateAt n (\u => Just xo) v) s

myBoard : SquareBoard 3 XO
myBoard = makeBoard Nothing 3

getRow : SquareBoard k a -> Fin k -> Vect k (Maybe a)
getRow (SB v) k = index k v

getCol : SquareBoard k a -> Fin k -> Vect k (Maybe a)
getCol (SB v) k = index k $ transpose v

getMarker : SquareBoard k a -> Fin k -> Fin k -> Maybe a
getMarker (SB v) m n = index n $ index m v
