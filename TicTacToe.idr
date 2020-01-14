module TicTacToe

import Data.Vect

data SquareBoard : Nat -> Type -> Type where
    SB : Vect i (Vect i (Maybe a)) -> SquareBoard i a


myReplicate : a -> (k : Nat) -> Vect k a
myReplicate a Z = Nil
myReplicate a (S k) = a :: myReplicate a k

makeBoard : (Maybe a) -> (k : Nat) -> SquareBoard k a
makeBoard a k =  SB $ myReplicate (myReplicate a k) k


-- empty : a -> SquareBoard a b
-- empty a = SB $ Nothing :: (Nothin)