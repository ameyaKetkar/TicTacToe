module TicTacToe

import Control.Monad.State
import Data.Vect

data SquareBoard : Nat -> Type -> Type where
    SB : Vect i (Vect i (Maybe a)) -> SquareBoard i a

data XO = X | O

implementation Eq XO where
  X == X = True
  O == O = True
  _ == _ = False

implementation Enum XO where
  succ X = O
  succ O = X
  pred = succ
  toNat X = 0
  toNat O = 1
  fromNat (S x) = succ (fromNat x)
  fromNat Z = X

data GameOver a = Winner a | Tie

record GameState (k : Nat) a where
  constructor MkGameState
  whoseTurn : a
  board : SquareBoard k a

myReplicate : a -> (k : Nat) -> Vect k a
myReplicate a Z = Nil
myReplicate a (S k) = a :: myReplicate a k

makeBoard : (Maybe a) -> (k : Nat) -> SquareBoard k a
makeBoard a k =  SB $ myReplicate (myReplicate a k) k

myBoard : SquareBoard 3 XO
myBoard = makeBoard Nothing 3

getRow : SquareBoard k a -> Fin k -> Vect k (Maybe a)
getRow (SB v) k = index k v

getCol : SquareBoard k a -> Fin k -> Vect k (Maybe a)
getCol (SB v) k = index k $ transpose v

getMarker : SquareBoard k a -> Fin k -> Fin k -> Maybe a
getMarker (SB v) m n = index n $ index m v

addToken : (b : SquareBoard k a) -> (m : Fin k) -> (n : Fin k) -> {default Refl cellFree : getMarker b m n = Nothing} -> a -> SquareBoard k a
addToken (SB s) m n xo = SB $ updateAt m (\v => updateAt n (\u => Just xo) v) s

boardFull : SquareBoard k a -> Bool
boardFull (SB v) = all (all (not . isNothing)) v

allEq : (Eq a, Monoid a) => {k: Nat} -> Vect k a -> a
allEq {k = S z} x with (all (== head x) (tail x))
  | True = head x
  | _    = neutral
allEq {k = Z} x = neutral

checkRows : Eq a => SquareBoard k a -> Maybe a
checkRows (SB v) = concatMap allEq v

checkCols : Eq a => SquareBoard k a -> Maybe a
checkCols (SB v) = checkRows $ SB $ transpose v

checkMainDiag : Eq a => SquareBoard k a -> Maybe a
checkMainDiag b = allEq ((\i => getMarker b i i) <$> range)

checkOtherDiag : Eq a => SquareBoard k a -> Maybe a
checkOtherDiag (SB v) = checkMainDiag $ SB $ reverse v

transposeBoard : SquareBoard k a -> SquareBoard k a
transposeBoard (SB v) = SB (transpose v)

gameState : Eq a => SquareBoard k a -> Maybe (GameOver a)
gameState b with (checkRows b <+> checkCols b <+> checkMainDiag b <+> checkOtherDiag b)
  | Just x = Just (Winner x)
  | Nothing = if boardFull b then Just Tie else Nothing

ValidMove : GameState k a -> Fin k -> Fin k -> a -> Type
ValidMove g m n player = (getMarker (board g) m n = Nothing, whoseTurn g = a)

takeTurn : (Eq a, Enum a) => (g : GameState k a) -> (m : Fin k) -> (n : Fin k) -> (player : a) -> {default (Refl, Refl) validMove : ValidMove g m n player} -> GameState k a
takeTurn g m n player {validMove = (cellFree, _)} =
  MkGameState (succ (whoseTurn g)) (addToken (board g) m n player {cellFree})
