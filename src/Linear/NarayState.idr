module Linear.NarayState

import public Core.NarayAlphabet
import public Math.NarayanaPolynomial
import Data.Vect

%default total

||| A QTT linear state container indexed by alphabet dimension n and capacity budget.
public export
record NarayState (n : Nat) where
  constructor MkNarayState
  stateDimension : Nat
  stateBudget    : Nat
  stateTokens    : Vect stateDimension (NarayAlphabet n)

||| Initializes a default NarayState for Binary n=2.
public export
initNarayState2 : NarayState 2
initNarayState2 = MkNarayState 2 2 [Naray2 Bit2Zero, Naray2 Bit2One]

||| Initializes a default NarayState for Ternary n=3.
public export
initNarayState3 : NarayState 3
initNarayState3 = MkNarayState 3 3 [Naray3 Bit3MinusOne, Naray3 Bit3Zero, Naray3 Bit3PlusOne]

||| Linear QTT state transition preserving multiplicity (1 state : NarayState n).
public export
stepNarayStateLinear : (1 state : NarayState n) -> NarayState n
stepNarayStateLinear (MkNarayState dim budget tokens) =
  MkNarayState dim (S budget) tokens

||| Linear state split operation.
public export
splitNarayStateLinear : (1 state : NarayState n) -> (NarayState n, NarayState n)
splitNarayStateLinear (MkNarayState dim budget tokens) =
  ( MkNarayState dim budget tokens
  , MkNarayState dim budget tokens
  )
