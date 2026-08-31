module Math.AlgebraOfBoole

import public Core.NarayAlphabet
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. ALGEBRA OF BOOLE OPERATORS (F2 RING ARITHMETIC)
------------------------------------------------------------------------

||| Addition in the Algebra of Boole (XOR): 1 + 1 = 0.
%inline
public export
addBit2 : Bit2 -> Bit2 -> Bit2
addBit2 Bit2Zero b2       = b2
addBit2 b1       Bit2Zero = b1
addBit2 Bit2One  Bit2One  = Bit2Zero

||| Multiplication in the Algebra of Boole (AND).
%inline
public export
mulBit2 : Bit2 -> Bit2 -> Bit2
mulBit2 Bit2Zero _        = Bit2Zero
mulBit2 _        Bit2Zero = Bit2Zero
mulBit2 Bit2One  Bit2One  = Bit2One

||| Complement in the Algebra of Boole: ¬x = 1 + x.
%inline
public export
notBit2 : Bit2 -> Bit2
notBit2 b = addBit2 Bit2One b

||| Inclusive OR derived algebraically: x ∨ y = x + y + x*y.
%inline
public export
orBit2 : Bit2 -> Bit2 -> Bit2
orBit2 b1 b2 = addBit2 (addBit2 b1 b2) (mulBit2 b1 b2)

||| Subtraction in F2: x - y = x + y (since -1 = +1 mod 2).
%inline
public export
subBit2 : Bit2 -> Bit2 -> Bit2
subBit2 b1 b2 = addBit2 b1 b2

------------------------------------------------------------------------
-- 2. FORMAL PROOFS OF ALGEBRA OF BOOLE THEOREMS
------------------------------------------------------------------------

||| Theorem 1: Self-Annihilation / Additive Inverse (x + x = 0).
public export
proofBooleSelfAnnihilation : (b : Bit2) -> addBit2 b b = Bit2Zero
proofBooleSelfAnnihilation Bit2Zero = Refl
proofBooleSelfAnnihilation Bit2One  = Refl

||| Theorem 2: Idempotency of Multiplication (x^2 = x).
public export
proofBooleIdempotency : (b : Bit2) -> mulBit2 b b = b
proofBooleIdempotency Bit2Zero = Refl
proofBooleIdempotency Bit2One  = Refl

||| Theorem 3: Additive Commutativity (x + y = y + x).
public export
proofBooleAddCommutative : (b1, b2 : Bit2) -> addBit2 b1 b2 = addBit2 b2 b1
proofBooleAddCommutative Bit2Zero Bit2Zero = Refl
proofBooleAddCommutative Bit2Zero Bit2One  = Refl
proofBooleAddCommutative Bit2One  Bit2Zero = Refl
proofBooleAddCommutative Bit2One  Bit2One  = Refl

||| Theorem 4: Multiplicative Commutativity (x * y = y * x).
public export
proofBooleMulCommutative : (b1, b2 : Bit2) -> mulBit2 b1 b2 = mulBit2 b2 b1
proofBooleMulCommutative Bit2Zero Bit2Zero = Refl
proofBooleMulCommutative Bit2Zero Bit2One  = Refl
proofBooleMulCommutative Bit2One  Bit2Zero = Refl
proofBooleMulCommutative Bit2One  Bit2One  = Refl

||| Theorem 5: Multiplicative Identity (x * 1 = x).
public export
proofBooleMulIdentity : (b : Bit2) -> mulBit2 b Bit2One = b
proofBooleMulIdentity Bit2Zero = Refl
proofBooleMulIdentity Bit2One  = Refl

||| Theorem 6: Complement Derivation (¬x = 1 + x).
public export
proofBooleComplement : (b : Bit2) -> notBit2 b = addBit2 Bit2One b
proofBooleComplement Bit2Zero = Refl
proofBooleComplement Bit2One  = Refl

||| Theorem 7: Inclusive OR Expansion (x ∨ y = x + y + x*y).
public export
proofBooleInclusiveOr : (b1, b2 : Bit2) -> orBit2 b1 b2 = addBit2 (addBit2 b1 b2) (mulBit2 b1 b2)
proofBooleInclusiveOr Bit2Zero Bit2Zero = Refl
proofBooleInclusiveOr Bit2Zero Bit2One  = Refl
proofBooleInclusiveOr Bit2One  Bit2Zero = Refl
proofBooleInclusiveOr Bit2One  Bit2One  = Refl

||| Theorem 8: Subtraction Equivalence (x - y = x + y).
public export
proofBooleSubtraction : (b1, b2 : Bit2) -> subBit2 b1 b2 = addBit2 b1 b2
proofBooleSubtraction Bit2Zero Bit2Zero = Refl
proofBooleSubtraction Bit2Zero Bit2One  = Refl
proofBooleSubtraction Bit2One  Bit2Zero = Refl
proofBooleSubtraction Bit2One  Bit2One  = Refl

------------------------------------------------------------------------
-- 3. BOOLE-MÖBIUS SELF-INVERSE TRANSFORM (T^2 = I)
------------------------------------------------------------------------

||| 2-element Boole-Möbius transform over F2: T([a, b]) = [a, a + b].
%inline
public export
mobiusTransform2 : Vect 2 Bit2 -> Vect 2 Bit2
mobiusTransform2 (a :: b :: []) = a :: addBit2 a b :: []

||| Theorem 9: Boole-Möbius Transform is self-inverse (T^2 = I).
public export
proofBooleMobiusSelfInverse : (v : Vect 2 Bit2) -> mobiusTransform2 (mobiusTransform2 v) = v
proofBooleMobiusSelfInverse (Bit2Zero :: Bit2Zero :: []) = Refl
proofBooleMobiusSelfInverse (Bit2Zero :: Bit2One  :: []) = Refl
proofBooleMobiusSelfInverse (Bit2One  :: Bit2Zero :: []) = Refl
proofBooleMobiusSelfInverse (Bit2One  :: Bit2One  :: []) = Refl
