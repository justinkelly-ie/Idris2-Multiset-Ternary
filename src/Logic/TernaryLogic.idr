module Logic.TernaryLogic

import Data.List
import Data.Nat
import Math.Multiset
import Math.BoxInt
import public Core.NarayAlphabet

%default covering

------------------------------------------------------------------------
-- 1. BALANCED TERNARY LOGIC OPERATORS (KLEENE / ŁUKASIEWICZ / F3)
------------------------------------------------------------------------

||| 3-Valued Kleene Negation: ¬(-1) = +1, ¬(0) = 0, ¬(+1) = -1.
%inline
public export
notBit3 : Bit3 -> Bit3
notBit3 Bit3MinusOne = Bit3PlusOne
notBit3 Bit3Zero     = Bit3Zero
notBit3 Bit3PlusOne  = Bit3MinusOne

||| 3-Valued Kleene AND (MIN operator over {-1, 0, +1}):
||| -1 ∧ x = -1,  +1 ∧ x = x,  0 ∧ 0 = 0.
%inline
public export
andBit3 : Bit3 -> Bit3 -> Bit3
andBit3 Bit3MinusOne _            = Bit3MinusOne
andBit3 _            Bit3MinusOne = Bit3MinusOne
andBit3 Bit3PlusOne  b2           = b2
andBit3 b1           Bit3PlusOne  = b1
andBit3 Bit3Zero     Bit3Zero     = Bit3Zero

||| 3-Valued Kleene OR (MAX operator over {-1, 0, +1}):
||| +1 ∨ x = +1,  -1 ∨ x = x,  0 ∨ 0 = 0.
%inline
public export
orBit3 : Bit3 -> Bit3 -> Bit3
orBit3 Bit3PlusOne  _           = Bit3PlusOne
orBit3 _           Bit3PlusOne = Bit3PlusOne
orBit3 Bit3MinusOne b2          = b2
orBit3 b1          Bit3MinusOne = b1
orBit3 Bit3Zero    Bit3Zero    = Bit3Zero

||| Field addition over F3 (balanced mod 3):
||| (+1) + (+1) = -1, (-1) + (-1) = +1, (+1) + (-1) = 0.
%inline
public export
addBit3 : Bit3 -> Bit3 -> Bit3
addBit3 b1 b2 = case addNaray (Naray3 b1) (Naray3 b2) of Naray3 res => res

||| Field multiplication over F3 (balanced mod 3):
||| (-1) * (-1) = +1, (+1) * (-1) = -1, 0 * x = 0.
%inline
public export
mulBit3 : Bit3 -> Bit3 -> Bit3
mulBit3 b1 b2 = case mulNaray (Naray3 b1) (Naray3 b2) of Naray3 res => res

public export
Num Bit3 where
  (+) = addBit3
  (*) = mulBit3
  fromInteger n = case mod (if n >= 0 then n else (3 - ((-n) `mod` 3))) 3 of
                    1 => Bit3PlusOne
                    2 => Bit3MinusOne
                    _ => Bit3Zero

public export
Neg Bit3 where
  negate = notBit3
  (-) x y = addBit3 x (notBit3 y)

------------------------------------------------------------------------
-- 2. TERNARY MULTISET POLYNUMBERS & FUNCTIONS
------------------------------------------------------------------------

||| A Ternary Polynumber: a multiset of 3-adic term indices with Bit3 counts in {-1, 0, +1}.
||| Index 0 = constant term.
||| Index k: 3-adic expansion encodes variable powers across ternary variables.
public export
TernaryPolynumber : Type
TernaryPolynumber = Multiset Bit3 Nat

||| A 3-Valued Boolean/Ternary Function (truth table of 3^N entries) as a multiset.
public export
TernaryFunction : Type
TernaryFunction = Multiset Bit3 Nat

||| Constant zero ternary polynumber.
public export
zeroTernaryPoly : TernaryPolynumber
zeroTernaryPoly = ZeroM

||| Constant unit (+1) ternary polynumber.
public export
unitTernaryPoly : TernaryPolynumber
unitTernaryPoly = AddM 0 Bit3PlusOne ZeroM

------------------------------------------------------------------------
-- 3. TERNARY MULTISET ARITHMETIC
------------------------------------------------------------------------

||| Ternary multiset addition: concatenates terms and compresses identical term indices.
public export
addTernaryPoly : TernaryPolynumber -> TernaryPolynumber -> TernaryPolynumber
addTernaryPoly p q = addMultiset p q

||| Ternary multiset multiplication combining 3-adic term powers and F3 coefficients.
public export
mulTernaryPoly : TernaryPolynumber -> TernaryPolynumber -> TernaryPolynumber
mulTernaryPoly ZeroM _ = ZeroM
mulTernaryPoly (AddM ki ci rest) ys =
  addTernaryPoly (mulInner ki ci ys) (mulTernaryPoly rest ys)
  where
    mulInner : Nat -> Bit3 -> TernaryPolynumber -> TernaryPolynumber
    mulInner _ _ ZeroM = ZeroM
    mulInner ki ci (AddM kj cj rest) =
      let prodIdx = ki + kj
          prodCoeff = mulBit3 ci cj
      in insertItem prodIdx prodCoeff (mulInner ki ci rest)

------------------------------------------------------------------------
-- 4. 3-VALUED MÖBIUS TRANSFORM & TRUTH TABLES
------------------------------------------------------------------------
 
||| Converts a 3-valued truth table list of 3^N Bit3 entries into a sparse multiset.
public export
denseToSparse3 : List Bit3 -> Multiset Bit3 Nat
denseToSparse3 = go 0
  where
    go : Nat -> List Bit3 -> Multiset Bit3 Nat
    go _ [] = ZeroM
    go idx (x :: rest) =
      if x == Bit3Zero
        then go (S idx) rest
        else AddM idx x (go (S idx) rest)

||| Converts a sparse ternary multiset into a dense 3^N Bit3 list.
public export
sparseToDense3 : (size : Nat) -> Multiset Bit3 Nat -> List Bit3
sparseToDense3 size m = map (\idx => lookupTVal idx m) [0 .. minus size 1]
  where
    lookupTVal : Nat -> Multiset Bit3 Nat -> Bit3
    lookupTVal _ ZeroM = Bit3Zero
    lookupTVal idx (AddM k v rest) =
      if k == idx then addBit3 v (lookupTVal idx rest)
      else lookupTVal idx rest

||| Computes the 3-valued Möbius transform over a 3-valued truth table list.
public export
mobiusTransform3 : List Bit3 -> List Bit3
mobiusTransform3 [] = []
mobiusTransform3 table =
  let n = length table
      indices = [0 .. minus n 1]
  in map (\i => foldl addBit3 Bit3Zero (map (\j => getAt j table) indices)) indices
  where
    getAt : Nat -> List Bit3 -> Bit3
    getAt Z (x :: _) = x
    getAt (S k) (_ :: xs) = getAt k xs
    getAt _ [] = Bit3Zero

------------------------------------------------------------------------
-- 5. FORMAL THEOREMS & INVARIANTS OF TERNARY LOGIC
------------------------------------------------------------------------

||| Theorem 1: Involution of 3-Valued Kleene Negation: ¬(¬x) = x.
public export
proofBit3Involution : (b : Bit3) -> notBit3 (notBit3 b) = b
proofBit3Involution Bit3MinusOne = Refl
proofBit3Involution Bit3Zero     = Refl
proofBit3Involution Bit3PlusOne  = Refl

||| Theorem 2: Commutativity of 3-Valued AND: x ∧ y = y ∧ x.
public export
proofBit3AndCommutative : (b1, b2 : Bit3) -> andBit3 b1 b2 = andBit3 b2 b1
proofBit3AndCommutative Bit3MinusOne Bit3MinusOne = Refl
proofBit3AndCommutative Bit3MinusOne Bit3Zero     = Refl
proofBit3AndCommutative Bit3MinusOne Bit3PlusOne  = Refl
proofBit3AndCommutative Bit3Zero     Bit3MinusOne = Refl
proofBit3AndCommutative Bit3Zero     Bit3Zero     = Refl
proofBit3AndCommutative Bit3Zero     Bit3PlusOne  = Refl
proofBit3AndCommutative Bit3PlusOne  Bit3MinusOne = Refl
proofBit3AndCommutative Bit3PlusOne  Bit3Zero     = Refl
proofBit3AndCommutative Bit3PlusOne  Bit3PlusOne  = Refl

||| Theorem 3: Commutativity of 3-Valued OR: x ∨ y = y ∨ x.
public export
proofBit3OrCommutative : (b1, b2 : Bit3) -> orBit3 b1 b2 = orBit3 b2 b1
proofBit3OrCommutative Bit3MinusOne Bit3MinusOne = Refl
proofBit3OrCommutative Bit3MinusOne Bit3Zero     = Refl
proofBit3OrCommutative Bit3MinusOne Bit3PlusOne  = Refl
proofBit3OrCommutative Bit3Zero     Bit3MinusOne = Refl
proofBit3OrCommutative Bit3Zero     Bit3Zero     = Refl
proofBit3OrCommutative Bit3Zero     Bit3PlusOne  = Refl
proofBit3OrCommutative Bit3PlusOne  Bit3MinusOne = Refl
proofBit3OrCommutative Bit3PlusOne  Bit3Zero     = Refl
proofBit3OrCommutative Bit3PlusOne  Bit3PlusOne  = Refl

||| Theorem 4: 3-Valued De Morgan's First Law: ¬(x ∧ y) = ¬x ∨ ¬y.
public export
proofBit3DeMorganAnd : (b1, b2 : Bit3) -> notBit3 (andBit3 b1 b2) = orBit3 (notBit3 b1) (notBit3 b2)
proofBit3DeMorganAnd Bit3MinusOne Bit3MinusOne = Refl
proofBit3DeMorganAnd Bit3MinusOne Bit3Zero     = Refl
proofBit3DeMorganAnd Bit3MinusOne Bit3PlusOne  = Refl
proofBit3DeMorganAnd Bit3Zero     Bit3MinusOne = Refl
proofBit3DeMorganAnd Bit3Zero     Bit3Zero     = Refl
proofBit3DeMorganAnd Bit3Zero     Bit3PlusOne  = Refl
proofBit3DeMorganAnd Bit3PlusOne  Bit3MinusOne = Refl
proofBit3DeMorganAnd Bit3PlusOne  Bit3Zero     = Refl
proofBit3DeMorganAnd Bit3PlusOne  Bit3PlusOne  = Refl

||| Theorem 5: 3-Valued De Morgan's Second Law: ¬(x ∨ y) = ¬x ∧ ¬y.
public export
proofBit3DeMorganOr : (b1, b2 : Bit3) -> notBit3 (orBit3 b1 b2) = andBit3 (notBit3 b1) (notBit3 b2)
proofBit3DeMorganOr Bit3MinusOne Bit3MinusOne = Refl
proofBit3DeMorganOr Bit3MinusOne Bit3Zero     = Refl
proofBit3DeMorganOr Bit3MinusOne Bit3PlusOne  = Refl
proofBit3DeMorganOr Bit3Zero     Bit3MinusOne = Refl
proofBit3DeMorganOr Bit3Zero     Bit3Zero     = Refl
proofBit3DeMorganOr Bit3Zero     Bit3PlusOne  = Refl
proofBit3DeMorganOr Bit3PlusOne  Bit3MinusOne = Refl
proofBit3DeMorganOr Bit3PlusOne  Bit3Zero     = Refl
proofBit3DeMorganOr Bit3PlusOne  Bit3PlusOne  = Refl
