module Math.NarayanaPolynomial

import public Math.BoxInt
import Data.Vect

%default total

||| Exact constructive division over Nat that evaluates at compile time.
%inline
public export
narayDivNat : Nat -> Nat -> Nat
narayDivNat _ Z = Z
narayDivNat num den = go num num den
  where
    go : Nat -> Nat -> Nat -> Nat
    go Z _ _ = Z
    go (S fuel) rem d = 
      if rem < d then Z
      else S (go fuel (minus rem d) d)

||| Exact factorial function using Nat.
%inline
public export
fact : Nat -> Nat
fact Z = 1
fact (S k) = (S k) * fact k

||| Exact combination function n choose k.
%inline
public export
nChooseK : Nat -> Nat -> Nat
nChooseK n k = 
  if k > n then 0
  else narayDivNat (fact n) ((fact k) * (fact (minus n k)))

||| Computes the Narayana number N(n, k) = (1/n) * (n choose k) * (n choose (k-1)).
%inline
public export
narayanaNumber : Nat -> Nat -> Nat
narayanaNumber Z _ = 0
narayanaNumber _ Z = 0
narayanaNumber n k =
  if k > n then 0
  else
    let c1 = nChooseK n k
        c2 = nChooseK n (minus k 1)
        prodVal = c1 * c2
    in narayDivNat prodVal n

||| Computes the Catalan number C_n = (1 / (n+1)) * (2n choose n).
%inline
public export
catalanNumber : Nat -> Nat
catalanNumber Z = 1
catalanNumber n = narayDivNat (nChooseK (2 * n) n) (S n)

||| Computes the sum of Narayana numbers sum_{k=1}^n N(n, k).
%inline
public export
sumNarayanaNumbers : Nat -> Nat
sumNarayanaNumbers Z = 0
sumNarayanaNumbers n = go n n
  where
    go : Nat -> Nat -> Nat
    go Z _ = 0
    go (S k) totalN = narayanaNumber totalN (S k) + go k totalN

||| Evaluates the Narayana generating polynomial N_n(t) = sum_{k=1}^n N(n, k) * t^(k-1) at integer t.
%inline
public export
evalNarayanaPoly : Nat -> Integer -> Integer
evalNarayanaPoly Z _ = 0
evalNarayanaPoly n t = go n n
  where
    power : Integer -> Nat -> Integer
    power _ Z = 1
    power x (S p) = x * power x p

    go : Nat -> Nat -> Integer
    go Z _ = 0
    go (S k) totalN = 
      let coeff = cast {to=Integer} (narayanaNumber totalN (S k))
          term = coeff * power t k
      in term + go k totalN

||| Computes the vector of Narayana numbers for a given order n.
public export
narayanaVector : (n : Nat) -> Vect n Nat
narayanaVector Z = []
narayanaVector n = generateVector n n
  where
    generateVector : (len : Nat) -> (totalN : Nat) -> Vect len Nat
    generateVector Z _ = []
    generateVector (S j) totalN = 
      let k = minus totalN j
          nk = narayanaNumber totalN k
      in nk :: generateVector j totalN
