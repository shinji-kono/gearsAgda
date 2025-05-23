-- {-# OPTIONS --cubical-compatible --allow-unsolved-metas #-}
{-# OPTIONS --cubical-compatible --safe #-}
module ModelChecking where

open import Level renaming (zero to Z ; suc to succ)

open import Data.Nat hiding (compare)
open import Data.Nat.Properties as NatProp
open import Data.Maybe
-- open import Data.Maybe.Properties
open import Data.Empty
open import Data.List
-- open import Data.Tree.Binary
-- open import Data.Product
open import Function as F hiding (const)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import logic
open import Data.Unit hiding ( _≟_ ) -- ;  _≤?_ ; _≤_)
open import Relation.Binary.Definitions

record AtomicNat : Set where
   field
      ptr : ℕ       -- memory pointer ( unique id of DataGear )
      value : ℕ

init-AtomicNat : AtomicNat
init-AtomicNat = record { ptr = 0 ; value = 0 }

--
-- single process implemenation
--

f_set : {n : Level } {t : Set n} → AtomicNat → (value : ℕ) → ( AtomicNat → t ) → t
f_set a v next = next record a { value = v }

--
-- Coda Gear
--

data Code : Set  where
   CC_nop : Code

--
-- all possible arguments in -APIs
--
record AtomicNat-API : Set where
   field
      next : Code
      fail : Code
      value : ℕ
      impl : AtomicNat

data Error : Set where
   E_panic : Error
   E_cas_fail : Error

--
-- Data Gear
--
--      waiting / pointer / available
--

data Data : Set where
   -- D_AtomicNat :  AtomicNat → ℕ → Data
   CD_AtomicNat :  AtomicNat → Data

-- data API : Set where
--    A_AtomicNat :  AtomicNat-API → API
--    A_Phil :      Phil-API → API


record Context  : Set  where
   field
      next :      Code 
      fail :      Code

      --  -API list (frame in Gears Agda )  --- a Data of API
      -- api : List API
      -- c_Phil-API :     Maybe Phil-API
      -- c_Phil-API :     ?
      -- c_AtomicNat-API : AtomicNat-API

      mbase :     ℕ
      -- memory :    ?
      error :     Data
      fail_next :      Code

--
-- second level stub
--
AtomicInt_cas_stub : {n : Level} {t : Set n} → Context  → ( Code → Context → t ) → t
AtomicInt_cas_stub {_} {t} c next = ? 


code_table :  {n : Level} {t : Set n} → Code → Context → ( Code → Context → t) → t
code_table = ?

step : {n : Level} {t : Set n} → List Context → (List Context → t) → t
step {n} {t} [] next0 = next0 []
step {n} {t} (p ∷ ps) next0 = code_table (Context.next p) p ( λ code np → next0 (update-context ps np ++ ( record np { next = code } ∷ [] )))  where
    update-context : List Context → Context  → List Context 
    update-context [] _ = []
    update-context (c1 ∷ t) np = ? -- record c1 { memory = Context.memory np  ; mbase = Context.mbase np } ∷ t

init-context : Context
init-context = record {
      next = CC_nop
    ; fail = CC_nop
    -- ; c_Phil-API = ?
    -- ; c_AtomicNat-API = record { next = CC_nop ; fail = CC_nop ; value = 0 ; impl = init-AtomicNat } 
    ; mbase = 0
    -- ; memory = ?
    ; error = ?
    ; fail_next = CC_nop
  }

alloc-data : {n : Level} {t : Set n} → ( c : Context ) → ( Context → ℕ → t ) → t
alloc-data {n} {t} c next = next record c { mbase =  suc ( Context.mbase c ) } mnext  where
     mnext = suc ( Context.mbase c )

new-data : {n : Level} {t : Set n} → ( c : Context ) → (ℕ → Data ) → ( Context → ℕ → t ) → t
new-data  c x next  = alloc-data c $ λ c1 n → ? -- insertTree (Context.memory c1) n (x n) ( λ bt → next record c1 { memory = bt } n )

init-AtomicNat0 :  {n : Level} {t : Set n} → Context  → ( Context →  ℕ → t ) → t
init-AtomicNat0 c1  next = ?

add< : { i : ℕ } (j : ℕ ) → i < suc i + j
add<  {i} j = begin
        suc i ≤⟨ m≤m+n (suc i) j ⟩
        suc i + j ∎  where open ≤-Reasoning

nat-<> : { x y : ℕ } → x < y → y < x → ⊥
nat-<> {x} {y} x<y y<x with <-cmp x y
... | tri< a ¬b ¬c = ⊥-elim ( ¬c y<x )
... | tri≈ ¬a b ¬c = ⊥-elim ( ¬c y<x )
... | tri> ¬a ¬b c = ⊥-elim ( ¬a x<y )

nat-≤> : { x y : ℕ } → x ≤ y → y < x → ⊥
nat-≤> {x} {y} x≤y y<x with <-cmp x y
... | tri< a ¬b ¬c = ⊥-elim ( ¬c y<x )
... | tri≈ ¬a b ¬c = ⊥-elim ( ¬c y<x )
... | tri> ¬a ¬b c = ?


nat-<≡ : { x : ℕ } → x < x → ⊥
nat-<≡  {x} x<x with <-cmp x x
... | tri< a ¬b ¬c = ⊥-elim ( ¬c x<x )
... | tri≈ ¬a b ¬c = ⊥-elim ( ¬c x<x )
... | tri> ¬a ¬b c = ⊥-elim ( ¬a x<x )

nat-≡< : { x y : ℕ } → x ≡ y → x < y → ⊥
nat-≡< refl lt = nat-<≡ lt

lemma3 : {i j : ℕ} → 0 ≡ i → j < i → ⊥
lemma3 refl ()
lemma5 : {i j : ℕ} → i < 1 → j < i → ⊥
lemma5 {i} {j} i<1 j<i with <-cmp j i
... | tri< a ¬b ¬c = ⊥-elim ( ¬c ? )
... | tri≈ ¬a b ¬c = ⊥-elim  (¬a j<i )
... | tri> ¬a ¬b c = ⊥-elim ( ¬a j<i )

¬x<x : {x : ℕ} → ¬ (x < x)
¬x<x x<x = ?

TerminatingLoopS : {l m : Level} {t : Set l} (Index : Set m ) → {Invraiant : Index → Set m } → ( reduce : Index → ℕ)
   → (r : Index) → (p : Invraiant r)
   → (loop : (r : Index)  → Invraiant r → (next : (r1 : Index)  → Invraiant r1 → reduce r1 < reduce r  → t ) → t) → t
TerminatingLoopS {_} {_} {t} Index {Invraiant} reduce r p loop with <-cmp 0 (reduce r)
... | tri≈ ¬a b ¬c = loop r p (λ r1 p1 lt → ⊥-elim (lemma3 b lt) )
... | tri< a ¬b ¬c = loop r p (λ r1 p1 lt1 → TerminatingLoop1 (reduce r) r r1 (m≤n⇒m≤1+n lt1) p1 lt1 ) where
    TerminatingLoop1 : (j : ℕ) → (r r1 : Index) → reduce r1 < suc j  → Invraiant r1 →  reduce r1 < reduce r → t
    TerminatingLoop1 zero r r1 n≤j p1 lt = loop r1 p1 (λ r2 p1 lt1 → ⊥-elim (lemma5 n≤j lt1))
    TerminatingLoop1 (suc j) r r1  n≤j p1 lt with <-cmp (reduce r1) (suc j)
    ... | tri< a ¬b ¬c = TerminatingLoop1 j r r1 a p1 lt
    ... | tri≈ ¬a b ¬c = loop r1 p1 (λ r2 p2 lt1 → TerminatingLoop1 j r1 r2 (subst (λ k → reduce r2 < k ) b lt1 ) p2 lt1 )
    ... | tri> ¬a ¬b c =  ⊥-elim ( nat-≤> c n≤j )

-- loop exexution

-- concurrnt execution

-- state db ( binary tree of processes )

-- depth first execution

-- verify temporal logic poroerries



