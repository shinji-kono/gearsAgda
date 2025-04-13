{-# OPTIONS --cubical-compatible #-}
-- {-# OPTIONS --cubical-compatible --safe #-}
module DPP where

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

open import ModelChecking


--
-- single process implemenation
--


record Phil  : Set  where
   field 
      ptr : ℕ
      left right : AtomicNat

init-Phil : Phil
init-Phil = record { ptr = 0 ; left = init-AtomicNat ; right = init-AtomicNat }

pickup_rfork : {n : Level} {t : Set n} → Phil → ( Phil → t ) → t
pickup_lfork : {n : Level} {t : Set n} → Phil → ( Phil → t ) → t
eating : {n : Level} {t : Set n} → Phil → ( Phil → t ) → t
putdown_rfork : {n : Level} {t : Set n} → Phil → ( Phil → t ) → t
putdown_lfork : {n : Level} {t : Set n} → Phil → ( Phil → t ) → t
thinking : {n : Level} {t : Set n} → Phil → ( Phil → t ) → t

pickup_rfork p next = f_set (Phil.right p) (Phil.ptr p) ( λ f → pickup_lfork record p { right = f } next )
pickup_lfork p next = f_set (Phil.left p) (Phil.ptr p) ( λ f → eating record p { left = f } next )
eating p next = putdown_rfork p next
putdown_rfork p next = f_set (Phil.right p) 0 ( λ f → putdown_lfork record p { right = f } next )
putdown_lfork p next = f_set (Phil.left p) 0 ( λ f → thinking record p { left = f } next )
thinking p next = next p

run : Phil
run = pickup_rfork record { ptr = 1 ; left = record { ptr = 2 ; value = 0 } ; right = record { ptr = 3 ; value = 0 } } $ λ p → p

--
-- Coda Gear
--

data Code : Set  where
   C_nop : Code
   C_cas_int : Code
   C_putdown_rfork : Code 
   C_putdown_lfork : Code 
   C_thinking : Code 
   C_pickup_rfork : Code 
   C_pickup_lfork : Code 
   C_eating : Code 

--
-- all possible arguments in -APIs
--

record Phil-API : Set  where
   field 
      next : Code
      impl : Phil

--
-- Data Gear
--
--      waiting / pointer / available
--
data Data : Set where
   -- D_AtomicNat :  AtomicNat → ℕ → Data
   D_AtomicNat :  AtomicNat → Data
   D_Phil :      Phil → Data
   D_Error :      Error → Data

-- data API : Set where
--    A_AtomicNat :  AtomicNat-API → API
--    A_Phil :      Phil-API → API

-- open import hoareBinaryTree

data bt {n : Level} (A : Set n) : Set n where
  leaf : bt A
  node :  (key : ℕ) → (value : A) →
    (left : bt A ) → (right : bt A ) → bt A

updateTree : {n m : Level} {A : Set n} {t : Set m} → (tree : bt A) → (key : ℕ) → (value : A) → (empty : bt A → t ) → (next : A → bt A  → t ) → t
updateTree = ?

insertTree : {n m : Level} {A : Set n} {t : Set m} → (tree : bt A) → (key : ℕ) → (value : A) → (next : bt A → t ) → t
insertTree = ?


--
-- second level stub
--

-- putdown_rfork : Phil → (? → t) → t
-- putdown_rfork p next = goto p->lfork->cas( 0 , putdown_lfork, putdown_lfork ) , next

Phil_putdown_rfork_sub : {n : Level} {t : Set n} → Context  → ( Code → Context → t ) → t
Phil_putdown_rfork_sub c next = next C_cas_int record c {
    c_AtomicNat-API = record { impl = Phil.right phil ; value =  0 ; fail = C_putdown_lfork ; next = C_putdown_lfork } }  where
    phil : Phil
    phil = Phil-API.impl ( Context.c_Phil-API c )

Phil_putdown_lfork_sub : {n : Level} {t : Set n} → Context  → ( Code → Context → t ) → t
Phil_putdown_lfork_sub c next = next C_cas_int record c { 
    c_AtomicNat-API = record { impl = Phil.left phil ; value =  0 ; fail = C_thinking ; next = C_thinking } }  where
    phil : Phil
    phil = Phil-API.impl ( Context.c_Phil-API c )

Phil_thiking : {n : Level} {t : Set n} → Context  → ( Code → Context → t ) → t
Phil_thiking c next = next C_pickup_rfork c  

Phil_pickup_lfork_sub : {n : Level} {t : Set n} → Context  → ( Code → Context → t ) → t
Phil_pickup_lfork_sub c next = next C_cas_int record c { 
    c_AtomicNat-API = record { impl = Phil.left phil ; value =  Phil.ptr phil ; fail = C_pickup_lfork ; next = C_pickup_rfork } }  where
    phil : Phil
    phil = Phil-API.impl ( Context.c_Phil-API c )

Phil_pickup_rfork_sub : {n : Level} {t : Set n} → Context  → ( Code → Context → t ) → t
Phil_pickup_rfork_sub c next = next C_cas_int record c { 
    c_AtomicNat-API = record { impl = Phil.left phil ; value =  Phil.ptr phil ; fail = C_pickup_rfork ; next = C_eating } }  where
    phil : Phil
    phil = Phil-API.impl ( Context.c_Phil-API c )

Phil_eating_sub : {n : Level} {t : Set n} → Context  → ( Code → Context → t ) → t
Phil_eating_sub c next =  next C_putdown_rfork c 

code_table :  {n : Level} {t : Set n} → Code → Context → ( Code → Context → t) → t
code_table C_nop  = λ c  next  → next C_nop c
code_table C_cas_int  = AtomicInt_cas_stub
code_table C_putdown_rfork = Phil_putdown_rfork_sub
code_table C_putdown_lfork = Phil_putdown_lfork_sub
code_table C_thinking = Phil_thiking
code_table C_pickup_rfork = Phil_pickup_lfork_sub
code_table C_pickup_lfork = Phil_pickup_rfork_sub
code_table C_eating = Phil_eating_sub


init-Phil-0 : (ps : List Context) → (left right : AtomicNat ) → List Context
init-Phil-0 ps left right = new-data (c1 ps) ( λ ptr → D_Phil (p ptr) )  $ λ c ptr → record c { c_Phil-API = record { next = C_thinking ; impl = p ptr }} ∷ ps where
    p : ℕ → Phil
    p ptr = record  init-Phil { ptr = ptr ; left = left ; right = right }  
    c1 :  List Context → Context
    c1 [] =  init-context
    c1 (c2 ∷ ct) =  c2

init-AtomicNat1 :  {n : Level} {t : Set n} → Context  → ( Context →  AtomicNat → t ) → t
init-AtomicNat1 c1  next = new-data c1  ( λ ptr → D_AtomicNat (a ptr) ) $ λ c2 ptr → next c2 (a ptr) where
    a : ℕ → AtomicNat
    a ptr = record { ptr = ptr ; value = 0 }

init-Phil-1 : (c1 : Context) → Context
init-Phil-1 c1 = record c1 { memory = mem2 $ mem1 $ mem ; mbase = n + 3 } where
   n : ℕ
   n = Context.mbase c1
   left  = record { ptr = suc n ; value = 0}
   right = record { ptr = suc (suc n) ; value = 0}
   mem : bt Data
   mem = insertTree ( Context.memory c1) (suc n) (D_AtomicNat left)
      $ λ t →  t
   mem1 : bt Data → bt Data
   mem1 t = insertTree t (suc (suc n)) (D_AtomicNat right )
      $ λ t →  t
   mem2 : bt Data → bt Data
   mem2 t = insertTree t (n + 3) (D_Phil record { ptr = n + 3 ; left = left ; right = right })  
      $ λ t →  t
     
test-i0 : bt Data
test-i0 =  Context.memory (init-Phil-1 init-context)

make-phil : ℕ → Context
make-phil zero = init-context
make-phil (suc n) = init-Phil-1 ( make-phil n )

test-i5 : bt Data
test-i5 =  Context.memory (make-phil 5)

-- loop exexution

-- concurrnt execution

-- state db ( binary tree of processes )

-- depth first execution

-- verify temporal logic poroerries



