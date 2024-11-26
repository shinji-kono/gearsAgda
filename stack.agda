open import Level renaming (suc to succ ; zero to Zero )
module stack  where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Data.Nat hiding (compare)
open import Data.Maybe

ex : 1 + 2 ≡ 3
ex = refl

-- data Bool {n : Level } : Set n where
--   True  : Bool
--   False : Bool

-- record _∧_ {n : Level } (a : Set n) (b : Set n): Set n where
--   field
--     pi1 : a
--     pi2 : b

-- data _∨_ {n : Level } (a : Set n) (b : Set n): Set n where
--    pi1  : a -> a ∨ b
--    pi2  : b -> a ∨ b

-- data Maybe {n : Level } (a : Set n) : Set n where
--   nothing : Maybe a
--   just    : a -> Maybe a

record StackMethods {n m : Level } (a : Set n ) {t : Set m } (stackImpl : Set n ) : Set (m Level.⊔ n) where
  field
    push : stackImpl -> a -> (stackImpl -> t) -> t
    pop  : stackImpl -> (stackImpl -> Maybe a -> t) -> t
    pop2 : stackImpl -> (stackImpl -> Maybe a -> Maybe a -> t) -> t
    get  : stackImpl -> (stackImpl -> Maybe a -> t) -> t
    get2 : stackImpl -> (stackImpl -> Maybe a -> Maybe a -> t) -> t
    clear : stackImpl -> (stackImpl -> t) -> t 
open StackMethods

record Stack {n m : Level } (a : Set n ) {t : Set m } (si : Set n ) : Set (m Level.⊔ n) where
  field
    stack : si
    stackMethods : StackMethods {n} {m} a {t} si
  pushStack :  a -> (Stack a si -> t) -> t
  pushStack d next = push (stackMethods ) (stack ) d (\s1 -> next (record {stack = s1 ; stackMethods = stackMethods } ))
  popStack : (Stack a si -> Maybe a  -> t) -> t
  popStack next = pop (stackMethods ) (stack ) (\s1 d1 -> next (record {stack = s1 ; stackMethods = stackMethods }) d1 )
  pop2Stack :  (Stack a si -> Maybe a -> Maybe a -> t) -> t
  pop2Stack next = pop2 (stackMethods ) (stack ) (\s1 d1 d2 -> next (record {stack = s1 ; stackMethods = stackMethods }) d1 d2)
  getStack :  (Stack a si -> Maybe a  -> t) -> t
  getStack next = get (stackMethods ) (stack ) (\s1 d1 -> next (record {stack = s1 ; stackMethods = stackMethods }) d1 )
  get2Stack :  (Stack a si -> Maybe a -> Maybe a -> t) -> t
  get2Stack next = get2 (stackMethods ) (stack ) (\s1 d1 d2 -> next (record {stack = s1 ; stackMethods = stackMethods }) d1 d2)
  clearStack : (Stack a si -> t) -> t
  clearStack next = clear (stackMethods ) (stack ) (\s1 -> next (record {stack = s1 ; stackMethods = stackMethods } ))

open Stack

{--
data Element {n : Level } (a : Set n) : Set n where
  cons : a -> Maybe (Element a) -> Element a


datum : {n : Level } {a : Set n} -> Element a -> a
datum (cons a _) = a

next : {n : Level } {a : Set n} -> Element a -> Maybe (Element a)
next (cons _ n) = n
--}


-- cannot define recrusive record definition. so use linked list with maybe.
record Element {l : Level} (a : Set l) : Set l where
  inductive
  constructor cons
  field
    datum : a  -- `data` is reserved by Agda.
    next : Maybe (Element a)

open Element


record SingleLinkedStack {n : Level } (a : Set n) : Set n where
  field
    top : Maybe (Element a)
open SingleLinkedStack

pushSingleLinkedStack : {n m : Level } {t : Set m } {Data : Set n} -> SingleLinkedStack Data -> Data -> (Code : SingleLinkedStack Data -> t) -> t
pushSingleLinkedStack stack datum next = next stack1
  where
    element = cons datum (top stack)
    stack1  = record {top = just element}


popSingleLinkedStack : {n m : Level } {t : Set m } {a  : Set n} -> SingleLinkedStack a -> (Code : SingleLinkedStack a -> (Maybe a) -> t) -> t
popSingleLinkedStack stack cs with (top stack)
...                                | nothing = cs stack  nothing
...                                | just d  = cs stack1 (just data1)
  where
    data1  = datum d
    stack1 = record { top = (next d) }

pop2SingleLinkedStack : {n m : Level } {t : Set m } {a  : Set n} -> SingleLinkedStack a -> (Code : SingleLinkedStack a -> (Maybe a) -> (Maybe a) -> t) -> t
pop2SingleLinkedStack {n} {m} {t} {a} stack cs with (top stack)
...                                | nothing = cs stack nothing nothing
...                                | just d = pop2SingleLinkedStack' {n} {m} stack cs
  where
    pop2SingleLinkedStack' : {n m : Level } {t : Set m }  -> SingleLinkedStack a -> (Code : SingleLinkedStack a -> (Maybe a) -> (Maybe a) -> t) -> t
    pop2SingleLinkedStack' stack cs with (next d)
    ...              | nothing = cs stack nothing nothing
    ...              | just d1 = cs (record {top = (next d1)}) (just (datum d)) (just (datum d1))
    

getSingleLinkedStack : {n m : Level } {t : Set m } {a  : Set n} -> SingleLinkedStack a -> (Code : SingleLinkedStack a -> (Maybe a) -> t) -> t
getSingleLinkedStack stack cs with (top stack)
...                                | nothing = cs stack  nothing
...                                | just d  = cs stack (just data1)
  where
    data1  = datum d

get2SingleLinkedStack : {n m : Level } {t : Set m } {a  : Set n} -> SingleLinkedStack a -> (Code : SingleLinkedStack a -> (Maybe a) -> (Maybe a) -> t) -> t
get2SingleLinkedStack {n} {m} {t} {a} stack cs with (top stack)
...                                | nothing = cs stack nothing nothing
...                                | just d = get2SingleLinkedStack' {n} {m} stack cs
  where
    get2SingleLinkedStack' : {n m : Level} {t : Set m } -> SingleLinkedStack a -> (Code : SingleLinkedStack a -> (Maybe a) -> (Maybe a) -> t) -> t
    get2SingleLinkedStack' stack cs with (next d)
    ...              | nothing = cs stack nothing nothing
    ...              | just d1 = cs stack (just (datum d)) (just (datum d1))

clearSingleLinkedStack : {n m : Level } {t : Set m } {a : Set n} -> SingleLinkedStack a -> (SingleLinkedStack a -> t) -> t
clearSingleLinkedStack stack next = next (record {top = nothing})


emptySingleLinkedStack : {n : Level } {a : Set n} -> SingleLinkedStack a
emptySingleLinkedStack = record {top = nothing}

-----
-- Basic stack implementations are specifications of a Stack
--
singleLinkedStackSpec : {n m : Level } {t : Set m } {a : Set n} -> StackMethods {n} {m} a {t} (SingleLinkedStack a)
singleLinkedStackSpec = record {
                                   push = pushSingleLinkedStack
                                 ; pop  = popSingleLinkedStack
                                 ; pop2 = pop2SingleLinkedStack
                                 ; get  = getSingleLinkedStack
                                 ; get2 = get2SingleLinkedStack
                                 ; clear = clearSingleLinkedStack
                           }

createSingleLinkedStack : {n m : Level } {t : Set m } {a : Set n} -> Stack {n} {m} a {t} (SingleLinkedStack a)
createSingleLinkedStack = record {
                             stack = emptySingleLinkedStack ;
                             stackMethods = singleLinkedStackSpec 
                           }

